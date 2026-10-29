/-
  * LinuxProcessSem.Checks.Sys.Kernel.Sys — the getpid (172), gettid (178), setsid (157),
    uname (160), prlimit64 (261), prctl (167) checkers, and the id readers
    and setters (getuid/geteuid/getgid/getegid, setuid/setgid,
    setresuid/setresgid), and their proofs

  Answers to Linux [kernel/sys.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`).  Lengths are compared as `Int`
  (`((…).length : Int)`), `andb`/`orb` are `&&`/`||`, and a `Bool`-valued
  comparison `a < b` is spelled that way in an `if` and `decide (a < b)`
  where a `Bool` is wanted.  An effect literal is the anonymous constructor
  pattern `⟨r, [], [], [], [], []⟩`; a singleton write ledger
  `((a, bs) :: nil)` is the list literal `[(a, bs)]`; and the copy-in
  ledger's length field is a `Nat` (`access_ranges_eqb`), so `16` is plain
  `16`.

  The four obligations per checker are proved as follows:

  * the spec's leading `get_model` reader is peeled with `bind_getModel`
    (rewrite `bind getModel k i m o` to `k m i m o` in one go), and `input`
    with `input_bind_ok_inv` / `get_model_bind_ok_inv`
    (`Checks.Sys.Prelude`);
  * an effect's five payload lists are knocked out with
    `cases … <;> cases … <;> simp only [check_x] at H`, and the dead shapes
    closed with `exact nomatch H`;
  * branch tests are split with `by_cases h : <test> = true` and the branch
    taken with `rw [ite_eq_left h]` / `rw [ite_eq_right h]`; for a `Bool` test the
    negation is `ite_eq_right (by simp [h])`, because Lean's `if` on a `Bool` is
    an `if` on `b = true`;
  * monadic bodies are inverted with explicit `obtain`/`bind_ok` steps,
    since `inv_ok` deliberately stops at constructor injectivities and one
    conjunction (`Checks.Sys.Prelude`'s note).

  A `SysSpec` is a FUNCTION, so a spec that opens with a branch test is an
  `if` at function type, and `by_cases` — which normalises its goal — would
  try to reduce it.  Every proof whose conclusion mentions a spec therefore
  `generalize`s that conclusion into a local `Q : Prop` first, splits
  against `Q` (an opaque variable, so nothing reduces), and rewrites `Q`
  back with `rw [← hP]` at the leaves.  This is the same device
  `Checks/Sys/Kernel/Groups.lean` documents.

  Eleven steps performed inline elsewhere are named, proved once and used by
  the proofs below; they add no public surface:

  * `tid_match_of` — the checker's tid test, read as the spec's `choose`
    predicate (`cases` rewrites the hypothesis, so the equation is pushed in
    with `simpa only [hm]`);
  * `modify_modify_ret_only_inv` / `modify_pure_inv` /
    `set_creds_ret_only_ok` — invert the deterministic
    `modify ;; modify ;; ret_only(pure)` tails of `setsid_spec`,
    `uname_spec`, `prlimit64_spec` and the id setters;
  * `modify_modify_ret_only_no_unmodeled` / `modify_pure_no_unmodeled` /
    `set_creds_ret_only_no_unmodeled` / `errno_from_err_ret_no_unmodeled` —
    the same tails never decline, which closes the fail-closed directions of
    the credential setters;
  * `errno_from_err_ret_ok_inv` — invert `errno_from errs ;; err_ret`;
  * `check_setid_no_unmodeled` / `check_setresid_no_unmodeled` — the two
    credential acceptors are total, so their `sound_unmodeled` directions
    are vacuous.  (Lean has no `match goal`, so these branches are named
    rather than split by a tactic.)

  ORDERING NOTE.  The four credential checkers are declared in the
  definitions section at the head of the file rather than after the
  `prlimit64` proofs, because the sixteen credential obligations that follow
  use them.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Fork
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sys

namespace LinuxSem.Checks.Sys.Kernel.Sys

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Fork

/-! ## getpid and gettid -/

/-- getpid: the SAME check as [check_set_tid_address], because
    [Kernel.Sys.getpid_spec] is the same relation — see the argument there.
    Sharing the checker keeps the two calls from drifting apart in the
    executable model the way sharing the spec does in the relational
    one. -/
def check_getpid : SyscallEffect → Model → check_result :=
  check_set_tid_address

/-- gettid: the SAME check again, and for a shorter reason than
    [check_getpid]'s — [Kernel.Sys.gettid_spec] is
    [Fork.set_tid_address_spec] because the two syscalls return the same
    expression, with no thread-group-leader side condition in between
    (see the argument there). -/
def check_gettid : SyscallEffect → Model → check_result :=
  check_set_tid_address

/-! ## setsid (157) -/

/-- setsid: no writes.  -EPERM is always admissible — the model does
    not track what would make it fail, and a failure records nothing,
    because a kernel that refused one call can allow the next.  A
    session id is admissible only while no setsid has SUCCEEDED, and
    only in the tid envelope, agreeing with any tid already observed.
    The two are disjoint on the observed return for every [Model]:
    [errno_ret EPERM] is [-1] read unsigned, far above
    [PID_MAX_ENVELOPE].  See [Kernel.Sys.setsid_spec]. -/
def check_setsid (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if bv_eqb ret (errno_ret EPERM) then .CheckOk m []
      else if m_setsid_succeeded m then .CheckReject
      else if (decide (0 < (ret.toNat : Int)) &&
              decide ((ret.toNat : Int) < PID_MAX_ENVELOPE) &&
              (match m_tid m with
               | none => true
               | some t0 => bv_eqb ret t0))
      then .CheckOk (with_setsid_succeeded (with_tid ret m)) []
      else .CheckReject
  | _ => .CheckReject

/-! ## prlimit64 (261) -/

/-- The READ arm's effect shape, split out so the fail-closed direction
    has something to point at: this answers [CheckOk] or [CheckReject]
    and NEVER [CheckUnmodeled], exactly as [check_getrandom_zero] does
    for its arm.  [bs0] is [m_rlimit_core]: [Some] once the limit is
    pinned, in which case the delivered bytes must be exactly it, and
    [None] before, in which case any well-formed pair is admissible and
    becomes the pin. -/
def check_rlim64_read (old_rlim : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨r, [(a, bs)], [], [], [], []⟩ =>
      if !(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a old_rlim) then
        .CheckReject
      else
        match bs0 with
        | some b0 => if listN_eqb bs b0 then .CheckOk m [] else .CheckReject
        | none =>
            if rlim64_wf bs then .CheckOk (with_rlimit_core bs m) [] else .CheckReject
  | _ => .CheckReject

/-- prlimit64: [Kernel.Sys.prlimit64_spec] carries the argument — why only
    [RLIMIT_CORE], why only pid 0, and why exactly one of the two
    pointers may be non-NULL.  This mirrors its branch structure one for
    one.  The read's ledger entry is the 16 bytes of the [struct
    rlimit64] at [old_rlim]: once the limit is pinned it must be exactly
    the recorded bytes, and before it is pinned any well-formed pair is
    admissible and becomes the pin. -/
def check_prlimit64 (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(w_is0 pid) then .CheckUnmodeled
  else if (resource.toNat : Int) ≠ RLIMIT_CORE then .CheckUnmodeled
  else if (w_is0 new_rlim && w_is0 old_rlim) then .CheckUnmodeled
  else if (!(w_is0 new_rlim) && !(w_is0 old_rlim)) then .CheckUnmodeled
  else if w_is0 new_rlim then
    match read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
    | none =>
        if !(access_okb old_rlim 16) then check_ret_only eff (errno_ret EFAULT) m []
        else .CheckUnmodeled
    | some _ => check_rlim64_read old_rlim (m_rlimit_core m) eff m
  else
    match m_rlimit_core m with
    | none => .CheckUnmodeled
    | some bs0 =>
        match read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
        | none =>
            if !(access_okb new_rlim 16) then check_ret_only eff (errno_ret EFAULT) m []
            else .CheckUnmodeled
        | some nb =>
            if (rlim64_hard nb).toNat < (rlim64_soft nb).toNat then
              check_ret_only_copyins [(new_rlim, 16)] eff (errno_ret EINVAL) m []
            else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then
              .CheckUnmodeled
            else
              check_ret_only_copyins [(new_rlim, 16)] eff (BitVec.ofInt 64 0)
                (with_rlimit_core nb m) []

/-! ## uname (160) -/

/-- uname: the copy-out arm, split out for the same reason
    [check_rlim64_read] is — it answers [CheckOk] or [CheckReject] and
    never [CheckUnmodeled], which is what the fail-closed direction
    points at.  [bs0] is [m_utsname]: [Some] once the name is pinned, in
    which case the delivered bytes must be exactly it, and [None] before,
    in which case any buffer inside [utsname_wf]'s envelope is admissible
    and becomes the pin. -/
def check_uname_copy (name : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨r, [(a, bs)], [], [], [], []⟩ =>
      if !(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a name) then
        .CheckReject
      else
        match bs0 with
        | some b0 => if listN_eqb bs b0 then .CheckOk m [] else .CheckReject
        | none =>
            if utsname_wf bs then .CheckOk (with_utsname bs m) [] else .CheckReject
  | _ => .CheckReject

/-- uname: [Kernel.Sys.uname_spec] carries the argument — why the
    390-byte range is one gate rather than six, and why a range
    [access_ok] admits but memory does not wholly back is a decline
    rather than an -EFAULT.  This mirrors its branch structure one for
    one. -/
def check_uname (i : SyscallInput) (name : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(access_okb name NEW_UTSNAME_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none => .CheckUnmodeled
    | some _ => check_uname_copy name (m_utsname m) eff m

/-! ## prctl (167) -/

/-- prctl: [Kernel.Sys.prctl_spec] carries the whole argument -- why
    only [PR_CAPBSET_READ], why its answer is the constant 1 rather than
    a choice, and why every other option declines.  This mirrors its
    three branches one for one.  TOTAL ON ITS OWN OPTION: once the
    option is [PR_CAPBSET_READ] this answers [CheckOk] or [CheckReject]
    and never [CheckUnmodeled], so the decline is a fact about the
    OPTION and about nothing else.  `Checks/ProcessCreation.lean` pins
    [prctl_modeled_options] with `prctl_modeled_options_are`, so the
    closed-list reading is a THEOREM, not the spec's own prose.  What this
    file adds on top is the TOTALITY above. -/
def check_prctl (option_ arg2 : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if (option_.toNat : Int) ≠ PR_CAPBSET_READ then .CheckUnmodeled
  else if CAP_LAST_CAP < (arg2.toNat : Int)
  then check_ret_only eff (errno_ret EINVAL) m []
  else check_ret_only eff (BitVec.ofInt 64 1) m []

/-! ## The credentials -/

/-- [getuid] (174), [geteuid] (175), [getgid] (176), [getegid] (177):
    the stored id and nothing else.  TOTAL — there is no argument to
    reject and no allocation to fail, so this acceptor never declines
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/sys.c,
    [SYSCALL_DEFINE0(getuid)] and its three siblings). -/
def check_getid (sel : Creds → word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (sel (m_creds m)) m []

/-- The shape every fallible id-setter branch shares: the observation is
    admissible if it is an injectable errno from [errs], which leaves the
    model alone, or the branch's own answer [r], which steps the model to
    [mR]. -/
def check_setid_result (errs : List Int) (r : word) (mR : Model)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in errs ret then .CheckOk m []
      else if bv_eqb ret r then .CheckOk mR [] else .CheckReject
  | _ => .CheckReject

/-- [setuid] (146) and [setgid] (144), over the triple [get] reads and
    [put] writes; [user] is what admits -EAGAIN (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/sys.c, [__sys_setuid] /
    [__sys_setgid]).  The tests are in the kernel's order: [(uid_t)-1]
    is -EINVAL before anything is allocated, then the privileged
    transition that moves all three ids, then the unprivileged one that
    moves only the effective id and answers -EPERM for any other target.
    TOTAL — every branch answers, so this acceptor never declines. -/
def check_setid (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let c := m_creds m
  let t := get c
  if bv_eqb v ID_MINUS_ONE then check_ret_only eff (errno_ret EINVAL) m []
  else if creds_privileged c then
    check_setid_result (setid_errnos (user && !(bv_eqb v t.id_real)))
      (BitVec.ofInt 64 0) (with_creds (put (IdTriple.mkIdTriple v v v) c) m) eff m
  else if bv_eqb v t.id_real || bv_eqb v t.id_saved then
    check_setid_result (setid_errnos false) (BitVec.ofInt 64 0)
      (with_creds (put (IdTriple.mkIdTriple t.id_real v t.id_saved) c) m) eff m
  else
    check_setid_result (setid_errnos false) (errno_ret EPERM) m eff m

/-- [setresuid] (147) and [setresgid] (149), the same way
    (Linux v6.18.46, commit 1f99e9ab748f, kernel/sys.c,
    [__sys_setresuid] / [__sys_setresgid]).  [(uid_t)-1] in a position
    means leave that id alone; a call that asks for nothing returns 0
    before any allocation;
    a call that would install an id the process does not already hold
    needs privilege, and is refused -EPERM before [prepare_creds], so
    that refusal can never answer -ENOMEM.  TOTAL for the same reason as
    [check_setid]. -/
def check_setresid (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  let c := m_creds m
  let t := get c
  let pick (a : word) (cur : word) := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then
    check_ret_only eff (BitVec.ofInt 64 0) m []
  else
    let is_old (x : word) :=
      bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged c) then
      check_ret_only eff (errno_ret EPERM) m []
    else
      check_setid_result (setid_errnos (user && !(bv_eqb nr t.id_real)))
        (BitVec.ofInt 64 0) (with_creds (put (IdTriple.mkIdTriple nr ne ns) c) m) eff m

/- =========================================================================
   Private helpers

   The two inversions below are the steps performed inline elsewhere.
   Neither leaves this file.
   ========================================================================= -/

/-- The checker's tid test, read as the spec's [choose] predicate: a
    matching [bv_eqb] means the observed return IS the recorded tid.
    (footgun (c): `cases` on `m_tid` rewrites the hypothesis,
    so the equation has to be pushed in with `simpa only [hm]`). -/
theorem tid_match_of (m : Model) (r : word)
    (h : (match m_tid m with
          | none => true
          | some t0 => bv_eqb r t0) = true) :
    match m_tid m with
    | none => True
    | some t0 => r = t0 := by
  cases hm : m_tid m with
  | none => trivial
  | some t0 => exact (Fs.bv_eqb_eq r t0).mp (by simpa only [hm] using h)

/-- Invert `modify f ;; modify g ;; ret_only r`: the effect is the single
    return [r], the model is [g (f m)], and nothing is emitted.
    The two-write form of `Checks.Sys.Kernel.Fork`'s
    `seqSpec_modify_ret_only_inv`. -/
theorem modify_modify_ret_only_inv (f g : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (modify f) (fun _ => bind (modify g) (fun _ => ret_only r)) i m
          (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = g (f m) ∧ evs = [] := by
  obtain ⟨u1, m1, evs1, evs2, hf, hrest, hevs⟩ := H
  cases hf
  obtain ⟨u2, m2, evs3, evs4, hg, hr, hevs2⟩ := hrest
  cases hg
  cases hr
  simp only [List.nil_append] at hevs hevs2
  subst hevs2
  exact ⟨rfl, rfl, hevs⟩

/-- ...and that the same two writes followed by a `ret_only` never
    decline: a state write and a `pure` both answer. -/
theorem modify_modify_ret_only_no_unmodeled (f g : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ bind (modify f) (fun _ => bind (modify g) (fun _ => ret_only r)) i m .unmodeled := by
  intro H
  rcases H with h | ⟨u1, m1, evs1, h1, h2⟩
  · simp only [LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · rcases h2 with h2 | ⟨u2, m2, evs2, h3, h4⟩
    · simp only [LinuxSem.LinuxProcessSem.modify] at h2
      exact nomatch h2
    · simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at h4
      exact nomatch h4

/-- Invert `modify f ;; pure e`: the effect is [e], the model is [f m], and
    nothing is emitted. -/
theorem modify_pure_inv (f : Model → Model) (eff0 : SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (modify f) (fun _ => pure eff0) i m (.ok eff m' evs)) :
    eff = eff0 ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m1, evs1, evs2, hm, hp, hevs⟩ := H
  cases hm
  cases hp
  simp only [List.nil_append] at hevs
  exact ⟨rfl, rfl, hevs⟩

/-- ...and that the same write followed by a `pure` never declines. -/
theorem modify_pure_no_unmodeled (f : Model → Model) (eff0 : SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ (bind (M := Model) (I := SyscallInput) (E := event)
        (modify f) (fun _ => pure eff0) i m .unmodeled) := by
  intro H
  rcases H with h | ⟨u, m1, evs1, h1, h2⟩
  · simp only [LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · simp only [LinuxSem.LinuxProcessSem.pure] at h2
    exact nomatch h2

/- =========================================================================
   prctl (167): the four obligations, over its own option only
   ========================================================================= -/

theorem check_prctl_sound_ok (option_ arg2 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_prctl option_ arg2 eff m = .CheckOk m' evs) :
    prctl_spec option_ arg2 i m (.ok eff m' evs) := by
  generalize hP : (prctl_spec option_ arg2 i m (.ok eff m' evs)) = Q at *
  simp only [check_prctl] at H
  by_cases ho : (option_.toNat : Int) ≠ PR_CAPBSET_READ
  · simp only [ite_eq_left ho] at H
    exact nomatch H
  · simp only [ite_eq_right ho] at H
    by_cases hc : CAP_LAST_CAP < (arg2.toNat : Int)
    · simp only [ite_eq_left hc] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [← hP]
      simp only [prctl_spec, ite_eq_right ho, ite_eq_left hc, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hc] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (BitVec.ofInt 64 1) m [] m' evs).mp H
      rw [← hP]
      simp only [prctl_spec, ite_eq_right ho, ite_eq_right hc, ret_only,
        LinuxSem.LinuxProcessSem.pure]

/-- The option test is the ONLY thing that declines, so a
    [CheckUnmodeled] forces the same branch in the spec. -/
theorem check_prctl_sound_unmodeled (option_ arg2 : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_prctl option_ arg2 eff m = .CheckUnmodeled) :
    prctl_spec option_ arg2 i m .unmodeled := by
  generalize hP : (prctl_spec option_ arg2 i m .unmodeled) = Q at *
  simp only [check_prctl] at H
  by_cases ho : (option_.toNat : Int) ≠ PR_CAPBSET_READ
  · simp only [ite_eq_left ho] at H
    rw [← hP]
    simp only [prctl_spec, ite_eq_left ho, unmodeled]
  · simp only [ite_eq_right ho] at H
    by_cases hc : CAP_LAST_CAP < (arg2.toNat : Int)
    · simp only [ite_eq_left hc] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · simp only [ite_eq_right hc] at H
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 1) m [])

theorem check_prctl_complete_ok (option_ arg2 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : prctl_spec option_ arg2 i m (.ok eff m' evs)) :
    check_prctl option_ arg2 eff m = .CheckOk m' evs := by
  generalize hP : (check_prctl option_ arg2 eff m = .CheckOk m' evs) = Q at *
  simp only [prctl_spec] at H
  by_cases ho : (option_.toNat : Int) ≠ PR_CAPBSET_READ
  · simp only [ite_eq_left ho] at H
    simp only [unmodeled] at H
    exact nomatch H
  · simp only [ite_eq_right ho] at H
    by_cases hc : CAP_LAST_CAP < (arg2.toNat : Int)
    · simp only [ite_eq_left hc] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      rw [← hP]
      simp only [check_prctl, ite_eq_right ho, ite_eq_left hc]
      simp [check_ret_only, bv_eqb_refl]
    · simp only [ite_eq_right hc] at H
      simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      rw [← hP]
      simp only [check_prctl, ite_eq_right ho, ite_eq_right hc]
      simp [check_ret_only, bv_eqb_refl]

theorem check_prctl_complete_unmodeled (option_ arg2 : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : prctl_spec option_ arg2 i m .unmodeled) :
    check_prctl option_ arg2 eff m = .CheckUnmodeled := by
  generalize hP : (check_prctl option_ arg2 eff m = .CheckUnmodeled) = Q at *
  simp only [prctl_spec] at H
  by_cases ho : (option_.toNat : Int) ≠ PR_CAPBSET_READ
  · rw [← hP]
    simp only [check_prctl, ite_eq_left ho]
  · exfalso
    simp only [ite_eq_right ho] at H
    by_cases hc : CAP_LAST_CAP < (arg2.toNat : Int)
    · simp only [ite_eq_left hc] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · simp only [ite_eq_right hc] at H
      simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H

/- =========================================================================
   getpid (172) and gettid (178)

   Both checkers are `check_set_tid_address` and both specs are
   `set_tid_address_spec`, so each obligation is the set_tid_address one
   discharged by application rather than by a second copy of the proof.
   ========================================================================= -/

theorem check_getpid_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_getpid eff m = .CheckOk m' evs) :
    getpid_spec i m (.ok eff m' evs) :=
  check_set_tid_address_sound_ok eff m m' evs i H

theorem check_getpid_sound_unmodeled (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_getpid eff m = .CheckUnmodeled) :
    getpid_spec i m .unmodeled :=
  check_set_tid_address_sound_unmodeled eff m i H

theorem check_getpid_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : getpid_spec i m (.ok eff m' evs)) :
    check_getpid eff m = .CheckOk m' evs :=
  check_set_tid_address_complete_ok eff m m' evs i H

theorem check_getpid_complete_unmodeled (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : getpid_spec i m .unmodeled) :
    check_getpid eff m = .CheckUnmodeled :=
  check_set_tid_address_complete_unmodeled m i eff H

theorem check_gettid_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_gettid eff m = .CheckOk m' evs) :
    gettid_spec i m (.ok eff m' evs) :=
  check_set_tid_address_sound_ok eff m m' evs i H

theorem check_gettid_sound_unmodeled (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_gettid eff m = .CheckUnmodeled) :
    gettid_spec i m .unmodeled :=
  check_set_tid_address_sound_unmodeled eff m i H

theorem check_gettid_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : gettid_spec i m (.ok eff m' evs)) :
    check_gettid eff m = .CheckOk m' evs :=
  check_set_tid_address_complete_ok eff m m' evs i H

theorem check_gettid_complete_unmodeled (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : gettid_spec i m .unmodeled) :
    check_gettid eff m = .CheckUnmodeled :=
  check_set_tid_address_complete_unmodeled m i eff H

/- =========================================================================
   setsid (157)
   ========================================================================= -/

/-- No session id can be mistaken for the -EPERM arm: [errno_ret EPERM]
    is [-1] read as an unsigned 64-bit register and every admissible id
    is below [PID_MAX_ENVELOPE].  This is what keeps [check_setsid] a
    function of the observed return rather than a choice, and it holds
    for every [Model], not merely every reachable one. -/
theorem setsid_id_not_eperm (r : word) (H : (r.toNat : Int) < PID_MAX_ENVELOPE) :
    bv_eqb r (errno_ret EPERM) = false := by
  cases h : bv_eqb r (errno_ret EPERM) with
  | false => rfl
  | true =>
    exfalso
    have hr : r = errno_ret 1 := by
      simpa only [EPERM] using (Fs.bv_eqb_eq r (errno_ret EPERM)).mp h
    subst hr
    have h1 : ((errno_ret 1).toNat : Int) = two_pow_64 - 1 :=
      errno_ret_unsigned 1 (by decide) (by decide)
    rw [h1] at H
    unfold two_pow_64 PID_MAX_ENVELOPE at H
    omega

theorem check_setsid_sound_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_setsid eff m = .CheckOk m' evs) :
    setsid_spec i m (.ok eff m' evs) := by
  generalize hP : (setsid_spec i m (.ok eff m' evs)) = Q at *
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_setsid] at H
  case nil.nil.nil.nil.nil =>
    by_cases hp : bv_eqb ret (errno_ret EPERM) = true
    · have hret : ret = errno_ret EPERM := (Fs.bv_eqb_eq ret (errno_ret EPERM)).mp hp
      subst hret
      simp only [ite_eq_left hp] at H
      obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
      subst hm'; subst hevs
      cases hs : m_setsid_succeeded m with
      | true =>
        rw [← hP]
        simp only [setsid_spec, getModelSpec, bind_getModel]
        rw [ite_eq_left hs]
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      | false =>
        rw [← hP]
        simp only [setsid_spec, getModelSpec, bind_getModel]
        rw [ite_eq_right (by simp [hs])]
        exact alt_l _ _ _ _ _ (by
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])
    · simp only [ite_eq_right hp] at H
      cases hs : m_setsid_succeeded m with
      | true =>
        simp only [hs] at H
        exact nomatch H
      | false =>
        rw [ite_eq_right (by simp [hs])] at H
        by_cases hv : (decide (0 < (ret.toNat : Int)) &&
              decide ((ret.toNat : Int) < PID_MAX_ENVELOPE) &&
              (match m_tid m with
               | none => true
               | some t0 => bv_eqb ret t0)) = true
        · rw [ite_eq_left hv] at H
          obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
          subst hm'; subst hevs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
          obtain ⟨⟨hlo, hhi⟩, hpin⟩ := hv
          rw [← hP]
          simp only [setsid_spec, getModelSpec, bind_getModel]
          rw [ite_eq_right (by simp [hs])]
          refine alt_r _ _ _ _ _ ?_
          refine bind_ok0 (choose _)
            (fun tid => bind (set_tid tid) fun _ =>
              bind set_setsid_succeeded fun _ => ret_only tid)
            i m ret m (mkEffect ret [] [])
            (with_setsid_succeeded (with_tid ret m)) [] ?_ ?_
          · exact choose_ok _ ret i m ⟨hlo, hhi, tid_match_of m ret hpin⟩
          · exact bind_ok (modify (with_tid ret))
              (fun _ => bind (modify with_setsid_succeeded) (fun _ => ret_only ret))
              i m () (with_tid ret m) [] (mkEffect ret [] [])
              (with_setsid_succeeded (with_tid ret m)) []
              (modify_ok _ _ _)
              (bind_ok (modify with_setsid_succeeded) (fun _ => ret_only ret)
                i (with_tid ret m) () (with_setsid_succeeded (with_tid ret m)) []
                (mkEffect ret [] []) (with_setsid_succeeded (with_tid ret m)) []
                (modify_ok _ _ _) (pure_ok _ _ _))
        · rw [ite_eq_right hv] at H
          exact nomatch H
  all_goals exact nomatch H

/-- setsid is TOTAL: every effect shape is accepted or rejected, never
    declined.  [Kernel.Sys.setsid_spec] has no [unmodeled] arm, and this
    is the checker half of saying so. -/
theorem check_setsid_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_setsid eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_setsid] at H
  case nil.nil.nil.nil.nil =>
    by_cases hp : bv_eqb ret (errno_ret EPERM) = true
    · rw [ite_eq_left hp] at H
      exact nomatch H
    · rw [ite_eq_right hp] at H
      cases hs : m_setsid_succeeded m with
      | true =>
        rw [ite_eq_left hs] at H
        exact nomatch H
      | false =>
        rw [ite_eq_right (by simp [hs])] at H
        by_cases hv : (decide (0 < (ret.toNat : Int)) &&
              decide ((ret.toNat : Int) < PID_MAX_ENVELOPE) &&
              (match m_tid m with
               | none => true
               | some t0 => bv_eqb ret t0)) = true
        · rw [ite_eq_left hv] at H
          exact nomatch H
        · rw [ite_eq_right hv] at H
          exact nomatch H
  all_goals exact nomatch H

theorem check_setsid_sound_unmodeled (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_setsid eff m = .CheckUnmodeled) :
    setsid_spec i m .unmodeled :=
  absurd H (check_setsid_no_unmodeled eff m)

theorem check_setsid_complete_ok (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : setsid_spec i m (.ok eff m' evs)) :
    check_setsid eff m = .CheckOk m' evs := by
  generalize hP : (check_setsid eff m = .CheckOk m' evs) = Q at *
  simp only [setsid_spec, getModelSpec, bind_getModel] at H
  cases hs : m_setsid_succeeded m with
  | true =>
    rw [ite_eq_left hs] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨heff, hm', hevs⟩ := H
    subst heff; subst hm'; subst hevs
    rw [← hP]
    simp [check_setsid, bv_eqb_refl]
  | false =>
    rw [ite_eq_right (by simp [hs])] at H
    rcases H with h | h
    · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at h
      obtain ⟨heff, hm', hevs⟩ := h
      subst heff; subst hm'; subst hevs
      rw [← hP]
      simp [check_setsid, bv_eqb_refl]
    · obtain ⟨tid0, m1, evs1, evs2, hc, hk, hevs⟩ := h
      obtain ⟨t0, hPmem, heq⟩ := hc
      simp only [Outcome.ok.injEq] at heq
      obtain ⟨htid, hm1, hevs1⟩ := heq
      rw [hm1] at hk
      rw [htid] at hk
      rw [hevs1] at hevs
      obtain ⟨hEff, hm', hevs2⟩ :=
        modify_modify_ret_only_inv (with_tid t0) with_setsid_succeeded t0
          i m eff m' evs2 hk
      subst hEff; subst hm'; subst hevs2
      simp only [List.nil_append] at hevs
      subst hevs
      obtain ⟨hlo, hhi, hpin⟩ := hPmem
      rw [← hP]
      simp only [check_setsid]
      rw [setsid_id_not_eperm t0 hhi]
      rw [ite_eq_right (by simp)]
      rw [ite_eq_right (by simp [hs])]
      have hval : (decide (0 < (t0.toNat : Int)) &&
            decide ((t0.toNat : Int) < PID_MAX_ENVELOPE) &&
            (match m_tid m with
             | none => true
             | some t0' => bv_eqb t0 t0')) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        refine ⟨⟨hlo, hhi⟩, ?_⟩
        cases hm : m_tid m with
        | none => rfl
        | some t0' =>
          simp only [hm] at hpin ⊢
          exact (Fs.bv_eqb_eq t0 t0').mpr hpin
      rw [hval]
      simp

theorem check_setsid_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : setsid_spec i m .unmodeled) :
    check_setsid eff m = .CheckUnmodeled := by
  exfalso
  simp only [setsid_spec, getModelSpec, bind_getModel] at H
  cases hs : m_setsid_succeeded m with
  | true =>
    rw [ite_eq_left hs] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | false =>
    rw [ite_eq_right (by simp [hs])] at H
    rcases H with h | h
    · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at h
      exact nomatch h
    · simp only [LinuxSem.LinuxProcessSem.bind] at h
      rcases h with h | ⟨tid, m1, evs1, hc, hk⟩
      · exact absurd h (choose_no_unmodeled _ i m)
      · exact absurd hk
          (modify_modify_ret_only_no_unmodeled (with_tid tid) with_setsid_succeeded tid i m1)

/- =========================================================================
   prlimit64 (261): the read arm
   ========================================================================= -/

/-- What a [CheckOk] out of the read arm tells you: the effect is a
    16-byte write of the limit at [old_rlim] returning 0, and either it
    repeated the pin or it created one. -/
theorem check_rlim64_read_ok (old_rlim : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_rlim64_read old_rlim bs0 eff m = .CheckOk m' evs) :
    ∃ bs, eff = mkEffect (BitVec.ofInt 64 0) [(old_rlim, bs)] [] ∧ evs = [] ∧
      ((bs0 = some bs ∧ m' = m) ∨
       (bs0 = none ∧ rlim64_wf bs = true ∧ m' = with_rlimit_core bs m)) := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  rcases ws with _ | ⟨⟨a, bs⟩, rest⟩
  · simp only [check_rlim64_read] at H
    exact nomatch H
  · rcases rest with _ | ⟨⟨a2, bs2⟩, rest2⟩
    · cases zs <;> cases us <;> cases cs <;> cases ks
      · simp only [check_rlim64_read] at H
        by_cases hb : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a old_rlim) = true
        · rw [ite_eq_right (by rw [hb]; simp)] at H
          simp only [Bool.and_eq_true] at hb
          obtain ⟨HR, HA⟩ := hb
          have hr : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r (BitVec.ofInt 64 0)).mp HR
          have ha : a = old_rlim := (Fs.bv_eqb_eq a old_rlim).mp HA
          subst hr
          subst ha
          cases bs0 with
          | some b0 =>
            dsimp only at H
            by_cases hl : listN_eqb bs b0 = true
            · rw [ite_eq_left hl] at H
              have hbb : bs = b0 := (listN_eqb_eq bs b0).mp hl
              obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
              subst hm'; subst hevs
              exact ⟨bs, rfl, rfl, Or.inl ⟨by rw [hbb], rfl⟩⟩
            · rw [ite_eq_right hl] at H
              exact nomatch H
          | none =>
            dsimp only at H
            by_cases hw : rlim64_wf bs = true
            · rw [ite_eq_left hw] at H
              obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
              subst hm'; subst hevs
              exact ⟨bs, rfl, rfl, Or.inr ⟨rfl, hw, rfl⟩⟩
            · rw [ite_eq_right hw] at H
              exact nomatch H
        · have hnb : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a old_rlim)) = true := by
            cases h : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a old_rlim) with
            | true => exact absurd h hb
            | false => rfl
          rw [ite_eq_left hnb] at H
          exact nomatch H
      all_goals simp only [check_rlim64_read] at H; exact nomatch H
    · simp only [check_rlim64_read] at H
      exact nomatch H

theorem check_rlim64_read_no_unmodeled (old_rlim : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) :
    check_rlim64_read old_rlim bs0 eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  rcases ws with _ | ⟨⟨a, bs⟩, rest⟩
  · simp only [check_rlim64_read] at H
    exact nomatch H
  · rcases rest with _ | ⟨⟨a2, bs2⟩, rest2⟩
    · cases zs <;> cases us <;> cases cs <;> cases ks
      · simp only [check_rlim64_read] at H
        by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a old_rlim)) = true
        · rw [ite_eq_left hg] at H
          exact nomatch H
        · rw [ite_eq_right hg] at H
          cases bs0 with
          | some b0 =>
            dsimp only at H
            by_cases hl : listN_eqb bs b0 = true
            · rw [ite_eq_left hl] at H
              exact nomatch H
            · rw [ite_eq_right hl] at H
              exact nomatch H
          | none =>
            dsimp only at H
            by_cases hw : rlim64_wf bs = true
            · rw [ite_eq_left hw] at H
              exact nomatch H
            · rw [ite_eq_right hw] at H
              exact nomatch H
      all_goals simp only [check_rlim64_read] at H; exact nomatch H
    · simp only [check_rlim64_read] at H
      exact nomatch H

/- =========================================================================
   uname (160): the copy arm and the four obligations
   ========================================================================= -/

/-- What a [CheckOk] out of the copy arm tells you: the effect is one
    390-byte write of the utsname at [name] returning 0, and either it
    repeated the pin or it created one. -/
theorem check_uname_copy_ok (name : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_uname_copy name bs0 eff m = .CheckOk m' evs) :
    ∃ bs, eff = mkEffect (BitVec.ofInt 64 0) [(name, bs)] [] ∧ evs = [] ∧
      ((bs0 = some bs ∧ m' = m) ∨
       (bs0 = none ∧ utsname_wf bs = true ∧ m' = with_utsname bs m)) := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  rcases ws with _ | ⟨⟨a, bs⟩, rest⟩
  · simp only [check_uname_copy] at H
    exact nomatch H
  · rcases rest with _ | ⟨⟨a2, bs2⟩, rest2⟩
    · cases zs <;> cases us <;> cases cs <;> cases ks
      · simp only [check_uname_copy] at H
        by_cases hb : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a name) = true
        · rw [ite_eq_right (by rw [hb]; simp)] at H
          simp only [Bool.and_eq_true] at hb
          obtain ⟨HR, HA⟩ := hb
          have hr : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r (BitVec.ofInt 64 0)).mp HR
          have ha : a = name := (Fs.bv_eqb_eq a name).mp HA
          subst hr
          subst ha
          cases bs0 with
          | some b0 =>
            dsimp only at H
            by_cases hl : listN_eqb bs b0 = true
            · rw [ite_eq_left hl] at H
              have hbb : bs = b0 := (listN_eqb_eq bs b0).mp hl
              obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
              subst hm'; subst hevs
              exact ⟨bs, rfl, rfl, Or.inl ⟨by rw [hbb], rfl⟩⟩
            · rw [ite_eq_right hl] at H
              exact nomatch H
          | none =>
            by_cases hw : utsname_wf bs = true
            · rw [ite_eq_left hw] at H
              obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
              subst hm'; subst hevs
              exact ⟨bs, rfl, rfl, Or.inr ⟨rfl, hw, rfl⟩⟩
            · rw [ite_eq_right hw] at H
              exact nomatch H
        · have hnb : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a name)) = true := by
            cases h : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a name) with
            | true => exact absurd h hb
            | false => rfl
          rw [ite_eq_left hnb] at H
          exact nomatch H
      all_goals simp only [check_uname_copy] at H; exact nomatch H
    · simp only [check_uname_copy] at H
      exact nomatch H

theorem check_uname_copy_no_unmodeled (name : word) (bs0 : Option (List byte))
    (eff : SyscallEffect) (m : Model) :
    check_uname_copy name bs0 eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  rcases ws with _ | ⟨⟨a, bs⟩, rest⟩
  · simp only [check_uname_copy] at H
    exact nomatch H
  · rcases rest with _ | ⟨⟨a2, bs2⟩, rest2⟩
    · cases zs <;> cases us <;> cases cs <;> cases ks
      · simp only [check_uname_copy] at H
        by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a name)) = true
        · rw [ite_eq_left hg] at H
          exact nomatch H
        · rw [ite_eq_right hg] at H
          cases bs0 with
          | some b0 =>
            dsimp only at H
            by_cases hl : listN_eqb bs b0 = true
            · rw [ite_eq_left hl] at H
              exact nomatch H
            · rw [ite_eq_right hl] at H
              exact nomatch H
          | none =>
            by_cases hw : utsname_wf bs = true
            · rw [ite_eq_left hw] at H
              exact nomatch H
            · rw [ite_eq_right hw] at H
              exact nomatch H
      all_goals simp only [check_uname_copy] at H; exact nomatch H
    · simp only [check_uname_copy] at H
      exact nomatch H

theorem check_uname_sound_ok (i : SyscallInput) (name : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_uname i name eff m = .CheckOk m' evs) :
    uname_spec name i m (.ok eff m' evs) := by
  generalize hP : (uname_spec name i m (.ok eff m' evs)) = Q at *
  simp only [check_uname] at H
  by_cases ho : (!(access_okb name NEW_UTSNAME_SIZE)) = true
  · rw [ite_eq_left ho] at H
    obtain ⟨heff, hm', hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [uname_spec]
    simp only [LinuxSem.LinuxProcessSem.bind]
    refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
    simp only [getModelSpec]
    refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
    rw [ite_eq_left ho]
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right ho] at H
    cases hw : read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none =>
      rw [hw] at H
      dsimp only at H
      exact nomatch H
    | some bs1 =>
      rw [hw] at H
      dsimp only at H
      obtain ⟨bs, heff, hevs, hcases⟩ :=
        check_uname_copy_ok name (m_utsname m) eff m m' evs H
      rw [heff, hevs] at hP
      rcases hcases with ⟨hm, hm'⟩ | ⟨hm, hw2, hm'⟩
      · rw [hm'] at hP
        rw [← hP]
        simp only [uname_spec]
        simp only [LinuxSem.LinuxProcessSem.bind]
        refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
        simp only [getModelSpec]
        refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
        rw [ite_eq_right ho]
        rw [hw]
        dsimp only
        rw [hm]
        dsimp only
        simp only [LinuxSem.LinuxProcessSem.pure]
      · rw [hm'] at hP
        rw [← hP]
        simp only [uname_spec]
        simp only [LinuxSem.LinuxProcessSem.bind]
        refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
        simp only [getModelSpec]
        refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
        rw [ite_eq_right ho]
        rw [hw]
        dsimp only
        rw [hm]
        dsimp only
        simp only [LinuxSem.LinuxProcessSem.bind]
        refine ⟨bs, m, [], [], choose_ok _ bs i m hw2, ?_, rfl⟩
        simp only [set_utsname, modifySpec, LinuxSem.LinuxProcessSem.modify,
          LinuxSem.LinuxProcessSem.pure]
        exact ⟨(), with_utsname bs m, [], [], rfl, rfl, rfl⟩

theorem check_uname_sound_unmodeled (i : SyscallInput) (name : word) (eff : SyscallEffect)
    (m : Model) (H : check_uname i name eff m = .CheckUnmodeled) :
    uname_spec name i m .unmodeled := by
  generalize hP : (uname_spec name i m .unmodeled) = Q at *
  simp only [check_uname] at H
  by_cases ho : (!(access_okb name NEW_UTSNAME_SIZE)) = true
  · rw [ite_eq_left ho] at H
    rw [← hP]
    simp only [uname_spec]
    simp only [LinuxSem.LinuxProcessSem.bind]
    refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
    simp only [getModelSpec]
    refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
    rw [ite_eq_left ho]
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  · rw [ite_eq_right ho] at H
    cases hw : read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none =>
      rw [← hP]
      simp only [uname_spec]
      simp only [LinuxSem.LinuxProcessSem.bind]
      refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
      simp only [getModelSpec]
      refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
      rw [ite_eq_right ho]
      rw [hw]
      dsimp only
      exact unmodeled_intro i m
    | some bs1 =>
      rw [hw] at H
      dsimp only at H
      exact absurd H (check_uname_copy_no_unmodeled name (m_utsname m) eff m)

theorem check_uname_complete_ok (i : SyscallInput) (name : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : uname_spec name i m (.ok eff m' evs)) :
    check_uname i name eff m = .CheckOk m' evs := by
  generalize hP : (check_uname i name eff m = .CheckOk m' evs) = Q at *
  simp only [uname_spec] at H
  have H1 := input_bind_ok_inv _ i m eff m' evs H
  simp only [getModelSpec] at H1
  have H2 := get_model_bind_ok_inv _ i m eff m' evs H1
  by_cases ho : (!(access_okb name NEW_UTSNAME_SIZE)) = true
  · rw [ite_eq_left ho] at H2
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H2
    obtain ⟨heff, hm', hevs⟩ := H2
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [check_uname]
    rw [ite_eq_left ho]
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right ho] at H2
    cases hw : read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none =>
      rw [hw] at H2
      simp only [unmodeled] at H2
      exact nomatch H2
    | some bs1 =>
      rw [hw] at H2
      cases hm : m_utsname m with
      | some bs0 =>
        rw [hm] at H2
        simp only [LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H2
        obtain ⟨heff, hm', hevs⟩ := H2
        rw [heff, hm', hevs] at hP
        rw [← hP]
        simp only [check_uname]
        rw [ite_eq_right ho]
        rw [hw]
        dsimp only
        rw [hm]
        simp [check_uname_copy, bv_eqb_refl, listN_eqb_eq]
      | none =>
        rw [hm] at H2
        obtain ⟨bs, m1, evs1, evs2, hc, hk, hevs⟩ := H2
        obtain ⟨bs0, hPmem, heq⟩ := hc
        simp only [Outcome.ok.injEq] at heq
        obtain ⟨hbs, hm1, hevs1⟩ := heq
        rw [hm1] at hk
        rw [hbs] at hk
        rw [hevs1] at hevs
        obtain ⟨hEff, hm', hevs2⟩ :=
          modify_pure_inv (with_utsname bs0) (mkEffect (BitVec.ofInt 64 0) [(name, bs0)] [])
            i m eff m' evs2 hk
        rw [hevs2] at hevs
        simp only [List.nil_append] at hevs
        rw [hEff, hm', hevs] at hP
        rw [← hP]
        simp only [check_uname]
        rw [ite_eq_right ho]
        rw [hw]
        dsimp only
        rw [hm]
        simp [check_uname_copy, bv_eqb_refl, hPmem]

theorem check_uname_complete_unmodeled (i : SyscallInput) (name : word) (m : Model)
    (eff : SyscallEffect) (H : uname_spec name i m .unmodeled) :
    check_uname i name eff m = .CheckUnmodeled := by
  generalize hP : (check_uname i name eff m = .CheckUnmodeled) = Q at *
  simp only [uname_spec] at H
  have H1 := input_bind_unmodeled_inv _ i m H
  simp only [getModelSpec] at H1
  have H2 := get_model_bind_unmodeled_inv _ i m H1
  by_cases ho : (!(access_okb name NEW_UTSNAME_SIZE)) = true
  · rw [ite_eq_left ho] at H2
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H2
    exact nomatch H2
  · rw [ite_eq_right ho] at H2
    cases hw : read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none =>
      rw [← hP]
      simp only [check_uname]
      rw [ite_eq_right ho]
      rw [hw]
    | some bs1 =>
      rw [hw] at H2
      cases hm : m_utsname m with
      | some bs0 =>
        rw [hm] at H2
        simp only [LinuxSem.LinuxProcessSem.pure] at H2
        exact nomatch H2
      | none =>
        rw [hm] at H2
        simp only [LinuxSem.LinuxProcessSem.bind] at H2
        rcases H2 with h | ⟨bs, m1, evs1, hc, hk⟩
        · exact absurd h (choose_no_unmodeled _ i m)
        · obtain ⟨bs0, hPmem, heq⟩ := hc
          simp only [Outcome.ok.injEq] at heq
          obtain ⟨hbs, hm1, hevs1⟩ := heq
          rw [hm1, hbs] at hk
          exact absurd hk
            (modify_pure_no_unmodeled (with_utsname bs0)
              (mkEffect (BitVec.ofInt 64 0) [(name, bs0)] []) i m)

/- =========================================================================
   prlimit64 (261): the four obligations
   ========================================================================= -/

theorem check_prlimit64_sound_ok (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckOk m' evs) :
    prlimit64_spec pid resource new_rlim old_rlim i m (.ok eff m' evs) := by
  generalize hP : (prlimit64_spec pid resource new_rlim old_rlim i m (.ok eff m' evs)) = Q at *
  simp only [check_prlimit64] at H
  by_cases h1 : (!(w_is0 pid)) = true
  · rw [ite_eq_left h1] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : (resource.toNat : Int) ≠ RLIMIT_CORE
    · rw [ite_eq_left h2] at H
      exact nomatch H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (w_is0 new_rlim && w_is0 old_rlim) = true
      · rw [ite_eq_left h3] at H
        exact nomatch H
      · rw [ite_eq_right h3] at H
        by_cases h4 : (!(w_is0 new_rlim) && !(w_is0 old_rlim)) = true
        · rw [ite_eq_left h4] at H
          exact nomatch H
        · rw [ite_eq_right h4] at H
          by_cases hn : w_is0 new_rlim = true
          · rw [ite_eq_left hn] at H
            cases hw : read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
            | none =>
              rw [hw] at H
              dsimp only at H
              by_cases ha : (!(access_okb old_rlim 16)) = true
              · rw [ite_eq_left ha] at H
                obtain ⟨heff, hm', hevs⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
                rw [heff, hm', hevs] at hP
                rw [← hP]
                simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  LinuxSem.LinuxProcessSem.bind]
                refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                simp only [getModelSpec]
                refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                rw [ite_eq_left hn]
                rw [hw]
                dsimp only
                rw [ite_eq_left ha]
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
              · rw [ite_eq_right ha] at H
                exact nomatch H
            | some bs1 =>
              rw [hw] at H
              dsimp only at H
              obtain ⟨bs, heff, hevs, hcases⟩ :=
                check_rlim64_read_ok old_rlim (m_rlimit_core m) eff m m' evs H
              rw [heff, hevs] at hP
              rcases hcases with ⟨hpin, hm'⟩ | ⟨hpin, hwf, hm'⟩
              · rw [hm'] at hP
                rw [← hP]
                simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  LinuxSem.LinuxProcessSem.bind]
                refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                simp only [getModelSpec]
                refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                rw [ite_eq_left hn]
                rw [hw]
                dsimp only
                rw [hpin]
                dsimp only
                simp only [LinuxSem.LinuxProcessSem.pure]
              · rw [hm'] at hP
                rw [← hP]
                simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  LinuxSem.LinuxProcessSem.bind]
                refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                simp only [getModelSpec]
                refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                rw [ite_eq_left hn]
                rw [hw]
                dsimp only
                rw [hpin]
                dsimp only
                simp only [LinuxSem.LinuxProcessSem.bind]
                refine ⟨bs, m, [], [], choose_ok _ bs i m hwf, ?_, rfl⟩
                simp only [set_rlimit_core, modifySpec,
                  LinuxSem.LinuxProcessSem.modify,
                  LinuxSem.LinuxProcessSem.pure]
                exact ⟨(), with_rlimit_core bs m, [], [], rfl, rfl, rfl⟩
          · rw [ite_eq_right hn] at H
            cases hm : m_rlimit_core m with
            | none =>
              rw [hm] at H
              dsimp only at H
              exact nomatch H
            | some bs0 =>
              rw [hm] at H
              dsimp only at H
              cases hw : read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
              | none =>
                rw [hw] at H
                dsimp only at H
                by_cases ha : (!(access_okb new_rlim 16)) = true
                · rw [ite_eq_left ha] at H
                  obtain ⟨heff, hm', hevs⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
                  rw [heff, hm', hevs] at hP
                  rw [← hP]
                  simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                    LinuxSem.LinuxProcessSem.bind]
                  refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                  simp only [getModelSpec]
                  refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                  rw [ite_eq_right hn]
                  rw [hm]
                  dsimp only
                  rw [hw]
                  dsimp only
                  rw [ite_eq_left ha]
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
                · rw [ite_eq_right ha] at H
                  exact nomatch H
              | some nb =>
                rw [hw] at H
                dsimp only at H
                by_cases hi : (rlim64_hard nb).toNat < (rlim64_soft nb).toNat
                · rw [ite_eq_left hi] at H
                  obtain ⟨heff, hm', hevs⟩ :=
                    (check_ret_only_copyins_ok_iff [(new_rlim, 16)] eff
                      (errno_ret EINVAL) m [] m' evs).mp H
                  rw [heff, hm', hevs] at hP
                  rw [← hP]
                  simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                    LinuxSem.LinuxProcessSem.bind]
                  refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                  simp only [getModelSpec]
                  refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                  rw [ite_eq_right hn]
                  rw [hm]
                  dsimp only
                  rw [hw]
                  dsimp only
                  rw [ite_eq_left hi]
                  exact record_copyins_ok (reads := [(new_rlim, 16)])
                    (by
                      simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure])
                · rw [ite_eq_right hi] at H
                  by_cases hh : (!(bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) = true
                  · rw [ite_eq_left hh] at H
                    exact nomatch H
                  · rw [ite_eq_right hh] at H
                    obtain ⟨heff, hm', hevs⟩ :=
                      (check_ret_only_copyins_ok_iff [(new_rlim, 16)] eff
                        (BitVec.ofInt 64 0) (with_rlimit_core nb m) [] m' evs).mp H
                    rw [heff, hm', hevs] at hP
                    rw [← hP]
                    simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                      LinuxSem.LinuxProcessSem.bind]
                    refine ⟨i, m, [], [], input_ok i m, ?_, rfl⟩
                    simp only [getModelSpec]
                    refine ⟨m, m, [], [], getModel_ok i m, ?_, rfl⟩
                    rw [ite_eq_right hn]
                    rw [hm]
                    dsimp only
                    rw [hw]
                    dsimp only
                    rw [ite_eq_right hi]
                    rw [ite_eq_right hh]
                    refine record_copyins_ok (reads := [(new_rlim, 16)]) ?_
                    simp only [LinuxSem.LinuxProcessSem.bind]
                    refine ⟨(), with_rlimit_core nb m, [], [], ?_, ?_, rfl⟩
                    · rfl
                    · simp only [ret_only, LinuxSem.LinuxProcessSem.pure]

theorem check_prlimit64_sound_unmodeled (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckUnmodeled) :
    prlimit64_spec pid resource new_rlim old_rlim i m .unmodeled := by
  generalize hP : (prlimit64_spec pid resource new_rlim old_rlim i m .unmodeled) = Q at *
  simp only [check_prlimit64] at H
  by_cases h1 : (!(w_is0 pid)) = true
  · rw [ite_eq_left h1] at H
    rw [← hP]
    simp only [prlimit64_spec, ite_eq_left h1, unmodeled]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (resource.toNat : Int) ≠ RLIMIT_CORE
    · rw [ite_eq_left h2] at H
      rw [← hP]
      simp only [prlimit64_spec, ite_eq_right h1, ite_eq_left h2, unmodeled]
    · rw [ite_eq_right h2] at H
      by_cases h3 : (w_is0 new_rlim && w_is0 old_rlim) = true
      · rw [ite_eq_left h3] at H
        rw [← hP]
        simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, unmodeled]
      · rw [ite_eq_right h3] at H
        by_cases h4 : (!(w_is0 new_rlim) && !(w_is0 old_rlim)) = true
        · rw [ite_eq_left h4] at H
          rw [← hP]
          simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4, unmodeled]
        · rw [ite_eq_right h4] at H
          by_cases hn : w_is0 new_rlim = true
          · rw [ite_eq_left hn] at H
            cases hw : read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
            | none =>
              rw [hw] at H
              dsimp only at H
              by_cases ha : (!(access_okb old_rlim 16)) = true
              · rw [ite_eq_left ha] at H
                exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
              · rw [ite_eq_right ha] at H
                rw [← hP]
                simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  LinuxSem.LinuxProcessSem.bind]
                refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
                simp only [getModelSpec]
                refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
                rw [ite_eq_left hn]
                rw [hw]
                dsimp only
                rw [ite_eq_right ha]
                exact unmodeled_intro i m
            | some bs1 =>
              rw [hw] at H
              dsimp only at H
              exact absurd H
                (check_rlim64_read_no_unmodeled old_rlim (m_rlimit_core m) eff m)
          · rw [ite_eq_right hn] at H
            cases hm : m_rlimit_core m with
            | none =>
              rw [hm] at H
              dsimp only at H
              rw [← hP]
              simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                LinuxSem.LinuxProcessSem.bind]
              refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
              simp only [getModelSpec]
              refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
              rw [ite_eq_right hn]
              rw [hm]
              dsimp only
              exact unmodeled_intro i m
            | some bs0 =>
              rw [hm] at H
              dsimp only at H
              cases hw : read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
              | none =>
                rw [hw] at H
                dsimp only at H
                by_cases ha : (!(access_okb new_rlim 16)) = true
                · rw [ite_eq_left ha] at H
                  exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
                · rw [ite_eq_right ha] at H
                  rw [← hP]
                  simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                    LinuxSem.LinuxProcessSem.bind]
                  refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
                  simp only [getModelSpec]
                  refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
                  rw [ite_eq_right hn]
                  rw [hm]
                  dsimp only
                  rw [hw]
                  dsimp only
                  rw [ite_eq_right ha]
                  exact unmodeled_intro i m
              | some nb =>
                rw [hw] at H
                dsimp only at H
                by_cases hi : (rlim64_hard nb).toNat < (rlim64_soft nb).toNat
                · rw [ite_eq_left hi] at H
                  exact absurd H
                    (check_ret_only_copyins_no_unmodeled [(new_rlim, 16)] eff
                      (errno_ret EINVAL) m [])
                · rw [ite_eq_right hi] at H
                  by_cases hh : (!(bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) = true
                  · rw [ite_eq_left hh] at H
                    rw [← hP]
                    simp only [prlimit64_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                      LinuxSem.LinuxProcessSem.bind]
                    refine Or.inr ⟨i, m, [], input_ok i m, ?_⟩
                    simp only [getModelSpec]
                    refine Or.inr ⟨m, m, [], getModel_ok i m, ?_⟩
                    rw [ite_eq_right hn]
                    rw [hm]
                    dsimp only
                    rw [hw]
                    dsimp only
                    rw [ite_eq_right hi]
                    rw [ite_eq_left hh]
                    exact record_copyins_unmodeled (unmodeled_intro i m)
                  · rw [ite_eq_right hh] at H
                    exact absurd H
                      (check_ret_only_copyins_no_unmodeled [(new_rlim, 16)] eff
                        (BitVec.ofInt 64 0) (with_rlimit_core nb m) [])

theorem check_prlimit64_complete_ok (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : prlimit64_spec pid resource new_rlim old_rlim i m (.ok eff m' evs)) :
    check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckOk m' evs := by
  generalize hP : (check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckOk m' evs) = Q at *
  simp only [prlimit64_spec] at H
  by_cases h1 : (!(w_is0 pid)) = true
  · rw [ite_eq_left h1] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : (resource.toNat : Int) ≠ RLIMIT_CORE
    · rw [ite_eq_left h2] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (w_is0 new_rlim && w_is0 old_rlim) = true
      · rw [ite_eq_left h3] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right h3] at H
        by_cases h4 : (!(w_is0 new_rlim) && !(w_is0 old_rlim)) = true
        · rw [ite_eq_left h4] at H
          simp only [unmodeled] at H
          exact nomatch H
        · rw [ite_eq_right h4] at H
          have H1 := input_bind_ok_inv _ i m eff m' evs H
          simp only [getModelSpec] at H1
          have H2 := get_model_bind_ok_inv _ i m eff m' evs H1
          by_cases hn : w_is0 new_rlim = true
          · rw [ite_eq_left hn] at H2
            cases hw : read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
            | none =>
              rw [hw] at H2
              dsimp only at H2
              by_cases ha : (!(access_okb old_rlim 16)) = true
              · rw [ite_eq_left ha] at H2
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at H2
                obtain ⟨heff, hm', hevs⟩ := H2
                rw [heff, hm', hevs] at hP
                rw [← hP]
                simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                simp only [ite_eq_left hn, hw, ite_eq_left ha]
                simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right ha] at H2
                simp only [unmodeled] at H2
                exact nomatch H2
            | some bs1 =>
              rw [hw] at H2
              dsimp only at H2
              cases hm : m_rlimit_core m with
              | none =>
                rw [hm] at H2
                dsimp only at H2
                obtain ⟨bs, m1, evs1, evs2, hc, hk, hevs⟩ := H2
                obtain ⟨bs0, hPmem, heq⟩ := hc
                simp only [Outcome.ok.injEq] at heq
                obtain ⟨hbs, hm1, hevs1⟩ := heq
                rw [hm1, hbs] at hk
                rw [hevs1] at hevs
                obtain ⟨hEff, hm', hevs2⟩ :=
                  modify_pure_inv (with_rlimit_core bs0)
                    (mkEffect (BitVec.ofInt 64 0) [(old_rlim, bs0)] []) i m eff m' evs2 hk
                rw [hevs2] at hevs
                simp only [List.nil_append] at hevs
                rw [hEff, hm', hevs] at hP
                rw [← hP]
                simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                simp only [ite_eq_left hn, hw, hm]
                simp [check_rlim64_read, bv_eqb_refl, hPmem]
              | some bs0 =>
                rw [hm] at H2
                dsimp only at H2
                simp only [LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at H2
                obtain ⟨heff, hm', hevs⟩ := H2
                rw [heff, hm', hevs] at hP
                rw [← hP]
                simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                simp only [ite_eq_left hn, hw, hm]
                simp [check_rlim64_read, bv_eqb_refl, listN_eqb_eq]
          · rw [ite_eq_right hn] at H2
            cases hm : m_rlimit_core m with
            | none =>
              rw [hm] at H2
              dsimp only at H2
              simp only [unmodeled] at H2
              exact nomatch H2
            | some bs0 =>
              rw [hm] at H2
              dsimp only at H2
              cases hw : read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
              | none =>
                rw [hw] at H2
                dsimp only at H2
                by_cases ha : (!(access_okb new_rlim 16)) = true
                · rw [ite_eq_left ha] at H2
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at H2
                  obtain ⟨heff, hm', hevs⟩ := H2
                  rw [heff, hm', hevs] at hP
                  rw [← hP]
                  simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                  simp only [ite_eq_right hn, hm, hw, ite_eq_left ha]
                  simp [check_ret_only, bv_eqb_refl]
                · rw [ite_eq_right ha] at H2
                  simp only [unmodeled] at H2
                  exact nomatch H2
              | some nb =>
                rw [hw] at H2
                dsimp only at H2
                by_cases hi : (rlim64_hard nb).toNat < (rlim64_soft nb).toNat
                · rw [ite_eq_left hi] at H2
                  obtain ⟨core, Hcore, hEff⟩ :=
                    record_copyins_ok_inv [(new_rlim, 16)] _ i m eff m' evs H2
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at Hcore
                  obtain ⟨heffc, hm', hevs⟩ := Hcore
                  rw [heffc] at hEff
                  simp only [mkEffect, List.append_nil] at hEff
                  rw [hEff, hm', hevs] at hP
                  rw [← hP]
                  simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                  simp only [ite_eq_right hn, hm, hw, ite_eq_left hi]
                  exact check_ret_only_copyins_refl [(new_rlim, 16)] (errno_ret EINVAL) m []
                · rw [ite_eq_right hi] at H2
                  by_cases hh : (!(bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) = true
                  · rw [ite_eq_left hh] at H2
                    obtain ⟨core, Hcore, -⟩ :=
                      record_copyins_ok_inv [(new_rlim, 16)] _ i m eff m' evs H2
                    simp only [unmodeled] at Hcore
                    exact nomatch Hcore
                  · rw [ite_eq_right hh] at H2
                    obtain ⟨core, Hcore, hEff⟩ :=
                      record_copyins_ok_inv [(new_rlim, 16)] _ i m eff m' evs H2
                    obtain ⟨hcore, hm2, hevs⟩ :=
                      modify_pure_inv (with_rlimit_core nb) (mkEffect (BitVec.ofInt 64 0) [] [])
                        i m core m' evs Hcore
                    rw [hcore] at hEff
                    simp only [mkEffect, List.append_nil] at hEff
                    rw [hEff, hm2, hevs] at hP
                    rw [← hP]
                    simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                    simp only [ite_eq_right hn, hm, hw, ite_eq_right hi, ite_eq_right hh]
                    exact check_ret_only_copyins_refl [(new_rlim, 16)]
                      (BitVec.ofInt 64 0) (with_rlimit_core nb m) []

theorem check_prlimit64_complete_unmodeled (i : SyscallInput) (pid resource new_rlim old_rlim : word)
    (m : Model) (eff : SyscallEffect)
    (H : prlimit64_spec pid resource new_rlim old_rlim i m .unmodeled) :
    check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckUnmodeled := by
  generalize hP : (check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckUnmodeled) = Q at *
  simp only [prlimit64_spec] at H
  by_cases h1 : (!(w_is0 pid)) = true
  · rw [ite_eq_left h1] at H
    rw [← hP]
    simp only [check_prlimit64, ite_eq_left h1]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (resource.toNat : Int) ≠ RLIMIT_CORE
    · rw [ite_eq_left h2] at H
      rw [← hP]
      simp only [check_prlimit64, ite_eq_right h1, ite_eq_left h2]
    · rw [ite_eq_right h2] at H
      by_cases h3 : (w_is0 new_rlim && w_is0 old_rlim) = true
      · rw [ite_eq_left h3] at H
        rw [← hP]
        simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
      · rw [ite_eq_right h3] at H
        by_cases h4 : (!(w_is0 new_rlim) && !(w_is0 old_rlim)) = true
        · rw [ite_eq_left h4] at H
          rw [← hP]
          simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
        · rw [ite_eq_right h4] at H
          have H1 := input_bind_unmodeled_inv _ i m H
          simp only [getModelSpec] at H1
          have H2 := get_model_bind_unmodeled_inv _ i m H1
          by_cases hn : w_is0 new_rlim = true
          · rw [ite_eq_left hn] at H2
            cases hw : read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
            | none =>
              rw [hw] at H2
              dsimp only at H2
              by_cases ha : (!(access_okb old_rlim 16)) = true
              · rw [ite_eq_left ha] at H2
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H2
                exact nomatch H2
              · rw [ite_eq_right ha] at H2
                rw [← hP]
                simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                simp only [ite_eq_left hn, hw, ite_eq_right ha]
            | some bs1 =>
              rw [hw] at H2
              dsimp only at H2
              cases hm : m_rlimit_core m with
              | none =>
                rw [hm] at H2
                dsimp only at H2
                simp only [LinuxSem.LinuxProcessSem.bind] at H2
                rcases H2 with h | ⟨bs, m1, evs1, hc, hk⟩
                · exact absurd h (choose_no_unmodeled _ i m)
                · exact absurd hk (by
                    have h := modify_pure_no_unmodeled (with_rlimit_core bs)
                      (mkEffect (BitVec.ofInt 64 0) [(old_rlim, bs)] []) i m1
                    simpa only [set_rlimit_core, modifySpec,
                      LinuxSem.LinuxProcessSem.bind] using h)
              | some bs0 =>
                rw [hm] at H2
                dsimp only at H2
                simp only [LinuxSem.LinuxProcessSem.pure] at H2
                exact nomatch H2
          · rw [ite_eq_right hn] at H2
            cases hm : m_rlimit_core m with
            | none =>
              rw [hm] at H2
              dsimp only at H2
              rw [← hP]
              simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
              simp only [ite_eq_right hn, hm]
            | some bs0 =>
              rw [hm] at H2
              dsimp only at H2
              cases hw : read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
              | none =>
                rw [hw] at H2
                dsimp only at H2
                by_cases ha : (!(access_okb new_rlim 16)) = true
                · rw [ite_eq_left ha] at H2
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H2
                  exact nomatch H2
                · rw [ite_eq_right ha] at H2
                  rw [← hP]
                  simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                  simp only [ite_eq_right hn, hm, hw, ite_eq_right ha]
              | some nb =>
                rw [hw] at H2
                dsimp only at H2
                by_cases hi : (rlim64_hard nb).toNat < (rlim64_soft nb).toNat
                · rw [ite_eq_left hi] at H2
                  have Hcore := record_copyins_unmodeled_inv _ _ i m H2
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at Hcore
                  exact nomatch Hcore
                · rw [ite_eq_right hi] at H2
                  by_cases hh : (!(bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) = true
                  · rw [ite_eq_left hh] at H2
                    rw [← hP]
                    simp only [check_prlimit64, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
                    simp only [ite_eq_right hn, hm, hw, ite_eq_right hi, ite_eq_left hh]
                  · rw [ite_eq_right hh] at H2
                    have Hcore := record_copyins_unmodeled_inv _ _ i m H2
                    exact absurd Hcore
                      (seqSpec_modify_ret_only_no_unmodeled (with_rlimit_core nb)
                        (BitVec.ofInt 64 0) i m)

/- =========================================================================
   Credentials — getuid (174) / geteuid (175) / getgid (176) /
   getegid (177) / setuid (146) / setgid (144) / setresuid (147) /
   setresgid (149)
   ========================================================================= -/

/-- A setter's success answer is 0, which is not an errno: the injected
    and the deterministic arm of its [alt] can never claim the same
    return. -/
theorem errno_ret_in_setid_zero (b : Bool) :
    errno_ret_in (setid_errnos b) (BitVec.ofInt 64 0) = false := by
  cases b <;> rfl

/-- -EPERM is a verdict the setters reach from the credentials, never an
    environment failure the target may inject, so it is disjoint from the
    injectable set too. -/
theorem errno_ret_in_setid_eperm (b : Bool) :
    errno_ret_in (setid_errnos b) (errno_ret EPERM) = false := by
  cases b <;> rfl

/-- The [alt] every fallible credential-setter branch ends in: an
    injectable errno, or the branch's own deterministic arm [c2].  All
    this needs to know about [c2] is that it admits exactly [r] with the
    model at [mR]. -/
theorem check_setid_result_sound_ok (errs : List Int) (r : word) (mR : Model)
    (c2 : SysSpec SyscallEffect) (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (Hc2 : c2 i m (.ok (mkEffect r [] []) mR []))
    (H : check_setid_result errs r mR eff m = .CheckOk m' evs) :
    alt (bind (errno_from errs) (fun e => err_ret e)) c2 i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_setid_result] at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in errs ret = true
    · rw [ite_eq_left he] at H
      obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
      subst hm'; subst hevs
      obtain ⟨e, hmem, hret⟩ := (errno_ret_in_true errs ret).mp he
      subst hret
      refine alt_l _ _ _ _ _ ?_
      simp only [errno_from, LinuxSem.LinuxProcessSem.bind]
      refine ⟨e, m, [], [], choose_ok _ e i m hmem, ?_, rfl⟩
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right he] at H
      by_cases hr : bv_eqb ret r = true
      · rw [ite_eq_left hr] at H
        obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
        subst hm'; subst hevs
        have hret : ret = r := (Fs.bv_eqb_eq ret r).mp hr
        subst hret
        exact alt_r _ _ _ _ _ (by simpa only [mkEffect] using Hc2)
      · rw [ite_eq_right hr] at H
        exact nomatch H
  all_goals exact nomatch H

/-- Every branch of a credential setter answers, so this acceptor never
    declines. -/
theorem check_setid_result_no_unmodeled (errs : List Int) (r : word) (mR : Model)
    (eff : SyscallEffect) (m : Model) :
    check_setid_result errs r mR eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_setid_result] at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in errs ret = true
    · rw [ite_eq_left he] at H
      exact nomatch H
    · rw [ite_eq_right he] at H
      by_cases hr : bv_eqb ret r = true
      · rw [ite_eq_left hr] at H
        exact nomatch H
      · rw [ite_eq_right hr] at H
        exact nomatch H
  all_goals exact nomatch H

/-- Invert `errno_from errs ;; err_ret`: the effect is the single return
    of a member of [errs], and nothing is emitted.  `inv_ok` would do this
    inline. -/
theorem errno_from_err_ret_ok_inv (errs : List Int) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (errno_from errs) (fun e => err_ret e) i m (.ok eff m' evs)) :
    ∃ e, e ∈ errs ∧ eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  simp only [errno_from, LinuxSem.LinuxProcessSem.bind] at H
  obtain ⟨e, m1, evs1, evs2, hc, hk, hevs⟩ := H
  obtain ⟨e0, hmem, heq⟩ := hc
  simp only [Outcome.ok.injEq] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  rw [h2, h1] at hk
  rw [h3] at hevs
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
    Outcome.ok.injEq] at hk
  obtain ⟨heff, hm', hevs2⟩ := hk
  rw [hevs2] at hevs
  simp only [List.nil_append] at hevs
  exact ⟨e0, hmem, heff, hm', hevs⟩

/-! ## getuid / geteuid / getgid / getegid -/

/-- `errno_from errs ;; err_ret` never declines: its only failure would be
    the environment choice leaving the modeled surface, which it cannot. -/
theorem errno_from_err_ret_no_unmodeled (errs : List Int) (i : SyscallInput)
    (m : Model) :
    ¬ bind (errno_from errs) (fun e => err_ret e) i m .unmodeled := by
  intro H
  rcases H with H | ⟨e, m1, evs1, H, H2⟩
  · exact absurd H (choose_no_unmodeled _ i m)
  · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H2
    exact nomatch H2

/-- ...and neither does the deterministic arm that installs the new
    credentials. -/
theorem set_creds_ret_only_no_unmodeled (c' : Creds) (i : SyscallInput) (m : Model) :
    ¬ (bind (set_creds c') (fun _ => ret_only (BitVec.ofInt 64 0))) i m .unmodeled := by
  intro H
  rcases H with H | ⟨u, m1, evs1, H, H2⟩
  · simp only [set_creds, modifySpec, LinuxSem.LinuxProcessSem.modify] at H
    exact nomatch H
  · simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H2
    exact nomatch H2

/-- The deterministic arm every credential-setter branch commits:
    install the new credentials and answer 0. -/
theorem set_creds_ret_only_ok (c' : Creds) (m : Model) (i : SyscallInput) :
    (bind (set_creds c') (fun _ => ret_only (BitVec.ofInt 64 0))) i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) (with_creds c' m) []) := by
  simp only [set_creds, modifySpec]
  exact bind_ok (modify (with_creds c')) (fun _ => ret_only (BitVec.ofInt 64 0)) i m
    () (with_creds c' m) [] (mkEffect (BitVec.ofInt 64 0) [] []) (with_creds c' m) []
    (modify_ok _ i m) (pure_ok _ _ _)

theorem check_getid_sound_ok (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_getid sel eff m = .CheckOk m' evs) :
    getid_spec sel i m (.ok eff m' evs) := by
  generalize hP : (getid_spec sel i m (.ok eff m' evs)) = Q at *
  simp only [check_getid] at H
  obtain ⟨heff, hm', hevs⟩ :=
    (check_ret_only_ok_iff eff (sel (m_creds m)) m [] m' evs).mp H
  rw [heff, hm', hevs] at hP
  rw [← hP]
  simp only [getid_spec, getModelSpec, bind_getModel, ret_only,
    LinuxSem.LinuxProcessSem.pure]

/-- The readers are total, so this direction is vacuous. -/
theorem check_getid_sound_unmodeled (sel : Creds → word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput) (H : check_getid sel eff m = .CheckUnmodeled) :
    getid_spec sel i m .unmodeled := by
  simp only [check_getid] at H
  exact absurd H (check_ret_only_no_unmodeled eff (sel (m_creds m)) m [])

theorem check_getid_complete_ok (sel : Creds → word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : getid_spec sel i m (.ok eff m' evs)) :
    check_getid sel eff m = .CheckOk m' evs := by
  generalize hP : (check_getid sel eff m = .CheckOk m' evs) = Q at *
  simp only [getid_spec, getModelSpec, bind_getModel, ret_only,
    LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
  obtain ⟨heff, hm', hevs⟩ := H
  rw [heff, hm', hevs] at hP
  rw [← hP]
  simp [check_getid, check_ret_only, bv_eqb_refl]

/-- Vacuous for the same reason: the spec cannot decline either. -/
theorem check_getid_complete_unmodeled (sel : Creds → word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect) (H : getid_spec sel i m .unmodeled) :
    check_getid sel eff m = .CheckUnmodeled := by
  simp only [getid_spec, getModelSpec, bind_getModel, ret_only,
    LinuxSem.LinuxProcessSem.pure] at H
  exact nomatch H

/-! ## setuid / setgid -/

/-- Every branch of a credential setter answers, so [check_setid] never
    declines. -/
theorem check_setid_no_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m : Model) :
    check_setid get put user v eff m ≠ .CheckUnmodeled := by
  intro H
  simp only [check_setid] at H
  by_cases h1 : bv_eqb v ID_MINUS_ONE = true
  · rw [ite_eq_left h1] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right h1] at H
    by_cases h2 : creds_privileged (m_creds m) = true
    · rw [ite_eq_left h2] at H
      exact absurd H (check_setid_result_no_unmodeled _ _ _ eff m)
    · rw [ite_eq_right h2] at H
      cases h3 : (bv_eqb v (get (m_creds m)).id_real ||
          bv_eqb v (get (m_creds m)).id_saved) with
      | true =>
        rw [ite_eq_left h3] at H
        exact absurd H (check_setid_result_no_unmodeled _ _ _ eff m)
      | false =>
        rw [ite_eq_right (by simp [h3])] at H
        exact absurd H (check_setid_result_no_unmodeled _ _ _ eff m)

theorem check_setid_sound_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_setid get put user v eff m = .CheckOk m' evs) :
    setid_spec get put user v i m (.ok eff m' evs) := by
  generalize hP : (setid_spec get put user v i m (.ok eff m' evs)) = Q at *
  simp only [check_setid] at H
  by_cases h1 : bv_eqb v ID_MINUS_ONE = true
  · rw [ite_eq_left h1] at H
    obtain ⟨heff, hm', hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [setid_spec, getModelSpec, bind_getModel]
    rw [ite_eq_left h1]
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right h1] at H
    by_cases h2 : creds_privileged (m_creds m) = true
    · rw [ite_eq_left h2] at H
      have hc2 := set_creds_ret_only_ok (put (IdTriple.mkIdTriple v v v) (m_creds m)) m i
      rw [← hP]
      simp only [setid_spec, getModelSpec, bind_getModel]
      rw [ite_eq_right h1]
      rw [ite_eq_left h2]
      exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs hc2 H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (bv_eqb v (get (m_creds m)).id_real ||
          bv_eqb v (get (m_creds m)).id_saved) = true
      · rw [ite_eq_left h3] at H
        have hc2 := set_creds_ret_only_ok (put (IdTriple.mkIdTriple (get (m_creds m)).id_real v
          (get (m_creds m)).id_saved) (m_creds m)) m i
        rw [← hP]
        simp only [setid_spec, getModelSpec, bind_getModel]
        rw [ite_eq_right h1]
        rw [ite_eq_right h2]
        rw [ite_eq_left h3]
        exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs hc2 H
      · rw [ite_eq_right h3] at H
        rw [← hP]
        simp only [setid_spec, getModelSpec, bind_getModel]
        rw [ite_eq_right h1]
        rw [ite_eq_right h2]
        rw [ite_eq_right h3]
        exact check_setid_result_sound_ok (setid_errnos false) (errno_ret EPERM) m
          (err_ret EPERM) i eff m m' evs
          (pure_ok (mkEffect (errno_ret EPERM) [] []) i m) H

theorem check_setid_sound_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_setid get put user v eff m = .CheckUnmodeled) :
    setid_spec get put user v i m .unmodeled :=
  absurd H (check_setid_no_unmodeled get put user v eff m)

theorem check_setid_complete_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : setid_spec get put user v i m (.ok eff m' evs)) :
    check_setid get put user v eff m = .CheckOk m' evs := by
  generalize hP : (check_setid get put user v eff m = .CheckOk m' evs) = Q at *
  simp only [setid_spec, getModelSpec, bind_getModel] at H
  by_cases h1 : bv_eqb v ID_MINUS_ONE = true
  · rw [ite_eq_left h1] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨heff, hm', hevs⟩ := H
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [check_setid]
    rw [ite_eq_left h1]
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right h1] at H
    by_cases h2 : creds_privileged (m_creds m) = true
    · rw [ite_eq_left h2] at H
      rcases H with H | H
      · obtain ⟨e, hmem, heff, hm', hevs⟩ := errno_from_err_ret_ok_inv _ i m eff m' evs H
        rw [heff, hm', hevs] at hP
        rw [← hP]
        simp only [check_setid]
        rw [ite_eq_right h1]
        rw [ite_eq_left h2]
        simp [check_setid_result, errno_ret_in_intro _ e hmem]
      · obtain ⟨heff, hm', hevs⟩ :=
          modify_pure_inv (with_creds (put (IdTriple.mkIdTriple v v v) (m_creds m)))
            (mkEffect (BitVec.ofInt 64 0) [] []) i m eff m' evs H
        rw [heff, hm', hevs] at hP
        rw [← hP]
        simp only [check_setid]
        rw [ite_eq_right h1]
        rw [ite_eq_left h2]
        simp only [check_setid_result]
        rw [show errno_ret_in (setid_errnos (user && !(bv_eqb v (get (m_creds m)).id_real)))
          (BitVec.ofInt 64 0) = false from errno_ret_in_setid_zero _]
        simp only [Bool.false_eq_true, ite_false, bv_eqb_refl, ite_true]
    · rw [ite_eq_right h2] at H
      by_cases h3 : (bv_eqb v (get (m_creds m)).id_real ||
          bv_eqb v (get (m_creds m)).id_saved) = true
      · rw [ite_eq_left h3] at H
        rcases H with H | H
        · obtain ⟨e, hmem, heff, hm', hevs⟩ := errno_from_err_ret_ok_inv _ i m eff m' evs H
          rw [heff, hm', hevs] at hP
          rw [← hP]
          simp only [check_setid]
          rw [ite_eq_right h1]
          rw [ite_eq_right h2]
          rw [ite_eq_left h3]
          simp [check_setid_result, errno_ret_in_intro _ e hmem]
        · obtain ⟨heff, hm', hevs⟩ :=
            modify_pure_inv (with_creds (put (IdTriple.mkIdTriple (get (m_creds m)).id_real v
              (get (m_creds m)).id_saved) (m_creds m)))
              (mkEffect (BitVec.ofInt 64 0) [] []) i m eff m' evs H
          rw [heff, hm', hevs] at hP
          rw [← hP]
          simp only [check_setid]
          rw [ite_eq_right h1]
          rw [ite_eq_right h2]
          rw [ite_eq_left h3]
          simp only [check_setid_result]
          rw [show errno_ret_in (setid_errnos false) (BitVec.ofInt 64 0) = false from
            errno_ret_in_setid_zero _]
          simp only [Bool.false_eq_true, ite_false, bv_eqb_refl, ite_true]
      · rw [ite_eq_right h3] at H
        rcases H with H | H
        · obtain ⟨e, hmem, heff, hm', hevs⟩ := errno_from_err_ret_ok_inv _ i m eff m' evs H
          rw [heff, hm', hevs] at hP
          rw [← hP]
          simp only [check_setid]
          rw [ite_eq_right h1]
          rw [ite_eq_right h2]
          rw [ite_eq_right h3]
          simp [check_setid_result, errno_ret_in_intro _ e hmem]
        · have hc : (mkEffect (errno_ret EPERM) [] []) = mkEffect (errno_ret EPERM) [] [] := rfl
          cases hc
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨heff, hm', hevs⟩ := H
          rw [heff, hm', hevs] at hP
          rw [← hP]
          simp only [check_setid]
          rw [ite_eq_right h1]
          rw [ite_eq_right h2]
          rw [ite_eq_right h3]
          simp only [check_setid_result]
          rw [show errno_ret_in (setid_errnos false) (errno_ret EPERM) = false from
            errno_ret_in_setid_eperm _]
          simp only [Bool.false_eq_true, ite_false, bv_eqb_refl, ite_true]

theorem check_setid_complete_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : setid_spec get put user v i m .unmodeled) :
    check_setid get put user v eff m = .CheckUnmodeled := by
  exfalso
  simp only [setid_spec, getModelSpec, bind_getModel] at H
  by_cases h1 : bv_eqb v ID_MINUS_ONE = true
  · rw [ite_eq_left h1] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : creds_privileged (m_creds m) = true
    · rw [ite_eq_left h2] at H
      rcases H with H | H
      · exact absurd H (errno_from_err_ret_no_unmodeled _ i m)
      · exact absurd H (set_creds_ret_only_no_unmodeled _ i m)
    · rw [ite_eq_right h2] at H
      by_cases h3 : (bv_eqb v (get (m_creds m)).id_real ||
          bv_eqb v (get (m_creds m)).id_saved) = true
      · rw [ite_eq_left h3] at H
        rcases H with H | H
        · exact absurd H (errno_from_err_ret_no_unmodeled _ i m)
        · exact absurd H (set_creds_ret_only_no_unmodeled _ i m)
      · rw [ite_eq_right h3] at H
        rcases H with H | H
        · exact absurd H (errno_from_err_ret_no_unmodeled _ i m)
        · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H

/-! ## setresuid / setresgid -/

/-- Every branch of [check_setresid] answers, so it never declines. -/
theorem check_setresid_no_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m : Model) :
    check_setresid get put user r e s eff m ≠ .CheckUnmodeled := by
  intro H
  simp only [check_setresid] at H
  generalize hnr : (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) = nr at H
  generalize hne : (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) = ne at H
  generalize hns : (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) = ns at H
  by_cases h1 : (bv_eqb nr (get (m_creds m)).id_real &&
      bv_eqb ne (get (m_creds m)).id_eff &&
      bv_eqb ns (get (m_creds m)).id_saved) = true
  · rw [ite_eq_left h1] at H
    exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!( (bv_eqb nr (get (m_creds m)).id_real ||
          bv_eqb nr (get (m_creds m)).id_eff ||
          bv_eqb nr (get (m_creds m)).id_saved) &&
        (bv_eqb ne (get (m_creds m)).id_real ||
          bv_eqb ne (get (m_creds m)).id_eff ||
          bv_eqb ne (get (m_creds m)).id_saved) &&
        (bv_eqb ns (get (m_creds m)).id_real ||
          bv_eqb ns (get (m_creds m)).id_eff ||
          bv_eqb ns (get (m_creds m)).id_saved)) &&
      !(creds_privileged (m_creds m))) = true
    · rw [ite_eq_left h2] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EPERM) m [])
    · rw [ite_eq_right h2] at H
      exact absurd H (check_setid_result_no_unmodeled _ _ _ eff m)


theorem check_setresid_sound_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_setresid get put user r e s eff m = .CheckOk m' evs) :
    setresid_spec get put user r e s i m (.ok eff m' evs) := by
  generalize hP : (setresid_spec get put user r e s i m (.ok eff m' evs)) = Q at *
  simp only [check_setresid] at H
  generalize hnr : (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) = nr at H
  generalize hne : (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) = ne at H
  generalize hns : (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) = ns at H
  by_cases h1 : (bv_eqb nr (get (m_creds m)).id_real &&
      bv_eqb ne (get (m_creds m)).id_eff &&
      bv_eqb ns (get (m_creds m)).id_saved) = true
  · rw [ite_eq_left h1] at H
    obtain ⟨heff, hm', hevs⟩ :=
      (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [setresid_spec, getModelSpec, bind_getModel]
    rw [hnr, hne, hns]
    rw [ite_eq_left h1]
    simp only [ret_only, LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!( (bv_eqb nr (get (m_creds m)).id_real ||
          bv_eqb nr (get (m_creds m)).id_eff ||
          bv_eqb nr (get (m_creds m)).id_saved) &&
        (bv_eqb ne (get (m_creds m)).id_real ||
          bv_eqb ne (get (m_creds m)).id_eff ||
          bv_eqb ne (get (m_creds m)).id_saved) &&
        (bv_eqb ns (get (m_creds m)).id_real ||
          bv_eqb ns (get (m_creds m)).id_eff ||
          bv_eqb ns (get (m_creds m)).id_saved)) &&
      !(creds_privileged (m_creds m))) = true
    · rw [ite_eq_left h2] at H
      obtain ⟨heff, hm', hevs⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EPERM) m [] m' evs).mp H
      rw [heff, hm', hevs] at hP
      rw [← hP]
      simp only [setresid_spec, getModelSpec, bind_getModel]
      rw [hnr, hne, hns]
      rw [ite_eq_right h1]
      rw [ite_eq_left h2]
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right h2] at H
      have hc2 := set_creds_ret_only_ok (put (IdTriple.mkIdTriple nr ne ns) (m_creds m)) m i
      rw [← hP]
      simp only [setresid_spec, getModelSpec, bind_getModel]
      rw [hnr, hne, hns]
      rw [ite_eq_right h1]
      rw [ite_eq_right h2]
      exact check_setid_result_sound_ok _ _ _ _ i eff m m' evs hc2 H

theorem check_setresid_sound_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_setresid get put user r e s eff m = .CheckUnmodeled) :
    setresid_spec get put user r e s i m .unmodeled :=
  absurd H (check_setresid_no_unmodeled get put user r e s eff m)

theorem check_setresid_complete_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : setresid_spec get put user r e s i m (.ok eff m' evs)) :
    check_setresid get put user r e s eff m = .CheckOk m' evs := by
  generalize hP : (check_setresid get put user r e s eff m = .CheckOk m' evs) = Q at *
  simp only [setresid_spec, getModelSpec, bind_getModel] at H
  generalize hnr : (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) = nr at H
  generalize hne : (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) = ne at H
  generalize hns : (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) = ns at H
  by_cases h1 : (bv_eqb nr (get (m_creds m)).id_real &&
      bv_eqb ne (get (m_creds m)).id_eff &&
      bv_eqb ns (get (m_creds m)).id_saved) = true
  · rw [ite_eq_left h1] at H
    simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨heff, hm', hevs⟩ := H
    rw [heff, hm', hevs] at hP
    rw [← hP]
    simp only [check_setresid]
    rw [hnr, hne, hns]
    rw [ite_eq_left h1]
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!( (bv_eqb nr (get (m_creds m)).id_real ||
          bv_eqb nr (get (m_creds m)).id_eff ||
          bv_eqb nr (get (m_creds m)).id_saved) &&
        (bv_eqb ne (get (m_creds m)).id_real ||
          bv_eqb ne (get (m_creds m)).id_eff ||
          bv_eqb ne (get (m_creds m)).id_saved) &&
        (bv_eqb ns (get (m_creds m)).id_real ||
          bv_eqb ns (get (m_creds m)).id_eff ||
          bv_eqb ns (get (m_creds m)).id_saved)) &&
      !(creds_privileged (m_creds m))) = true
    · rw [ite_eq_left h2] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨heff, hm', hevs⟩ := H
      rw [heff, hm', hevs] at hP
      rw [← hP]
      simp only [check_setresid]
      rw [hnr, hne, hns]
      rw [ite_eq_right h1]
      rw [ite_eq_left h2]
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right h2] at H
      rcases H with H | H
      · obtain ⟨en, hmem, heff, hm', hevs⟩ := errno_from_err_ret_ok_inv _ i m eff m' evs H
        rw [heff, hm', hevs] at hP
        rw [← hP]
        simp only [check_setresid]
        rw [hnr, hne, hns]
        rw [ite_eq_right h1]
        rw [ite_eq_right h2]
        simp only [check_setid_result]
        rw [show errno_ret_in (setid_errnos (user && !(bv_eqb nr (get (m_creds m)).id_real)))
          (errno_ret en) = true from errno_ret_in_intro _ en hmem]
        simp only [ite_true]
      · obtain ⟨heff, hm', hevs⟩ :=
          modify_pure_inv (with_creds (put (IdTriple.mkIdTriple nr ne ns) (m_creds m)))
            (mkEffect (BitVec.ofInt 64 0) [] []) i m eff m' evs H
        rw [heff, hm', hevs] at hP
        rw [← hP]
        simp only [check_setresid]
        rw [hnr, hne, hns]
        rw [ite_eq_right h1]
        rw [ite_eq_right h2]
        simp only [check_setid_result]
        rw [show errno_ret_in (setid_errnos (user && !(bv_eqb nr (get (m_creds m)).id_real)))
          (BitVec.ofInt 64 0) = false from errno_ret_in_setid_zero _]
        simp only [Bool.false_eq_true, ite_false, bv_eqb_refl, ite_true]

theorem check_setresid_complete_unmodeled (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : setresid_spec get put user r e s i m .unmodeled) :
    check_setresid get put user r e s eff m = .CheckUnmodeled := by
  exfalso
  simp only [setresid_spec, getModelSpec, bind_getModel] at H
  generalize hnr : (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) = nr at H
  generalize hne : (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) = ne at H
  generalize hns : (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) = ns at H
  by_cases h1 : (bv_eqb nr (get (m_creds m)).id_real &&
      bv_eqb ne (get (m_creds m)).id_eff &&
      bv_eqb ns (get (m_creds m)).id_saved) = true
  · rw [ite_eq_left h1] at H
    simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!( (bv_eqb nr (get (m_creds m)).id_real ||
          bv_eqb nr (get (m_creds m)).id_eff ||
          bv_eqb nr (get (m_creds m)).id_saved) &&
        (bv_eqb ne (get (m_creds m)).id_real ||
          bv_eqb ne (get (m_creds m)).id_eff ||
          bv_eqb ne (get (m_creds m)).id_saved) &&
        (bv_eqb ns (get (m_creds m)).id_real ||
          bv_eqb ns (get (m_creds m)).id_eff ||
          bv_eqb ns (get (m_creds m)).id_saved)) &&
      !(creds_privileged (m_creds m))) = true
    · rw [ite_eq_left h2] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right h2] at H
      rcases H with H | H
      · exact absurd H (errno_from_err_ret_no_unmodeled _ i m)
      · exact absurd H (set_creds_ret_only_no_unmodeled _ i m)

end LinuxSem.Checks.Sys.Kernel.Sys
