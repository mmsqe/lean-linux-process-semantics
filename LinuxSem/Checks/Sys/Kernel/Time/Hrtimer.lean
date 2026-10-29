/-
  * LinuxProcessSem.Checks.Sys.Kernel.Time.Hrtimer — the nanosleep (101) checker, and its proofs

  Answers to Linux [kernel/time/hrtimer.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); a length is a `Nat` on both sides (so `16`, not
  `16%nat`); `in_mem i` is the record field `i.in_mem`; and an effect
  literal is the anonymous constructor pattern `⟨r, [], [], [], [], _⟩` over
  `SyscallEffect`.

  Both accepting arms end in a `match eff with` over the effect's shape, and
  every proof below has to read that match backwards or rule it out.  Four
  `private` shape lemmas (`eff_nils_ok`, `eff_mixed_ok`,
  `eff_nils_ne_unmodeled`, `eff_mixed_ne_unmodeled`) do it once — the same
  device `Checks.Sys.Kernel.Time.PosixTimers` uses for its one-write arms.

  The first test of both the spec and the checker is
  `!(timespec_valid_b req)` in front of a whole subtree, and in the spec that
  subtree is a `SysSpec`, a FUNCTION: the test sits over an `if` at function
  type, `(if … then … else …) i m o`.  Lean's `by_cases` both has to DECIDE
  that test and rewrites the `if` it finds in the goal, so on this shape it
  reduces `timespec_valid_b req` — `decide (tv_sec_of req < 2^63)` on an
  opaque `req` — and dies of `maximum recursion depth` rather than a
  finding.  The proofs below therefore split with `cases h : …` on the
  BOOLEAN (which rewrites the term without deciding it), rewrite the
  hypothesis with `h`, and discharge the now-literal `if true = true` /
  `if false = true` with the two `private` lemmas `ite_true_cond` /
  `ite_false_cond`.  Nothing is wrong with the statements — only with
  normalising a goal that still carries the undecided test.

  The `complete_*` directions start from the spec, so they run its steps
  backwards.  `Checks.Sys.Prelude` supplies the `input` / `record_copyins` /
  `getModel` peels; the `*_ok_inv` / `*_ne_unmodeled` lemmas in the
  scaffolding section below are the rest of what this spec's body uses
  (`ret_only`, `err_ret`, the `modify` that opens `slept`, and `choose`).
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

namespace LinuxSem.Checks.Sys.Kernel.Time.Hrtimer

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.LinuxProcessSem.Specs

/-- nanosleep: an unreadable request declines; an invalid one is
    -EINVAL; and otherwise BOTH outcomes are admissible, so the
    acceptor decides which arm it is being shown from the return value.

    THE REQUEST'S SECONDS FIELD GATES NOTHING.  A `tv_sec` at or
    above `Uapi.KTIME_SEC_MAX` does not decline here, and
    `Kernel.Time.Hrtimer.nanosleep_spec` says why it must not: the
    remainder the same spec may write reaches that band, and the
    standard retry loop feeds the remainder back as the next request.
    The conversion `ktime_set` performs lives in
    `Uapi.timespec_ktime` and is read by `nanosleep_clock`, not by a
    guard.

    - 0 with no writes is the completed sleep, and carries the whole
      request into `m_clock`, saturated at `Uapi.KTIME_MAX`.
    - -EINTR is the interruption.  With a NULL `rmtp` it carries no
      write and moves nothing, the slept duration being unknowable;
      with a non-NULL one it MUST carry exactly one write at `rmtp`
      that `Kernel.Time.Hrtimer.nanosleep_rem_ok_b` admits, and carries
      the part of the request that provably elapsed into `m_clock`.

    That last "must" is the sharp claim: with a remainder destination,
    an -EINTR and no write is REJECTED, because `do_nanosleep` reports
    success rather than an interruption when it has no positive
    remainder to write.

    AND EVERY ACCEPTED OUTCOME MUST CARRY THE COPY-IN.  The request
    reaches the kernel through `get_timespec64`, so an effect that
    claims one of these outcomes without the 16-byte read at `rqtp` in
    its ledger describes a kernel that decided the call without looking
    at the request, and is rejected.  The requirement sits on the
    accepting arms only: every `CheckUnmodeled` verdict is
    reached before any effect is inspected and must stay reachable
    whatever ledger that effect carries, or
    `check_nanosleep_complete_unmodeled` would be false.

    THERE IS NO GATE ON THE MODEL'S CLOCK EITHER.  A sleep whose
    deadline would leave `ktime_t` is one Linux serves at a saturated
    deadline rather than refusing, so
    `Kernel.Time.Hrtimer.nanosleep_clock` clamps and this acceptor
    reads `m` only to compute the new clock.  That is why the two
    declines that remain — an unreadable request and an unwritable
    `rmtp` — are decided without it, and why they are the only ones. -/
def check_nanosleep (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => .CheckUnmodeled
  | some req =>
      if !(timespec_valid_b req)
      then check_ret_only_copyins [(rqtp, 16)] eff (errno_ret EINVAL) m []
      else if w_is0 rmtp
      then
        check_copyins [(rqtp, 16)] eff
        (match eff with
         | ⟨r, [], [], [], [], _⟩ =>
             if bv_eqb r (BitVec.ofInt 64 0)
             then .CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
             else if bv_eqb r (errno_ret EINTR) then .CheckOk m []
             else .CheckReject
         | _ => .CheckReject)
      else
        match read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none => .CheckUnmodeled
        | some _ =>
            check_copyins [(rqtp, 16)] eff
            (match eff with
             | ⟨r, [], [], [], [], _⟩ =>
                 if bv_eqb r (BitVec.ofInt 64 0)
                 then .CheckOk (with_clock (nanosleep_clock (m_clock m) req []) m) []
                 else .CheckReject
             | ⟨r, [(a, rem)], [], [], [], _⟩ =>
                 if bv_eqb r (errno_ret EINTR) && bv_eqb a rmtp
                    && nanosleep_rem_ok_b rem
                 then .CheckOk
                        (with_clock (nanosleep_clock (m_clock m) req rem) m) []
                 else .CheckReject
             | _ => .CheckReject)

/-! ## The branch lemmas

    The four `eff_*` lemmas read the checker's `match eff with` backwards
    (or rule it out); the two `ite_*_cond` lemmas reduce an `if` whose test
    `cases` has already rewritten to a literal (see the file header's
    note on the function-type `if`); the `*_ok_inv` /
    `*_ne_unmodeled` lemmas read the spec's arm bodies back, which is
    what the `complete_*` directions need. -/

/-- An acceptance of the NIL-writes arm names the return value, fixes the
    effect to that return with empty writes/zeros/unmaps/copies and an
    arbitrary ledger, and passes the acceptance on to the branch body. -/
private theorem eff_nils_ok {f : word → check_result} {eff : SyscallEffect}
    {m' : Model} {evs : List event}
    (H : (match eff with
          | ⟨r, [], [], [], [], _⟩ => f r
          | _ => .CheckReject) = .CheckOk m' evs) :
    ∃ (r : word) (ks : List (word × Nat)),
      eff = ⟨r, [], [], [], [], ks⟩ ∧ f r = .CheckOk m' evs := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  split at H
  · rename_i r' ks' heq
    exact ⟨r', ks', heq, H⟩
  · exact nomatch H

/-- An acceptance of the TWO-SHAPE arm is one of its two shapes, with the
    acceptance passed on to the matching branch body. -/
private theorem eff_mixed_ok {f : word → check_result}
    {g : word → word → List byte → check_result} {eff : SyscallEffect}
    {m' : Model} {evs : List event}
    (H : (match eff with
          | ⟨r, [], [], [], [], _⟩ => f r
          | ⟨r, [(a, rem)], [], [], [], _⟩ => g r a rem
          | _ => .CheckReject) = .CheckOk m' evs) :
    (∃ (r : word) (ks : List (word × Nat)),
        eff = ⟨r, [], [], [], [], ks⟩ ∧ f r = .CheckOk m' evs) ∨
    (∃ (r a : word) (rem : List byte) (ks : List (word × Nat)),
        eff = ⟨r, [(a, rem)], [], [], [], ks⟩ ∧ g r a rem = .CheckOk m' evs) := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  split at H
  · rename_i r' ks' heq
    exact Or.inl ⟨r', ks', heq, H⟩
  · rename_i r' a' rem' ks' heq
    exact Or.inr ⟨r', a', rem', ks', heq, H⟩
  · exact nomatch H

/-- Neither shape of the two-shape arm, nor its fallback, is
    `CheckUnmodeled`: the arm can never decline. -/
private theorem eff_mixed_ne_unmodeled {f : word → check_result}
    {g : word → word → List byte → check_result}
    (hf : ∀ r, f r ≠ .CheckUnmodeled)
    (hg : ∀ r a rem, g r a rem ≠ .CheckUnmodeled) (eff : SyscallEffect) :
    (match eff with
     | ⟨r, [], [], [], [], _⟩ => f r
     | ⟨r, [(a, rem)], [], [], [], _⟩ => g r a rem
     | _ => .CheckReject) ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro hh
  split at hh
  · rename_i r' ks' heq
    exact hf _ hh
  · rename_i r' a' rem' ks' heq
    exact hg _ _ _ hh
  · exact nomatch hh

/-- The same, for the single-shape arm. -/
private theorem eff_nils_ne_unmodeled {f : word → check_result}
    (hf : ∀ r, f r ≠ .CheckUnmodeled) (eff : SyscallEffect) :
    (match eff with
     | ⟨r, [], [], [], [], _⟩ => f r
     | _ => .CheckReject) ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro hh
  split at hh
  · rename_i r' ks' heq
    exact hf _ hh
  · exact nomatch hh

/-- `ret_only` answers its argument, with the model and events untouched. -/
private theorem ret_only_ok_inv {r : word} {i : SyscallInput} {m : Model}
    {core : SyscallEffect} {m' : Model} {evs : List event}
    (H : ret_only r i m (.ok core m' evs)) :
    core = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  simp only [ret_only, LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
  exact H

/-- `err_ret e` is `ret_only` of the negated errno. -/
private theorem err_ret_ok_inv {e : Int} {i : SyscallInput} {m : Model}
    {core : SyscallEffect} {m' : Model} {evs : List event}
    (H : err_ret e i m (.ok core m' evs)) :
    core = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] :=
  ret_only_ok_inv H

/-- `ret_only` never declines. -/
private theorem ret_only_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ret_only r i m .unmodeled → False := by
  intro H
  simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
  exact nomatch H

/-- `err_ret` never declines either. -/
private theorem err_ret_ne_unmodeled (e : Int) (i : SyscallInput) (m : Model) :
    err_ret e i m .unmodeled → False :=
  ret_only_ne_unmodeled (errno_ret e) i m

/-- The completed-sleep arm of the spec, read back: `slept` is a `modify`
    the arm cannot fail on, followed by `ret_only`, so an outcome is the
    clock write, its model, and no event. -/
private theorem slept_ok_inv {f : Model → Model} {r : word} {i : SyscallInput}
    {m : Model} {core : SyscallEffect} {m' : Model} {evs : List event}
    (H : seqSpec (modifySpec f) (ret_only r) i m (.ok core m' evs)) :
    core = mkEffect r [] [] ∧ m' = f m ∧ evs = [] := by
  unfold seqSpec at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := H
  have hc' : x = () ∧ m1 = f m ∧ evs1 = [] := by
    simpa only [modifySpec, LinuxSem.LinuxProcessSem.modify,
      Outcome.ok.injEq] using hc
  obtain ⟨rfl, rfl, rfl⟩ := hc'
  obtain ⟨hcore, hm', hevs2⟩ := ret_only_ok_inv hk
  refine ⟨hcore, hm', ?_⟩
  rw [hevs, hevs2]
  rfl

/-- …and the same arm never declines. -/
private theorem slept_ne_unmodeled {f : Model → Model} {r : word}
    (i : SyscallInput) (m : Model) :
    seqSpec (modifySpec f) (ret_only r) i m .unmodeled → False := by
  intro H
  unfold seqSpec at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with hc | ⟨x, m1, evs1, hc, hk⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at hc
    exact nomatch hc
  · exact ret_only_ne_unmodeled r i m1 hk

/-- The interruption arm's body, read back: the same `modify`, followed
    by the remainder write's `pure`. -/
private theorem rem_ok_inv {f : Model → Model} {r : word}
    {w : List (word × List byte)} {i : SyscallInput} {m : Model}
    {core : SyscallEffect} {m' : Model} {evs : List event}
    (H : seqSpec (modifySpec f) (pure (mkEffect r w [])) i m (.ok core m' evs)) :
    core = mkEffect r w [] ∧ m' = f m ∧ evs = [] := by
  unfold seqSpec at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := H
  have hc' : x = () ∧ m1 = f m ∧ evs1 = [] := by
    simpa only [modifySpec, LinuxSem.LinuxProcessSem.modify,
      Outcome.ok.injEq] using hc
  obtain ⟨rfl, rfl, rfl⟩ := hc'
  simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hk
  obtain ⟨hcore, hm', hevs2⟩ := hk
  refine ⟨hcore, hm', ?_⟩
  rw [hevs, hevs2]
  rfl

/-- The interruption arm never declines either. -/
private theorem rem_ne_unmodeled {f : Model → Model} {e : SyscallEffect}
    (i : SyscallInput) (m : Model) :
    seqSpec (modifySpec f) (pure e) i m .unmodeled → False := by
  intro H
  unfold seqSpec at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with hc | ⟨x, m1, evs1, hc, hk⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at hc
    exact nomatch hc
  · simp only [LinuxSem.LinuxProcessSem.pure] at hk
    exact nomatch hk

/-- What the acceptor demands of the ledger, read back out of an
    acceptance.  Soundness needs it before it can peel
    `record_copyins`, because the ledger has to be known before the
    effect can be split into the part the body produces and the part
    the wrapper prepends. -/
private theorem check_nanosleep_ok_copyins (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_nanosleep i rqtp rmtp eff m = .CheckOk m' evs) :
    eff.eff_copyins = [(rqtp, 16)] := by
  unfold check_nanosleep at H
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => rw [hrq] at H; exact nomatch H
  | some req =>
    rw [hrq] at H
    dsimp only at H
    cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [hv] at H
      rw [ite_true_cond] at H
      obtain ⟨heff, -⟩ := (check_ret_only_copyins_ok_iff [(rqtp, 16)] eff
        (errno_ret EINVAL) m [] m' evs).mp H
      rw [heff]
      rfl
    | false =>
      rw [hv] at H
      rw [ite_false_cond] at H
      cases hrm : w_is0 rmtp with
      | true =>
        rw [hrm] at H
        rw [ite_true_cond] at H
        unfold check_copyins at H
        by_cases hacc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] = true
        · exact (access_ranges_eqb_eq _ _).mp hacc
        · rw [ite_eq_right hacc] at H
          exact nomatch H
      | false =>
        rw [hrm] at H
        rw [ite_false_cond] at H
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none => rw [hwm] at H; exact nomatch H
        | some bs0 =>
          rw [hwm] at H
          dsimp only at H
          unfold check_copyins at H
          by_cases hacc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] = true
          · exact (access_ranges_eqb_eq _ _).mp hacc
          · rw [ite_eq_right hacc] at H
            exact nomatch H

/-- Peeling `record_copyins` off the spec on the accepting side.  The
    acceptor has already forced the effect's ledger to be exactly the
    request's copy-in, so what is left to prove is the arm's body
    against the same effect with an empty ledger.  All four proofs
    below reach this step. -/
private theorem nanosleep_ledger_ok (rqtp : word) (spec : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (ret : word) (ws : List (word × List byte))
    (zs us : List (word × word)) (cs : List MemCopy) (m' : Model) (evs : List event)
    (H : spec i m (.ok (⟨ret, ws, zs, us, cs, []⟩ : SyscallEffect) m' evs)) :
    record_copyins [(rqtp, 16)] spec i m
      (.ok (⟨ret, ws, zs, us, cs, [(rqtp, 16)]⟩ : SyscallEffect) m' evs) :=
  record_copyins_ok_empty rfl H

/-- The field equations of an equality between two literal effects: the
    return value and the four memory lists (the ledger is left out, since
    the callers either keep it or have already fixed it). -/
private theorem effect_fields {a b : word} {w1 w2 : List (word × List byte)}
    {z1 z2 u1 u2 : List (word × word)} {c1 c2 : List MemCopy}
    {k1 k2 : List (word × Nat)}
    (h : (⟨a, w1, z1, u1, c1, k1⟩ : SyscallEffect) = ⟨b, w2, z2, u2, c2, k2⟩) :
    a = b ∧ w1 = w2 ∧ z1 = z2 ∧ u1 = u2 ∧ c1 = c2 :=
  ⟨congrArg SyscallEffect.eff_ret h, congrArg SyscallEffect.eff_writes h,
   congrArg SyscallEffect.eff_zeros h, congrArg SyscallEffect.eff_unmaps h,
   congrArg SyscallEffect.eff_copies h⟩

/-- What an acceptance of `check_copyins` forces: the claimed ledger is
    the one demanded, and the arm's own body accepted. -/
private theorem check_copyins_ok_iff (reads : List (word × Nat)) (eff : SyscallEffect)
    (result : check_result) (m : Model) (evs : List event) :
    check_copyins reads eff result = .CheckOk m evs ↔
      eff.eff_copyins = reads ∧ result = .CheckOk m evs := by
  unfold check_copyins
  by_cases h : access_ranges_eqb eff.eff_copyins reads = true
  · rw [ite_eq_left h]
    exact ⟨fun hr => ⟨(access_ranges_eqb_eq _ _).mp h, hr⟩, fun hh => hh.2⟩
  · rw [ite_eq_right h]
    constructor
    · intro hc
      exact nomatch hc
    · rintro ⟨heff, -⟩
      rw [heff] at h
      exact absurd (access_ranges_eqb_refl reads) h

/-! ## The checker ≡ the spec -/

theorem check_nanosleep_sound_ok (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_nanosleep i rqtp rmtp eff m = .CheckOk m' evs) :
    nanosleep_spec rqtp rmtp i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  have hks : ks = [(rqtp, 16)] :=
    check_nanosleep_ok_copyins i rqtp rmtp ⟨ret, ws, zs, us, cs, ks⟩ m m' evs H
  subst hks
  unfold check_nanosleep at H
  unfold nanosleep_spec
  refine bind_ok0 inputSpec _ i m i m _ _ _ rfl ?_
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => rw [hrq] at H; exact nomatch H
  | some req =>
    rw [hrq] at H
    dsimp only at H
    refine nanosleep_ledger_ok rqtp _ i m ret ws zs us cs m' evs ?_
    cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [hv] at H
      rw [ite_true_cond] at H
      rw [ite_true_cond]
      obtain ⟨heff, rfl, rfl⟩ := (check_ret_only_copyins_ok_iff [(rqtp, 16)] _
        (errno_ret EINVAL) m [] m' evs).mp H
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := effect_fields heff
      rfl
    | false =>
      rw [hv] at H
      rw [ite_false_cond] at H
      rw [ite_false_cond]
      refine bind_ok0 getModelSpec _ i m m m _ _ _ rfl ?_
      cases hrm : w_is0 rmtp with
      | true =>
        rw [hrm] at H
        rw [ite_true_cond] at H
        rw [ite_true_cond]
        obtain ⟨hacc, hres⟩ := (check_copyins_ok_iff [(rqtp, 16)] _ _ m' evs).mp H
        obtain ⟨rr, kks, heq, hf⟩ := eff_nils_ok hres
        obtain ⟨hret, hws, hzs, hus, hcs⟩ := effect_fields heq
        rw [hret, hws, hzs, hus, hcs]
        cases h0 : bv_eqb rr (BitVec.ofInt 64 0) with
        | true =>
          rw [h0] at hf
          rw [ite_true_cond] at hf
          simp only [check_result.CheckOk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          rw [Fs.bv_eqb_eq] at h0
          subst h0
          refine alt_l _ _ i m _ ?_
          refine bind_ok0 (modifySpec (with_clock (nanosleep_clock (m_clock m) req []))) _
            i m () (with_clock (nanosleep_clock (m_clock m) req []) m) _ _ [] rfl ?_
          exact pure_ok _ _ _
        | false =>
          rw [h0] at hf
          rw [ite_false_cond] at hf
          cases he : bv_eqb rr (errno_ret EINTR) with
          | true =>
            rw [he] at hf
            rw [ite_true_cond] at hf
            simp only [check_result.CheckOk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            rw [Fs.bv_eqb_eq] at he
            subst he
            refine alt_r _ _ i m _ ?_
            rfl
          | false =>
            rw [he] at hf
            rw [ite_false_cond] at hf
            exact nomatch hf
      | false =>
        rw [hrm] at H
        rw [ite_false_cond] at H
        rw [ite_false_cond]
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none =>
          rw [hwm] at H
          dsimp only at H
          exact nomatch H
        | some bs0 =>
          rw [hwm] at H
          dsimp only at H
          obtain ⟨hacc, hres⟩ := (check_copyins_ok_iff [(rqtp, 16)] _ _ m' evs).mp H
          rcases eff_mixed_ok hres with ⟨rr, kks, heq, hf⟩ | ⟨rr, aa, rem, kks, heq, hf⟩
          · obtain ⟨hret, hws, hzs, hus, hcs⟩ := effect_fields heq
            rw [hret, hws, hzs, hus, hcs]
            cases h0 : bv_eqb rr (BitVec.ofInt 64 0) with
            | true =>
              rw [h0] at hf
              rw [ite_true_cond] at hf
              simp only [check_result.CheckOk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              rw [Fs.bv_eqb_eq] at h0
              subst h0
              refine alt_l _ _ i m _ ?_
              refine bind_ok0 (modifySpec (with_clock (nanosleep_clock (m_clock m) req []))) _
                i m () (with_clock (nanosleep_clock (m_clock m) req []) m) _ _ [] rfl ?_
              exact pure_ok _ _ _
            | false =>
              rw [h0] at hf
              rw [ite_false_cond] at hf
              exact nomatch hf
          · obtain ⟨hret, hws, hzs, hus, hcs⟩ := effect_fields heq
            rw [hret, hws, hzs, hus, hcs]
            cases hok : (bv_eqb rr (errno_ret EINTR) && bv_eqb aa rmtp
              && nanosleep_rem_ok_b rem) with
            | true =>
              rw [hok] at hf
              rw [ite_true_cond] at hf
              simp only [check_result.CheckOk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true] at hok
              obtain ⟨⟨hr, ha⟩, hrem⟩ := hok
              rw [Fs.bv_eqb_eq] at hr ha
              subst hr; subst ha
              refine alt_r _ _ i m _ ?_
              refine bind_ok0 (choose (fun rem => nanosleep_rem_ok_b rem = true)) _
                i m rem m _ _ _ (choose_ok _ rem i m hrem) ?_
              refine bind_ok0 (modifySpec (with_clock (nanosleep_clock (m_clock m) req rem))) _
                i m () (with_clock (nanosleep_clock (m_clock m) req rem) m) _ _ [] rfl ?_
              exact pure_ok _ i _
            | false =>
              rw [hok] at hf
              rw [ite_false_cond] at hf
              exact nomatch hf

theorem check_nanosleep_sound_unmodeled (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_nanosleep i rqtp rmtp eff m = .CheckUnmodeled) :
    nanosleep_spec rqtp rmtp i m .unmodeled := by
  unfold check_nanosleep at H
  unfold nanosleep_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none =>
    exact unmodeled_intro i m
  | some req =>
    rw [hrq] at H
    dsimp only at H
    refine record_copyins_unmodeled ?_
    cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [hv] at H
      rw [ite_true_cond] at H
      exact absurd H (check_ret_only_copyins_no_unmodeled [(rqtp, 16)] eff
        (errno_ret EINVAL) m [])
    | false =>
      rw [hv] at H
      rw [ite_false_cond] at H
      refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
      cases hrm : w_is0 rmtp with
      | true =>
        rw [hrm] at H
        rw [ite_true_cond] at H
        unfold check_copyins at H
        by_cases hacc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] = true
        · rw [ite_eq_left hacc] at H
          exact absurd H (eff_nils_ne_unmodeled (fun r => by
            intro hh
            cases h0 : bv_eqb r (BitVec.ofInt 64 0) with
            | true => rw [h0, ite_true_cond] at hh; exact nomatch hh
            | false =>
              rw [h0, ite_false_cond] at hh
              cases he : bv_eqb r (errno_ret EINTR) with
              | true => rw [he, ite_true_cond] at hh; exact nomatch hh
              | false => rw [he, ite_false_cond] at hh; exact nomatch hh) eff)
        · rw [ite_eq_right hacc] at H
          exact nomatch H
      | false =>
        rw [hrm] at H
        rw [ite_false_cond] at H
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none =>
          exact unmodeled_intro i m
        | some bs0 =>
          rw [hwm] at H
          dsimp only at H
          unfold check_copyins at H
          by_cases hacc : access_ranges_eqb eff.eff_copyins [(rqtp, 16)] = true
          · rw [ite_eq_left hacc] at H
            exact absurd H (eff_mixed_ne_unmodeled
              (fun r => by
                intro hh
                cases h0 : bv_eqb r (BitVec.ofInt 64 0) with
                | true => rw [h0, ite_true_cond] at hh; exact nomatch hh
                | false => rw [h0, ite_false_cond] at hh; exact nomatch hh)
              (fun r a rem => by
                intro hh
                cases hok : (bv_eqb r (errno_ret EINTR) && bv_eqb a rmtp
                  && nanosleep_rem_ok_b rem) with
                | true => rw [hok, ite_true_cond] at hh; exact nomatch hh
                | false => rw [hok, ite_false_cond] at hh; exact nomatch hh) eff)
          · rw [ite_eq_right hacc] at H
            exact nomatch H

theorem check_nanosleep_complete_ok (i : SyscallInput) (rqtp rmtp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : nanosleep_spec rqtp rmtp i m (.ok eff m' evs)) :
    check_nanosleep i rqtp rmtp eff m = .CheckOk m' evs := by
  unfold check_nanosleep
  unfold nanosleep_spec at H
  have h1 := input_bind_ok_inv _ i m eff m' evs H
  dsimp only at h1
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => rw [hrq] at h1; exact nomatch h1
  | some req =>
    rw [hrq] at h1
    dsimp only at h1
    dsimp only
    obtain ⟨core, Hcore, heff⟩ := record_copyins_ok_inv [(rqtp, 16)] _ i m eff m' evs h1
    cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [hv] at Hcore
      rw [ite_true_cond] at Hcore
      obtain ⟨hcore, hm', hevs⟩ := err_ret_ok_inv Hcore
      rw [heff, hcore, hm', hevs]
      try dsimp only
      exact check_ret_only_copyins_refl [(rqtp, 16)] (errno_ret EINVAL) m []
    | false =>
      rw [hv] at Hcore
      rw [ite_false_cond] at Hcore
      have h2 := get_model_bind_ok_inv _ i m core m' evs Hcore
      cases hrm : w_is0 rmtp with
      | true =>
        rw [hrm] at h2
        rw [ite_true_cond] at h2
        try dsimp only
        rcases h2 with h2 | h2
        · obtain ⟨hcore, hm', hevs⟩ := slept_ok_inv h2
          subst hcore; subst hm'; subst hevs
          rw [heff]
          dsimp only
          refine (check_copyins_ok_iff [(rqtp, 16)] _ _ _ _).mpr ⟨rfl, ?_⟩
          rfl
        · obtain ⟨hcore, hm', hevs⟩ := err_ret_ok_inv h2
          rw [heff, hcore, hm', hevs]
          try dsimp only
          refine (check_copyins_ok_iff [(rqtp, 16)] _ _ _ _).mpr ⟨rfl, ?_⟩
          rfl
      | false =>
        rw [hrm] at h2
        rw [ite_false_cond] at h2
        try dsimp only
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none =>
          rw [hwm] at h2
          dsimp only at h2
          exact nomatch h2
        | some bs0 =>
          rw [hwm] at h2
          dsimp only at h2
          try dsimp only
          rcases h2 with h2 | h2
          · obtain ⟨hcore, hm', hevs⟩ := slept_ok_inv h2
            rw [heff, hcore, hm', hevs]
            try dsimp only
            refine (check_copyins_ok_iff [(rqtp, 16)] _ _ _ _).mpr ⟨rfl, ?_⟩
            rfl
          · obtain ⟨rem, hrem, h2⟩ := choose_bind_ok_inv _ _ _ _ _ _ _ h2
            obtain ⟨hcore, hm', hevs⟩ := rem_ok_inv h2
            rw [heff, hcore, hm', hevs]
            try dsimp only
            refine (check_copyins_ok_iff [(rqtp, 16)] _ _ _ _).mpr ⟨rfl, ?_⟩
            /- Unfold `with_copyins` before the rewrite: `rw` no longer
               `whnf`s the target, so the `match` on
               `with_copyins … (mkEffect … (rmtp, rem) …)` stays stuck and
               `bv_eqb rmtp rmtp` is not yet IN the goal — only the arm's
               pattern variable `a` is.  `simp only` performs the
               unfolding and lets the arm compute. -/
            simp only [with_copyins]
            rw [show bv_eqb rmtp rmtp = true from bv_eqb_refl rmtp, hrem]
            rfl

theorem check_nanosleep_complete_unmodeled (i : SyscallInput) (rqtp rmtp : word)
    (m : Model) (eff : SyscallEffect)
    (H : nanosleep_spec rqtp rmtp i m .unmodeled) :
    check_nanosleep i rqtp rmtp eff m = .CheckUnmodeled := by
  unfold check_nanosleep
  unfold nanosleep_spec at H
  have h1 := input_bind_unmodeled_inv _ i m H
  dsimp only at h1
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => rfl
  | some req =>
    rw [hrq] at h1
    dsimp only at h1
    -- `record_copyins`'s `spec` argument is the spec's body — an `if` at
    -- FUNCTION type — and asking the inversion lemma to unify its `spec`
    -- metavariable with that term loops (the same obstacle the file
    -- header records for `by_cases`).  Peeling it in place avoids the
    -- unification; the second `bind` branch is `pure`'s and cannot decline.
    unfold record_copyins at h1
    unfold LinuxSem.LinuxProcessSem.bind at h1
    rcases h1 with h2 | ⟨eff0, m1, evs1, h2, himp⟩
    · dsimp only
      cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [hv] at h2
      rw [ite_true_cond] at h2
      try dsimp only
      exact absurd h2 (err_ret_ne_unmodeled EINVAL i m)
    | false =>
      rw [hv] at h2
      rw [ite_false_cond] at h2
      try dsimp only
      have h3 := get_model_bind_unmodeled_inv _ i m h2
      cases hrm : w_is0 rmtp with
      | true =>
        rw [hrm] at h3
        rw [ite_true_cond] at h3
        try dsimp only
        rcases h3 with h3 | h3
        · exact absurd h3 (slept_ne_unmodeled i m)
        · exact absurd h3 (err_ret_ne_unmodeled EINTR i m)
      | false =>
        rw [hrm] at h3
        rw [ite_false_cond] at h3
        try dsimp only
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none => rfl
        | some bs0 =>
          rw [hwm] at h3
          dsimp only at h3
          try dsimp only
          rcases h3 with h3 | h3
          · exact absurd h3 (slept_ne_unmodeled i m)
          · obtain ⟨rem, hrem, h3⟩ := choose_bind_unmodeled_inv _ _ _ _ h3
            exact absurd h3 (rem_ne_unmodeled i m)
    · simp only [LinuxSem.LinuxProcessSem.pure] at himp
      exact nomatch himp

end LinuxSem.Checks.Sys.Kernel.Time.Hrtimer





