/-
  * LinuxProcessSem.Checks.Sys.Kernel.Signal — the rt_sigaction (134) and rt_sigprocmask (135) checkers, and their proofs

  Answers to Linux [kernel/signal.c]: this file holds the checkers for the syscalls
  defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The file also holds the tkill (130), tgkill (131) and sigaltstack (132)
  checkers, the two named in the title first and the three below them.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`;
  words are 64 bits and `bv_and` is `&&&`; a size test is an `Int`
  comparison (`((ss_size_of bs).toNat : Int) < MINSIGSTKSZ`); an effect
  literal is the anonymous constructor pattern
  `⟨r, [], [], [], [], []⟩`, `mkEffect` being the three-field abbreviation;
  and `%bool` on `&&` is `&&` on `Bool`.

  `bv_eqb` is `a == b` (`Riscv.Prelude.bv_eqb`), so the two spellings name
  the same function.  The checkers below spell the tests `==`, matching
  `Sys/Kernel/Signal.lean`, because a bootstrap lemma (`bind_inputSpec`,
  `check_write_oset_ok_iff`, …) then matches the spec's own `if` conditions
  syntactically instead of relying on defeq — `simp only [ite_eq_left h]` does
  not see through `bv_eqb`.  The same reason makes `check_ret_only`'s
  `bv_eqb` (in `Checks.Sys.Prelude`, where the spec side is an equality of
  effects and not an `if`) the one place the older spelling survives.

  Each proof peels the spec's `get_model`/`input` readers with
  `bind_getModel` and with `bind_inputSpec` (the canonical
  `LinuxSem.LinuxProcessSem` one, reached through the `open` below) — one
  `↔` covering both directions and both outcome shapes, so
  `simp only [bind_inputSpec]` peels it wherever it sits.  `dsimp only`
  performs the beta/iota/zeta reduction, and a `CheckUnmodeled = CheckOk`
  equation is eliminated by `nomatch`.

  A spec is a `SysSpec`, a FUNCTION, so its body is an `if` at function
  type (`(if … then unmodeled else …) i m o`).  Lean's `whnf` on a goal
  that mentions it tries to reduce that `if`, which means deciding a test on
  an opaque word (`(ss_size_of bs).toNat < MINSIGSTKSZ` above all, whose
  `Decidable` instance unfolds through `BitVec.toNat`); `by_cases`
  normalises its goal, so it can recurse without bottoming out.  Every
  proof here therefore `generalize`s its conclusion into a local `Q : Prop`
  first, splits against `Q` (an opaque variable, so no reduction happens),
  and only then rewrites `Q` back into the spec and discharges the branch
  with `simp only`.

  `sigaltstack_at`, `sigset_at`, `sigaction_flags` and `m_tid` are
  `match`ed on.  Lean's `cases h : f x with` reduces the `match` in the
  immediate goal but NOT in a hypothesis already collected, so the proofs
  below follow the `cases` with `simp only [h] at H` when the `match` sits
  in `H`.  Where the `match` is inside a recorded `let` or behind a `bind`,
  the equation is rewritten explicitly.

  `ite_eq_right h` needs `h : ¬ c` for the very `c` of the `if` in the goal, and
  a `(by …)` argument inside a `simp only [...]` list is elaborated BEFORE
  simp sees the goal, so its `c` is still a metavariable.  Hypotheses of the
  shape `b = false` are therefore consumed with
  `rw [check_x, ite_eq_right (by rw [h]; …)]` (a sequential `rw` knows the goal)
  rather than in a `simp only` list, and the `= false` reading is what
  `check_write_oset_efault` / `check_write_oset_stored` state
  (`negb b = true` is `b = false`, the same test with the `Bool` unboxed).
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Signal

namespace LinuxSem.Checks.Sys.Kernel.Signal

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
open LinuxSem.Checks.Sys.Prelude

/-- The spec monad's [bind] under an unambiguous name.  Lean's root [bind]
    is [Bind.bind], so the unqualified name is ambiguous; the notation gives
    every statement below one spelling.  (Tactic arguments still need the
    fully qualified name where the notation cannot reach, e.g. inside
    `simp only` lists with binders.) -/
local notation "bind" => LinuxSem.LinuxProcessSem.bind

/-! ## sigaltstack (132) -/

/-- sigaltstack: no arm touches user memory, so every admissible outcome
    is a bare return; exactly one of them carries the model forward with
    the alternate-stack bit set, the install.  SS_DISABLE succeeds and
    does NOT set it: the kernel zeroes [ss_size] before the store, so the
    record stays in the shape the arms below can answer from.  The
    declining arms are the ones whose answer would need the user stack
    pointer, or the stored flags word (see [Signal.sigaltstack_spec]). -/
def check_sigaltstack (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if m_sigaltstack_installed m then .CheckUnmodeled
  else if !(w_is0 uoss) then .CheckUnmodeled
  else if w_is0 uss then check_ret_only eff (BitVec.ofInt 64 0) m []
  else
    match sigaltstack_at i.in_mem uss with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some bs =>
        if !(ss_mode_ok (ss_flags_of bs))
        then check_ret_only eff (errno_ret EINVAL) m []
        else if ss_disabling (ss_flags_of bs)
        then check_ret_only eff (BitVec.ofInt 64 0) m []
        else if (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))
        then .CheckUnmodeled
        else if ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
        then check_ret_only eff (errno_ret ENOMEM) m []
        else check_ret_only eff (BitVec.ofInt 64 0) (with_sigaltstack_installed m) []

/-! ## rt_sigaction (134) -/

/-- rt_sigaction: nothing is recorded, so every admissible outcome is a
    bare return; the declining arms are the ones whose answer would need
    a stored disposition (see [Signal.rt_sigaction_spec]). -/
def check_rt_sigaction (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(ss == BitVec.ofInt 64 8)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(w_is0 oact) then .CheckUnmodeled
  else if w_is0 act
  then (if sig_valid sig then check_ret_only eff (BitVec.ofInt 64 0) m []
        else check_ret_only eff (errno_ret EINVAL) m [])
  else
    match sigaction_flags i.in_mem act with
    | none => check_ret_only eff (errno_ret EFAULT) m []
    | some fl =>
        if !(sig_valid sig) then check_ret_only eff (errno_ret EINVAL) m []
        else if sig_kernel_only sig then check_ret_only eff (errno_ret EINVAL) m []
        else if !(sa_flags_ok fl) then .CheckUnmodeled
        else if sigaction_accepted sig then check_ret_only eff (BitVec.ofInt 64 0) m []
        else .CheckUnmodeled

/-- An effect that is exactly one write and nothing else, in the shape
    [check_ret_only] has for an effect that is nothing at all.  Local to
    this file because one syscall produces that shape; it moves to
    [Checks.Sys.Prelude] when a second one does. -/
def check_one_write (eff : SyscallEffect) (r a : word)
    (bs : List byte) (m' : Model) : check_result :=
  match eff with
  | ⟨ret, ws, [], [], [], []⟩ =>
      if bv_eqb ret r && writes_eqb ws [(a, bs)]
      then .CheckOk m' [] else .CheckReject
  | _ => .CheckReject

/-- The [oset] copy-out acceptor, mirroring [Kernel.Signal.write_oset]
    arm for arm and testing the same booleans in the same order —
    [State.access_okb] BEFORE the [in_wmem] walk, because the walk wraps
    at 2^64 and the range test does not.

    Both answering arms demand an empty copy-in ledger, which is what
    [write_oset] itself produces; the callers that run it under a
    [Syscall.record_copyins] use [check_write_oset_copyins] below. -/
def check_write_oset (i : SyscallInput) (oset old : word)
    (eff : SyscallEffect) (m' : Model) : check_result :=
  if !(access_okb oset NSIG_BYTES)
  then check_ret_only eff (errno_ret EFAULT) m' []
  else
    match read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
    | none => .CheckUnmodeled
    | some _ =>
        check_one_write eff (BitVec.ofInt 64 0) oset
          (Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int)) m'

/-- The same, under a recorded copy-in ledger.  [check_ret_only_copyins]
    stands to [check_ret_only] exactly as this stands to
    [check_write_oset], and for the same reason: the ledger is attached
    outside the arm that produced the effect. -/
def check_write_oset_copyins (reads : List (word × Nat))
    (i : SyscallInput) (oset old : word) (eff : SyscallEffect) (m' : Model)
    : check_result :=
  match check_write_oset i oset old (clear_copyins eff) m' with
  | .CheckOk m'' evs =>
      if access_ranges_eqb eff.eff_copyins reads
      then .CheckOk m'' evs else .CheckReject
  | result => result

/-- rt_sigprocmask's acceptor, mirroring
    [Kernel.Signal.rt_sigprocmask_spec].

    The arms that answer WITHOUT touching [oset] still use
    [check_ret_only], which demands all five effect lists be empty — so
    an effect claiming a write on the bad-size -EINVAL, or on the [nset]
    -EFAULT, is rejected rather than accepted as an inert errno.  That
    is what separates the two -EFAULTs this syscall can return: the one
    raised by [copy_from_user] writes nothing and RECORDS nothing, and
    the one raised by [copy_to_user] writes nothing and records the
    eight bytes it had already read. -/
def check_rt_sigprocmask (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(ss == BitVec.ofInt 64 NSIG_BYTES)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let old := m_sigmask m
    if w_is0 nset
    then (if w_is0 oset then check_ret_only eff (BitVec.ofInt 64 0) m []
          else check_write_oset i oset old eff m)
    else
      match sigset_at i.in_mem nset with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some raw =>
          if !(how_valid how)
          then check_ret_only_copyins [(nset, NSIG_BYTES.toNat)]
                 eff (errno_ret EINVAL) m []
          else
            let m' := sigmask_deliver_model
                        (sigmask_apply how old (sigmask_strip raw)) m
            if w_is0 oset
            then check_ret_only_copyins [(nset, NSIG_BYTES.toNat)]
                   eff (BitVec.ofInt 64 0) m' []
            else check_write_oset_copyins [(nset, NSIG_BYTES.toNat)]
                   i oset old eff m'

/-! ## tkill (130) and tgkill (131) -/

/-- The acceptor mirrors the spec's branches.  Two things are worth
    naming rather than reading off the code.

    THE EFFECT SHAPE IS EMPTY on every branch: neither call writes user
    memory, zeroes or unmaps anything, or copies anything in.  A claimed
    write is therefore a reject rather than a decline, so an effect
    that forges one fails.

    THE FATAL BRANCH STILL CLAIMS 0.  The syscall's own return value is
    what a kernel would have put in a0 had the process lived; the process
    does not, and [Run.sstep_killed] discards the effect.  Requiring the
    0 here rather than admitting anything keeps the acceptor total on the
    shape and costs nothing: no trace can distinguish the two. -/
def check_send_sigabrt (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if !(ret == BitVec.ofInt 64 0) then .CheckReject
      else if sigabrt_blocked (m_sigmask m)
      then .CheckOk (with_sigabrt_pending m) []
      else .CheckOk (with_killed (BitVec.ofInt 64 SIGABRT) m) []
  | _ => .CheckReject

def check_tkill_self (pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(m_abort_terminal m) then .CheckUnmodeled
  else
    match m_tid m with
    | none => .CheckUnmodeled
    | some t =>
        if !(pid == t) then .CheckUnmodeled
        else if !(tkill_sig_valid sig)
        then check_ret_only eff (errno_ret EINVAL) m []
        else if sig == BitVec.ofInt 64 SIGABRT then check_send_sigabrt eff m
        else .CheckUnmodeled

def check_tkill (pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(m_abort_terminal m) then .CheckUnmodeled
  else if !(pid_positive pid)
  then check_ret_only eff (errno_ret EINVAL) m []
  else check_tkill_self pid sig eff m

def check_tgkill (tgid pid sig : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(m_abort_terminal m) then .CheckUnmodeled
  else if !(pid_positive pid && pid_positive tgid)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    match m_tid m with
    | none => .CheckUnmodeled
    | some t =>
        if !(pid == t) then .CheckUnmodeled
        else if !(tgid == t)
        then check_ret_only eff (errno_ret ESRCH) m []
        else check_tkill_self pid sig eff m

/- =========================================================================
   Private helpers

   These name the steps — `bind_ok0`/`bind_unmodeled2` plus
   `input_ok`/`get_model_ok`, the `cbn` and `inv_ok` reductions — that the
   proofs below would otherwise perform inline.  None of them leaves this
   file.
   ========================================================================= -/

/- `bind_inputSpec` — peel the spec's `input` reader, in BOTH directions
   and for either outcome shape, so `simp only [bind_inputSpec]` performs
   the step wherever the `bind` sits — is the canonical
   `LinuxSem.LinuxProcessSem.bind_inputSpec`, reached through the `open`
   above. -/

/-- …and build the same step on the goal side. -/
theorem seqSpec_modifySpec_ret_only_ok (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) :
    seqSpec (modifySpec f) (ret_only r) i m (.ok (mkEffect r [] []) (f m) []) :=
  ⟨(), f m, [], [], rfl, rfl, by simp⟩

/-- One `seqSpec (modifySpec f) k` step, both directions and either
    outcome shape: the state write always answers, so the step is [k] at
    the updated model. -/
theorem seqSpec_modifySpec_ok {A : Type} (f : Model → Model) (k : SysSpec A)
    (i : SyscallInput) (m : Model) {x : A} {m' : Model} {evs : List event}
    (H : k i (f m) (.ok x m' evs)) :
    seqSpec (modifySpec f) k i m (.ok x m' evs) :=
  ⟨(), f m, [], evs, rfl, H, by simp⟩

theorem seqSpec_modifySpec_inv {A : Type} (f : Model → Model) (k : SysSpec A)
    (i : SyscallInput) (m : Model) {x : A} {m' : Model} {evs : List event}
    (H : seqSpec (modifySpec f) k i m (.ok x m' evs)) :
    k i (f m) (.ok x m' evs) := by
  obtain ⟨u, m2, evs1, evs2, hm, hk, hevs⟩ := H
  cases hm
  simp only [List.nil_append] at hevs
  subst hevs
  exact hk

theorem seqSpec_modifySpec_unmodeled {A : Type} (f : Model → Model) (k : SysSpec A)
    (i : SyscallInput) (m : Model) (H : k i (f m) .unmodeled) :
    seqSpec (modifySpec f) k i m .unmodeled :=
  Or.inr ⟨(), f m, [], rfl, H⟩

theorem seqSpec_modifySpec_unmodeled_inv {A : Type} (f : Model → Model) (k : SysSpec A)
    (i : SyscallInput) (m : Model) (H : seqSpec (modifySpec f) k i m .unmodeled) :
    k i (f m) .unmodeled := by
  rcases H with h | ⟨u, m1, evs1, h, hk⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · cases h
    exact hk

/-- Clearing the ledger and putting the old one back is the identity, and
    the ledger field is exactly what [clear_copyins] overwrites — the step
    [Checks.Sys.Prelude.record_copyins_clear_ok] performs on effects. -/
theorem with_copyins_clear_copyins (eff : SyscallEffect) :
    with_copyins eff.eff_copyins (clear_copyins eff) = eff := by
  obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
  rfl

theorem check_sigaltstack_sound_ok (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sigaltstack i uss uoss eff m = .CheckOk m' evs) :
    sigaltstack_spec uss uoss i m (.ok eff m' evs) := by
  generalize hP : (sigaltstack_spec uss uoss i m (.ok eff m' evs)) = Q at *
  simp only [check_sigaltstack] at H
  by_cases hw : m_sigaltstack_installed m = true
  · rw [ite_eq_left hw] at H
    exact nomatch H
  · rw [ite_eq_right hw] at H
    by_cases ho : (!(w_is0 uoss)) = true
    · rw [ite_eq_left ho] at H
      exact nomatch H
    · rw [ite_eq_right ho] at H
      by_cases hu : w_is0 uss = true
      · rw [ite_eq_left hu] at H
        obtain ⟨heff, hm, hevs⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        subst heff; subst hm; subst hevs
        rw [← hP]
        simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw, ite_eq_right ho,
          ite_eq_left hu, ret_only, LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right hu] at H
        cases hbs : sigaltstack_at i.in_mem uss with
        | none =>
          simp only [hbs] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
          subst heff; subst hm; subst hevs
          rw [← hP]
          simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw, ite_eq_right ho,
            ite_eq_right hu, bind_inputSpec, hbs, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
        | some bs =>
          simp only [hbs] at H
          by_cases hmode : (!(ss_mode_ok (ss_flags_of bs))) = true
          · rw [ite_eq_left hmode] at H
            obtain ⟨heff, hm, hevs⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
            subst heff; subst hm; subst hevs
            rw [← hP]
            simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw, ite_eq_right ho,
              ite_eq_right hu, bind_inputSpec, hbs, ite_eq_left hmode, err_ret, ret_only,
              LinuxSem.LinuxProcessSem.pure]
          · rw [ite_eq_right hmode] at H
            by_cases hdis : ss_disabling (ss_flags_of bs) = true
            · rw [ite_eq_left hdis] at H
              obtain ⟨heff, hm, hevs⟩ :=
                (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
              subst heff; subst hm; subst hevs
              rw [← hP]
              simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw, ite_eq_right ho,
                ite_eq_right hu, bind_inputSpec, hbs, ite_eq_right hmode, ite_eq_left hdis, ret_only,
                LinuxSem.LinuxProcessSem.pure]
            · rw [ite_eq_right hdis] at H
              by_cases hzero : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
              · rw [ite_eq_left hzero] at H
                exact nomatch H
              · rw [ite_eq_right hzero] at H
                by_cases hsz : ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
                · rw [ite_eq_left hsz] at H
                  obtain ⟨heff, hm, hevs⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
                  subst heff; subst hm; subst hevs
                  rw [← hP]
                  simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw,
                    ite_eq_right ho, ite_eq_right hu, bind_inputSpec, hbs, ite_eq_right hmode, ite_eq_right hdis,
                    ite_eq_right hzero, ite_eq_left hsz, err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure]
                · rw [ite_eq_right hsz] at H
                  obtain ⟨heff, hm, hevs⟩ :=
                    (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                      (with_sigaltstack_installed m) [] m' evs).mp H
                  subst heff; subst hm; subst hevs
                  rw [← hP]
                  simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw,
                    ite_eq_right ho, ite_eq_right hu, bind_inputSpec, hbs, ite_eq_right hmode, ite_eq_right hdis,
                    ite_eq_right hzero, ite_eq_right hsz]
                  exact seqSpec_modifySpec_ret_only_ok with_sigaltstack_installed _ i m

theorem check_sigaltstack_sound_unmodeled (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_sigaltstack i uss uoss eff m = .CheckUnmodeled) :
    sigaltstack_spec uss uoss i m .unmodeled := by
  generalize hP : (sigaltstack_spec uss uoss i m .unmodeled) = Q at *
  simp only [check_sigaltstack] at H
  by_cases hw : m_sigaltstack_installed m = true
  · rw [ite_eq_left hw] at H
    rw [← hP]
    simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_left hw, unmodeled]
  · rw [ite_eq_right hw] at H
    by_cases ho : (!(w_is0 uoss)) = true
    · rw [ite_eq_left ho] at H
      rw [← hP]
      simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw, ite_eq_left ho, unmodeled]
    · rw [ite_eq_right ho] at H
      by_cases hu : w_is0 uss = true
      · rw [ite_eq_left hu] at H
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · rw [ite_eq_right hu] at H
        cases hbs : sigaltstack_at i.in_mem uss with
        | none =>
          simp only [hbs] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        | some bs =>
          simp only [hbs] at H
          by_cases hmode : (!(ss_mode_ok (ss_flags_of bs))) = true
          · rw [ite_eq_left hmode] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hmode] at H
            by_cases hdis : ss_disabling (ss_flags_of bs) = true
            · rw [ite_eq_left hdis] at H
              exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
            · rw [ite_eq_right hdis] at H
              by_cases hzero : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
              · rw [ite_eq_left hzero] at H
                rw [← hP]
                simp only [sigaltstack_spec, getModelSpec, bind_getModel, ite_eq_right hw,
                  ite_eq_right ho, ite_eq_right hu, bind_inputSpec, hbs, ite_eq_right hmode, ite_eq_right hdis,
                  ite_eq_left hzero, unmodeled]
              · rw [ite_eq_right hzero] at H
                by_cases hsz : ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
                · rw [ite_eq_left hsz] at H
                  exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
                · rw [ite_eq_right hsz] at H
                  exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                    (with_sigaltstack_installed m) [])

theorem check_sigaltstack_complete_ok (i : SyscallInput) (uss uoss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : sigaltstack_spec uss uoss i m (.ok eff m' evs)) :
    check_sigaltstack i uss uoss eff m = .CheckOk m' evs := by
  generalize hP : (check_sigaltstack i uss uoss eff m = .CheckOk m' evs) = Q at *
  simp only [sigaltstack_spec, getModelSpec, bind_getModel] at H
  by_cases hw : m_sigaltstack_installed m = true
  · rw [ite_eq_left hw] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hw] at H
    by_cases ho : (!(w_is0 uoss)) = true
    · rw [ite_eq_left ho] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right ho] at H
      by_cases hu : w_is0 uss = true
      · rw [ite_eq_left hu] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        rw [← hP]
        simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_left hu, check_ret_only,
          bv_eqb_refl, ite_eq_left]
      · rw [ite_eq_right hu] at H
        simp only [bind_inputSpec] at H
        cases hbs : sigaltstack_at i.in_mem uss with
        | none =>
          simp only [hbs] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs, check_ret_only,
            bv_eqb_refl, ite_eq_left]
        | some bs =>
          simp only [hbs] at H
          by_cases hmode : (!(ss_mode_ok (ss_flags_of bs))) = true
          · rw [ite_eq_left hmode] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            rw [← hP]
            simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs, ite_eq_left hmode,
              check_ret_only, bv_eqb_refl, ite_eq_left]
          · rw [ite_eq_right hmode] at H
            by_cases hdis : ss_disabling (ss_flags_of bs) = true
            · rw [ite_eq_left hdis] at H
              simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
                Outcome.ok.injEq] at H
              obtain ⟨rfl, rfl, rfl⟩ := H
              rw [← hP]
              simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs,
                ite_eq_right hmode, ite_eq_left hdis, check_ret_only, bv_eqb_refl, ite_eq_left]
            · rw [ite_eq_right hdis] at H
              by_cases hzero : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
              · rw [ite_eq_left hzero] at H
                simp only [unmodeled] at H
                exact nomatch H
              · rw [ite_eq_right hzero] at H
                by_cases hsz : ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
                · rw [ite_eq_left hsz] at H
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  rw [← hP]
                  simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs,
                    ite_eq_right hmode, ite_eq_right hdis, ite_eq_right hzero, ite_eq_left hsz, check_ret_only,
                    bv_eqb_refl, ite_eq_left]
                · rw [ite_eq_right hsz] at H
                  obtain ⟨heff, hm', hevs⟩ :=
                    seqSpec_modify_ret_only_inv with_sigaltstack_installed
                      (BitVec.ofInt 64 0) i m eff m' evs H
                  subst heff; subst hm'; subst hevs
                  rw [← hP]
                  simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs,
                    ite_eq_right hmode, ite_eq_right hdis, ite_eq_right hzero, ite_eq_right hsz, check_ret_only,
                    bv_eqb_refl, ite_eq_left]

theorem check_sigaltstack_complete_unmodeled (i : SyscallInput) (uss uoss : word)
    (m : Model) (eff : SyscallEffect)
    (H : sigaltstack_spec uss uoss i m .unmodeled) :
    check_sigaltstack i uss uoss eff m = .CheckUnmodeled := by
  generalize hP : (check_sigaltstack i uss uoss eff m = .CheckUnmodeled) = Q at *
  simp only [sigaltstack_spec, getModelSpec, bind_getModel] at H
  by_cases hw : m_sigaltstack_installed m = true
  · rw [ite_eq_left hw] at H
    rw [← hP]
    simp only [check_sigaltstack, ite_eq_left hw]
  · rw [ite_eq_right hw] at H
    by_cases ho : (!(w_is0 uoss)) = true
    · rw [ite_eq_left ho] at H
      rw [← hP]
      simp only [check_sigaltstack, ite_eq_right hw, ite_eq_left ho]
    · rw [ite_eq_right ho] at H
      by_cases hu : w_is0 uss = true
      · rw [ite_eq_left hu] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      · rw [ite_eq_right hu] at H
        simp only [bind_inputSpec] at H
        cases hbs : sigaltstack_at i.in_mem uss with
        | none =>
          simp only [hbs] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        | some bs =>
          simp only [hbs] at H
          by_cases hmode : (!(ss_mode_ok (ss_flags_of bs))) = true
          · rw [ite_eq_left hmode] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · rw [ite_eq_right hmode] at H
            by_cases hdis : ss_disabling (ss_flags_of bs) = true
            · rw [ite_eq_left hdis] at H
              simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
              exact nomatch H
            · rw [ite_eq_right hdis] at H
              by_cases hzero : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
              · rw [ite_eq_left hzero] at H
                rw [← hP]
                simp only [check_sigaltstack, ite_eq_right hw, ite_eq_right ho, ite_eq_right hu, hbs,
                  ite_eq_right hmode, ite_eq_right hdis, ite_eq_left hzero]
              · rw [ite_eq_right hzero] at H
                by_cases hsz : ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
                · rw [ite_eq_left hsz] at H
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
                  exact nomatch H
                · rw [ite_eq_right hsz] at H
                  exact absurd H (seqSpec_modify_ret_only_never_unmodeled _
                    (BitVec.ofInt 64 0) i m)

theorem check_rt_sigaction_sound_ok (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_rt_sigaction i sig act oact ss eff m = .CheckOk m' evs) :
    rt_sigaction_spec sig act oact ss i m (.ok eff m' evs) := by
  generalize hP : (rt_sigaction_spec sig act oact ss i m (.ok eff m' evs)) = Q at *
  simp only [check_rt_sigaction] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 8)) = true
  · rw [ite_eq_left hss] at H
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    subst heff; subst hm; subst hevs
    rw [← hP]
    simp only [rt_sigaction_spec, ite_eq_left hss, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right hss] at H
    by_cases ho : (!(w_is0 oact)) = true
    · rw [ite_eq_left ho] at H
      exact nomatch H
    · rw [ite_eq_right ho] at H
      by_cases hact : w_is0 act = true
      · rw [ite_eq_left hact] at H
        by_cases hv : sig_valid sig = true
        · rw [ite_eq_left hv] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
          subst heff; subst hm; subst hevs
          rw [← hP]
          simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_left hact, ite_eq_left hv,
            ret_only, LinuxSem.LinuxProcessSem.pure]
        · rw [ite_eq_right hv] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          subst heff; subst hm; subst hevs
          rw [← hP]
          simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_left hact, ite_eq_right hv,
            err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right hact] at H
        cases hfl : sigaction_flags i.in_mem act with
        | none =>
          simp only [hfl] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
          subst heff; subst hm; subst hevs
          rw [← hP]
          simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, bind_inputSpec,
            hfl, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
        | some fl =>
          simp only [hfl] at H
          by_cases hv : (!(sig_valid sig)) = true
          · rw [ite_eq_left hv] at H
            obtain ⟨heff, hm, hevs⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
            subst heff; subst hm; subst hevs
            rw [← hP]
            simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, bind_inputSpec,
              hfl, ite_eq_left hv, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
          · rw [ite_eq_right hv] at H
            by_cases hk : sig_kernel_only sig = true
            · rw [ite_eq_left hk] at H
              obtain ⟨heff, hm, hevs⟩ :=
                (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
              subst heff; subst hm; subst hevs
              rw [← hP]
              simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, bind_inputSpec,
                hfl, ite_eq_right hv, ite_eq_left hk, err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure]
            · rw [ite_eq_right hk] at H
              by_cases hfo : (!(sa_flags_ok fl)) = true
              · rw [ite_eq_left hfo] at H
                exact nomatch H
              · rw [ite_eq_right hfo] at H
                by_cases hac : sigaction_accepted sig = true
                · rw [ite_eq_left hac] at H
                  obtain ⟨heff, hm, hevs⟩ :=
                    (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
                  subst heff; subst hm; subst hevs
                  rw [← hP]
                  simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact,
                    bind_inputSpec, hfl, ite_eq_right hv, ite_eq_right hk, ite_eq_right hfo, ite_eq_left hac,
                    ret_only, LinuxSem.LinuxProcessSem.pure]
                · rw [ite_eq_right hac] at H
                  exact nomatch H

theorem check_rt_sigaction_sound_unmodeled (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_rt_sigaction i sig act oact ss eff m = .CheckUnmodeled) :
    rt_sigaction_spec sig act oact ss i m .unmodeled := by
  generalize hP : (rt_sigaction_spec sig act oact ss i m .unmodeled) = Q at *
  simp only [check_rt_sigaction] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 8)) = true
  · rw [ite_eq_left hss] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hss] at H
    by_cases ho : (!(w_is0 oact)) = true
    · rw [ite_eq_left ho] at H
      rw [← hP]
      simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_left ho, unmodeled]
    · rw [ite_eq_right ho] at H
      by_cases hact : w_is0 act = true
      · rw [ite_eq_left hact] at H
        by_cases hv : sig_valid sig = true
        · rw [ite_eq_left hv] at H
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right hv] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      · rw [ite_eq_right hact] at H
        cases hfl : sigaction_flags i.in_mem act with
        | none =>
          simp only [hfl] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        | some fl =>
          simp only [hfl] at H
          by_cases hv : (!(sig_valid sig)) = true
          · rw [ite_eq_left hv] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · rw [ite_eq_right hv] at H
            by_cases hk : sig_kernel_only sig = true
            · rw [ite_eq_left hk] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            · rw [ite_eq_right hk] at H
              by_cases hfo : (!(sa_flags_ok fl)) = true
              · rw [ite_eq_left hfo] at H
                rw [← hP]
                simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact,
                  bind_inputSpec, hfl, ite_eq_right hv, ite_eq_right hk, ite_eq_left hfo, unmodeled]
              · rw [ite_eq_right hfo] at H
                by_cases hac : sigaction_accepted sig = true
                · rw [ite_eq_left hac] at H
                  exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
                · rw [ite_eq_right hac] at H
                  rw [← hP]
                  simp only [rt_sigaction_spec, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact,
                    bind_inputSpec, hfl, ite_eq_right hv, ite_eq_right hk, ite_eq_right hfo, ite_eq_right hac,
                    unmodeled]

theorem check_rt_sigaction_complete_ok (i : SyscallInput) (sig act oact ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : rt_sigaction_spec sig act oact ss i m (.ok eff m' evs)) :
    check_rt_sigaction i sig act oact ss eff m = .CheckOk m' evs := by
  generalize hP : (check_rt_sigaction i sig act oact ss eff m = .CheckOk m' evs) = Q at *
  simp only [rt_sigaction_spec] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 8)) = true
  · rw [ite_eq_left hss] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_rt_sigaction, ite_eq_left hss, check_ret_only, bv_eqb_refl, ite_eq_left]
  · rw [ite_eq_right hss] at H
    by_cases ho : (!(w_is0 oact)) = true
    · rw [ite_eq_left ho] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right ho] at H
      by_cases hact : w_is0 act = true
      · rw [ite_eq_left hact] at H
        by_cases hv : sig_valid sig = true
        · rw [ite_eq_left hv] at H
          simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_left hact, ite_eq_left hv,
            check_ret_only, bv_eqb_refl, ite_eq_left]
        · rw [ite_eq_right hv] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_left hact, ite_eq_right hv,
            check_ret_only, bv_eqb_refl, ite_eq_left]
      · rw [ite_eq_right hact] at H
        simp only [bind_inputSpec] at H
        cases hfl : sigaction_flags i.in_mem act with
        | none =>
          simp only [hfl] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl,
            check_ret_only, bv_eqb_refl, ite_eq_left]
        | some fl =>
          simp only [hfl] at H
          by_cases hv : (!(sig_valid sig)) = true
          · rw [ite_eq_left hv] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            rw [← hP]
            simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl, ite_eq_left hv,
              check_ret_only, bv_eqb_refl, ite_eq_left]
          · rw [ite_eq_right hv] at H
            by_cases hk : sig_kernel_only sig = true
            · rw [ite_eq_left hk] at H
              simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                Outcome.ok.injEq] at H
              obtain ⟨rfl, rfl, rfl⟩ := H
              rw [← hP]
              simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl,
                ite_eq_right hv, ite_eq_left hk, check_ret_only, bv_eqb_refl, ite_eq_left]
            · rw [ite_eq_right hk] at H
              by_cases hfo : (!(sa_flags_ok fl)) = true
              · rw [ite_eq_left hfo] at H
                simp only [unmodeled] at H
                exact nomatch H
              · rw [ite_eq_right hfo] at H
                by_cases hac : sigaction_accepted sig = true
                · rw [ite_eq_left hac] at H
                  simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  rw [← hP]
                  simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl,
                    ite_eq_right hv, ite_eq_right hk, ite_eq_right hfo, ite_eq_left hac, check_ret_only, bv_eqb_refl,
                    ite_eq_left]
                · rw [ite_eq_right hac] at H
                  simp only [unmodeled] at H
                  exact nomatch H

theorem check_rt_sigaction_complete_unmodeled (i : SyscallInput) (sig act oact ss : word)
    (m : Model) (eff : SyscallEffect)
    (H : rt_sigaction_spec sig act oact ss i m .unmodeled) :
    check_rt_sigaction i sig act oact ss eff m = .CheckUnmodeled := by
  generalize hP : (check_rt_sigaction i sig act oact ss eff m = .CheckUnmodeled) = Q at *
  simp only [rt_sigaction_spec] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 8)) = true
  · rw [ite_eq_left hss] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right hss] at H
    by_cases ho : (!(w_is0 oact)) = true
    · rw [ite_eq_left ho] at H
      rw [← hP]
      simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_left ho]
    · rw [ite_eq_right ho] at H
      by_cases hact : w_is0 act = true
      · rw [ite_eq_left hact] at H
        by_cases hv : sig_valid sig = true
        · rw [ite_eq_left hv] at H
          simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        · rw [ite_eq_right hv] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
      · rw [ite_eq_right hact] at H
        simp only [bind_inputSpec] at H
        cases hfl : sigaction_flags i.in_mem act with
        | none =>
          simp only [hfl] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        | some fl =>
          simp only [hfl] at H
          by_cases hv : (!(sig_valid sig)) = true
          · rw [ite_eq_left hv] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · rw [ite_eq_right hv] at H
            by_cases hk : sig_kernel_only sig = true
            · rw [ite_eq_left hk] at H
              simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
              exact nomatch H
            · rw [ite_eq_right hk] at H
              by_cases hfo : (!(sa_flags_ok fl)) = true
              · rw [ite_eq_left hfo] at H
                rw [← hP]
                simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl,
                  ite_eq_right hv, ite_eq_right hk, ite_eq_left hfo]
              · rw [ite_eq_right hfo] at H
                by_cases hac : sigaction_accepted sig = true
                · rw [ite_eq_left hac] at H
                  simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
                  exact nomatch H
                · rw [ite_eq_right hac] at H
                  rw [← hP]
                  simp only [check_rt_sigaction, ite_eq_right hss, ite_eq_right ho, ite_eq_right hact, hfl,
                    ite_eq_right hv, ite_eq_right hk, ite_eq_right hfo, ite_eq_right hac]

/-- An effect that is exactly one write and nothing else, in the shape
    [check_ret_only] has for an effect that is nothing at all.  Local to
    this file because one syscall produces that shape; it moves to
    [Checks.Sys.Prelude] when a second one does. -/

theorem check_one_write_ok_iff (eff : SyscallEffect) (r a : word) (bs : List byte)
    (m1 m' : Model) (evs : List event) :
    check_one_write eff r a bs m1 = .CheckOk m' evs ↔
      (eff = mkEffect r [(a, bs)] [] ∧ m' = m1 ∧ evs = []) := by
  obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
  cases zs <;> cases us <;> cases cs <;> cases cin <;>
    simp only [check_one_write]
  case nil.nil.nil.nil =>
    by_cases hc : (bv_eqb ret r && writes_eqb ws [(a, bs)]) = true
    · have hret : bv_eqb ret r = true := (Bool.and_eq_true ..).mp hc |>.1
      have hws : writes_eqb ws [(a, bs)] = true := (Bool.and_eq_true ..).mp hc |>.2
      obtain rfl : ret = r := (Fs.bv_eqb_eq ret r).mp hret
      obtain rfl : ws = [(a, bs)] := (writes_eqb_eq ws [(a, bs)]).mp hws
      rw [ite_eq_left hc]
      simp only [check_result.CheckOk.injEq, mkEffect]
      constructor
      · rintro ⟨hm, hevs⟩
        subst hm
        subst hevs
        simp
      · rintro ⟨-, hm, hevs⟩
        subst hm
        subst hevs
        simp
    · rw [ite_eq_right hc]
      constructor
      · intro h
        exact nomatch h
      · rintro ⟨heff, -⟩
        exfalso
        apply hc
        have hret : ret = r := by simpa [mkEffect] using congrArg SyscallEffect.eff_ret heff
        have hws : ws = [(a, bs)] :=
          by simpa [mkEffect] using congrArg SyscallEffect.eff_writes heff
        subst hret
        subst hws
        simp [bv_eqb_refl, writes_eqb_eq]
  all_goals simp [mkEffect]

theorem check_write_oset_ok_iff (i : SyscallInput) (oset old : word) (eff : SyscallEffect)
    (m1 m' : Model) (evs : List event) :
    check_write_oset i oset old eff m1 = .CheckOk m' evs ↔
      (m' = m1 ∧ evs = [] ∧ eff.eff_copyins = [] ∧
       write_oset oset old i m1 (.ok eff m1 [])) := by
  by_cases ha : (!(access_okb oset NSIG_BYTES)) = true
  · -- the access_ok arm: -EFAULT, exactly [check_ret_only]'s shape
    have hchk : check_write_oset i oset old eff m1
        = check_ret_only eff (errno_ret EFAULT) m1 [] := by
      simp only [check_write_oset, ite_eq_left ha]
    rw [hchk, check_ret_only_ok_iff]
    constructor
    · rintro ⟨heff, hm, hevs⟩
      subst heff
      subst hm
      subst hevs
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp only [write_oset, ite_eq_left ha, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure]
    · rintro ⟨hm, hevs, -, hspec⟩
      subst hm
      subst hevs
      refine ⟨?_, rfl, rfl⟩
      simp only [write_oset, ite_eq_left ha, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hspec
      exact hspec.1
  · cases hw : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
    | none =>
      -- the walk fails: the arm declines, and so does the spec
      have hchk : check_write_oset i oset old eff m1 = .CheckUnmodeled := by
        simp only [check_write_oset, ite_eq_right ha, hw]
      rw [hchk]
      constructor
      · intro h
        exact nomatch h
      · rintro ⟨-, -, -, hspec⟩
        simp only [write_oset, ite_eq_right ha, bind_inputSpec, hw,
          LinuxSem.LinuxProcessSem.unmodeled] at hspec
        exact nomatch hspec
    | some bs =>
      -- the walk succeeds: one write, of the old mask, at [oset]
      have hchk : check_write_oset i oset old eff m1
          = check_one_write eff (BitVec.ofInt 64 0) oset
              (Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int)) m1 := by
        simp only [check_write_oset, ite_eq_right ha, hw]
      rw [hchk, check_one_write_ok_iff]
      constructor
      · rintro ⟨heff, hm, hevs⟩
        subst heff
        subst hm
        subst hevs
        refine ⟨rfl, rfl, rfl, ?_⟩
        simp only [write_oset, ite_eq_right ha, bind_inputSpec, hw,
          LinuxSem.LinuxProcessSem.pure]
      · rintro ⟨hm, hevs, -, hspec⟩
        subst hm
        subst hevs
        refine ⟨?_, rfl, rfl⟩
        simp only [write_oset, ite_eq_right ha, bind_inputSpec, hw,
          LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hspec
        exact hspec.1

theorem check_write_oset_no_ok_unmodeled (i : SyscallInput) (oset old : word)
    (eff : SyscallEffect) (m1 : Model)
    (H : check_write_oset i oset old eff m1 = .CheckUnmodeled) :
    ∀ m, write_oset oset old i m .unmodeled := by
  intro m
  by_cases ha : (!(access_okb oset NSIG_BYTES)) = true
  · have hchk : check_write_oset i oset old eff m1
        = check_ret_only eff (errno_ret EFAULT) m1 [] := by
      simp only [check_write_oset, ite_eq_left ha]
    rw [hchk] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m1 [])
  · cases hw : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
    | none =>
      simp only [write_oset, ite_eq_right ha, bind_inputSpec, hw,
        LinuxSem.LinuxProcessSem.unmodeled]
    | some bs =>
      have hchk : check_write_oset i oset old eff m1
          = check_one_write eff (BitVec.ofInt 64 0) oset
              (Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int)) m1 := by
        simp only [check_write_oset, ite_eq_right ha, hw]
      rw [hchk] at H
      obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
      cases zs <;> cases us <;> cases cs <;> cases cin <;>
        simp only [check_one_write] at H
      case nil.nil.nil.nil =>
        by_cases hc : (bv_eqb ret (BitVec.ofInt 64 0) &&
            writes_eqb ws [(oset, Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int))]) = true
        · rw [ite_eq_left hc] at H
          exact nomatch H
        · rw [ite_eq_right hc] at H
          exact nomatch H
      all_goals exact nomatch H

/-- The two shapes [write_oset] can produce, accepted.  They are what the
    completeness proof's leaves reduce to, and naming them keeps that
    proof readable instead of six copies of the same [cbn]. -/
theorem check_write_oset_efault (i : SyscallInput) (oset old : word) (m : Model)
    (Ha : access_okb oset NSIG_BYTES = false) :
    check_write_oset i oset old (mkEffect (errno_ret EFAULT) [] []) m = .CheckOk m [] := by
  rw [check_write_oset, ite_eq_left (by simp [Ha])]
  exact (check_ret_only_ok_iff _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem check_write_oset_stored (i : SyscallInput) (oset old : word) (m : Model)
    (bs : List byte)
    (Ha : access_okb oset NSIG_BYTES = true)
    (Hw : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) = some bs) :
    check_write_oset i oset old
      (mkEffect (BitVec.ofInt 64 0)
         [(oset, Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int))] []) m
      = .CheckOk m [] := by
  rw [check_write_oset, ite_eq_right (by simp [Ha]), Hw]
  exact (check_one_write_ok_iff _ _ _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

/-- [check_write_oset_copyins] discharged from its two parts: the arm's
    own verdict and the ledger.  The same shape [check_ret_only_copyins]
    has, and it exists so the completeness proof never has to reduce
    through [clear_copyins] by hand. -/
theorem check_write_oset_copyins_ok (reads : List (word × Nat)) (i : SyscallInput)
    (oset old : word) (eff : SyscallEffect) (m : Model)
    (H : check_write_oset i oset old (clear_copyins eff) m = .CheckOk m [])
    (Hc : eff.eff_copyins = reads) :
    check_write_oset_copyins reads i oset old eff m = .CheckOk m [] := by
  unfold check_write_oset_copyins
  rw [H]
  try dsimp only
  rw [Hc, ite_eq_left (access_ranges_eqb_refl reads)]


theorem check_rt_sigprocmask_sound_ok (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs) :
    rt_sigprocmask_spec how nset oset ss i m (.ok eff m' evs) := by
  generalize hP : (rt_sigprocmask_spec how nset oset ss i m (.ok eff m' evs)) = Q at *
  simp only [check_rt_sigprocmask] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    subst heff; subst hm; subst hevs
    rw [← hP]
    simp only [rt_sigprocmask_spec, ite_eq_left hss, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right hss] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        obtain ⟨heff, hm, hevs⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        subst heff; subst hm; subst hevs
        rw [← hP]
        simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_left hn,
          ite_eq_left ho, ret_only, LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right ho] at H
        obtain ⟨hm, hevs, -, hspec⟩ :=
          (check_write_oset_ok_iff i oset (m_sigmask m) eff m m' evs).mp H
        subst hm; subst hevs
        rw [← hP]
        simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_left hn,
          ite_eq_right ho]
        exact hspec
    · rw [ite_eq_right hn] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        obtain ⟨heff, hm, hevs⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
        subst heff; subst hm; subst hevs
        rw [← hP]
        simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_right hn,
          bind_inputSpec, hsr, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      | some raw =>
        simp only [hsr] at H
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
              (errno_ret EINVAL) m [] m' evs).mp H
          subst heff; subst hm; subst hevs
          rw [← hP]
          simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_right hn,
            bind_inputSpec, hsr, ite_eq_left hh, err_ret, ret_only]
          exact record_copyins_ok_empty rfl rfl
        · rw [ite_eq_right hh] at H
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            obtain ⟨heff, hm, hevs⟩ :=
              (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
                (BitVec.ofInt 64 0)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] m' evs).mp H
            subst heff; subst hm; subst hevs
            rw [← hP]
            simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_right hn,
              bind_inputSpec, hsr, ite_eq_right hh, ite_eq_left ho, ret_only]
            exact record_copyins_ok_empty rfl
              (seqSpec_modifySpec_ret_only_ok _ (BitVec.ofInt 64 0) i m)
          · rw [ite_eq_right ho] at H
            -- the copy-out arm, under a recorded ledger
            unfold check_write_oset_copyins at H
            cases hcw : check_write_oset i oset (m_sigmask m) (clear_copyins eff)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) with
            | CheckOk m2 evs2 =>
              simp only [hcw] at H
              by_cases hled : access_ranges_eqb eff.eff_copyins
                  [(nset, NSIG_BYTES.toNat)] = true
              · rw [ite_eq_left hled] at H
                obtain ⟨hm2, hevs2⟩ := check_result.CheckOk.inj H
                obtain ⟨hdel, hevsz, hcin, hspec⟩ :=
                  (check_write_oset_ok_iff i oset (m_sigmask m) (clear_copyins eff)
                    (sigmask_deliver_model
                      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) m2 evs2).mp hcw
                have hreads : eff.eff_copyins = [(nset, NSIG_BYTES.toNat)] :=
                  (access_ranges_eqb_eq _ _).mp hled
                have hm' : m' = sigmask_deliver_model
                    (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m := hm2 ▸ hdel
                have hevs' : evs = [] := hevs2 ▸ hevsz
                rw [← hP]
                simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel,
                  ite_eq_right hn, bind_inputSpec, hsr, ite_eq_right hh, ite_eq_right ho]
                have heff' : eff
                    = with_copyins [(nset, NSIG_BYTES.toNat)] (clear_copyins eff) := by
                  rw [← with_copyins_clear_copyins eff, hreads]
                  rfl
                have hok : (Outcome.ok eff m' evs : Outcome SyscallEffect Model event)
                    = .ok (with_copyins [(nset, NSIG_BYTES.toNat)] (clear_copyins eff))
                        (sigmask_deliver_model
                          (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] := by
                  rw [hm', hevs', heff']
                  simp only [clear_copyins, with_copyins]
                rw [hok]
                exact record_copyins_ok_empty hcin (seqSpec_modifySpec_ok _ _ i m hspec)
              · rw [ite_eq_right hled] at H
                exact nomatch H
            | CheckReject =>
              simp only [hcw] at H
              exact nomatch H
            | CheckUnmodeled =>
              simp only [hcw] at H
              exact nomatch H
theorem check_rt_sigprocmask_sound_unmodeled (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_rt_sigprocmask i how nset oset ss eff m = .CheckUnmodeled) :
    rt_sigprocmask_spec how nset oset ss i m .unmodeled := by
  generalize hP : (rt_sigprocmask_spec how nset oset ss i m .unmodeled) = Q at *
  simp only [check_rt_sigprocmask] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hss] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · rw [ite_eq_right ho] at H
        rw [← hP]
        simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_left hn,
          ite_eq_right ho]
        exact check_write_oset_no_ok_unmodeled i oset (m_sigmask m) eff m H m
    · rw [ite_eq_right hn] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      | some raw =>
        simp only [hsr] at H
        rw [← hP]
        simp only [rt_sigprocmask_spec, ite_eq_right hss, getModelSpec, bind_getModel, ite_eq_right hn,
          bind_inputSpec, hsr]
        apply record_copyins_unmodeled
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          simp only [ite_eq_left hh]
          exact absurd H (check_ret_only_copyins_no_unmodeled [(nset, NSIG_BYTES.toNat)]
            eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hh] at H
          simp only [ite_eq_right hh]
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            simp only [ite_eq_left ho]
            exact absurd H (check_ret_only_copyins_no_unmodeled [(nset, NSIG_BYTES.toNat)]
              eff (BitVec.ofInt 64 0)
              (sigmask_deliver_model
                (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [])
          · rw [ite_eq_right ho] at H
            simp only [ite_eq_right ho]
            apply seqSpec_modifySpec_unmodeled
            unfold check_write_oset_copyins at H
            cases hcw : check_write_oset i oset (m_sigmask m) (clear_copyins eff)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) with
            | CheckOk m2 evs2 =>
              simp only [hcw] at H
              by_cases hled : access_ranges_eqb eff.eff_copyins
                  [(nset, NSIG_BYTES.toNat)] = true
              · rw [ite_eq_left hled] at H
                exact nomatch H
              · rw [ite_eq_right hled] at H
                exact nomatch H
            | CheckReject =>
              simp only [hcw] at H
              exact nomatch H
            | CheckUnmodeled =>
              simp only [hcw] at H
              exact check_write_oset_no_ok_unmodeled i oset (m_sigmask m) (clear_copyins eff)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) hcw
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m)


theorem check_rt_sigprocmask_complete_ok (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : rt_sigprocmask_spec how nset oset ss i m (.ok eff m' evs)) :
    check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs := by
  generalize hP : (check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs) = Q at *
  simp only [rt_sigprocmask_spec] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨heff, hm, hevs⟩ := H
    rw [hevs, heff, hm] at hP
    rw [← hP]
    simp only [check_rt_sigprocmask, ite_eq_left hss, check_ret_only, bv_eqb_refl, ite_eq_left]
  · rw [ite_eq_right hss] at H
    simp only [getModelSpec, bind_getModel] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨heff, hm, hevs⟩ := H
        rw [hevs, heff, hm] at hP
        rw [← hP]
        simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_left hn, ite_eq_left ho, check_ret_only,
          bv_eqb_refl, ite_eq_left]
      · rw [ite_eq_right ho] at H
        cases ha : access_okb oset NSIG_BYTES with
        | false =>
          -- the range test fails: -EFAULT, and the checker answers it too
          simp only [write_oset] at H
          rw [ite_eq_left (by simp [ha])] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨heff, hm, hevs⟩ := H
          rw [hevs, heff, hm] at hP
          rw [← hP]
          simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_left hn, ite_eq_right ho]
          exact check_write_oset_efault i oset (m_sigmask m) m ha
        | true =>
          simp only [write_oset] at H
          rw [ite_eq_right (by simp [ha])] at H
          simp only [bind_inputSpec] at H
          cases hwr : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
          | none =>
            simp only [hwr] at H
            simp only [LinuxSem.LinuxProcessSem.unmodeled] at H
            exact nomatch H
          | some bs =>
            simp only [hwr] at H
            simp only [LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨heff, hm, hevs⟩ := H
            rw [hevs, heff, hm] at hP
            rw [← hP]
            simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_left hn, ite_eq_right ho]
            exact check_write_oset_stored i oset (m_sigmask m) m bs ha hwr
    · rw [ite_eq_right hn] at H
      simp only [bind_inputSpec] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨heff, hm, hevs⟩ := H
        rw [hevs, heff, hm] at hP
        rw [← hP]
        simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, check_ret_only,
          bv_eqb_refl, ite_eq_left]
      | some raw =>
        simp only [hsr] at H
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          obtain ⟨core, Hcore, heffc⟩ := record_copyins_ok_inv [(nset, NSIG_BYTES.toNat)]
            (err_ret EINVAL) i m eff m' evs H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at Hcore
          obtain ⟨hcore, hm', hevs'⟩ := Hcore
          rw [hcore] at heffc
          rw [hevs', hm'] at hP
          rw [← hP]
          simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, ite_eq_left hh]
          have heffn : eff = with_copyins [(nset, NSIG_BYTES.toNat)]
              (mkEffect (errno_ret EINVAL) [] []) := by
            rw [heffc]
            simp only [mkEffect, List.append_nil]
          rw [heffn]
          exact check_ret_only_copyins_refl _ _ _ _
        · rw [ite_eq_right hh] at H
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            obtain ⟨core, Hcore, heffc⟩ := record_copyins_ok_inv [(nset, NSIG_BYTES.toNat)]
              (seqSpec (set_sigmask_deliver
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
                (ret_only (BitVec.ofInt 64 0))) i m eff m' evs H
            obtain ⟨hcore, hm', hevs'⟩ := seqSpec_modify_ret_only_inv
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
              (BitVec.ofInt 64 0) i m core m' evs Hcore
            rw [hcore] at heffc
            rw [hevs', hm'] at hP
            rw [← hP]
            simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, ite_eq_right hh, ite_eq_left ho]
            have heffn : eff = with_copyins [(nset, NSIG_BYTES.toNat)]
                (mkEffect (BitVec.ofInt 64 0) [] []) := by
              rw [heffc]
              simp only [mkEffect, List.append_nil]
            rw [heffn]
            exact check_ret_only_copyins_refl _ _ _ _
          · rw [ite_eq_right ho] at H
            obtain ⟨core, Hcore, heffc⟩ := record_copyins_ok_inv [(nset, NSIG_BYTES.toNat)]
              (seqSpec (set_sigmask_deliver
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
                (write_oset oset (m_sigmask m))) i m eff m' evs H
            have Hw := seqSpec_modifySpec_inv
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
              (write_oset oset (m_sigmask m)) i m Hcore
            cases ha : access_okb oset NSIG_BYTES with
            | false =>
              simp only [write_oset] at Hw
              rw [ite_eq_left (by simp [ha])] at Hw
              simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                Outcome.ok.injEq] at Hw
              obtain ⟨hcore, hm', hevs'⟩ := Hw
              rw [hcore] at heffc
              rw [hevs', hm'] at hP
              rw [← hP]
              simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, ite_eq_right hh, ite_eq_right ho]
              have heffn : eff = with_copyins [(nset, NSIG_BYTES.toNat)]
                  (mkEffect (errno_ret EFAULT) [] []) := by
                rw [heffc]
                simp only [mkEffect, List.append_nil]
              rw [heffn]
              exact check_write_oset_copyins_ok _ _ _ _ _ _
                (check_write_oset_efault i oset (m_sigmask m)
                  (sigmask_deliver_model
                    (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) ha) rfl
            | true =>
              simp only [write_oset] at Hw
              rw [ite_eq_right (by simp [ha])] at Hw
              simp only [bind_inputSpec] at Hw
              cases hwr : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
              | none =>
                simp only [hwr] at Hw
                simp only [LinuxSem.LinuxProcessSem.unmodeled] at Hw
                exact nomatch Hw
              | some bs =>
                simp only [hwr] at Hw
                simp only [LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at Hw
                obtain ⟨hcore, hm', hevs'⟩ := Hw
                rw [hcore] at heffc
                rw [hevs', hm'] at hP
                rw [← hP]
                simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, ite_eq_right hh,
                  ite_eq_right ho]
                have heffn : eff = with_copyins [(nset, NSIG_BYTES.toNat)]
                    (mkEffect (BitVec.ofInt 64 0)
                      [(oset, Z_to_le_bytes NSIG_BYTES.toNat ((m_sigmask m).toNat : Int))]
                      []) := by
                  rw [heffc]
                  simp only [mkEffect, List.append_nil]
                rw [heffn]
                exact check_write_oset_copyins_ok _ _ _ _ _ _
                  (check_write_oset_stored i oset (m_sigmask m)
                    (sigmask_deliver_model
                      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) bs ha hwr) rfl

theorem check_rt_sigprocmask_complete_unmodeled (i : SyscallInput) (how nset oset ss : word)
    (m : Model) (eff : SyscallEffect)
    (H : rt_sigprocmask_spec how nset oset ss i m .unmodeled) :
    check_rt_sigprocmask i how nset oset ss eff m = .CheckUnmodeled := by
  generalize hP : (check_rt_sigprocmask i how nset oset ss eff m = .CheckUnmodeled) = Q at *
  simp only [rt_sigprocmask_spec] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right hss] at H
    simp only [getModelSpec, bind_getModel] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      · rw [ite_eq_right ho] at H
        cases ha : access_okb oset NSIG_BYTES with
        | false =>
          simp only [write_oset] at H
          rw [ite_eq_left (by simp [ha])] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        | true =>
          simp only [write_oset] at H
          rw [ite_eq_right (by simp [ha])] at H
          simp only [bind_inputSpec] at H
          cases hwr : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
          | some bs =>
            simp only [hwr] at H
            simp only [LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          | none =>
            simp only [hwr] at H
            rw [← hP]
            simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_left hn, ite_eq_right ho]
            rw [show check_write_oset i oset (m_sigmask m) eff m = .CheckUnmodeled from by
              rw [check_write_oset, ite_eq_right (by simp [ha]), hwr]]
    · rw [ite_eq_right hn] at H
      simp only [bind_inputSpec] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      | some raw =>
        simp only [hsr] at H
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          have H' := record_copyins_unmodeled_inv [(nset, NSIG_BYTES.toNat)]
            (err_ret EINVAL) i m H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H'
          exact nomatch H'
        · rw [ite_eq_right hh] at H
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            have H' := record_copyins_unmodeled_inv [(nset, NSIG_BYTES.toNat)]
              (seqSpec (set_sigmask_deliver
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
                (ret_only (BitVec.ofInt 64 0))) i m H
            have H'' := seqSpec_modifySpec_unmodeled_inv
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
              (ret_only (BitVec.ofInt 64 0)) i m H'
            simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H''
            exact nomatch H''
          · rw [ite_eq_right ho] at H
            have H' := record_copyins_unmodeled_inv [(nset, NSIG_BYTES.toNat)]
              (seqSpec (set_sigmask_deliver
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
                (write_oset oset (m_sigmask m))) i m H
            have H'' := seqSpec_modifySpec_unmodeled_inv
              (sigmask_deliver_model (sigmask_apply how (m_sigmask m) (sigmask_strip raw)))
              (write_oset oset (m_sigmask m)) i m H'
            cases ha : access_okb oset NSIG_BYTES with
            | false =>
              simp only [write_oset] at H''
              rw [ite_eq_left (by simp [ha])] at H''
              simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H''
              exact nomatch H''
            | true =>
              simp only [write_oset] at H''
              rw [ite_eq_right (by simp [ha])] at H''
              simp only [bind_inputSpec] at H''
              cases hwr : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
              | some bs =>
                simp only [hwr] at H''
                simp only [LinuxSem.LinuxProcessSem.pure] at H''
                exact nomatch H''
              | none =>
                simp only [hwr] at H''
                rw [← hP]
                simp only [check_rt_sigprocmask, ite_eq_right hss, ite_eq_right hn, hsr, ite_eq_right hh,
                  ite_eq_right ho]
                unfold check_write_oset_copyins
                rw [show check_write_oset i oset (m_sigmask m) (clear_copyins eff)
                      (sigmask_deliver_model
                        (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m)
                    = .CheckUnmodeled from by
                  rw [check_write_oset, ite_eq_right (by simp [ha]), hwr]]

/-- [Kernel.Signal.mask_launchable] carried across a whole run, which is
    what makes [Run.valid_sigmask] a property of every reachable state and
    not only of the entry one.  Its two halves are proved where the
    arithmetic lives; this is the step that says the checker has no other
    way to move the field.

    It matters because [oset] copies the mask out verbatim: a reachable
    state with SIGKILL or SIGSTOP set would put a trace in the model that
    Linux cannot produce, which is the second of the three priorities
    rather than the first. -/
theorem check_rt_sigprocmask_keeps_mask_launchable (i : SyscallInput)
    (how nset oset ss : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hm : mask_launchable (m_sigmask m))
    (H : check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs) :
    mask_launchable (m_sigmask m') := by
  simp only [check_rt_sigprocmask] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    obtain ⟨-, hm, -⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [hm]; exact Hm
  · rw [ite_eq_right hss] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        obtain ⟨-, hm, -⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        rw [hm]; exact Hm
      · rw [ite_eq_right ho] at H
        obtain ⟨hm, -, -, -⟩ :=
          (check_write_oset_ok_iff i oset (m_sigmask m) eff m m' evs).mp H
        rw [hm]; exact Hm
    · rw [ite_eq_right hn] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        obtain ⟨-, hm, -⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
        rw [hm]; exact Hm
      | some raw =>
        simp only [hsr] at H
        have Hinst : mask_launchable
            (m_sigmask (sigmask_deliver_model
              (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m)) := by
          rw [m_sigmask_sigmask_deliver_model]
          exact sigmask_apply_launchable how (m_sigmask m) (sigmask_strip raw) Hm
            (sigmask_strip_launchable raw)
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          obtain ⟨-, hm, -⟩ :=
            (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
              (errno_ret EINVAL) m [] m' evs).mp H
          rw [hm]; exact Hm
        · rw [ite_eq_right hh] at H
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            obtain ⟨-, hm, -⟩ :=
              (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
                (BitVec.ofInt 64 0)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] m' evs).mp H
            rw [hm]; exact Hinst
          · rw [ite_eq_right ho] at H
            unfold check_write_oset_copyins at H
            cases hcw : check_write_oset i oset (m_sigmask m) (clear_copyins eff)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) with
            | CheckOk m2 evs2 =>
              simp only [hcw] at H
              by_cases hled : access_ranges_eqb eff.eff_copyins
                  [(nset, NSIG_BYTES.toNat)] = true
              · rw [ite_eq_left hled] at H
                obtain ⟨hm2, -⟩ := check_result.CheckOk.inj H
                obtain ⟨hdel, -, -, -⟩ :=
                  (check_write_oset_ok_iff i oset (m_sigmask m) (clear_copyins eff)
                    (sigmask_deliver_model
                      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) m2 evs2).mp hcw
                rw [← hm2, hdel]
                exact Hinst
              · rw [ite_eq_right hled] at H
                exact nomatch H
            | CheckReject =>
              simp only [hcw] at H
              exact nomatch H
            | CheckUnmodeled =>
              simp only [hcw] at H
              exact nomatch H

/-- The framing statement in the shape the [Checks.VmMapsDisjoint]
    [check_syscall_preserves_vm_wf] cascade consumes.  That cascade consumes
    this very lemma: `Checks.VmMapsDisjoint.arm_rt_sigprocmask_preserves_vm`
    (`VmMapsDisjoint/Chain/Arms.lean`) is `simp only [arm_rt_sigprocmask]` +
    this frame + `exact Hwf`, the table induction
    `checked_table_preserves_vm` includes it, and
    `check_syscall_preserves_vm_wf` turns that into the syscall-wide claim.
    So the syscall-wide preservation is a PROVED claim about the checker in
    this tree, not a hypothesis.

    IT IS STATED HERE RATHER THAN THERE because the arm CHANGES the
    model, so the cascade's generic [vm_frame2] cannot close it: that
    tactic reduces through the checker combinators it knows, and this
    checker's [check_write_oset] and [check_one_write] are not among
    them.  The proof needs [check_write_oset_ok_iff], which lives here.

    The arm does not hand back the very model it was given, but what the
    rest of the tree consumes is only the VM half, and that is true by
    construction — the model changes only inside [ProcState], through
    [State.with_sigmask] and, on the delivery branch, [State.with_killed]
    over it; both rebuild that record alone and carry every other
    subsystem across ([Kernel.Signal.m_vmmaps_sigmask_deliver_model]). -/
theorem check_rt_sigprocmask_frame (i : SyscallInput) (how nset oset ss : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  simp only [check_rt_sigprocmask] at H
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · rw [ite_eq_left hss] at H
    obtain ⟨-, hm, -⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [hm]
  · rw [ite_eq_right hss] at H
    by_cases hn : w_is0 nset = true
    · rw [ite_eq_left hn] at H
      by_cases ho : w_is0 oset = true
      · rw [ite_eq_left ho] at H
        obtain ⟨-, hm, -⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        rw [hm]
      · rw [ite_eq_right ho] at H
        obtain ⟨hm, -, -, -⟩ :=
          (check_write_oset_ok_iff i oset (m_sigmask m) eff m m' evs).mp H
        rw [hm]
    · rw [ite_eq_right hn] at H
      cases hsr : sigset_at i.in_mem nset with
      | none =>
        simp only [hsr] at H
        obtain ⟨-, hm, -⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
        rw [hm]
      | some raw =>
        simp only [hsr] at H
        by_cases hh : (!(how_valid how)) = true
        · rw [ite_eq_left hh] at H
          obtain ⟨-, hm, -⟩ :=
            (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
              (errno_ret EINVAL) m [] m' evs).mp H
          rw [hm]
        · rw [ite_eq_right hh] at H
          by_cases ho : w_is0 oset = true
          · rw [ite_eq_left ho] at H
            obtain ⟨-, hm, -⟩ :=
              (check_ret_only_copyins_ok_iff [(nset, NSIG_BYTES.toNat)] eff
                (BitVec.ofInt 64 0)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) [] m' evs).mp H
            rw [hm, m_vmmaps_sigmask_deliver_model]
          · rw [ite_eq_right ho] at H
            unfold check_write_oset_copyins at H
            cases hcw : check_write_oset i oset (m_sigmask m) (clear_copyins eff)
                (sigmask_deliver_model
                  (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) with
            | CheckOk m2 evs2 =>
              simp only [hcw] at H
              by_cases hled : access_ranges_eqb eff.eff_copyins
                  [(nset, NSIG_BYTES.toNat)] = true
              · rw [ite_eq_left hled] at H
                obtain ⟨hm2, -⟩ := check_result.CheckOk.inj H
                obtain ⟨hdel, -, -, -⟩ :=
                  (check_write_oset_ok_iff i oset (m_sigmask m) (clear_copyins eff)
                    (sigmask_deliver_model
                      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m) m2 evs2).mp hcw
                rw [← hm2, hdel, m_vmmaps_sigmask_deliver_model]
              · rw [ite_eq_right hled] at H
                exact nomatch H
            | CheckReject =>
              simp only [hcw] at H
              exact nomatch H
            | CheckUnmodeled =>
              simp only [hcw] at H
              exact nomatch H

theorem check_send_sigabrt_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_send_sigabrt eff m = .CheckOk m' evs) :
    send_sigabrt i m (.ok eff m' evs) := by
  generalize hP : (send_sigabrt i m (.ok eff m' evs)) = Q at *
  obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cin <;>
    simp only [check_send_sigabrt] at H
  case nil.nil.nil.nil.nil =>
    by_cases hr : (!(ret == BitVec.ofInt 64 0)) = true
    · rw [ite_eq_left hr] at H
      exact nomatch H
    · rw [ite_eq_right hr] at H
      have hret : ret = BitVec.ofInt 64 0 := by
        have hb : (ret == BitVec.ofInt 64 0) = true := by
          cases h : (ret == BitVec.ofInt 64 0) with
          | false => exact absurd (by rw [h]; rfl) hr
          | true => rfl
        exact beq_iff_eq.mp hb
      subst hret
      by_cases hb : sigabrt_blocked (m_sigmask m) = true
      · rw [ite_eq_left hb] at H
        obtain ⟨hm, hevs⟩ := check_result.CheckOk.inj H
        rw [← hm, ← hevs] at hP
        rw [← hP]
        simp only [send_sigabrt, getModelSpec, bind_getModel, ite_eq_left hb, set_sigabrt_pending]
        exact seqSpec_modifySpec_ret_only_ok with_sigabrt_pending (BitVec.ofInt 64 0) i m
      · rw [ite_eq_right hb] at H
        obtain ⟨hm, hevs⟩ := check_result.CheckOk.inj H
        rw [← hm, ← hevs] at hP
        rw [← hP]
        simp only [send_sigabrt, getModelSpec, bind_getModel, ite_eq_right hb, set_killed]
        exact seqSpec_modifySpec_ret_only_ok (with_killed (BitVec.ofInt 64 SIGABRT))
          (BitVec.ofInt 64 0) i m
  all_goals exact nomatch H

theorem check_send_sigabrt_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_send_sigabrt eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cin <;>
    simp only [check_send_sigabrt] at H
  case nil.nil.nil.nil.nil =>
    by_cases hr : (!(ret == BitVec.ofInt 64 0)) = true
    · rw [ite_eq_left hr] at H
      exact nomatch H
    · rw [ite_eq_right hr] at H
      by_cases hb : sigabrt_blocked (m_sigmask m) = true
      · rw [ite_eq_left hb] at H
        exact nomatch H
      · rw [ite_eq_right hb] at H
        exact nomatch H
  all_goals exact nomatch H

theorem check_send_sigabrt_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : send_sigabrt i m (.ok eff m' evs)) :
    check_send_sigabrt eff m = .CheckOk m' evs := by
  generalize hP : (check_send_sigabrt eff m = .CheckOk m' evs) = Q at *
  simp only [send_sigabrt, getModelSpec, bind_getModel] at H
  by_cases hb : sigabrt_blocked (m_sigmask m) = true
  · rw [ite_eq_left hb] at H
    obtain ⟨hcore, hm', hevs'⟩ := seqSpec_modify_ret_only_inv with_sigabrt_pending
      (BitVec.ofInt 64 0) i m eff m' evs H
    rw [hcore, hm', hevs'] at hP
    rw [← hP]
    simp [check_send_sigabrt, hb]
  · rw [ite_eq_right hb] at H
    obtain ⟨hcore, hm', hevs'⟩ := seqSpec_modify_ret_only_inv
      (with_killed (BitVec.ofInt 64 SIGABRT)) (BitVec.ofInt 64 0) i m eff m' evs H
    rw [hcore, hm', hevs'] at hP
    rw [← hP]
    simp [check_send_sigabrt, hb]

theorem check_send_sigabrt_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : send_sigabrt i m .unmodeled) :
    check_send_sigabrt eff m = .CheckUnmodeled := by
  exfalso
  simp only [send_sigabrt, getModelSpec, bind_getModel] at H
  by_cases hb : sigabrt_blocked (m_sigmask m) = true
  · rw [ite_eq_left hb] at H
    exact absurd H (seqSpec_modify_ret_only_never_unmodeled with_sigabrt_pending
      (BitVec.ofInt 64 0) i m)
  · rw [ite_eq_right hb] at H
    exact absurd H (seqSpec_modify_ret_only_never_unmodeled
      (with_killed (BitVec.ofInt 64 SIGABRT)) (BitVec.ofInt 64 0) i m)

theorem check_tkill_self_sound_ok (pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_tkill_self pid sig eff m = .CheckOk m' evs) :
    tkill_self pid sig i m (.ok eff m' evs) := by
  generalize hP : (tkill_self pid sig i m (.ok eff m' evs)) = Q at *
  simp only [check_tkill_self] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    cases htid : m_tid m with
    | none =>
      simp only [htid] at H
      exact nomatch H
    | some t =>
      simp only [htid] at H
      by_cases hpid : (!(pid == t)) = true
      · rw [ite_eq_left hpid] at H
        exact nomatch H
      · rw [ite_eq_right hpid] at H
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · rw [ite_eq_left hsig] at H
          obtain ⟨heff, hm, hevs⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          rw [hevs, heff, hm] at hP
          rw [← hP]
          simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid,
            ite_eq_right hpid, ite_eq_left hsig, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
        · rw [ite_eq_right hsig] at H
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · rw [ite_eq_left habrt] at H
            rw [← hP]
            simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid,
              ite_eq_right hpid, ite_eq_right hsig, ite_eq_left habrt]
            exact check_send_sigabrt_sound_ok eff m m' evs i H
          · rw [ite_eq_right habrt] at H
            exact nomatch H

theorem check_tkill_self_sound_unmodeled (pid sig : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_tkill_self pid sig eff m = .CheckUnmodeled) :
    tkill_self pid sig i m .unmodeled := by
  generalize hP : (tkill_self pid sig i m .unmodeled) = Q at *
  simp only [check_tkill_self] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_left hterm, unmodeled]
  · rw [ite_eq_right hterm] at H
    cases htid : m_tid m with
    | none =>
      simp only [htid] at H
      rw [← hP]
      simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid, unmodeled]
    | some t =>
      simp only [htid] at H
      by_cases hpid : (!(pid == t)) = true
      · rw [ite_eq_left hpid] at H
        rw [← hP]
        simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid,
          ite_eq_left hpid, unmodeled]
      · rw [ite_eq_right hpid] at H
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · rw [ite_eq_left hsig] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hsig] at H
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · rw [ite_eq_left habrt] at H
            rw [← hP]
            simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid,
              ite_eq_right hpid, ite_eq_right hsig, ite_eq_left habrt]
            exact absurd H (check_send_sigabrt_no_unmodeled eff m)
          · rw [ite_eq_right habrt] at H
            rw [← hP]
            simp only [tkill_self, getModelSpec, bind_getModel, ite_eq_right hterm, htid,
              ite_eq_right hpid, ite_eq_right hsig, ite_eq_right habrt, unmodeled]

theorem check_tkill_self_complete_ok (pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : tkill_self pid sig i m (.ok eff m' evs)) :
    check_tkill_self pid sig eff m = .CheckOk m' evs := by
  generalize hP : (check_tkill_self pid sig eff m = .CheckOk m' evs) = Q at *
  simp only [tkill_self, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    cases htid : m_tid m with
    | none =>
      simp only [htid] at H
      simp only [unmodeled] at H
      exact nomatch H
    | some t =>
      simp only [htid] at H
      by_cases hpid : (!(pid == t)) = true
      · rw [ite_eq_left hpid] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hpid] at H
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · rw [ite_eq_left hsig] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨heff, hm, hevs⟩ := H
          rw [hevs, heff, hm] at hP
          rw [← hP]
          simp only [check_tkill_self, ite_eq_right hterm, htid, ite_eq_right hpid, ite_eq_left hsig,
            check_ret_only, bv_eqb_refl, ite_eq_left]
        · rw [ite_eq_right hsig] at H
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · rw [ite_eq_left habrt] at H
            rw [← hP]
            simp only [check_tkill_self, ite_eq_right hterm, htid, ite_eq_right hpid, ite_eq_right hsig,
              ite_eq_left habrt]
            exact check_send_sigabrt_complete_ok eff m m' evs i H
          · rw [ite_eq_right habrt] at H
            simp only [unmodeled] at H
            exact nomatch H

theorem check_tkill_self_complete_unmodeled (pid sig : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : tkill_self pid sig i m .unmodeled) :
    check_tkill_self pid sig eff m = .CheckUnmodeled := by
  generalize hP : (check_tkill_self pid sig eff m = .CheckUnmodeled) = Q at *
  simp only [tkill_self, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [check_tkill_self, ite_eq_left hterm]
  · rw [ite_eq_right hterm] at H
    cases htid : m_tid m with
    | none =>
      simp only [htid] at H
      rw [← hP]
      simp only [check_tkill_self, ite_eq_right hterm, htid]
    | some t =>
      simp only [htid] at H
      by_cases hpid : (!(pid == t)) = true
      · rw [ite_eq_left hpid] at H
        rw [← hP]
        simp only [check_tkill_self, ite_eq_right hterm, htid, ite_eq_left hpid]
      · rw [ite_eq_right hpid] at H
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · rw [ite_eq_left hsig] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        · rw [ite_eq_right hsig] at H
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · rw [ite_eq_left habrt] at H
            rw [← hP]
            simp only [check_tkill_self, ite_eq_right hterm, htid, ite_eq_right hpid, ite_eq_right hsig,
              ite_eq_left habrt]
            exact check_send_sigabrt_complete_unmodeled m i eff H
          · rw [ite_eq_right habrt] at H
            rw [← hP]
            simp only [check_tkill_self, ite_eq_right hterm, htid, ite_eq_right hpid, ite_eq_right hsig,
              ite_eq_right habrt]

/-! ## The abort path: tkill (130) and tgkill (131) -/

theorem check_tkill_sound_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_tkill pid sig eff m = .CheckOk m' evs) :
    tkill_spec pid sig i m (.ok eff m' evs) := by
  generalize hP : (tkill_spec pid sig i m (.ok eff m' evs)) = Q at *
  simp only [check_tkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid)) = true
    · rw [ite_eq_left hpos] at H
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [hevs, heff, hm] at hP
      rw [← hP]
      simp only [tkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_left hpos,
        err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right hpos] at H
      rw [← hP]
      simp only [tkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos]
      exact check_tkill_self_sound_ok pid sig eff m m' evs i H

theorem check_tkill_sound_unmodeled (pid sig : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_tkill pid sig eff m = .CheckUnmodeled) :
    tkill_spec pid sig i m .unmodeled := by
  generalize hP : (tkill_spec pid sig i m .unmodeled) = Q at *
  simp only [check_tkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [tkill_spec, getModelSpec, bind_getModel, ite_eq_left hterm, unmodeled]
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid)) = true
    · rw [ite_eq_left hpos] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hpos] at H
      rw [← hP]
      simp only [tkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos]
      exact check_tkill_self_sound_unmodeled pid sig eff m i H

theorem check_tkill_complete_ok (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : tkill_spec pid sig i m (.ok eff m' evs)) :
    check_tkill pid sig eff m = .CheckOk m' evs := by
  generalize hP : (check_tkill pid sig eff m = .CheckOk m' evs) = Q at *
  simp only [tkill_spec, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid)) = true
    · rw [ite_eq_left hpos] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨heff, hm, hevs⟩ := H
      rw [hevs, heff, hm] at hP
      rw [← hP]
      simp only [check_tkill, ite_eq_right hterm, ite_eq_left hpos, check_ret_only, bv_eqb_refl, ite_eq_left]
    · rw [ite_eq_right hpos] at H
      rw [← hP]
      simp only [check_tkill, ite_eq_right hterm, ite_eq_right hpos]
      exact check_tkill_self_complete_ok pid sig eff m m' evs i H

theorem check_tkill_complete_unmodeled (pid sig : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : tkill_spec pid sig i m .unmodeled) :
    check_tkill pid sig eff m = .CheckUnmodeled := by
  generalize hP : (check_tkill pid sig eff m = .CheckUnmodeled) = Q at *
  simp only [tkill_spec, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [check_tkill, ite_eq_left hterm]
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid)) = true
    · rw [ite_eq_left hpos] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right hpos] at H
      rw [← hP]
      simp only [check_tkill, ite_eq_right hterm, ite_eq_right hpos]
      exact check_tkill_self_complete_unmodeled pid sig m i eff H

theorem check_tgkill_sound_ok (tgid pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_tgkill tgid pid sig eff m = .CheckOk m' evs) :
    tgkill_spec tgid pid sig i m (.ok eff m' evs) := by
  generalize hP : (tgkill_spec tgid pid sig i m (.ok eff m' evs)) = Q at *
  simp only [check_tgkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · rw [ite_eq_left hpos] at H
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [hevs, heff, hm] at hP
      rw [← hP]
      simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_left hpos,
        err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right hpos] at H
      cases htid : m_tid m with
      | none =>
        simp only [htid] at H
        exact nomatch H
      | some t =>
        simp only [htid] at H
        by_cases hpid : (!(pid == t)) = true
        · rw [ite_eq_left hpid] at H
          exact nomatch H
        · rw [ite_eq_right hpid] at H
          by_cases htg : (!(tgid == t)) = true
          · rw [ite_eq_left htg] at H
            obtain ⟨heff, hm, hevs⟩ :=
              (check_ret_only_ok_iff eff (errno_ret ESRCH) m [] m' evs).mp H
            rw [hevs, heff, hm] at hP
            rw [← hP]
            simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos,
              htid, ite_eq_right hpid, ite_eq_left htg, err_ret, ret_only,
              LinuxSem.LinuxProcessSem.pure]
          · rw [ite_eq_right htg] at H
            rw [← hP]
            simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos,
              htid, ite_eq_right hpid, ite_eq_right htg]
            exact check_tkill_self_sound_ok pid sig eff m m' evs i H

theorem check_tgkill_sound_unmodeled (tgid pid sig : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_tgkill tgid pid sig eff m = .CheckUnmodeled) :
    tgkill_spec tgid pid sig i m .unmodeled := by
  generalize hP : (tgkill_spec tgid pid sig i m .unmodeled) = Q at *
  simp only [check_tgkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_left hterm, unmodeled]
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · rw [ite_eq_left hpos] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hpos] at H
      cases htid : m_tid m with
      | none =>
        simp only [htid] at H
        rw [← hP]
        simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos,
          htid, unmodeled]
      | some t =>
        simp only [htid] at H
        by_cases hpid : (!(pid == t)) = true
        · rw [ite_eq_left hpid] at H
          rw [← hP]
          simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos,
            htid, ite_eq_left hpid, unmodeled]
        · rw [ite_eq_right hpid] at H
          by_cases htg : (!(tgid == t)) = true
          · rw [ite_eq_left htg] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESRCH) m [])
          · rw [ite_eq_right htg] at H
            rw [← hP]
            simp only [tgkill_spec, getModelSpec, bind_getModel, ite_eq_right hterm, ite_eq_right hpos,
              htid, ite_eq_right hpid, ite_eq_right htg]
            exact check_tkill_self_sound_unmodeled pid sig eff m i H

theorem check_tgkill_complete_ok (tgid pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : tgkill_spec tgid pid sig i m (.ok eff m' evs)) :
    check_tgkill tgid pid sig eff m = .CheckOk m' evs := by
  generalize hP : (check_tgkill tgid pid sig eff m = .CheckOk m' evs) = Q at *
  simp only [tgkill_spec, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · rw [ite_eq_left hpos] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨heff, hm, hevs⟩ := H
      rw [hevs, heff, hm] at hP
      rw [← hP]
      simp only [check_tgkill, ite_eq_right hterm, ite_eq_left hpos, check_ret_only, bv_eqb_refl, ite_eq_left]
    · rw [ite_eq_right hpos] at H
      cases htid : m_tid m with
      | none =>
        simp only [htid] at H
        simp only [unmodeled] at H
        exact nomatch H
      | some t =>
        simp only [htid] at H
        by_cases hpid : (!(pid == t)) = true
        · rw [ite_eq_left hpid] at H
          simp only [unmodeled] at H
          exact nomatch H
        · rw [ite_eq_right hpid] at H
          by_cases htg : (!(tgid == t)) = true
          · rw [ite_eq_left htg] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨heff, hm, hevs⟩ := H
            rw [hevs, heff, hm] at hP
            rw [← hP]
            simp only [check_tgkill, ite_eq_right hterm, ite_eq_right hpos, htid, ite_eq_right hpid, ite_eq_left htg,
              check_ret_only, bv_eqb_refl, ite_eq_left]
          · rw [ite_eq_right htg] at H
            rw [← hP]
            simp only [check_tgkill, ite_eq_right hterm, ite_eq_right hpos, htid, ite_eq_right hpid, ite_eq_right htg]
            exact check_tkill_self_complete_ok pid sig eff m m' evs i H

theorem check_tgkill_complete_unmodeled (tgid pid sig : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : tgkill_spec tgid pid sig i m .unmodeled) :
    check_tgkill tgid pid sig eff m = .CheckUnmodeled := by
  generalize hP : (check_tgkill tgid pid sig eff m = .CheckUnmodeled) = Q at *
  simp only [tgkill_spec, getModelSpec, bind_getModel] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    rw [← hP]
    simp only [check_tgkill, ite_eq_left hterm]
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · rw [ite_eq_left hpos] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right hpos] at H
      cases htid : m_tid m with
      | none =>
        simp only [htid] at H
        rw [← hP]
        simp only [check_tgkill, ite_eq_right hterm, ite_eq_right hpos, htid]
      | some t =>
        simp only [htid] at H
        by_cases hpid : (!(pid == t)) = true
        · rw [ite_eq_left hpid] at H
          rw [← hP]
          simp only [check_tgkill, ite_eq_right hterm, ite_eq_right hpos, htid, ite_eq_left hpid]
        · rw [ite_eq_right hpid] at H
          by_cases htg : (!(tgid == t)) = true
          · rw [ite_eq_left htg] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · rw [ite_eq_right htg] at H
            rw [← hP]
            simp only [check_tgkill, ite_eq_right hterm, ite_eq_right hpos, htid, ite_eq_right hpid, ite_eq_right htg]
            exact check_tkill_self_complete_unmodeled pid sig m i eff H

/-! ## Framing: neither arm touches the address space

    The proofs walk every `if` and `match` in the checker explicitly and
    reuse the two intermediate framing lemmas below, so the
    `check_send_sigabrt` acceptors' effect match is written out once. -/

/-- [check_send_sigabrt] carries the model forward through [ProcState]
    alone: the pending bit and the kill both rebuild that record. -/
theorem check_send_sigabrt_frame (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_send_sigabrt eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨ret, ws, zs, us, cs, cin⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cin <;>
    simp only [check_send_sigabrt] at H
  case nil.nil.nil.nil.nil =>
    by_cases hr : (!(ret == BitVec.ofInt 64 0)) = true
    · rw [ite_eq_left hr] at H
      exact nomatch H
    · rw [ite_eq_right hr] at H
      by_cases hb : sigabrt_blocked (m_sigmask m) = true
      · rw [ite_eq_left hb] at H
        obtain ⟨hm, -⟩ := check_result.CheckOk.inj H
        rw [← hm]
        simp
      · rw [ite_eq_right hb] at H
        obtain ⟨hm, -⟩ := check_result.CheckOk.inj H
        rw [← hm]
        simp
  all_goals exact nomatch H

/-- …and so does [check_tkill_self], whose only model-changing arm is
    that one. -/
theorem check_tkill_self_frame (pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_tkill_self pid sig eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  simp only [check_tkill_self] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    cases htid : m_tid m with
    | none =>
      simp only [htid] at H
      exact nomatch H
    | some t =>
      simp only [htid] at H
      by_cases hpid : (!(pid == t)) = true
      · rw [ite_eq_left hpid] at H
        exact nomatch H
      · rw [ite_eq_right hpid] at H
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · rw [ite_eq_left hsig] at H
          obtain ⟨-, hm, -⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          rw [hm]
        · rw [ite_eq_right hsig] at H
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · rw [ite_eq_left habrt] at H
            exact check_send_sigabrt_frame eff m m' evs H
          · rw [ite_eq_right habrt] at H
            exact nomatch H

/-- The framing statement the [Checks.VmMapsDisjoint] cascade consumes.
    `VmMapsDisjoint/Chain/Arms.lean` cites this lemma from
    `arm_tkill_preserves_vm` / `arm_tgkill_preserves_vm`, which
    `checked_table_preserves_vm` carries into
    `check_syscall_preserves_vm_wf`.
    Both arms change the model on one branch each -- the pending bit and
    the kill -- and neither touches the address space: [State.with_killed]
    and [State.with_sigabrt_pending] rebuild [ProcState] alone. -/
theorem check_tkill_frame (pid sig : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_tkill pid sig eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  simp only [check_tkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid)) = true
    · rw [ite_eq_left hpos] at H
      obtain ⟨-, hm, -⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [hm]
    · rw [ite_eq_right hpos] at H
      exact check_tkill_self_frame pid sig eff m m' evs H

theorem check_tgkill_frame (tgid pid sig : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_tgkill tgid pid sig eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  simp only [check_tgkill] at H
  by_cases hterm : (!(m_abort_terminal m)) = true
  · rw [ite_eq_left hterm] at H
    exact nomatch H
  · rw [ite_eq_right hterm] at H
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · rw [ite_eq_left hpos] at H
      obtain ⟨-, hm, -⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [hm]
    · rw [ite_eq_right hpos] at H
      cases htid : m_tid m with
      | none =>
        simp only [htid] at H
        exact nomatch H
      | some t =>
        simp only [htid] at H
        by_cases hpid : (!(pid == t)) = true
        · rw [ite_eq_left hpid] at H
          exact nomatch H
        · rw [ite_eq_right hpid] at H
          by_cases htg : (!(tgid == t)) = true
          · rw [ite_eq_left htg] at H
            obtain ⟨-, hm, -⟩ :=
              (check_ret_only_ok_iff eff (errno_ret ESRCH) m [] m' evs).mp H
            rw [hm]
          · rw [ite_eq_right htg] at H
            exact check_tkill_self_frame pid sig eff m m' evs H

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  The first group pins
    the computable predicates against the prose that cites them — `_NSIG`
    is 64 and INCLUSIVE, SIGKILL/SIGSTOP are the kernel-only pair, the
    `sigset_t` is eight bytes, `SS_DISABLE` is a mode and SIGABRT is bit 5
    of the mask.  The second pins the branch ORDER the proofs above
    follow, with the branch test supplied as a hypothesis: that is exactly
    what the proofs split on.

    They are sanity checks, not library lemmas.  `check_result` carries no
    `DecidableEq`, so each states the branch as an equation and closes it
    by unfolding the checker and discharging the branch test. -/

/-- `_NSIG` is 64 and the bound is INCLUSIVE: 64 is valid, 65 is not,
    and 0 is not (unlike [tkill_sig_valid], which keeps 0 as the
    permission probe). -/
example : sig_valid (BitVec.ofInt 64 64) = true ∧
    sig_valid (BitVec.ofInt 64 65) = false ∧
    sig_valid (BitVec.ofInt 64 0) = false := by decide

/-- …while [tkill_sig_valid] accepts 0 and stops at 64. -/
example : tkill_sig_valid (BitVec.ofInt 64 0) = true ∧
    tkill_sig_valid (BitVec.ofInt 64 64) = true ∧
    tkill_sig_valid (BitVec.ofInt 64 65) = false := by decide

/-- SIGKILL (9) and SIGSTOP (19) are the kernel-only pair, and they are
    the two bits [sigmask_strip] clears. -/
example : sig_kernel_only (BitVec.ofInt 64 9) = true ∧
    sig_kernel_only (BitVec.ofInt 64 19) = true ∧
    sig_kernel_only (BitVec.ofInt 64 15) = false := by decide

/-- A word with neither bit set is launchable, and the strip makes any
    word launchable. -/
example : mask_launchable (BitVec.ofInt 64 0) ∧
    mask_launchable (sigmask_strip (BitVec.ofInt 64 (-1))) := by
  constructor
  · unfold mask_launchable
    decide
  · exact sigmask_strip_launchable _

/-- `sa_flags_ok` accepts the empty flag word and rejects SA_RESTART,
    which is outside [sa_flags_accepted]. -/
example : sa_flags_ok (BitVec.ofInt 64 0) = true ∧
    sa_flags_ok (BitVec.ofInt 64 0x10000000) = false := by decide

/-- The `sigset_t` the two syscalls size-check is eight bytes, and
    `sigaltstack`'s `stack_t` is 24. -/
example : NSIG_BYTES = 8 ∧ SIGALTSTACK_BYTES = 24 ∧ MINSIGSTKSZ = 2048 :=
  ⟨rfl, rfl, rfl⟩

/-- SIGABRT is 6 and its mask is bit 5 — what [sigabrt_blocked] reads. -/
example : SIGABRT = 6 ∧ sigabrt_mask = 32 ∧
    sigabrt_blocked (BitVec.ofInt 64 32) = true ∧
    sigabrt_blocked (BitVec.ofInt 64 0) = false := by decide

/-- `rt_sigaction`'s FIRST branch is the bad-`sigsetsize` -EINVAL, before
    either pointer is looked at. -/
example (i : SyscallInput) (sig act oact ss : word) (eff : SyscallEffect) (m : Model)
    (h : (!(ss == BitVec.ofInt 64 8)) = true) :
    check_rt_sigaction i sig act oact ss eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_rt_sigaction, ite_eq_left h]

/-- `rt_sigaction`'s second is the [oact] decline. -/
example (i : SyscallInput) (sig act oact ss : word) (eff : SyscallEffect) (m : Model)
    (h : (!(ss == BitVec.ofInt 64 8)) = false) (ho : (!(w_is0 oact)) = true) :
    check_rt_sigaction i sig act oact ss eff m = .CheckUnmodeled := by
  rw [check_rt_sigaction, ite_eq_right (by rw [h]; simp), ite_eq_left ho]

/-- `rt_sigprocmask`'s first branch is the bad-`sigsetsize` -EINVAL, and
    it carries NO copy-in ledger. -/
example (i : SyscallInput) (how nset oset ss : word) (eff : SyscallEffect) (m : Model)
    (h : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true) :
    check_rt_sigprocmask i how nset oset ss eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_rt_sigprocmask, ite_eq_left h]

/-- `sigaltstack` declines on an installed stack, and on a non-NULL
    `uoss`, before reading either pointer's target. -/
example (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect) (m : Model)
    (h : m_sigaltstack_installed m = true) :
    check_sigaltstack i uss uoss eff m = .CheckUnmodeled := by
  simp only [check_sigaltstack, ite_eq_left h]

example (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect) (m : Model)
    (h : m_sigaltstack_installed m = false) (ho : (!(w_is0 uoss)) = true) :
    check_sigaltstack i uss uoss eff m = .CheckUnmodeled := by
  rw [check_sigaltstack, ite_eq_right (by rw [h]; simp), ite_eq_left ho]

/-- A BLOCKED SIGABRT leaves the pending bit and does NOT kill. -/
example (m : Model) (h : sigabrt_blocked (m_sigmask m) = true) :
    check_send_sigabrt (mkEffect (BitVec.ofInt 64 0) [] []) m
      = .CheckOk (with_sigabrt_pending m) [] := by
  simp only [check_send_sigabrt]
  rw [ite_eq_right (by decide), ite_eq_left h]

/-- An UNBLOCKED one kills, and the effect (0, no ledger) is discarded by
    the step that observes the kill. -/
example (m : Model) (h : sigabrt_blocked (m_sigmask m) = false) :
    check_send_sigabrt (mkEffect (BitVec.ofInt 64 0) [] []) m
      = .CheckOk (with_killed (BitVec.ofInt 64 SIGABRT) m) [] := by
  simp only [check_send_sigabrt]
  rw [ite_eq_right (by decide), ite_eq_right (by rw [h]; simp)]

/-- …and any other return value is REJECTED: the fatal branch still has to
    claim 0. -/
example (m : Model) :
    check_send_sigabrt (mkEffect (BitVec.ofInt 64 1) [] []) m = .CheckReject := by
  simp only [check_send_sigabrt]
  rw [ite_eq_left (by decide)]

/-- `tkill` with the abort declaration OFF is declined outright, before
    the pid is even read. -/
example (pid sig : word) (eff : SyscallEffect) (m : Model)
    (h : (!(m_abort_terminal m)) = true) :
    check_tkill pid sig eff m = .CheckUnmodeled := by
  simp only [check_tkill, ite_eq_left h]

/-- `tgkill` tests the abort declaration first too. -/
example (tgid pid sig : word) (eff : SyscallEffect) (m : Model)
    (h : (!(m_abort_terminal m)) = true) :
    check_tgkill tgid pid sig eff m = .CheckUnmodeled := by
  simp only [check_tgkill, ite_eq_left h]

/-- The `oset` copy-out tests `access_ok` BEFORE the memory walk, and a
    range that fails it is -EFAULT with an EMPTY ledger — a failed
    `copy_to_user` writes nothing. -/
example (i : SyscallInput) (oset old : word) (eff : SyscallEffect) (m : Model)
    (h : access_okb oset NSIG_BYTES = false) :
    check_write_oset i oset old eff m
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  rw [check_write_oset, ite_eq_left (by rw [h]; rfl)]

end LinuxSem.Checks.Sys.Kernel.Signal




