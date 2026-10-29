/-
  * LinuxProcessSem.Checks.Witness.Kernel.Signal — the rt_sigaction (134) and rt_sigprocmask (135) witnesses, and their proofs

  Answers to Linux [kernel/signal.c]: this file holds the witnesses for the syscalls
  defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  The file also holds the tkill (130), tgkill (131) and sigaltstack (132)
  witnesses, in that order.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` is `Checks/Witness/Prelude.lean`'s helper
  (the "return `r`, change nothing, emit nothing" outcome), and
  `outcome_copyins` is `Syscall.outcome_copyins` of this tree.

  Each proof peels the readers with `bind_step` — the `bind_step` of
  `Checks.Witness.Prelude` takes `input_ok`, `get_model_ok` or `modify_ok`
  as its premise — supplies the branch equations with `by_cases`, rewrites
  both sides with `simp only [ite_eq_left …]` / `[ite_eq_right …]`, and closes the
  ret-arms with the local `signal_ret_leaf` macro (named apart from the
  `ret_leaf` of `Checks/Witness/Fs/Open.lean` because macro declarations
  are global and the root module imports both files).
  `record_copyins_outcome` turns a proof of the arm's core into the
  recorded-ledger outcome, which is how the copy-in arms are discharged.

  The sigaltstack arm tests
  `((ss_size_of bs).toNat : Int) < MINSIGSTKSZ`, and `by_cases` on it
  makes `whnf` recurse through the `Decidable` instance of a
  `BitVec.toNat` of an opaque word.  That one split is therefore taken as
  `cases h : decide (…)` (then `decide_eq_true_eq` /
  `decide_eq_false_iff_not`), which never normalises the goal.  The
  checker file's proofs instead `generalize` their conclusion; see its
  header.

  [tkill_self_witness] steps through [send_sigabrt], whose body is two
  monad setters; the spec declares [set_sigabrt_pending] / [set_killed]
  locally in
  `Sys/Kernel/Signal.lean`, and the `modify_ok` steps below name the
  `with_sigabrt_pending` / `with_killed` functions directly.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Signal

namespace LinuxSem.Checks.Witness.Kernel.Signal

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
open LinuxSem.Checks.Witness.Prelude

/-- Close a `ret_outcome` / `ret_only` / `err_ret` leaf: the three are
    the same "return `r`, change nothing, emit nothing" outcome once the
    abbreviations are unfolded.  Named `signal_ret_leaf` rather than
    `ret_leaf` so it cannot collide with the identically-shaped macro
    `Checks/Witness/Fs/Open.lean` declares — macro declarations are
    global, and the root module imports both files. -/
macro "signal_ret_leaf" : tactic =>
  `(tactic| simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure])

/-- The spec monad's [bind] under an unambiguous name.  Lean's root
    [bind] is [Bind.bind], so the unqualified name would be ambiguous. -/
local notation "bind" => LinuxSem.LinuxProcessSem.bind

/-! ## sigaltstack (132) -/

/-- The spec is deterministic — no [choose], no [alt] — so the witness is
    its arm structure read as a function. -/
def sigaltstack_witness (uss uoss : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if m_sigaltstack_installed m then .unmodeled
  else if !(w_is0 uoss) then .unmodeled
  else if w_is0 uss then ret_outcome (BitVec.ofInt 64 0) m
  else
    match sigaltstack_at i.in_mem uss with
    | none => ret_outcome (errno_ret EFAULT) m
    | some bs =>
        if !(ss_mode_ok (ss_flags_of bs))
        then ret_outcome (errno_ret EINVAL) m
        else if ss_disabling (ss_flags_of bs)
        then ret_outcome (BitVec.ofInt 64 0) m
        else if (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs))
        then .unmodeled
        else if ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
        then ret_outcome (errno_ret ENOMEM) m
        else ret_outcome (BitVec.ofInt 64 0) (with_sigaltstack_installed m)

theorem sigaltstack_witness_ok (uss uoss : word) (i : SyscallInput) (m : Model) :
    sigaltstack_spec uss uoss i m (sigaltstack_witness uss uoss i m) := by
  unfold sigaltstack_spec sigaltstack_witness
  apply bind_step
  · exact getModel_ok i m
  · by_cases hw : m_sigaltstack_installed m = true
    · simp only [ite_eq_left hw]
      exact unmodeled_intro i m
    · simp only [ite_eq_right hw]
      by_cases ho : (!(w_is0 uoss)) = true
      · simp only [ite_eq_left ho]
        exact unmodeled_intro i m
      · simp only [ite_eq_right ho]
        by_cases hu : w_is0 uss = true
        · simp only [ite_eq_left hu]
          signal_ret_leaf
        · simp only [ite_eq_right hu]
          apply bind_step
          · exact input_ok i m
          · cases hbs : sigaltstack_at i.in_mem uss with
            | none =>
              signal_ret_leaf
            | some bs =>
              by_cases hmode : (!(ss_mode_ok (ss_flags_of bs))) = true
              · simp only [ite_eq_left hmode]
                signal_ret_leaf
              · simp only [ite_eq_right hmode]
                by_cases hdis : ss_disabling (ss_flags_of bs) = true
                · simp only [ite_eq_left hdis]
                  signal_ret_leaf
                · simp only [ite_eq_right hdis]
                  by_cases hzero : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
                  · simp only [ite_eq_left hzero]
                    exact unmodeled_intro i m
                  · simp only [ite_eq_right hzero]
                    cases hsz : decide (((ss_size_of bs).toNat : Int) < MINSIGSTKSZ) with
                    | true =>
                      simp only [ite_eq_left (decide_eq_true_eq.mp hsz)]
                      signal_ret_leaf
                    | false =>
                      simp only [ite_eq_right (decide_eq_false_iff_not.mp hsz)]
                      apply bind_step
                      · exact modify_ok with_sigaltstack_installed i m
                      · signal_ret_leaf

/-! ## rt_sigaction (134) -/

def rt_sigaction_witness (sig act oact ss : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(ss == BitVec.ofInt 64 8) then ret_outcome (errno_ret EINVAL) m
  else if !(w_is0 oact) then .unmodeled
  else if w_is0 act
  then (if sig_valid sig then ret_outcome (BitVec.ofInt 64 0) m
        else ret_outcome (errno_ret EINVAL) m)
  else
    match sigaction_flags i.in_mem act with
    | none => ret_outcome (errno_ret EFAULT) m
    | some fl =>
        if !(sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if sig_kernel_only sig then ret_outcome (errno_ret EINVAL) m
        else if !(sa_flags_ok fl) then .unmodeled
        else if sigaction_accepted sig then ret_outcome (BitVec.ofInt 64 0) m
        else .unmodeled

theorem rt_sigaction_witness_ok (sig act oact ss : word) (i : SyscallInput)
    (m : Model) :
    rt_sigaction_spec sig act oact ss i m
      (rt_sigaction_witness sig act oact ss i m) := by
  unfold rt_sigaction_spec rt_sigaction_witness
  by_cases hss : (!(ss == BitVec.ofInt 64 8)) = true
  · simp only [ite_eq_left hss]
    signal_ret_leaf
  · simp only [ite_eq_right hss]
    by_cases hoact : (!(w_is0 oact)) = true
    · simp only [ite_eq_left hoact]
      exact unmodeled_intro i m
    · simp only [ite_eq_right hoact]
      by_cases hact : w_is0 act = true
      · simp only [ite_eq_left hact]
        by_cases hv : sig_valid sig = true
        · simp only [ite_eq_left hv]
          signal_ret_leaf
        · simp only [ite_eq_right hv]
          signal_ret_leaf
      · simp only [ite_eq_right hact]
        apply bind_step
        · exact input_ok i m
        · cases hfl : sigaction_flags i.in_mem act with
          | none =>
            signal_ret_leaf
          | some fl =>
            by_cases hv : (!(sig_valid sig)) = true
            · simp only [ite_eq_left hv]
              signal_ret_leaf
            · simp only [ite_eq_right hv]
              by_cases hk : sig_kernel_only sig = true
              · simp only [ite_eq_left hk]
                signal_ret_leaf
              · simp only [ite_eq_right hk]
                by_cases hfo : (!(sa_flags_ok fl)) = true
                · simp only [ite_eq_left hfo]
                  exact unmodeled_intro i m
                · simp only [ite_eq_right hfo]
                  by_cases hac : sigaction_accepted sig = true
                  · simp only [ite_eq_left hac]
                    signal_ret_leaf
                  · simp only [ite_eq_right hac]
                    exact unmodeled_intro i m

/-! ## write_oset — the shared copy-out arm -/

/-- The [oset] copy-out is factored out the way the spec factors it, so the
    two stay in step arm for arm. -/
def write_oset_witness (oset old : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(access_okb oset NSIG_BYTES)
  then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
    | none => .unmodeled
    | some _ =>
        .ok (mkEffect (BitVec.ofInt 64 0)
              [(oset, Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int))]
              []) m []

theorem write_oset_witness_ok (oset old : word) (i : SyscallInput) (m : Model) :
    write_oset oset old i m (write_oset_witness oset old i m) := by
  unfold write_oset write_oset_witness
  by_cases ha : (!(access_okb oset NSIG_BYTES)) = true
  · simp only [ite_eq_left ha]
    signal_ret_leaf
  · simp only [ite_eq_right ha]
    apply bind_step
    · exact input_ok i m
    · cases hw : read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
      | none =>
        exact unmodeled_intro i m
      | some bs =>
        signal_ret_leaf

/-! ## rt_sigprocmask (135) -/

/-- The spec is deterministic — no [choose], no [alt] — so the witness is
    the spec's own arm structure read as a function.  The [oset] copy-out
    is factored out the way the spec factors it, so the two stay in step
    arm for arm. -/
def rt_sigprocmask_witness (how nset oset ss : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(ss == BitVec.ofInt 64 NSIG_BYTES)
  then ret_outcome (errno_ret EINVAL) m
  else
    let old := m_sigmask m
    if w_is0 nset
    then (if w_is0 oset then ret_outcome (BitVec.ofInt 64 0) m
          else write_oset_witness oset old i m)
    else
      match sigset_at i.in_mem nset with
      | none => ret_outcome (errno_ret EFAULT) m
      | some raw =>
          outcome_copyins [(nset, NSIG_BYTES.toNat)]
            (if !(how_valid how) then ret_outcome (errno_ret EINVAL) m
             else
               let m' := sigmask_deliver_model
                           (sigmask_apply how old (sigmask_strip raw)) m
               if w_is0 oset then ret_outcome (BitVec.ofInt 64 0) m'
               else write_oset_witness oset old i m')

theorem rt_sigprocmask_witness_ok (how nset oset ss : word) (i : SyscallInput)
    (m : Model) :
    rt_sigprocmask_spec how nset oset ss i m
      (rt_sigprocmask_witness how nset oset ss i m) := by
  unfold rt_sigprocmask_spec rt_sigprocmask_witness
  by_cases hss : (!(ss == BitVec.ofInt 64 NSIG_BYTES)) = true
  · simp only [ite_eq_left hss]
    signal_ret_leaf
  · simp only [ite_eq_right hss]
    apply bind_step
    · exact getModel_ok i m
    · by_cases hn : w_is0 nset = true
      · simp only [ite_eq_left hn]
        by_cases ho : w_is0 oset = true
        · simp only [ite_eq_left ho]
          signal_ret_leaf
        · simp only [ite_eq_right ho]
          exact write_oset_witness_ok oset (m_sigmask m) i m
      · simp only [ite_eq_right hn]
        apply bind_step
        · exact input_ok i m
        · cases hsr : sigset_at i.in_mem nset with
          | none =>
            signal_ret_leaf
          | some raw =>
            apply record_copyins_outcome
            by_cases hh : (!(how_valid how)) = true
            · simp only [ite_eq_left hh]
              signal_ret_leaf
            · simp only [ite_eq_right hh]
              apply bind_step
              · exact modify_ok
                  (sigmask_deliver_model
                    (sigmask_apply how (m_sigmask m) (sigmask_strip raw))) i m
              · by_cases ho : w_is0 oset = true
                · simp only [ite_eq_left ho]
                  signal_ret_leaf
                · simp only [ite_eq_right ho]
                  exact write_oset_witness_ok oset (m_sigmask m) i
                    (sigmask_deliver_model
                      (sigmask_apply how (m_sigmask m) (sigmask_strip raw)) m)

/-! ## tkill (130) and tgkill (131) -/

/-- The witness follows the spec's own branch structure, including the
    declaration gate at the head: with the declaration off every shape is
    [Unmodeled], which is the witness the dispatcher's progress theorem
    wants for a number the model declines. -/
def send_sigabrt_witness (m : Model) : Outcome SyscallEffect Model event :=
  if sigabrt_blocked (m_sigmask m)
  then ret_outcome (BitVec.ofInt 64 0) (with_sigabrt_pending m)
  else ret_outcome (BitVec.ofInt 64 0) (with_killed (BitVec.ofInt 64 SIGABRT) m)

theorem send_sigabrt_witness_ok (i : SyscallInput) (m : Model) :
    send_sigabrt i m (send_sigabrt_witness m) := by
  unfold send_sigabrt send_sigabrt_witness
  simp only [getModelSpec, bind_getModel]
  by_cases hb : sigabrt_blocked (m_sigmask m) = true
  · simp only [ite_eq_left hb]
    apply bind_step
    · exact modify_ok with_sigabrt_pending i m
    · signal_ret_leaf
  · simp only [ite_eq_right hb]
    apply bind_step
    · exact modify_ok (with_killed (BitVec.ofInt 64 SIGABRT)) i m
    · signal_ret_leaf

def tkill_self_witness (pid sig : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(m_abort_terminal m) then .unmodeled
  else
    match m_tid m with
    | none => .unmodeled
    | some t =>
        if !(pid == t) then .unmodeled
        else if !(tkill_sig_valid sig) then ret_outcome (errno_ret EINVAL) m
        else if sig == BitVec.ofInt 64 SIGABRT then send_sigabrt_witness m
        else .unmodeled

theorem tkill_self_witness_ok (pid sig : word) (i : SyscallInput) (m : Model) :
    tkill_self pid sig i m (tkill_self_witness pid sig m) := by
  unfold tkill_self tkill_self_witness
  simp only [getModelSpec, bind_getModel]
  by_cases hterm : (!(m_abort_terminal m)) = true
  · simp only [ite_eq_left hterm]
    exact unmodeled_intro i m
  · simp only [ite_eq_right hterm]
    cases htid : m_tid m with
    | none =>
      exact unmodeled_intro i m
    | some t =>
      by_cases hpid : (!(pid == t)) = true
      · simp only [ite_eq_left hpid]
        exact unmodeled_intro i m
      · simp only [ite_eq_right hpid]
        by_cases hsig : (!(tkill_sig_valid sig)) = true
        · simp only [ite_eq_left hsig]
          signal_ret_leaf
        · simp only [ite_eq_right hsig]
          by_cases habrt : (sig == BitVec.ofInt 64 SIGABRT) = true
          · simp only [ite_eq_left habrt]
            exact send_sigabrt_witness_ok i m
          · simp only [ite_eq_right habrt]
            exact unmodeled_intro i m

def tkill_witness (pid sig : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(m_abort_terminal m) then .unmodeled
  else if !(pid_positive pid) then ret_outcome (errno_ret EINVAL) m
  else tkill_self_witness pid sig m

theorem tkill_witness_ok (pid sig : word) (i : SyscallInput) (m : Model) :
    tkill_spec pid sig i m (tkill_witness pid sig m) := by
  unfold tkill_spec tkill_witness
  simp only [getModelSpec, bind_getModel]
  by_cases hterm : (!(m_abort_terminal m)) = true
  · simp only [ite_eq_left hterm]
    exact unmodeled_intro i m
  · simp only [ite_eq_right hterm]
    by_cases hpos : (!(pid_positive pid)) = true
    · simp only [ite_eq_left hpos]
      signal_ret_leaf
    · simp only [ite_eq_right hpos]
      exact tkill_self_witness_ok pid sig i m

def tgkill_witness (tgid pid sig : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(m_abort_terminal m) then .unmodeled
  else if !(pid_positive pid && pid_positive tgid)
  then ret_outcome (errno_ret EINVAL) m
  else
    match m_tid m with
    | none => .unmodeled
    | some t =>
        if !(pid == t) then .unmodeled
        else if !(tgid == t) then ret_outcome (errno_ret ESRCH) m
        else tkill_self_witness pid sig m

theorem tgkill_witness_ok (tgid pid sig : word) (i : SyscallInput) (m : Model) :
    tgkill_spec tgid pid sig i m (tgkill_witness tgid pid sig m) := by
  unfold tgkill_spec tgkill_witness
  simp only [getModelSpec, bind_getModel]
  by_cases hterm : (!(m_abort_terminal m)) = true
  · simp only [ite_eq_left hterm]
    exact unmodeled_intro i m
  · simp only [ite_eq_right hterm]
    by_cases hpos : (!(pid_positive pid && pid_positive tgid)) = true
    · simp only [ite_eq_left hpos]
      signal_ret_leaf
    · simp only [ite_eq_right hpos]
      cases htid : m_tid m with
      | none =>
        exact unmodeled_intro i m
      | some t =>
        by_cases hpid : (!(pid == t)) = true
        · simp only [ite_eq_left hpid]
          exact unmodeled_intro i m
        · simp only [ite_eq_right hpid]
          by_cases htg : (!(tgid == t)) = true
          · simp only [ite_eq_left htg]
            signal_ret_leaf
          · simp only [ite_eq_right htg]
            exact tkill_self_witness_ok pid sig i m

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the two
    computable shapes the prose names: a non-NULL `uoss` makes the
    sigaltstack witness the fail-closed `Unmodeled`, and the blocked
    SIGABRT witness leaves the pending bit rather than killing. -/

/-- A non-NULL `uoss` — with no stack installed — is a declined shape, and
    the witness says so. -/
example (uss uoss : word) (i : SyscallInput) (m : Model)
    (h : m_sigaltstack_installed m = false) (ho : (!(w_is0 uoss)) = true) :
    sigaltstack_witness uss uoss i m = .unmodeled := by
  rw [sigaltstack_witness, ite_eq_right (by rw [h]; simp), ite_eq_left ho]

/-- A declared, unblocked abort kills; a blocked one only sets the bit. -/
example (m : Model) (h : sigabrt_blocked (m_sigmask m) = true) :
    send_sigabrt_witness m
      = ret_outcome (BitVec.ofInt 64 0) (with_sigabrt_pending m) := by
  rw [send_sigabrt_witness, ite_eq_left h]

example (m : Model) (h : sigabrt_blocked (m_sigmask m) = false) :
    send_sigabrt_witness m
      = ret_outcome (BitVec.ofInt 64 0) (with_killed (BitVec.ofInt 64 SIGABRT) m) := by
  rw [send_sigabrt_witness, ite_eq_right (by rw [h]; simp)]

/-- With the declaration off, every witness on the abort path declines. -/
example (pid sig : word) (m : Model) (h : (!(m_abort_terminal m)) = true) :
    tkill_witness pid sig m = .unmodeled ∧ tgkill_witness 0 pid sig m = .unmodeled := by
  constructor
  · rw [tkill_witness, ite_eq_left h]
  · rw [tgkill_witness, ite_eq_left h]

end LinuxSem.Checks.Witness.Kernel.Signal
