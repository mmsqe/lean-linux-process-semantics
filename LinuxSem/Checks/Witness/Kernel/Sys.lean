/-
  * LinuxProcessSem.Checks.Witness.Kernel.Sys — the getpid (172), gettid (178), setsid (157),
    uname (160), prlimit64 (261), prctl (167), the id readers and the id
    setters' witnesses, and their proofs

  Answers to Linux [kernel/sys.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` / `ret_only` come from
  `Checks.Witness.Prelude` and `Sys.Syscall`.  The `Z` tests are the `Int`
  equality and comparison themselves (the same decision, with the `Bool`
  unboxed), as in `Sys/Kernel/Sys.lean`.  An `mkEffectU r [] [] [] [] []`
  literal is written as the anonymous constructor
  `⟨r, [], [], [], [], []⟩`.

  A witness's proof has the spec's own body as its goal, so the `if`-chains
  are `if`s at FUNCTION type and the same `generalize` device the checker
  file documents is used: the conclusion is abstracted into a local
  `Q : Prop` before any split, and `rw [← hP]` restores it at each leaf.
  The two `let`-bound bands of `setresid_spec` (the `pick`ed ids and their
  `is_old` tests) are `generalize`d into named words, so one `by_cases`
  serves the spec and the witness at once.

  `utsname_default_wf` decides `utsname_wf` over a 390-byte literal list,
  which outruns the default recursion depth; raising `maxRecDepth` supplies
  the fuel.  It is not a proof principle, and the term it is spent on is
  closed — the same note `Checks/Witness/Fs/Stat.lean` carries.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.Checks.Witness.Kernel.Fork
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sys

namespace LinuxSem.Checks.Witness.Kernel.Sys

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks.Witness.Prelude
open LinuxSem.Checks.Witness.Kernel.Fork

/-! ## getpid (172) and gettid (178) -/

/-- getpid witness: the same witness as set_tid_address's, because
    [Kernel.Sys.getpid_spec] is the same relation. -/
def getpid_witness : Model → Outcome SyscallEffect Model event :=
  set_tid_address_witness

theorem getpid_witness_ok (i : SyscallInput) (m : Model) :
    getpid_spec i m (getpid_witness m) :=
  set_tid_address_witness_ok i m

/-- gettid witness: the same witness again, because
    [Kernel.Sys.gettid_spec] is the same relation. -/
def gettid_witness : Model → Outcome SyscallEffect Model event :=
  set_tid_address_witness

theorem gettid_witness_ok (i : SyscallInput) (m : Model) :
    gettid_spec i m (gettid_witness m) :=
  set_tid_address_witness_ok i m

/-! ## setsid (157) -/

/-- setsid witness: -EPERM, which is admissible whatever the model
    believes — it is the only answer once a setsid has succeeded, and
    [Kernel.Sys.setsid_spec]'s untracked-environment arm before that.  It
    also leaves the model alone, which is why this witness needs no
    case split. -/
def setsid_witness (m : Model) : Outcome SyscallEffect Model event :=
  ret_outcome (errno_ret EPERM) m

theorem setsid_witness_ok (i : SyscallInput) (m : Model) :
    setsid_spec i m (setsid_witness m) := by
  generalize hP : (setsid_spec i m (setsid_witness m)) = Q at *
  cases hs : m_setsid_succeeded m with
  | true =>
    rw [← hP]
    simp [hs, setsid_spec, getModelSpec, bind_getModel, setsid_witness, ret_outcome, err_ret,
      ret_only, LinuxSem.LinuxProcessSem.pure]
  | false =>
    rw [← hP]
    simp only [setsid_spec, getModelSpec, bind_getModel, setsid_witness, hs,
      Bool.false_eq_true, ite_false]
    exact alt_l _ _ _ _ _ (by
      simp [ret_outcome, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])

/-! ## uname (160) -/

/-- One utsname inside [Kernel.Sys.utsname_wf]'s envelope: the two
    members the kernel source pins, and NUL for the four it does not.
    That is a name a real kernel can hold — [sethostname(name, 0)] and
    [setdomainname(name, 0)] each clear their member outright — but the
    witness does not need it to be: it exhibits ONE admissible outcome so
    that progress has something to step to, exactly as [rlim64_zero] does
    for the limit pair. -/
def utsname_default : List byte :=
  uts_literal uts_sysname_chars
  ++ uts_literal [] ++ uts_literal [] ++ uts_literal []
  ++ uts_literal uts_machine_chars
  ++ uts_literal []

set_option maxRecDepth 16000 in
theorem utsname_default_wf : utsname_wf utsname_default = true := by decide

/-- uname's witness: -EFAULT when the range fails [access_ok], the
    decline when memory does not wholly back a range it admits, and
    otherwise the pinned name — or, on the first call, [utsname_default],
    which then becomes the pin. -/
def uname_witness (name : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(access_okb name NEW_UTSNAME_SIZE)
  then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none => .unmodeled
    | some _ =>
        match m_utsname m with
        | some bs => .ok (mkEffect (BitVec.ofInt 64 0) [(name, bs)] []) m []
        | none =>
            .ok (mkEffect (BitVec.ofInt 64 0) [(name, utsname_default)] [])
              (with_utsname utsname_default m) []

theorem uname_witness_ok (name : word) (i : SyscallInput) (m : Model) :
    uname_spec name i m (uname_witness name i m) := by
  generalize hP : (uname_spec name i m (uname_witness name i m)) = Q at *
  rw [← hP]
  simp only [uname_spec]
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  simp only [getModelSpec]
  refine bind_step getModel _ i m m m _ (getModel_ok i m) ?_
  simp only [uname_witness]
  by_cases ho : (!(access_okb name NEW_UTSNAME_SIZE)) = true
  · simp only [ite_eq_left ho, err_ret, ret_only, ret_outcome,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right ho]
    cases hw : read_bytes_map i.in_wmem name (BitVec.ofInt 64 NEW_UTSNAME_SIZE) with
    | none =>
      dsimp only
      exact unmodeled_intro i m
    | some bs1 =>
      dsimp only
      cases hm : m_utsname m with
      | some bs =>
        dsimp only
        exact pure_ok _ i m
      | none =>
        dsimp only
        simp only [LinuxSem.LinuxProcessSem.bind]
        refine ⟨utsname_default, m, [], [], choose_ok _ utsname_default i m ?_, ?_, rfl⟩
        · exact utsname_default_wf
        · simp only [set_utsname, modifySpec, LinuxSem.LinuxProcessSem.modify,
            LinuxSem.LinuxProcessSem.pure]
          exact ⟨(), with_utsname utsname_default m, [], [], rfl, rfl, rfl⟩

/-! ## prlimit64 (261) -/

/-- The zero limit pair: soft 0, hard 0, sixteen little-endian zero bytes.
    [rlim64_wf] holds of it because `0 <= 0`. -/
def rlim64_zero : List byte := List.replicate 16 (BitVec.ofInt 8 0)

theorem rlim64_zero_wf : rlim64_wf rlim64_zero = true := by decide

/-- prlimit64's witness: the decline on every argument the spec declines,
    -EFAULT where the pointer is refused, the pinned pair on a read, the
    zero pair (which becomes the pin) on a first read, and on a write the
    -EINVAL, the decline, or the recorded pair installed. -/
def prlimit64_witness (pid resource new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !(w_is0 pid) then .unmodeled
  else if (resource.toNat : Int) ≠ RLIMIT_CORE then .unmodeled
  else if (w_is0 new_rlim && w_is0 old_rlim) then .unmodeled
  else if (!(w_is0 new_rlim) && !(w_is0 old_rlim)) then .unmodeled
  else if w_is0 new_rlim then
    match read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
    | none =>
        if !(access_okb old_rlim 16) then ret_outcome (errno_ret EFAULT) m
        else .unmodeled
    | some _ =>
        match m_rlimit_core m with
        | some bs => .ok (mkEffect (BitVec.ofInt 64 0) [(old_rlim, bs)] []) m []
        | none =>
            .ok (mkEffect (BitVec.ofInt 64 0) [(old_rlim, rlim64_zero)] [])
              (with_rlimit_core rlim64_zero m) []
  else
    match m_rlimit_core m with
    | none => .unmodeled
    | some bs0 =>
        match read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
        | none =>
            if !(access_okb new_rlim 16) then ret_outcome (errno_ret EFAULT) m
            else .unmodeled
        | some nb =>
            outcome_copyins [(new_rlim, 16)]
              (if (rlim64_hard nb).toNat < (rlim64_soft nb).toNat then
                 ret_outcome (errno_ret EINVAL) m
               else if !(bv_eqb (rlim64_hard nb) (rlim64_hard bs0)) then .unmodeled
               else ret_outcome (BitVec.ofInt 64 0) (with_rlimit_core nb m))

theorem prlimit64_witness_ok (pid resource new_rlim old_rlim : word)
    (i : SyscallInput) (m : Model) :
    prlimit64_spec pid resource new_rlim old_rlim i m
      (prlimit64_witness pid resource new_rlim old_rlim i m) := by
  generalize hP : (prlimit64_spec pid resource new_rlim old_rlim i m
    (prlimit64_witness pid resource new_rlim old_rlim i m)) = Q at *
  rw [← hP]
  simp only [prlimit64_spec, prlimit64_witness]
  by_cases h1 : (!(w_is0 pid)) = true
  · simp only [ite_eq_left h1]
    exact unmodeled_intro i m
  · simp only [ite_eq_right h1]
    by_cases h2 : (resource.toNat : Int) ≠ RLIMIT_CORE
    · simp only [ite_eq_left h2]
      exact unmodeled_intro i m
    · simp only [ite_eq_right h2]
      by_cases h3 : (w_is0 new_rlim && w_is0 old_rlim) = true
      · simp only [ite_eq_left h3]
        exact unmodeled_intro i m
      · simp only [ite_eq_right h3]
        by_cases h4 : (!(w_is0 new_rlim) && !(w_is0 old_rlim)) = true
        · simp only [ite_eq_left h4]
          exact unmodeled_intro i m
        · simp only [ite_eq_right h4]
          refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
          simp only [getModelSpec]
          refine bind_step getModel _ i m m m _ (getModel_ok i m) ?_
          by_cases hn : w_is0 new_rlim = true
          · simp only [ite_eq_left hn]
            cases hw : read_bytes_map i.in_wmem old_rlim (BitVec.ofInt 64 16) with
            | none =>
              dsimp only
              by_cases ha : (!(access_okb old_rlim 16)) = true
              · simp only [ite_eq_left ha]
                exact pure_ok _ i m
              · simp only [ite_eq_right ha]
                exact unmodeled_intro i m
            | some bs1 =>
              dsimp only
              cases hm : m_rlimit_core m with
              | some bs =>
                dsimp only
                exact pure_ok _ i m
              | none =>
                dsimp only
                simp only [LinuxSem.LinuxProcessSem.bind]
                refine ⟨rlim64_zero, m, [], [], choose_ok _ rlim64_zero i m ?_, ?_, rfl⟩
                · exact rlim64_zero_wf
                · simp only [set_rlimit_core, modifySpec,
                    LinuxSem.LinuxProcessSem.modify,
                    LinuxSem.LinuxProcessSem.pure]
                  exact ⟨(), with_rlimit_core rlim64_zero m, [], [], rfl, rfl, rfl⟩
          · simp only [ite_eq_right hn]
            cases hm : m_rlimit_core m with
            | none =>
              dsimp only
              exact unmodeled_intro i m
            | some bs0 =>
              dsimp only
              cases hw : read_bytes_map i.in_mem new_rlim (BitVec.ofInt 64 16) with
              | none =>
                dsimp only
                by_cases ha : (!(access_okb new_rlim 16)) = true
                · simp only [ite_eq_left ha]
                  exact pure_ok _ i m
                · simp only [ite_eq_right ha]
                  exact unmodeled_intro i m
              | some nb =>
                dsimp only
                apply record_copyins_outcome
                by_cases hi : (rlim64_hard nb).toNat < (rlim64_soft nb).toNat
                · simp only [ite_eq_left hi]
                  exact pure_ok _ i m
                · simp only [ite_eq_right hi]
                  by_cases hh : (!(bv_eqb (rlim64_hard nb) (rlim64_hard bs0))) = true
                  · simp only [ite_eq_left hh]
                    exact unmodeled_intro i m
                  · simp only [ite_eq_right hh]
                    simp only [LinuxSem.LinuxProcessSem.bind]
                    refine ⟨(), with_rlimit_core nb m, [], [], ?_, ?_, rfl⟩
                    · rfl
                    · exact pure_ok _ i (with_rlimit_core nb m)

/-! ## The credentials -/

/-- -ENOMEM is in every setter's injectable set: [prepare_creds] is
    reached on all of them. -/
theorem In_ENOMEM_setid_errnos (b : Bool) : ENOMEM ∈ setid_errnos b := by
  cases b <;> simp [setid_errnos]

/-- The readers are total: the stored id, and no model step. -/
def getid_witness (sel : Creds → word) (m : Model) : Outcome SyscallEffect Model event :=
  ret_outcome (sel (m_creds m)) m

theorem getid_witness_ok (sel : Creds → word) (i : SyscallInput) (m : Model) :
    getid_spec sel i m (getid_witness sel m) := by
  generalize hP : (getid_spec sel i m (getid_witness sel m)) = Q at *
  rw [← hP]
  simp only [getid_spec, getModelSpec, bind_getModel, getid_witness, ret_outcome, ret_only,
    LinuxSem.LinuxProcessSem.pure]

/-- [setuid]/[setgid]: -EINVAL for [(uid_t)-1], and otherwise the
    -ENOMEM every other branch admits — [prepare_creds] can fail on all
    three of them, so one witness covers the whole spec without deciding
    which branch the credentials take. -/
def setid_witness (v : word) (m : Model) : Outcome SyscallEffect Model event :=
  if bv_eqb v ID_MINUS_ONE then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (errno_ret ENOMEM) m

theorem setid_witness_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (v : word) (i : SyscallInput) (m : Model) :
    setid_spec get put user v i m (setid_witness v m) := by
  generalize hP : (setid_spec get put user v i m (setid_witness v m)) = Q at *
  rw [← hP]
  simp only [setid_spec, getModelSpec, bind_getModel, setid_witness]
  by_cases h1 : bv_eqb v ID_MINUS_ONE = true
  · simp only [ite_eq_left h1]
    exact pure_ok _ i m
  · simp only [ite_eq_right h1]
    by_cases h2 : creds_privileged (m_creds m) = true
    · simp only [ite_eq_left h2]
      refine alt_l _ _ _ _ _ ?_
      simp only [errno_from, LinuxSem.LinuxProcessSem.bind]
      refine ⟨ENOMEM, m, [], [], choose_ok _ ENOMEM i m (In_ENOMEM_setid_errnos _), ?_, rfl⟩
      exact pure_ok _ i m
    · simp only [ite_eq_right h2]
      by_cases h3 : (bv_eqb v (get (m_creds m)).id_real ||
          bv_eqb v (get (m_creds m)).id_saved) = true
      · simp only [ite_eq_left h3]
        refine alt_l _ _ _ _ _ ?_
        simp only [errno_from, LinuxSem.LinuxProcessSem.bind]
        refine ⟨ENOMEM, m, [], [], choose_ok _ ENOMEM i m (In_ENOMEM_setid_errnos _), ?_, rfl⟩
        exact pure_ok _ i m
      · simp only [ite_eq_right h3]
        refine alt_l _ _ _ _ _ ?_
        simp only [errno_from, LinuxSem.LinuxProcessSem.bind]
        refine ⟨ENOMEM, m, [], [], choose_ok _ ENOMEM i m (In_ENOMEM_setid_errnos _), ?_, rfl⟩
        exact pure_ok _ i m

/-- [setresuid]/[setresgid]: the no-op fast path and the -EPERM refusal
    are both total, and every remaining branch admits -ENOMEM, so the
    witness has to follow the spec's first two tests and can stop
    there. -/
def setresid_witness (get : Creds → IdTriple) (r e s : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  let t := get (m_creds m)
  let pick (a : word) (cur : word) := if bv_eqb a ID_MINUS_ONE then cur else a
  let nr := pick r t.id_real
  let ne := pick e t.id_eff
  let ns := pick s t.id_saved
  if bv_eqb nr t.id_real && bv_eqb ne t.id_eff && bv_eqb ns t.id_saved then
    ret_outcome (BitVec.ofInt 64 0) m
  else
    let is_old (x : word) :=
      bv_eqb x t.id_real || bv_eqb x t.id_eff || bv_eqb x t.id_saved
    if !(is_old nr && is_old ne && is_old ns) && !(creds_privileged (m_creds m)) then
      ret_outcome (errno_ret EPERM) m
    else
      ret_outcome (errno_ret ENOMEM) m

theorem setresid_witness_ok (get : Creds → IdTriple) (put : IdTriple → Creds → Creds)
    (user : Bool) (r e s : word) (i : SyscallInput) (m : Model) :
    setresid_spec get put user r e s i m (setresid_witness get r e s m) := by
  generalize hP : (setresid_spec get put user r e s i m (setresid_witness get r e s m)) = Q at *
  rw [← hP]
  simp only [setresid_spec, getModelSpec, bind_getModel, setresid_witness]
  by_cases h1 : (bv_eqb (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) (get (m_creds m)).id_real && bv_eqb (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) (get (m_creds m)).id_eff && bv_eqb (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) (get (m_creds m)).id_saved) = true
  · simp only [ite_eq_left h1]
    exact pure_ok _ i m
  · simp only [ite_eq_right h1]
    by_cases h2 : (!((bv_eqb (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) (get (m_creds m)).id_real || bv_eqb (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) (get (m_creds m)).id_eff || bv_eqb (if bv_eqb r ID_MINUS_ONE then (get (m_creds m)).id_real else r) (get (m_creds m)).id_saved) &&
        (bv_eqb (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) (get (m_creds m)).id_real || bv_eqb (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) (get (m_creds m)).id_eff || bv_eqb (if bv_eqb e ID_MINUS_ONE then (get (m_creds m)).id_eff else e) (get (m_creds m)).id_saved) &&
        (bv_eqb (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) (get (m_creds m)).id_real || bv_eqb (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) (get (m_creds m)).id_eff || bv_eqb (if bv_eqb s ID_MINUS_ONE then (get (m_creds m)).id_saved else s) (get (m_creds m)).id_saved)) && !(creds_privileged (m_creds m))) = true
    · simp only [ite_eq_left h2]
      exact pure_ok _ i m
    · simp only [ite_eq_right h2]
      refine alt_l _ _ _ _ _ ?_
      simp only [errno_from, LinuxSem.LinuxProcessSem.bind]
      refine ⟨ENOMEM, m, [], [], choose_ok _ ENOMEM i m (In_ENOMEM_setid_errnos _), ?_, rfl⟩
      exact pure_ok _ i m

/-! ## prctl (167) -/

/-- prctl witness: the arm's own answer, which is deterministic.
    [Kernel.Sys.prctl_spec] has no [alt] and no [choose] -- an option
    outside [prctl_modeled_options] declines, and [PR_CAPBSET_READ]
    answers -EINVAL or 1 by a test on [arg2] alone -- so the witness is
    the spec with the monad erased. -/
def prctl_witness (option_ arg2 : word) (m : Model) : Outcome SyscallEffect Model event :=
  if (option_.toNat : Int) ≠ PR_CAPBSET_READ then .unmodeled
  else if CAP_LAST_CAP < (arg2.toNat : Int)
  then ret_outcome (errno_ret EINVAL) m
  else ret_outcome (BitVec.ofInt 64 1) m

theorem prctl_witness_ok (option_ arg2 : word) (i : SyscallInput) (m : Model) :
    prctl_spec option_ arg2 i m (prctl_witness option_ arg2 m) := by
  generalize hP : (prctl_spec option_ arg2 i m (prctl_witness option_ arg2 m)) = Q at *
  rw [← hP]
  simp only [prctl_spec, prctl_witness]
  by_cases ho : (option_.toNat : Int) ≠ PR_CAPBSET_READ
  · simp only [ite_eq_left ho]
    exact unmodeled_intro i m
  · simp only [ite_eq_right ho]
    by_cases hc : CAP_LAST_CAP < (arg2.toNat : Int)
    · simp only [ite_eq_left hc]
      exact pure_ok _ i m
    · simp only [ite_eq_right hc]
      exact pure_ok _ i m

end LinuxSem.Checks.Witness.Kernel.Sys
