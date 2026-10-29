/-
  * LinuxProcessSem.Checks.Witness.Kernel.Fork — the set_tid_address (96), clone (220) and clone3 (435) witnesses, and their proofs

  Answers to Linux [kernel/fork.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` / `ret_only` come from
  `Checks.Witness.Prelude` and `Sys.Syscall`.

  A proof steps the spec's leading `get_model` with `bind_getModel` in one
  rewrite, and then builds the continuation with `bind_step`
  (`Checks.Witness.Prelude`) — which accepts either outcome shape and
  requires the first component to emit nothing, which every reader and
  state write does.  Each proof `generalize`s its conclusion into a local
  `Q : Prop` before any case split, because `clone_spec`/`clone3_spec`
  place their branch test in front of a whole subtree — an `if` at
  FUNCTION type — and `by_cases` would otherwise try to reduce it.  The
  branch tests are the same equations the checker file splits on, so a
  drift between the two files' branch order shows up as a proof failure in
  one of them.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork

namespace LinuxSem.Checks.Witness.Kernel.Fork

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks.Witness.Prelude

/-! ## set_tid_address (96) -/

/-- The recorded tid when there is one, and otherwise the smallest value
    the spec's envelope admits — 1.  The argument is ignored, as it is in
    the spec and in the kernel. -/
def set_tid_address_witness (m : Model) : Outcome SyscallEffect Model event :=
  match m_tid m with
  | some tid => ret_outcome tid m
  | none => ret_outcome (BitVec.ofInt 64 1) (with_tid (BitVec.ofInt 64 1) m)

theorem set_tid_address_witness_ok (i : SyscallInput) (m : Model) :
    set_tid_address_spec i m (set_tid_address_witness m) := by
  generalize hP : (set_tid_address_spec i m (set_tid_address_witness m)) = Q at *
  cases htid : m_tid m with
  | some tid =>
    rw [← hP]
    simp only [set_tid_address_spec, getModelSpec, bind_getModel, htid,
      set_tid_address_witness, ret_only, ret_outcome,
      LinuxSem.LinuxProcessSem.pure]
  | none =>
    rw [← hP]
    simp only [set_tid_address_spec, getModelSpec, bind_getModel, htid,
      set_tid_address_witness]
    refine bind_step (choose _) _ i m (BitVec.ofInt 64 1) m _ ?_ ?_
    · refine choose_ok _ (BitVec.ofInt 64 1) i m ?_
      decide
    · refine bind_step (modify (with_tid (BitVec.ofInt 64 1)))
        (fun _ => ret_only (BitVec.ofInt 64 1)) i m ()
        (with_tid (BitVec.ofInt 64 1) m) _ (modify_ok _ _ _) ?_
      exact pure_ok _ _ _

/-! ## clone / clone3 -/

/- clone / clone3 witness: the -EAGAIN arm, whose choice is a member of
   a list literal rather than a value to construct, and which leaves
   the model alone — so it is available whenever the argument gates let
   the call through.  The pid arm would have to invent an id inside an
   envelope, and is never needed to show the spec is receptive. -/
def clone_resolve_witness (m : Model) : Outcome SyscallEffect Model event :=
  if !(clone_no_shared_file_b (m_fds m)) then .unmodeled
  else ret_outcome (errno_ret EAGAIN) m

theorem clone_resolve_witness_ok (i : SyscallInput) (m : Model) :
    clone_resolve i m (clone_resolve_witness m) := by
  generalize hP : (clone_resolve i m (clone_resolve_witness m)) = Q at *
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [← hP]
    simp only [clone_resolve, getModelSpec, bind_getModel, clone_resolve_witness, ite_eq_left hg,
      unmodeled]
  · rw [← hP]
    simp only [clone_resolve, getModelSpec, bind_getModel, clone_resolve_witness, ite_eq_right hg]
    refine alt_l _ _ _ _ _ ?_
    refine bind_step (errno_from clone_errnos) _ i m EAGAIN m _ ?_ ?_
    · exact choose_ok (fun e => e ∈ clone_errnos) EAGAIN i m (by simp [clone_errnos])
    · simp only [err_ret, ret_only, ret_outcome, LinuxSem.LinuxProcessSem.pure]

def clone_witness (flags : word) (m : Model) : Outcome SyscallEffect Model event :=
  if clone_fork_flags_b flags then clone_resolve_witness m else .unmodeled

theorem clone_witness_ok (flags : word) (i : SyscallInput) (m : Model) :
    clone_spec flags i m (clone_witness flags m) := by
  generalize hP : (clone_spec flags i m (clone_witness flags m)) = Q at *
  by_cases hf : clone_fork_flags_b flags = true
  · rw [← hP]
    simp only [clone_spec, clone_witness, ite_eq_left hf]
    exact clone_resolve_witness_ok i m
  · rw [← hP]
    simp only [clone_spec, clone_witness, ite_eq_right hf, unmodeled]

/-- The same witness, carrying the copy-in ledger the [clone3] resolution
    records.  [clone_resolve_witness] answers with [mkEffect], whose
    [eff_copyins] is [], so [record_copyins_ok_empty] applies directly. -/
def clone3_resolve_witness (uargs : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(clone_no_shared_file_b (m_fds m)) then .unmodeled
  else .ok (with_copyins [(uargs, CLONE_ARGS_SIZE_nat)]
             (mkEffect (errno_ret EAGAIN) [] [])) m []

theorem clone3_resolve_witness_ok (i : SyscallInput) (uargs : word) (m : Model) :
    clone3_resolve uargs i m (clone3_resolve_witness uargs m) := by
  generalize hP : (clone3_resolve uargs i m (clone3_resolve_witness uargs m)) = Q at *
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [← hP]
    simp only [clone3_resolve, clone3_resolve_witness, ite_eq_left hg]
    refine record_copyins_unmodeled ?_
    simp only [clone_resolve, getModelSpec, bind_getModel, ite_eq_left hg, unmodeled]
  · rw [← hP]
    simp only [clone3_resolve, clone3_resolve_witness, ite_eq_right hg]
    refine record_copyins_ok_empty (reads := [(uargs, CLONE_ARGS_SIZE_nat)]) rfl ?_
    have h := clone_resolve_witness_ok i m
    simp only [clone_resolve_witness, ite_eq_right hg, ret_outcome] at h
    exact h

def clone3_witness (i : SyscallInput) (uargs size : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE)) then .unmodeled
  else match read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
       | none => .unmodeled                     -- unreadable clone_args
       | some bs =>
           if clone3_fork_args_b bs then clone3_resolve_witness uargs m
           else .unmodeled

theorem clone3_witness_ok (i : SyscallInput) (uargs size : word) (m : Model) :
    clone3_spec uargs size i m (clone3_witness i uargs size m) := by
  generalize hP : (clone3_spec uargs size i m (clone3_witness i uargs size m)) = Q at *
  by_cases hsz : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [← hP]
    simp only [clone3_spec, clone3_witness, ite_eq_left hsz, unmodeled]
  · rw [← hP]
    simp only [clone3_spec, ite_eq_right hsz]
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    simp only [clone3_witness, ite_eq_right hsz]
    cases hbs : read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
    | none =>
      simp only [unmodeled]
    | some bs =>
      by_cases ha : clone3_fork_args_b bs = true
      · simp only [ite_eq_left ha]
        exact clone3_resolve_witness_ok i uargs m
      · simp only [ite_eq_right ha, unmodeled]

/-! ## Sanity checks (not library lemmas)

    These are this module's own checks — the library proofs state none
    here — and they pin the two computable witnesses.  `set_tid_address_witness` records 1 on the first call and
    answers the recorded tid on every later one, and
    `clone_resolve_witness` answers -EAGAIN — a member of
    `Fork.clone_errnos` — with the model untouched. -/

/-- The first `set_tid_address` witness returns 1 and RECORDS it — the
    state the outcome carries is the model with `m_tid = some 1`. -/
example (m : Model) (h : m_tid m = none) :
    set_tid_address_witness m = ret_outcome (BitVec.ofInt 64 1)
      (with_tid (BitVec.ofInt 64 1) m) := by
  simp only [set_tid_address_witness, h]

/-- …and the recorded tid is what it returns on every later call. -/
example (m : Model) (tid : word) (h : m_tid m = some tid) :
    set_tid_address_witness m = ret_outcome tid m := by
  simp only [set_tid_address_witness, h]

/-- -EAGAIN is one of `Fork.clone_errnos`, so the witness's choice is
    inside the spec's injectable set. -/
example : EAGAIN ∈ clone_errnos := by simp [clone_errnos]

end LinuxSem.Checks.Witness.Kernel.Fork
