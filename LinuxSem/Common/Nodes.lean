/-
  * Common.Nodes — generic syscall nodes for the shape algebra, via the verified
    checker.

  Image-INDEPENDENT.  Every syscall boundary a per-binary proof crosses is a
  [ShapeAlg.node_ok] fact.  This file derives such facts ONCE from the
  verified executable acceptor [Checks.ExecutableSpecs.check_syscall]
  (sound and complete for [Specs.syscall_spec]):

  - [node_det]       : the checker admits exactly one (effect, model,
                       events) triple, into a non-halted model;
  - [node_ret_only]  : the special case "return value only" — covers
                       errno returns, zero-byte reads, close, ioctl ...;
  - [node_ret_only_copyins] : the same with a recorded copy-from-user
                       ledger ([with_copyins], e.g. openat's pathname);
  - [rz_exit_chk]    : the exit leaf (re-export of [ShapeAlg.rz_exit]);
  - [node_open]      : the openat node whose checker reduces to
                       [check_open_result_copyins] (errno alternatives +
                       the lowest-free-fd success), indexed by `Int + unit`;
  - [node_chk]       : an [I]-indexed silent node described by the
                       checker's exact answer family.

  Per-binary proofs reduce `check_syscall (sys_input segs ms x8) eff model`
  to one of these shapes by rewriting with their register/memory facts
  (see the `*_check` lemmas in `FileSim`, `MmapSim`, `CatSim`).

  Notes:
  - the nodes use the fault-free [realizes] only;
  - [sstep_svc_inv] has a third `CheckOk` arm for
    `Run.sstep_syscall_materialization_fault` and the successor model is
    the MATERIALIZED one ([materialize_model_accesses]); every node
    therefore takes an extra `m_vm_lazy m' = []` hypothesis on its
    post-model(s) (always true for our binaries: no MAP_NORESERVE), under
    which materialization is the identity
    ([State.materialize_model_accesses_no_lazy]);
  - [node_open]/[rz_open] are stated against FileSim's
    [check_open_result_copyins reads] (openat records the pathname
    bytes it read in `eff_copyins`); the successor MACHINE state is
    unchanged ([apply_effect_copyins_no_write]).

  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `bv_and` → `&&&`, `Z_to_bv 64 n` →
    `BitVec.ofInt 64 n`, `None`/`Some` → `none`/`some`, `<>` → `≠`,
    `~` → `¬`, record field projections `m_fs m` → `m_fs m` (Lean
    structure projections).
  - `halt_ev` is total: matches on `m_killed m'`, and Lean's
    `match` on `Option` keeps the same two branches.
  - Everything is proved here; there is no proof hole, `admit`, extra postulate or
    `unsafe`, and no declaration is deferred.
-/
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.FileSim
import LinuxSem.Common.ShapeAlg
import LinuxSem.Checks.ExecutableSpecs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace LinuxSem.Common.Nodes

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.FileSim
open LinuxSem.Common.ShapeAlg

/-- The FP state at process entry.  The `FileSim` open-result lemmas carry an
    `[FPState]` parameter that their statements do not mention (it is
    auto-bound from their proofs), so the nodes here fix it once, exactly as
    `ShapeAlg.lean` does for the same lemmas. -/
local instance nodes_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   The pending-syscall inversion
   ========================================================================= -/

/-- The event a HALTING step appends: an exit's `ExitEv`, or — when the
    post-model is killed — the `KillEv` of `Run.sstep_killed`.
    `Run.sstep_exit` carries `m_killed model' = none`, `sstep_killed`
    `m_killed model' = some sig`, and a killed model is halted
    ([State.m_killed_of_m_halted_none]), so the third arm below covers both
    steps with one `m_halted model' = some code` witness; every caller
    refutes that arm from its own "no outcome halts" fact and never looks at
    the event. -/
def halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | some sig => .KillEv sig (m_fs m')
  | none => .ExitEv code (m_fs m')

/-- Inversion of one transition at a pending syscall, phrased through the
    checker.  Three `CheckOk` sub-cases: the ordinary step (into the
    MATERIALIZED post-model), the materialization fault, the exit. -/
theorem sstep_svc_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (e : List event) (st : step_to)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hss : sstep segs (mkCfg ms model) e st) :
    (∃ eff model' evs,
        check_syscall (sys_input segs ms x8) eff model = .CheckOk model' evs ∧
        (((∃ model'', m_halted model' = none ∧ e = evs ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' ∧
            st = .SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          ∨ (m_halted model' = none ∧ e = [] ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = none ∧
            st = .SError)
          ∨ (∃ code, m_halted model' = some code ∧ e = evs ++ [halt_ev model' code] ∧
            st = .SNext (mkCfg ms model')))))
    ∨ (∃ eff, check_syscall (sys_input segs ms x8) eff model = .CheckUnmodeled ∧
        e = [] ∧ st = .SError) := by
  cases Hss with
  | instr a b c d p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_fault a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_unmodeled a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | syscall a b c d mp mpp evs1 p8 p9 hspec p11 hmat =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      exact Or.inl ⟨d, mp, e, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inl ⟨mpp, p11, rfl, hmat, rfl⟩⟩
  | syscall_materialization_fault a b c d mp evs1 p7 p8 hspec p10 hmat =>
      rw [Hsvc] at p8
      obtain rfl := Option.some.inj p8
      exact Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inr (Or.inl ⟨p10, rfl, hmat, rfl⟩)⟩
  | exit a b c d mp evs1 code p8 p9 hspec p11 hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      refine Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inr (Or.inr ⟨code, p11, ?_, rfl⟩)⟩
      rw [show halt_ev mp code = event.ExitEv code (m_fs mp) from by unfold halt_ev; rw [hk]]
  | killed a b c d mp evs1 sig p8 p9 hspec hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      cases hc : m_halted mp with
      | none =>
          rw [m_killed_of_m_halted_none mp hc] at hk
          simp at hk
      | some code =>
          refine Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
            Or.inr (Or.inr ⟨code, hc, ?_, rfl⟩)⟩
          rw [show halt_ev mp code = event.KillEv sig (m_fs mp) from by unfold halt_ev; rw [hk]]
  | syscall_unmodeled a b c p4 p5 hspec =>
      rw [Hsvc] at p5
      obtain rfl := Option.some.inj p5
      exact Or.inr ⟨mkEffect (BitVec.ofInt 64 0) [] [], (check_syscall_err_iff _ _ _).mpr hspec,
        rfl, rfl⟩

/-- The forward direction every node uses: an admissible, non-halting
    checker answer into a model without lazy mappings is an `sstep`. -/
theorem sstep_of_check (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hc : check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = []) :
    sstep segs (mkCfg ms model) evs
      (.SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')) := by
  refine .syscall ms model x8 eff m' m' evs Hh Hsvc ((check_syscall_ok_iff _ _ _ _ _).mp Hc) Hh' ?_
  rw [materialize_model_accesses_no_lazy m' (syscall_effect_accesses eff) Hlazy]

/-- An [I]-indexed silent-or-not node described through the checker: its
    `CheckOk` answers at this pending state are exactly the family
    `(effs i, ms' i, evs i)` (none halting, none lazy) and it never answers
    `CheckUnmodeled`. -/
theorem node_chk_ev (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (I : Type) (effs : I → SyscallEffect) (ms' : I → Model)
    (evs : I → List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : ∀ i, check_syscall (sys_input segs ms x8) (effs i) model
             = .CheckOk (ms' i) (evs i))
    (Hinv : ∀ (eff : SyscallEffect) (m' : Model) (ev : List event),
      check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
      ∃ i, eff = effs i ∧ m' = ms' i ∧ ev = evs i)
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh' : ∀ i, m_halted (ms' i) = none)
    (Hlazy : ∀ i, m_vm_lazy (ms' i) = []) :
    node_ok segs (mkCfg ms model) I evs
      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) := by
  constructor
  · intro i
    exact sstep_of_check segs ms model x8 (effs i) (ms' i) (evs i) Hh Hsvc
      (Hok i) (Hh' i) (Hlazy i)
  · intro e st hss
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, harm⟩ | ⟨eff, hc, he, hst⟩
    · rcases harm with ⟨m'', hh2, he, hmat, hst⟩ | ⟨hh2, he, hmat, hst⟩
                     | ⟨code, hh2, he, hst⟩
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
        rw [materialize_model_accesses_no_lazy (ms' i) _ (Hlazy i)] at hmat
        obtain rfl := Option.some.inj hmat
        exact ⟨i, he, hst⟩
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
        rw [materialize_model_accesses_no_lazy (ms' i) _ (Hlazy i)] at hmat
        cases hmat
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
        rw [Hh' i] at hh2
        cases hh2
    · exact absurd hc (Hnu eff)

/-- The silent special case. -/
theorem node_chk (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (I : Type) (effs : I → SyscallEffect) (ms' : I → Model)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : ∀ i, check_syscall (sys_input segs ms x8) (effs i) model
             = .CheckOk (ms' i) [])
    (Hinv : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs →
      ∃ i, eff = effs i ∧ m' = ms' i ∧ evs = [])
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh' : ∀ i, m_halted (ms' i) = none)
    (Hlazy : ∀ i, m_vm_lazy (ms' i) = []) :
    node_ok segs (mkCfg ms model) I (fun _ => [])
      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) :=
  node_chk_ev segs ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hinv Hnu Hh' Hlazy

/-- A deterministic, non-halting syscall node. -/
theorem node_det (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff0 : SyscallEffect) (m0 : Model) (evs0 : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs ↔
      (eff = eff0 ∧ m' = m0 ∧ evs = evs0))
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh0 : m_halted m0 = none)
    (Hlazy0 : m_vm_lazy m0 = []) :
    node_ok segs (mkCfg ms model) Unit (fun _ => evs0)
      (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0) := by
  refine node_chk_ev segs ms model x8 Unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
    Hh Hsvc ?_ ?_ Hnu ?_ ?_
  · intro i
    cases i
    exact (Hchk eff0 m0 evs0).mpr ⟨rfl, rfl, rfl⟩
  · intro eff m' ev hc
    obtain ⟨rfl, rfl, rfl⟩ := (Hchk eff m' ev).mp hc
    exact ⟨(), rfl, rfl, rfl⟩
  · intro i
    cases i
    exact Hh0
  · intro i
    cases i
    exact Hlazy0

/-- The return-only node (possibly emitting events). -/
theorem node_ret_only (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (r : word) (m' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only eff r m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = []) :
    node_ok segs (mkCfg ms model) Unit (fun _ => evs)
      (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m') := by
  rw [← apply_effect_no_write ms r]
  refine node_det segs ms model x8 (mkEffect r [] []) m' evs Hh Hsvc ?_ ?_ Hh' Hlazy
  · intro eff m'' evs'
    rw [Hchk]
    exact check_ret_only_ok_iff eff r m' evs m'' evs'
  · intro eff
    rw [Hchk]
    exact check_ret_only_no_unmodeled eff r m' evs

/-- The return-only node with a recorded copy-from-user ledger `reads`
    (openat's pathname, writes' source ranges): same successor state. -/
theorem node_ret_only_copyins (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (reads : List (word × Nat)) (r : word) (m' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only_copyins reads eff r m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = []) :
    node_ok segs (mkCfg ms model) Unit (fun _ => evs)
      (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m') := by
  rw [← apply_effect_copyins_no_write ms r reads]
  refine node_det segs ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs
    Hh Hsvc ?_ ?_ Hh' Hlazy
  · intro eff m'' evs'
    rw [Hchk]
    exact check_ret_only_copyins_ok_iff reads eff r m' evs m'' evs'
  · intro eff
    rw [Hchk]
    exact check_ret_only_copyins_no_unmodeled reads eff r m' evs

theorem rz_ret_only (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (r : word) (m' : Model) (evs : List event) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only eff r m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T) :
    realizes segs (mkCfg ms model) (t_emit evs T) :=
  rz_emit1 segs _ _ evs T
    (node_ret_only segs ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy) Hc

theorem rz_ret_only_copyins (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (reads : List (word × Nat)) (r : word) (m' : Model) (evs : List event)
    (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only_copyins reads eff r m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T) :
    realizes segs (mkCfg ms model) (t_emit evs T) :=
  rz_emit1 segs _ _ evs T
    (node_ret_only_copyins segs ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy) Hc

/-- Silent variants (no events): the shape is just the continuation. -/
theorem rz_ret_only_silent (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (r : word) (m' : Model) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only eff r m' [])
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T
    (node_ret_only segs ms model x8 r m' [] Hh Hsvc Hchk Hh' Hlazy) Hc

theorem rz_ret_only_copyins_silent (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (reads : List (word × Nat)) (r : word) (m' : Model)
    (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_ret_only_copyins reads eff r m' [])
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T
    (node_ret_only_copyins segs ms model x8 reads r m' [] Hh Hsvc Hchk Hh' Hlazy) Hc

/-- The deterministic node with a memory-writing effect (file read). -/
theorem rz_det (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff0 : SyscallEffect) (m0 : Model) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ (eff : SyscallEffect) (m' : Model) (evs : List event),
      check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs ↔
      (eff = eff0 ∧ m' = m0 ∧ evs = []))
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh0 : m_halted m0 = none) (Hlazy0 : m_vm_lazy m0 = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T
    (node_det segs ms model x8 eff0 m0 [] Hh Hsvc Hchk Hnu Hh0 Hlazy0) Hc

/-- A silent node with resolutions [I], each continuing as its own shape:
    the configuration realizes the union. -/
theorem rz_cases (segs : List Segment) (c : config) (I : Type) (nx : I → config)
    (T : I → TSet) (i0 : I)
    (Hnode : node_ok segs c I (fun _ => []) nx)
    (Hc : ∀ i, realizes segs (nx i) (T i)) :
    realizes segs c (t_alt T) :=
  .rz_conseq c (t_alt (fun i => t_emit [] (T i))) (t_alt T)
    (.rz_node c I (fun _ => []) nx T i0 Hnode Hc) (by
      intro tr
      constructor
      · rintro ⟨i, Hi⟩
        exact ⟨i, (t_emit_nil_eq (T i) (realizes_nonempty segs (nx i) (T i) (Hc i)) tr).1 Hi⟩
      · rintro ⟨i, Hi⟩
        exact ⟨i, (t_emit_nil_eq (T i) (realizes_nonempty segs (nx i) (T i) (Hc i)) tr).2 Hi⟩)

/-- The exit leaf: [ShapeAlg.rz_exit], re-exported under the checker
    naming for the callers that used [Nodes.rz_exit_chk]. -/
theorem rz_exit_chk (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hx8 : is_exit_no x8) :
    realizes segs (mkCfg ms model)
      (t_exit (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)) :=
  rz_exit segs ms model x8 Hh Hsvc Hx8

/- =========================================================================
   The openat node
   ========================================================================= -/

/-- The open node: the checker reduces to
    [check_open_result_copyins reads eff model mk].  Resolutions: an errno
    from [openat_errnos] (model unchanged), or the lowest free fd
    [alloc_fd (m_fds model)] (model [mk fd]).  The recorded pathname read
    [reads] lands in [eff_copyins] only, so the machine successor is the
    plain return. -/
def open_I (_model : Model) : Type :=
  { e : Int // e ∈ Sys.Fs.Open.openat_errnos } ⊕ Unit

def open_nx (ms : machine_state) (model : Model) (mk : word → Model)
    (i : open_I model) : config :=
  match i with
  | .inl ⟨e, _⟩ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | .inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
      (mk (alloc_fd (m_fds model)))

theorem node_open (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (reads : List (word × Nat)) (mk : word → Model)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_open_result_copyins reads eff model mk)
    (Hmk : ∀ fd, m_halted (mk fd) = none)
    (Hmklazy : ∀ fd, m_vm_lazy (mk fd) = [])
    (Hfree : fd_lookup (m_fds model) (alloc_fd (m_fds model)) = none) :
    node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk) := by
  constructor
  · intro i
    rcases i with ⟨e, he⟩ | u
    · have hchk : check_syscall (sys_input segs ms x8)
          (with_copyins reads (mkEffect (errno_ret e) [] [])) model
          = .CheckOk model [] := by
        rw [Hchk]
        exact (check_open_result_copyins_ok_iff reads _ model mk model []).mpr
          (Or.inl ⟨e, he, rfl, rfl, rfl⟩)
      have hgoal := sstep_of_check segs ms model x8 _ model [] Hh Hsvc hchk Hh Hlazy
      simpa only [open_nx, apply_effect_copyins_no_write] using hgoal
    · have hchk : check_syscall (sys_input segs ms x8)
          (with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])) model
          = .CheckOk (mk (alloc_fd (m_fds model))) [] := by
        rw [Hchk]
        exact (check_open_result_copyins_ok_iff reads _ model mk _ []).mpr
          (Or.inr ⟨alloc_fd (m_fds model), Hfree, rfl, rfl, rfl, rfl⟩)
      have hgoal := sstep_of_check segs ms model x8 _
        (mk (alloc_fd (m_fds model))) [] Hh Hsvc hchk
        (Hmk (alloc_fd (m_fds model))) (Hmklazy (alloc_fd (m_fds model)))
      simpa only [open_nx, apply_effect_copyins_no_write] using hgoal
  · intro e st hss
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, harm⟩ | ⟨eff, hc, he, hst⟩
    · rw [Hchk, check_open_result_copyins_ok_iff] at hc
      rcases hc with ⟨er, her, heff, hm, hev⟩ | ⟨fd, hlk, hfd, heff, hm, hev⟩
      · rcases harm with ⟨m'', hh2, he, hmat, hst⟩ | ⟨hh2, he, hmat, hst⟩
                       | ⟨code, hh2, he, hst⟩
        · rw [heff] at hmat hst
          rw [hm] at hmat
          rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
          have hm'' : m'' = model := (Option.some.inj hmat).symm
          rw [hm''] at hst
          rw [hev] at he
          exact ⟨.inl ⟨er, her⟩, he, by
            rw [hst]; simp only [open_nx, apply_effect_copyins_no_write]⟩
        · rw [heff] at hmat
          rw [hm] at hmat
          rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
          cases hmat
        · rw [hm] at hh2
          rw [Hh] at hh2
          cases hh2
      · rw [hfd] at heff hm
        rcases harm with ⟨m'', hh2, he, hmat, hst⟩ | ⟨hh2, he, hmat, hst⟩
                         | ⟨code, hh2, he, hst⟩
        · rw [heff] at hmat hst
          rw [hm] at hmat
          rw [materialize_model_accesses_no_lazy (mk (alloc_fd (m_fds model))) _
              (Hmklazy (alloc_fd (m_fds model)))] at hmat
          have hm'' : m'' = mk (alloc_fd (m_fds model)) := (Option.some.inj hmat).symm
          rw [hm''] at hst
          rw [hev] at he
          exact ⟨.inr (), he, by
            rw [hst]; simp only [open_nx, apply_effect_copyins_no_write]⟩
        · rw [heff] at hmat
          rw [hm] at hmat
          rw [materialize_model_accesses_no_lazy (mk (alloc_fd (m_fds model))) _
              (Hmklazy (alloc_fd (m_fds model)))] at hmat
          cases hmat
        · rw [hm] at hh2
          rw [Hmk (alloc_fd (m_fds model))] at hh2
          cases hh2
    · rw [Hchk] at hc
      exact absurd hc (check_open_result_copyins_never_unmodeled reads eff model mk)

theorem rz_open (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (reads : List (word × Nat)) (mk : word → Model) (A B : TSet)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
             = check_open_result_copyins reads eff model mk)
    (Hmk : ∀ fd, m_halted (mk fd) = none)
    (Hmklazy : ∀ fd, m_vm_lazy (mk fd) = [])
    (Hfree : fd_lookup (m_fds model) (alloc_fd (m_fds model)) = none)
    (HA : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                         (mk (alloc_fd (m_fds model)))) B) :
    realizes segs (mkCfg ms model) (t_alt2 A B) := by
  refine rz_alt2 segs (mkCfg ms model) { e : Int // e ∈ Sys.Fs.Open.openat_errnos } Unit
    (open_nx ms model mk) A B ⟨ENOMEM, ?_⟩ () ?_ ?_ ?_
  · exact ENOMEM_in_Sys.Fs.Open.openat_errnos
  · exact node_open segs ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree
  · intro i
    obtain ⟨e, he⟩ := i
    exact HA e he
  · intro u
    cases u
    exact HB

/-! -/

example (m : Model) (code : word) (Hk : m_killed m = none) :
    halt_ev m code = .ExitEv code (m_fs m) := by
  unfold halt_ev
  rw [Hk]

example (m : Model) (code sig : word) (Hk : m_killed m = some sig) :
    halt_ev m code = .KillEv sig (m_fs m) := by
  unfold halt_ev
  rw [Hk]

example (m : Model) : Nonempty (open_I m) := ⟨.inr ()⟩

end LinuxSem.Common.Nodes
