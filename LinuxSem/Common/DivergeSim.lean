/-
  * Common.DivergeSim — reusable trace-semantics infrastructure for a
    SILENTLY DIVERGING branch: execution reaches a machine state from
    which it loops forever without issuing another effectful step.

  TRUST BOUNDARY: image-INDEPENDENT proof library (like `Common.ExitSim`).
  Generic over the loaded segments `segs`.

  WHY THIS EXISTS.  The sealed ASan runtime answers an internal
  allocation failure with a tight infinite loop that makes NO further
  syscalls (typically a single self-jump, `j .` = `jal x0, 0`, or an
  equivalent closed loop over a few PCs).  An equivalence proof over
  the spec's failure-anytime mmap nondeterminism must show, at each
  refusal case-split, that the diverging resolution contributes no new
  complete trace and only already-covered prefixes: from the loop
  state, `Run.star` can emit nothing further, so `Run.obs_trace` gains
  only prefixes of the events already emitted (which the prefix
  closure of `bh_traces` contributes anyway), the branch can never
  take the explicit error transition (nothing lands in `bh_errors`),
  and — because the loop is an infinite non-erroring execution — the
  branch also REFUTES `bh_all_errors`, so the source-vacuity escape of
  `Equivalence.equiv` cannot fire through it.

  NO COINDUCTION IS NEEDED.  `bh_traces` holds only FINITE prefixes of
  finite `star` derivations, `bh_errors` is a finite reach, and
  `bh_all_errors` is inductive (accessibility), so "loops forever" is
  consumed purely inductively: a set of configurations closed under
  the one deterministic silent step absorbs every finite derivation
  that enters it.  Consequently every lemma here is `Qed` with no
  axioms beyond the baseline.

  STRUCTURE (three layers, from general to executable):

  - `silent_loop P`: a SET of configurations, each un-halted, with no
    pending syscall, whose accounted instruction step (`Run.
    mi_account_step`) succeeds and stays in the set.  This is the
    finite-cycle predicate in its most general, model-threading form
    (`silent_loop_cycle` shows the literal finite-set instance is
    definitional).  Core results: a `star` from a `silent_loop` state
    emits `[]` (`silent_loop_star`); no error transition is reachable
    (`silent_loop_no_error`); the observation set is exactly `{[]}`
    (`silent_loop_obs_iff`); and `all_traces_error` is refuted
    (`silent_loop_not_all_errors`).
  - `to_spin ms model`: "this machine state deterministically runs a
    straight line of silent instruction steps into a one-step
    FIXPOINT" — the reach-style predicate an example proof
    establishes at the post-refusal state, mirroring `ExitSim.to_exit`
    (which reaches an exit ecall where this reaches a self-jump).
    The base case is an accounted-step fixpoint; smart constructors
    cover the two ways proofs actually meet it: an instruction with
    an EMPTY access report (`ts_spin_no_access` — any model, lazy
    mappings included, so post-mmap ASan states are covered) and the
    no-lazy raw-step idiom the existing sim files use
    (`ts_spin_no_lazy`/`ts_step_no_lazy` compose with the
    `PropExec.step_*` lemmas over `mkst`).
  - `spin_c`: a fuel-bounded executable witness for `to_spin`, closed
    by `decide` on a concrete machine state (`spin_c_to_spin`; tactic
    `prove_to_spin`), keyed on recognizing the literal self-jump
    instruction `is_self_jump` (a decoded `Jal rd imm` with
    `rd = x0` and `imm.toInt = 0` — both the 4-byte `j .` and the
    compressed `c.j .` expand to exactly that).  Use it only when the
    state is concrete enough for the boolean to collapse; symbolic
    proofs chain `ts_step_no_access`/`ts_step_no_lazy` instead.

  HOW A SIM PROOF INVOKES IT.  At an mmap-refusal case-split the
  derivation stands at the post-refusal configuration `⟨ms, model⟩`
  with some emitted prefix `P` behind it.  Establish `to_spin ms model`
  (by `prove_to_spin`, or by chaining `ts_step_no_lazy` over
  `PropExec` step lemmas into `ts_spin_of_step_j`); then

  - in the FORWARD direction of a `*_obs_iff` proof, the tail `star`
    of the refusal branch collapses by `spin_star_nil` (so the branch
    trace is `P ++ [] = P`, a prefix of the already-covered complete
    trace);
  - in a `*_no_error` proof, the refusal branch's error reach is
    refuted by `spin_no_error_run` (and, at the split configuration
    itself, `spin_no_sstep_error`);
  - the BACKWARD direction needs nothing new: prefixes of `P` are
    already contributed by the derivation that reaches the split
    (`obs_trace_of_star`).

  `spin_branch_toy_*` at the bottom work a complete two-branch toy
  obligation in exactly this shape, and the `SelfJumpImage` section
  checks the executable layer end-to-end on a concrete image whose
  single instruction is the literal `j .` encoding 0x0000006f.

  NOTES.

  - `Section WithFP1`'s `Context {fx : FPState}` is threaded the way
    `Common.PropExec` threads it: only `step_j_self`, which is stated at
    the `PropExec.mkst` state shape, takes the `FPState` instance.
  - `Section WithSegs`'s `Variable segs` becomes an EXPLICIT LEADING
    parameter on every declaration that mentions it — the same
    convention `Run.lean`, `OmniRun.lean` and `ExitSim.lean` follow.
  - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` record constructor
    `⟨sp, brk0, mb, rnd⟩`; `mkImage segs pc ph` and `mkPhdrInfo a e n`
    are the corresponding structure literals.
  - `bv_signed imm = 0` is `imm.toInt = 0`, `Z.eqb a b` is `a == b`,
    `Z_to_bv n z` is `BitVec.ofInt n z`, `vm_compute; reflexivity` is
    `decide`.
  - DEVIATION (definitional only).  `is_self_jump`'s decode test is
    factored through `self_jump_instr`, a `Bool`-valued function of the
    DECODED instruction, so that the elimination lemma
    `is_self_jump_to_spin` can case on the instruction once instead of
    matching the nested pattern `some (Jal rd imm, _)` in place. -/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.Common.PropExec
import LinuxSem.Common.SharedFacts

set_option autoImplicit false

namespace LinuxSem.Common.DivergeSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Common.PropExec
open LinuxSem.Common.SharedFacts
open behavior

/-! The `StepTac.vm_refl_bv` idiom has no analogue: it exists  only to
    close a `bool_decide` cast without unfolding an opaque `Z_to_bv` well-
    formedness proof, and Lean's `decide` closes the same goals directly. -/

/- =========================================================================
   Prefix-order helpers
   ========================================================================= -/

/-- A prefix of the empty trace is empty. -/
theorem is_prefix_nil_inv {A : Type} (tr : List A) : is_prefix tr [] → tr = [] := by
  intro h
  cases tr with
  | nil => rfl
  | cons _ _ => simp [is_prefix] at h

/-- Prepending one and the same trace to both sides preserves the prefix
    order. -/
theorem is_prefix_app_mono {A : Type} (e : List A) {a b : List A} :
    is_prefix a b → is_prefix (e ++ a) (e ++ b) := by
  intro h
  induction e with
  | nil => simpa using h
  | cons x xs ih => exact ⟨rfl, ih⟩

/- =========================================================================
   Accounted-step plumbing (segment-generic)
   ========================================================================= -/

/-- Read an accounted step off a raw access report. -/
theorem mi_account_step_of_accesses (segs : List Segment) (ms : machine_state)
    (model : Model) (ms' : machine_state) (ranges : List (word × Nat))
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges)) :
    mi_account_step segs ms model =
      match materialize_model_accesses model ranges with
      | some model' => .MachineOk (ms', model')
      | none => .MachineFault := by
  have Hstep' : step_accesses segs ms
      = .MachineOk (⟨ms', ranges⟩ : access_report machine_state) := Hstep
  unfold mi_account_step
  rw [Hstep']
  rfl

/-- An access-free instruction steps the machine and leaves the model
    alone — no lazy hypothesis. -/
theorem mi_account_step_no_access (segs : List Segment) (ms : machine_state)
    (model : Model) (ms' : machine_state)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' [])) :
    mi_account_step segs ms model = .MachineOk (ms', model) := by
  rw [mi_account_step_of_accesses segs ms model ms' [] Hstep,
    materialize_model_accesses_nil]

/-- An accounted instruction step preserves haltedness (it can only
    charge lazy pages; `m_proc` is framed). -/
theorem mi_account_step_halted (segs : List Segment) (ms : machine_state)
    (model : Model) (ms' : machine_state) (model' : Model)
    (Hacc : mi_account_step segs ms model = .MachineOk (ms', model')) :
    m_halted model' = m_halted model := by
  obtain ⟨-, -, -, -, -, Hproc, -⟩ :=
    mi_account_step_model_frame segs ms model ms' model' Hacc
  unfold m_halted
  rw [Hproc]

/- =========================================================================
   The self-jump instruction: the accounted one-step fixpoint
   ========================================================================= -/

/-- `v_addi a 0 = a`.   -/
theorem v_addi_0 (a : word) : v_addi a 0 = a := by
  unfold v_addi
  rw [Int.add_zero, BitVec.ofInt_natCast]
  simp

/-- A decoded `Jal x0 imm` with `imm.toInt = 0` — the expansion of both
    `j .` (4 bytes, 0x0000006f) and `c.j .` (2 bytes) — is a one-step
    fixpoint of the machine semantics WITH AN EMPTY ACCESS REPORT, for an
    ARBITRARY machine state with no pending syscall (no `mkst` shape
    required: the spin state inherits whatever registers, reservation and
    fcsr the crashing runtime left behind). -/
theorem self_jump_step_accesses (segs : List Segment) (ms : machine_state)
    (w : BitVec 32) (rd : reg) (imm : BitVec 21) (sz : Int)
    (Hsvc : ms.ms_svc_pending = none)
    (Hfetch : fetch_word segs (ms_pc ms) = some w)
    (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, sz))
    (Hx0 : is_x0 rd = true)
    (Himm : imm.toInt = 0) :
    step_accesses segs ms = .MachineOk (mkAccessReport ms []) := by
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
  have Hsvc' : svc = none := Hsvc
  simp only [ms_pc] at Hfetch
  have himm0 : imm = 0 := by
    rw [← BitVec.toInt_inj, Himm]
    decide
  have hsext : sext 64 imm = (0 : word) := by
    rw [himm0]
    decide
  simp only [step_accesses, ms_pc, Hfetch, decode_exec_accesses, Hecall, Bool.false_eq_true,
    reduceIte, Hdecode, exec, rset, Hx0, ite_true, interp_eff_accesses, mkAccessReport,
    with_pc, hsext, Hsvc']
  simp

/-- The same, packaged at the accounted level: the self-jump is a
    fixpoint of `mi_account_step` with the model UNCHANGED — again with
    no hypothesis on the lazy ledger. -/
theorem self_jump_account_fix (segs : List Segment) (ms : machine_state)
    (model : Model) (w : BitVec 32) (rd : reg) (imm : BitVec 21) (sz : Int)
    (Hsvc : ms.ms_svc_pending = none)
    (Hfetch : fetch_word segs (ms_pc ms) = some w)
    (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, sz))
    (Hx0 : is_x0 rd = true)
    (Himm : imm.toInt = 0) :
    mi_account_step segs ms model = .MachineOk (ms, model) :=
  mi_account_step_no_access segs ms model ms
    (self_jump_step_accesses segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm)

section WithFP

variable [fx : FPState]

/-- The `PropExec.mkst` spelling, for symbolic straight-line proofs in
    the existing sim idiom. -/
theorem step_j_self (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 21) (sz : Int)
    (Hfetch : fetch_word segs pc = some w)
    (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, sz))
    (Hx0 : is_x0 rd = true)
    (Himm : imm.toInt = 0) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineOk (mkst regs pc mem rom) := by
  unfold RiscvSemantics.step
  rw [self_jump_step_accesses segs (mkst regs pc mem rom) w rd imm sz
    (show (mkst regs pc mem rom).ms_svc_pending = none from rfl)
    (show fetch_word segs (ms_pc (mkst regs pc mem rom)) = some w from Hfetch)
    Hecall Hdecode Hx0 Himm]
  simp only [drop_access_report, mkAccessReport]

end WithFP

/- =========================================================================
   silent_loop: a step-closed set of effect-free configurations
   ========================================================================= -/

/-- `P` is a set of configurations, each of which is un-halted, has no
    pending syscall, and whose accounted instruction step succeeds and
    lands back in `P`.  Execution entering `P` therefore runs forever,
    emits no event, and never reaches the error transition.  This is
    the "closed loop over a few PCs" predicate in its most general
    form: the loop body may even keep materializing fresh lazy pages
    forever, as long as every accounted step succeeds. -/
def silent_loop (segs : List Segment) (P : config → Prop) : Prop :=
  ∀ c, P c →
    m_halted c.cfg_model = none ∧
    c.cfg_ms.ms_svc_pending = none ∧
    ∃ (ms' : machine_state) (model' : Model),
      mi_account_step segs c.cfg_ms c.cfg_model = .MachineOk (ms', model') ∧
      P ⟨ms', model'⟩

/-- The finite-cycle instance is DEFINITIONAL: a concrete list of
    configurations, each stepping to a member, is a `silent_loop`. -/
theorem silent_loop_cycle (segs : List Segment) (cs : List config)
    (H : ∀ c, c ∈ cs →
      m_halted c.cfg_model = none ∧
      c.cfg_ms.ms_svc_pending = none ∧
      ∃ (ms' : machine_state) (model' : Model),
        mi_account_step segs c.cfg_ms c.cfg_model = .MachineOk (ms', model') ∧
        ⟨ms', model'⟩ ∈ cs) :
    silent_loop segs (fun c => c ∈ cs) :=
  fun c hc => H c hc

/-- From a `silent_loop` configuration the ONLY transition is the
    silent instruction step, and it stays in the loop. -/
theorem silent_loop_sstep (segs : List Segment) (P : config → Prop) (c : config)
    (evs : List event) (to : step_to) :
    silent_loop segs P → P c → sstep segs c evs to →
    evs = [] ∧ ∃ c', to = .SNext c' ∧ P c' := by
  intro Hloop HP Hstep
  obtain ⟨Hh, Hsvc, ms', model', Hacc, HP'⟩ := Hloop c HP
  obtain ⟨ms, model⟩ := c
  cases Hstep with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    rw [Hacc] at hacc
    cases hacc
    exact ⟨rfl, ⟨⟨ms', model'⟩, rfl, HP'⟩⟩
  | instr_fault ms0 model0 hh hsvc hacc =>
    rw [Hacc] at hacc
    exact nomatch hacc
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
    rw [Hacc] at hacc
    exact nomatch hacc
  | syscall ms0 model0 x8 eff m1 m2 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff m1 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | exit ms0 model0 x8 eff m1 evs0 code hh hsvc hspec hh' hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | killed ms0 model0 x8 eff m1 evs0 sig hh hsvc hspec hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_unmodeled ms0 model0 x8 hh hsvc hspec =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)

/-- One-level case analysis on a `star` derivation (a plain `cases`
    packaged so case-split proofs need no `inversion` bookkeeping). -/
theorem star_case (segs : List Segment) (c : config) (tr : List event) (c' : config)
    (H : star segs c tr c') :
    (tr = [] ∧ c' = c) ∨
    ∃ (evs : List event) (c2 : config) (tr2 : List event),
      sstep segs c evs (.SNext c2) ∧ star segs c2 tr2 c' ∧ tr = evs ++ tr2 := by
  cases H with
  | refl c0 => exact Or.inl ⟨rfl, rfl⟩
  | step c1 evs c2 tr2 c3 h1 h2 => exact Or.inr ⟨evs, c2, tr2, h1, h2, rfl⟩

/-- A finite run from inside the loop emits nothing and stays inside. -/
theorem silent_loop_star (segs : List Segment) (P : config → Prop)
    (Hloop : silent_loop segs P) :
    ∀ (c : config) (tr : List event) (c' : config),
      star segs c tr c' → P c → tr = [] ∧ P c' := by
  intro c tr c' Hstar
  induction Hstar with
  | refl c0 => intro HP; exact ⟨rfl, HP⟩
  | step c1 evs c2 tr2 c3 hstep htail ih =>
    intro HP
    obtain ⟨hev, c2', hto, HP2⟩ :=
      silent_loop_sstep segs P c1 evs (.SNext c2) Hloop HP hstep
    cases hto
    obtain ⟨htr, HP3⟩ := ih HP2
    exact ⟨by simp [hev, htr], HP3⟩

theorem silent_loop_star_nil (segs : List Segment) (P : config → Prop) (c : config)
    (tr : List event) (c' : config) :
    silent_loop segs P → P c → star segs c tr c' → tr = [] := by
  intro Hloop HP Hstar
  exact (silent_loop_star segs P Hloop c tr c' Hstar HP).1

/-- No error transition is reachable from inside the loop: nothing this
    branch does can land in `bh_errors`. -/
theorem silent_loop_no_error (segs : List Segment) (P : config → Prop) (c : config) :
    silent_loop segs P → P c → ¬ reaches_error segs c := by
  intro Hloop HP h
  obtain ⟨tr, c2, evs, Hstar, Herr⟩ := h
  obtain ⟨-, HP2⟩ := silent_loop_star segs P Hloop c tr c2 Hstar HP
  obtain ⟨-, c', Heq, -⟩ := silent_loop_sstep segs P c2 evs .SError Hloop HP2 Herr
  exact nomatch Heq

/-- ...and a fortiori nothing unmodeled is reachable. -/
theorem silent_loop_no_unmodeled (segs : List Segment) (P : config → Prop) (c : config) :
    silent_loop segs P → P c → ¬ reaches_unmodeled segs c := by
  intro Hloop HP
  exact no_error_no_unmodeled segs c (silent_loop_no_error segs P c Hloop HP)

/-- The loop's observation set is exactly `{[]}`: the branch contributes
    only prefixes of whatever was emitted BEFORE it was entered. -/
theorem silent_loop_obs_iff (segs : List Segment) (P : config → Prop) (c : config) :
    silent_loop segs P → P c → ∀ tr, obs_trace segs c tr ↔ tr = [] := by
  intro Hloop HP tr
  constructor
  · intro ⟨tr', c2, Hstar, Hpre⟩
    rw [silent_loop_star_nil segs P c tr' c2 Hloop HP Hstar] at Hpre
    exact is_prefix_nil_inv tr Hpre
  · intro h
    rw [h]
    exact obs_trace_nil segs c

/-- The loop is an infinite NON-erroring execution, so it refutes
    `all_traces_error`: a source binary whose refusal branch spins can
    never take `Equivalence.equiv`'s vacuity escape through that
    branch. -/
theorem silent_loop_not_all_errors (segs : List Segment) (P : config → Prop) (c : config) :
    silent_loop segs P → P c → ¬ all_traces_error segs c := by
  intro Hloop HP Hall
  revert HP
  induction Hall with
  | intro c0 hprog hnext ih =>
    intro HP
    obtain ⟨ms, model⟩ := c0
    obtain ⟨Hh, Hsvc, ms', model', Hacc, HP'⟩ := Hloop ⟨ms, model⟩ HP
    exact ih [] ⟨ms', model'⟩ (sstep.instr ms model ms' model' Hh Hsvc Hacc) HP'

/- =========================================================================
   to_spin: a deterministic straight line into a one-step fixpoint
   ========================================================================= -/

/-- "`ms` (running against `model`) silently reaches a one-step
    fixpoint": finitely many successful accounted instruction steps, no
    pending syscall anywhere, ending at a state whose accounted step is
    the identity.  The reach-style mirror of `ExitSim.to_exit`, with
    the model THREADED because the accounting layer may charge lazy
    pages on the way in. -/
inductive to_spin (segs : List Segment) : machine_state → Model → Prop where
  /-- The base case: an accounted-step fixpoint. -/
  | ts_spin (ms : machine_state) (model : Model) :
      ms.ms_svc_pending = none →
      mi_account_step segs ms model = .MachineOk (ms, model) →
      to_spin segs ms model
  /-- One deterministic silent step on the way in. -/
  | ts_step (ms : machine_state) (model : Model) (ms' : machine_state) (model' : Model) :
      ms.ms_svc_pending = none →
      mi_account_step segs ms model = .MachineOk (ms', model') →
      to_spin segs ms' model' →
      to_spin segs ms model

/-- Smart constructors, in decreasing order of generality. -/
theorem ts_spin_no_access (segs : List Segment) (ms : machine_state) (model : Model)
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms [])) :
    to_spin segs ms model :=
  .ts_spin ms model Hsvc (mi_account_step_no_access segs ms model ms Hstep)

theorem ts_step_no_access (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' []))
    (Hspin : to_spin segs ms' model) :
    to_spin segs ms model :=
  .ts_step ms model ms' model Hsvc (mi_account_step_no_access segs ms model ms' Hstep) Hspin

/-- The raw-step spellings the existing sim files produce
    (`PropExec.step_*` lemmas over `mkst` state raw
    `RiscvSemantics.step` equalities); they need the usual no-lazy
    hypothesis those files already thread. -/
theorem ts_spin_no_lazy (segs : List Segment) (ms : machine_state) (model : Model)
    (Hsvc : ms.ms_svc_pending = none)
    (Hlazy : m_vm_lazy model = [])
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms) :
    to_spin segs ms model := by
  refine .ts_spin ms model Hsvc ?_
  rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]

theorem ts_step_no_lazy (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (Hsvc : ms.ms_svc_pending = none)
    (Hlazy : m_vm_lazy model = [])
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hspin : to_spin segs ms' model) :
    to_spin segs ms model := by
  refine .ts_step ms model ms' model Hsvc ?_ Hspin
  rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]

/-- Entering the spin on the literal self-jump instruction. -/
theorem ts_spin_of_step_j (segs : List Segment) (ms : machine_state) (model : Model)
    (w : BitVec 32) (rd : reg) (imm : BitVec 21) (sz : Int)
    (Hsvc : ms.ms_svc_pending = none)
    (Hfetch : fetch_word segs (ms_pc ms) = some w)
    (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, sz))
    (Hx0 : is_x0 rd = true)
    (Himm : imm.toInt = 0) :
    to_spin segs ms model :=
  ts_spin_no_access segs ms model Hsvc
    (self_jump_step_accesses segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm)

/-- The set a `to_spin` derivation stays inside. -/
def spinning (segs : List Segment) (c : config) : Prop :=
  to_spin segs c.cfg_ms c.cfg_model ∧ m_halted c.cfg_model = none

theorem spinning_silent_loop (segs : List Segment) : silent_loop segs (spinning segs) := by
  intro c H
  obtain ⟨ms, model⟩ := c
  obtain ⟨Hspin, Hh⟩ := H
  cases Hspin with
  | ts_spin ms0 model0 Hsvc Hfix =>
    exact ⟨Hh, Hsvc, ms, model, Hfix, ⟨.ts_spin ms model Hsvc Hfix, Hh⟩⟩
  | ts_step ms0 model0 ms' model' Hsvc Hacc Hspin' =>
    refine ⟨Hh, Hsvc, ms', model', Hacc, Hspin', ?_⟩
    rw [mi_account_step_halted segs ms model ms' model' Hacc]
    exact Hh

/- =========================================================================
   The proof-facing trio at a spin state
   ========================================================================= -/

/-- In the FORWARD direction of a `*_obs_iff` proof: once the refusal
    branch's derivation stands at `⟨ms, model⟩` with `to_spin`, its tail
    `star` collapses to `[]`. -/
theorem spin_star_nil (segs : List Segment) (ms : machine_state) (model : Model)
    (tr : List event) (c' : config) :
    to_spin segs ms model → m_halted model = none →
    star segs ⟨ms, model⟩ tr c' → tr = [] := by
  intro Hspin Hh Hstar
  exact silent_loop_star_nil segs (spinning segs) ⟨ms, model⟩ tr c'
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩ Hstar

/-- The branch's own observation set is exactly `{[]}`. -/
theorem spin_obs_iff (segs : List Segment) (ms : machine_state) (model : Model) :
    to_spin segs ms model → m_halted model = none →
    ∀ tr, obs_trace segs ⟨ms, model⟩ tr ↔ tr = [] := by
  intro Hspin Hh
  exact silent_loop_obs_iff segs (spinning segs) ⟨ms, model⟩
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩

/-- In a `*_no_error` proof: the refusal branch never errors. -/
theorem spin_no_error_run (segs : List Segment) (ms : machine_state) (model : Model) :
    to_spin segs ms model → m_halted model = none →
    ¬ reaches_error segs ⟨ms, model⟩ := by
  intro Hspin Hh
  exact silent_loop_no_error segs (spinning segs) ⟨ms, model⟩
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩

/-- At the split configuration itself: no single erroring step. -/
theorem spin_no_sstep_error (segs : List Segment) (ms : machine_state) (model : Model) :
    to_spin segs ms model → m_halted model = none →
    ∀ evs, ¬ sstep segs ⟨ms, model⟩ evs .SError := by
  intro Hspin Hh evs Herr
  obtain ⟨-, c', Heq, -⟩ := silent_loop_sstep segs (spinning segs) ⟨ms, model⟩ evs .SError
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩ Herr
  exact nomatch Heq

theorem spin_no_unmodeled (segs : List Segment) (ms : machine_state) (model : Model) :
    to_spin segs ms model → m_halted model = none →
    ¬ reaches_unmodeled segs ⟨ms, model⟩ := by
  intro Hspin Hh
  exact silent_loop_no_unmodeled segs (spinning segs) ⟨ms, model⟩
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩

/-- The spin refutes the vacuity escape. -/
theorem spin_not_all_errors (segs : List Segment) (ms : machine_state) (model : Model) :
    to_spin segs ms model → m_halted model = none →
    ¬ all_traces_error segs ⟨ms, model⟩ := by
  intro Hspin Hh
  exact silent_loop_not_all_errors segs (spinning segs) ⟨ms, model⟩
    (spinning_silent_loop segs) ⟨Hspin, Hh⟩

/- =========================================================================
   Shape: a run that reaches a spin with prefix P
   contributes exactly the prefixes of P
   ========================================================================= -/

/-- Prefixes of any reached derivation are observable — the generic
    containment direction (nothing spin-specific; stated here because
    the spin glue consumes it together with `spin_star_nil`). -/
theorem obs_trace_of_star (segs : List Segment) (c0 : config) (evs : List event)
    (c : config) (tr : List event) :
    star segs c0 evs c → is_prefix tr evs → obs_trace segs c0 tr :=
  fun Hstar Hpre => ⟨evs, c, Hstar, Hpre⟩

/-- If a run reaches `⟨ms, model⟩` having emitted `P`, and the state
    spins, then (i) every prefix of `P` is observable from `c0`, and
    (ii) every continuation THROUGH the spin state adds nothing: the
    branch contributes exactly the prefixes of `P` to `bh_traces`.  In
    particular, if `P` is already a prefix of a complete trace the
    other resolution produces, the trace-set equality obligation is
    unaffected by this branch. -/
theorem spin_reach_obs (segs : List Segment) (c0 : config) (P : List event)
    (ms : machine_state) (model : Model) :
    star segs c0 P ⟨ms, model⟩ →
    to_spin segs ms model → m_halted model = none →
    (∀ tr, is_prefix tr P → obs_trace segs c0 tr) ∧
    (∀ (tr : List event) (c' : config), star segs ⟨ms, model⟩ tr c' → P ++ tr = P) := by
  intro Hstar Hspin Hh
  refine ⟨?_, ?_⟩
  · intro tr Hpre
    exact obs_trace_of_star segs c0 P ⟨ms, model⟩ tr Hstar Hpre
  · intro tr c' Htail
    rw [spin_star_nil segs ms model tr c' Hspin Hh Htail, List.append_nil]

/- =========================================================================
   Executable witness
   ========================================================================= -/

/-- The decode-side test of `is_self_jump`, as a `Bool`-valued function of
    the DECODED instruction: `jal x0` with a zero offset.  Factored out of
    `is_self_jump` so the elimination lemma
    file's -/
def self_jump_instr : Instr → Bool
  | .jal rd imm => is_x0 rd && (imm.toInt == 0)
  | _ => false

/-- The inline form this stands for — the `Bool` value is unchanged. -/
theorem self_jump_instr_eq_match (o : Option (Instr × Int)) :
    (match o with
     | some (i, _) => self_jump_instr i
     | none => false)
    = (match o with
       | some (Instr.jal rd imm, _) => is_x0 rd && (imm.toInt == 0)
       | _ => false) := by
  cases o with
  | none => rfl
  | some p =>
    obtain ⟨i, sz⟩ := p
    cases i <;> rfl

/-- Recognize the literal self-jump: no pending syscall, and the
    fetched word decodes to `Jal x0 imm` with `imm.toInt = 0`
    (both `j .` and `c.j .`).  The immutable-code fast path
    (`fetch_word`) is deliberately the only one tried: the ASan spin
    sits in the binary's r-x text segment.  A self-jump in a w+x
    segment must go through `ts_spin_no_lazy` by hand. -/
def is_self_jump (segs : List Segment) (ms : machine_state) : Bool :=
  match ms.ms_svc_pending with
  | some _ => false
  | none =>
    match fetch_word segs (ms_pc ms) with
    | some w =>
      if is_ecall w then false else
      match decodeAny w with
      | some (i, _) => self_jump_instr i
      | none => false
    | none => false

theorem is_self_jump_to_spin (segs : List Segment) (ms : machine_state) (model : Model) :
    is_self_jump segs ms = true → to_spin segs ms model := by
  intro H
  unfold is_self_jump at H
  cases hsvc : ms.ms_svc_pending with
  | some x8 =>
    simp only [hsvc] at H
    exact absurd H (by simp)
  | none =>
    cases hfetch : fetch_word segs (ms_pc ms) with
    | none =>
      simp only [hsvc, hfetch] at H
      exact absurd H (by simp)
    | some w =>
      cases hecall : is_ecall w with
      | true =>
        simp only [hsvc, hfetch, hecall] at H
        exact absurd H (by simp)
      | false =>
        cases hdec : decodeAny w with
        | none =>
          simp only [hsvc, hfetch, hecall, hdec] at H
          exact absurd H (by simp)
        | some p =>
          obtain ⟨i, sz⟩ := p
          simp only [hsvc, hfetch, hecall, hdec] at H
          cases i with
          | jal rd imm =>
            have H' : (is_x0 rd && (imm.toInt == 0)) = true := H
            simp only [Bool.and_eq_true, beq_iff_eq] at H'
            exact ts_spin_of_step_j segs ms model w rd imm sz hsvc hfetch hecall hdec H'.1 H'.2
          | _ => simp [self_jump_instr] at H

/-- Fuel-bounded executable straight-line-to-spin check, closed by
    `decide` on a concrete state (mirroring `ExitSim.sim_c`).
    NOTE: `decide` normalizes the whole term, so only use this when
    `ms`/`model` are concrete enough for the boolean to collapse —
    in particular never with an infinite `InputStream` buried in a
    concrete model.  Symbolic proofs chain the `ts_*` constructors. -/
def spin_c (segs : List Segment) (fuel : Nat) (ms : machine_state) (model : Model) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if is_self_jump segs ms then true
    else
      match ms.ms_svc_pending with
      | some _ => false
      | none =>
        match mi_account_step segs ms model with
        | .MachineOk (ms', model') => spin_c segs fuel ms' model'
        | _ => false

theorem spin_c_to_spin (segs : List Segment) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      spin_c segs fuel ms model = true → to_spin segs ms model := by
  intro fuel
  induction fuel with
  | zero =>
    intro ms model H
    simp only [spin_c] at H
    exact absurd H (by simp)
  | succ fuel ih =>
    intro ms model H
    simp only [spin_c] at H
    by_cases hj : is_self_jump segs ms = true
    · rw [ite_eq_left hj] at H
      exact is_self_jump_to_spin segs ms model hj
    · rw [ite_eq_right hj] at H
      cases hsvc : ms.ms_svc_pending with
      | some x8 =>
        rw [hsvc] at H
        exact absurd H (by simp)
      | none =>
        simp only [hsvc] at H
        split at H
        · rename_i ms' model' hacc
          exact .ts_step ms model ms' model' hsvc hacc (ih ms' model' H)
        · simp at H

/-- Close a `to_spin segs ms model` goal by execution, `fuel` steps
    deep.  Only for concrete states — see the `spin_c` note. -/
macro "prove_to_spin " fuel:term : tactic =>
  `(tactic| refine spin_c_to_spin _ ($fuel) _ _ (by decide))

/- =========================================================================
   Worked example 1: a toy two-branch obligation, in the shape of an
   mmap-refusal case-split
   ========================================================================= -/

/-- The toy: a configuration `c0` (think: the mmap ecall) with exactly
    two resolutions — a GRANT step emitting `evs_g` into a branch whose
    observations are the prefixes of `T` and which never errors, and a
    silent REFUSAL step into a spin.  Conclusion: the refusal branch
    changes NOTHING — the observation set from `c0` is exactly the
    prefixes of `evs_g ++ T`, and no error is reachable.  A real
    `MmapSim`-style proof runs the same three moves at its refusal arm:
    `spin_star_nil` on the tail star, `spin_no_sstep_error` /
    `spin_no_error_run` on the error reach, and the shared prefix is
    covered by the grant branch's prefix closure.
-/
theorem spin_branch_toy_obs_iff (segs : List Segment) (c0 c_g c_r : config)
    (evs_g T : List event) (P : config → Prop)
    (Hsplit : ∀ (evs : List event) (to : step_to), sstep segs c0 evs to →
      (evs = evs_g ∧ to = .SNext c_g) ∨ (evs = [] ∧ to = .SNext c_r))
    (Hstep_g : sstep segs c0 evs_g (.SNext c_g))
    (Hg_obs : ∀ tr, obs_trace segs c_g tr ↔ is_prefix tr T)
    (Hloop : silent_loop segs P) (HP_r : P c_r) :
    ∀ tr, obs_trace segs c0 tr ↔ is_prefix tr (evs_g ++ T) := by
  intro tr
  constructor
  · intro ⟨tr', cend, Hstar, Hpre⟩
    rcases star_case segs c0 tr' cend Hstar with ⟨h_tr, -⟩ | ⟨evs, c2, tr2, Hstep, Htail, h_tr⟩
    · subst h_tr
      rw [is_prefix_nil_inv tr Hpre]
      exact is_prefix_nil _
    · rcases Hsplit evs (.SNext c2) Hstep with ⟨hev, hto⟩ | ⟨hev, hto⟩
      · rw [h_tr, hev] at Hpre
        cases hto
        have Hobs2 : obs_trace segs c_g tr2 := ⟨tr2, cend, Htail, is_prefix_refl tr2⟩
        exact is_prefix_trans Hpre (is_prefix_app_mono evs_g ((Hg_obs tr2).mp Hobs2))
      · rw [h_tr, hev] at Hpre
        cases hto
        rw [silent_loop_star_nil segs P c_r tr2 cend Hloop HP_r Htail, List.append_nil] at Hpre
        rw [is_prefix_nil_inv tr Hpre]
        exact is_prefix_nil _
  · intro Hpre
    obtain ⟨tr'', cend, Hstar, HpreT⟩ := (Hg_obs T).mpr (is_prefix_refl T)
    exact ⟨evs_g ++ tr'', cend, star.step c0 evs_g c_g tr'' cend Hstep_g Hstar,
      is_prefix_trans Hpre (is_prefix_app_mono evs_g HpreT)⟩

theorem spin_branch_toy_no_error (segs : List Segment) (c0 c_g c_r : config)
    (evs_g : List event) (P : config → Prop)
    (Hsplit : ∀ (evs : List event) (to : step_to), sstep segs c0 evs to →
      (evs = evs_g ∧ to = .SNext c_g) ∨ (evs = [] ∧ to = .SNext c_r))
    (Hg_noerr : ¬ reaches_error segs c_g)
    (Hloop : silent_loop segs P) (HP_r : P c_r) :
    ¬ reaches_error segs c0 := by
  intro ⟨tr, cerr, evs, Hstar, Herr⟩
  rcases star_case segs c0 tr cerr Hstar with ⟨h_tr, h_c⟩ | ⟨evs1, c2, tr2, Hstep, Htail, -⟩
  · subst h_tr
    subst h_c
    rcases Hsplit evs .SError Herr with ⟨-, hto⟩ | ⟨-, hto⟩ <;> cases hto
  · rcases Hsplit evs1 (.SNext c2) Hstep with ⟨-, hto⟩ | ⟨-, hto⟩ <;> cases hto
    · exact Hg_noerr ⟨tr2, cerr, evs, Htail, Herr⟩
    · exact silent_loop_no_error segs P c_r Hloop HP_r ⟨tr2, cerr, evs, Htail, Herr⟩

/- =========================================================================
   Worked example 2: the literal `j .` binary, end to end
   ========================================================================= -/

/- A concrete image whose single instruction is the 4-byte `j .`
   encoding 0x0000006f (bytes 6f 00 00 00) in an r-x segment, entered
   at its base: the run emits nothing, never errors, and cannot take
   the vacuity escape — for EVERY entry, limit and input.  This pins
   the whole executable layer (fetch, decode, the x0/imm=0 test, the
   empty access report) against the real encoding. -/
namespace SelfJumpImage

def spin_seg : Segment :=
  { seg_base := 0x10000, seg_size := 4, seg_perms := "r-x", seg_bytes := ["6f000000"] }

def spin_segs : List Segment := [spin_seg]

def spin_img : Image := ⟨spin_segs, 0x10000, ⟨0x10040, 56, 6⟩⟩

theorem j_dot_decodes :
    decodeAny (BitVec.ofInt 32 0x6f) = some (Instr.jal 0 (BitVec.ofInt 21 0), 4) := by
  decide

theorem spin_img_to_spin (sp brk0 mbase : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) :
    to_spin spin_segs
      (init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩ sp rnd
        inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved spin_segs) brk0 mbase sp lim inp) := by
  refine ts_spin_of_step_j spin_segs _ _ (BitVec.ofInt 32 0x6f) 0 (BitVec.ofInt 21 0) 4
    rfl ?_ ?_ ?_ ?_ ?_
  · show fetch_word spin_segs (BitVec.ofInt 64 (Int.ofNat 0x10000))
      = some (BitVec.ofInt 32 0x6f)
    decide
  · decide
  · exact j_dot_decodes
  · decide
  · decide

theorem spin_img_obs_iff (lim : Int) (en : ExecEntry) (inp : ProcInput) (tr : List event) :
    bh_traces (run spin_img lim en inp) tr ↔ tr = [] := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  simp only [run, spin_img, init_config]
  exact spin_obs_iff spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl tr

theorem spin_img_no_error (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run spin_img lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  simp only [run, spin_img, init_config]
  exact spin_no_error_run spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl

theorem spin_img_not_all_errors (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_all_errors (run spin_img lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  simp only [run, spin_img, init_config]
  exact spin_not_all_errors spin_segs _ _ (spin_img_to_spin sp brk0 mbase rnd lim inp) rfl

/-- The executable path closes the same goal by computation when the
    inputs are concrete. -/
theorem spin_img_to_spin_by_execution :
    to_spin spin_segs
      (init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩
        (BitVec.ofInt 64 65536) ⟨BitVec.ofInt 128 0, fun _ => BitVec.ofInt 8 0⟩
        [[]] [] (BitVec.ofInt 64 1000) hwcap_rv64gc)
      (init_model (segments_reserved spin_segs) (BitVec.ofInt 64 1048576)
        (BitVec.ofInt 64 0x7fff7f800000) (BitVec.ofInt 64 65536) 0x40000000
        (mkProcInput [[]] [] [] IEof (BitVec.ofInt 64 1000) (BitVec.ofInt 64 1002) []
          net_silent default_nofile (BitVec.ofInt 64 0) hwcap_rv64gc false .Sv48)) := by
  prove_to_spin 1

/-! ## Sanity checks

    The decidable self-jump test is exercised end-to-end by
    `spin_img_to_spin_by_execution`; these pin the individual cases. -/

section Sanity

/-- `jal x0, 0` is the self-jump. -/
example : self_jump_instr (Instr.jal 0 0) = true := by decide

/-- A nonzero link register is not. -/
example : self_jump_instr (Instr.jal 1 0) = false := by decide

/-- A nonzero offset is not. -/
example : self_jump_instr (Instr.jal 0 4) = false := by decide

/-- Any other instruction is not. -/
example : self_jump_instr (Instr.lui 0 0) = false := by decide

/-- The image's single instruction IS the self-jump, at the entry state. -/
example :
    is_self_jump spin_segs
      (init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩
        (BitVec.ofInt 64 65536) ⟨BitVec.ofInt 128 0, fun _ => BitVec.ofInt 8 0⟩
        [[]] [] (BitVec.ofInt 64 1000) hwcap_rv64gc) = true := by
  decide

/-- A pending syscall short-circuits the test, as `is_self_jump`'s first
    match says. -/
example :
    is_self_jump spin_segs
      ({ init_machine_state spin_segs 0x10000 ⟨0x10040, 56, 6⟩
          (BitVec.ofInt 64 65536) ⟨BitVec.ofInt 128 0, fun _ => BitVec.ofInt 8 0⟩
          [[]] [] (BitVec.ofInt 64 1000) hwcap_rv64gc with
        ms_svc_pending := some 0 }) = false := by
  decide

end Sanity

end SelfJumpImage

end LinuxSem.Common.DivergeSim

