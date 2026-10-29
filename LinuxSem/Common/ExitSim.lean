/-
  * Common.ExitSim — reusable trace-semantics infrastructure for
    "exit-only" binaries (no observable I/O before the terminating
    exit/exit_group syscall), built on the star-based LinuxProcessSem.Run
    semantics.

  TRUST BOUNDARY: this file is part of the shared proof library, not
  the trusted specification.  It is image-INDEPENDENT: every lemma is generic over the
  loaded segments `segs` and the exit code `code`, so it is shared by all
  exit-only proofs.

  Exit codes and syscall numbers are `word = BitVec 64`, memory bytes are
  `byte = BitVec 8`, and the exit-number dispatch tests are `==` over
  `toNat` (mirroring the `Specs` dispatcher).  `N.land code 255`
  is `code &&& BitVec.ofInt 64 255`.  Stack-offset bookkeeping in the
  overlay lemmas is characterized in `Int` over unsigned values, so no
  no-wrap side conditions are needed.

  STRUCTURE.  An exit-only binary runs a finite, deterministic straight
  line of machine instructions and then executes `exit`/`exit_group`.  We
  capture that straight line with an inductive `to_exit segs code ms`
  ("`ms` deterministically reaches an exit ecall carrying code `code`"),
  prove it holds by a `decide`-checkable Fixpoint `sim_c`, read it
  as the omni judgment `to_exit_exec` (`OmniRun.exec` with the exact
  trace and exit code as postcondition), and from that one judgment
  derive:

  - `obs_trace` of the run is exactly the prefixes of
    `[ExitEv (code &&& BitVec.ofInt 64 255) (in_fs inp)]` (exit_obs_iff), and
  - the run can NEVER take the explicit error transition
    (`¬ reaches_error`; exit_no_error_run).

  The two facts combine into the `Equivalence.equiv` the `Equivalence`
  functor grades (exit_strong_equiv): two exit-only binaries that reach
  the same exit code are observably equivalent (neither errors).

  NOTES.

  - `Section WithSegs`'s two `Variable`s (`segs`, `code`) become EXPLICIT
    LEADING PARAMETERS on every declaration that mentions them, in that
    order — the same convention `Run.lean`, `OmniRun.lean` and
    `OmniEquivalence.lean` follow for their sections.
  - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` record constructor
    `⟨sp, brk0, mb, rnd⟩`.
  - `RiscvSemantics.step segs ms` is `RiscvSemantics.step segs ms` here
    too (this tree keeps `mi_loaded_segments` explicit), but the
    interpreter reads the loaded segments out of the machine's own `ms_rom`
    for `step_accesses`; both spellings are this tree's.
  - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_and` is `&&&`,
    `bv_unsigned w` is `(w.toNat : Int)`, `Z.eqb a b` is `a == b`,
    `nth_error` is `List.getElem?` (`bytes[i]?`), `length` is
    `List.length`, `lia` is `omega`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv

set_option autoImplicit false

namespace LinuxSem.Common.ExitSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv

/- =========================================================================
   Exit-syscall spec facts, derived directly from the relational spec.

   For a SyscallInput whose number is 93 (exit) or 94 (exit_group) the
   dispatcher routes to `exit_spec`, which has EXACTLY ONE outcome shape:
   halt the model at `code &&& 255`, no writes, no events.  We read those
   facts below keep this proof infrastructure independent of the executable
   checker representation.
   ========================================================================= -/

/-- The two syscall numbers the exit path answers to. -/
def is_exit_no (no : word) : Prop :=
  (no.toNat : Int) = 93 ∨ (no.toNat : Int) = 94

/-! ### The dispatcher's answer at 93 and 94

    The table carries `arm 93 (fun i => exit_spec (in_arg i 0))` and
    `arm 94 (fun i => exit_spec (in_arg i 0))`; both entries are read off
    `SyscallTable.spec_table`, so the two lemmas below compute the lookup
    rather than restating the table. -/

theorem lookup_arm_93 :
    lookup_arm spec_table (93 : Int) = some (arm 93 (fun i => exit_spec (in_arg i 0))) := by
  simp [lookup_arm, spec_table, arm]

theorem lookup_arm_94 :
    lookup_arm spec_table (94 : Int) = some (arm 94 (fun i => exit_spec (in_arg i 0))) := by
  simp [lookup_arm, spec_table, arm]

theorem syscall_spec_exit (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    is_exit_no i.in_sysno →
    (syscall_spec i m o ↔ exit_spec (in_arg i 0) i m o) := by
  intro H
  unfold syscall_spec dispatch
  rcases H with E | E
  · rw [E, lookup_arm_93]
    show (arm 93 (fun i => exit_spec (in_arg i 0))).sa_spec i m o ↔ _
    rfl
  · rw [E, lookup_arm_94]
    show (arm 94 (fun i => exit_spec (in_arg i 0))).sa_spec i m o ↔ _
    rfl

/-- …and that outcome is the ONLY one. -/
theorem exit_spec_ok_inv (code : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : exit_spec code i m (.ok eff m' evs)) :
    eff = mkEffect (BitVec.ofInt 64 0) [] [] ∧
    m' = with_halted (code &&& BitVec.ofInt 64 255) m ∧ evs = [] := by
  unfold exit_spec seqSpec modifySpec ret_only at H
  simp only [LinuxSem.LinuxProcessSem.bind,
             LinuxSem.LinuxProcessSem.modify,
             LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
  obtain ⟨x, m1, evs1, evs2, h1, h2, h3⟩ := H
  obtain ⟨-, hm1, hevs1⟩ := h1
  obtain ⟨heff, hm', hevs2⟩ := h2
  refine ⟨heff, ?_, ?_⟩
  · rw [hm', hm1]
  · rw [h3, hevs1, hevs2]
    rfl

/-- The unique admissible exit outcome exists. -/
theorem exit_dispatch_ok (i : SyscallInput) (m : Model) :
    is_exit_no i.in_sysno →
    (syscall_spec i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (in_arg i 0 &&& BitVec.ofInt 64 255) m) [])) := by
  intro Hno
  exact (syscall_spec_exit i m _ Hno).mpr (exit_spec_ok _ _ _)

/-- Every admissible exit outcome IS that unique one. -/
theorem exit_dispatch_ok_inv (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    is_exit_no i.in_sysno →
    syscall_spec i m (.ok eff m' evs) →
    (eff = mkEffect (BitVec.ofInt 64 0) [] [] ∧
     m' = with_halted (in_arg i 0 &&& BitVec.ofInt 64 255) m ∧ evs = []) := by
  intro Hno Hspec
  exact exit_spec_ok_inv _ _ _ _ _ _ ((syscall_spec_exit i m _ Hno).mp Hspec)

/-- Exit never takes the error transition. -/
theorem exit_dispatch_no_unmodeled (i : SyscallInput) (m : Model) :
    (is_exit_no i.in_sysno → ¬ syscall_spec i m .unmodeled) := by
  intro Hno Hspec
  have H := (syscall_spec_exit i m _ Hno).mp Hspec
  unfold exit_spec seqSpec modifySpec ret_only at H
  simp only [LinuxSem.LinuxProcessSem.bind,
             LinuxSem.LinuxProcessSem.modify,
             LinuxSem.LinuxProcessSem.pure, reduceCtorEq] at H
  rcases H with h | ⟨x, m1, evs1, h1, h2⟩
  · exact h
  · exact h2

/-- `in_arg (sys_input segs ms x8) 0` is `ms_gpr ms 0` (a0). -/
theorem in_arg0_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

/-- `in_sysno (sys_input segs ms x8) = x8`. -/
theorem in_sysno_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

/- =========================================================================
   `WithSegs`: the deterministic straight line to the exit ecall, and the
   one-step inversions it needs.
   ========================================================================= -/

/-- `to_exit segs code ms`: `ms` deterministically reaches an exit ecall
    carrying code `code`.  Either the pending syscall already IS
    exit/exit_group with `a0 = code`, or the next instruction steps
    (silently, successfully) to a state that does. -/
inductive to_exit (segs : List Segment) (code : word) : machine_state → Prop where
  /-- The pending syscall is exit/exit_group and `a0` carries `code`. -/
  | te_here (ms : machine_state) (x8 : word) :
      ms.ms_svc_pending = some x8 →
      is_exit_no x8 →
      ms_gpr ms 0 = code →
      to_exit segs code ms
  /-- One deterministic, successful, non-syscall instruction. -/
  | te_step (ms ms' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_exit segs code ms' →
      to_exit segs code ms

/-- `sim_c segs code fuel ms`: a fuel-bounded executable witness for
    `to_exit segs code ms`, closed by `decide` for a
    concrete straight-line binary. -/
def sim_c (segs : List Segment) (code : word) : Nat → machine_state → Bool
  | 0, _ => false
  | fuel + 1, ms =>
    match ms.ms_svc_pending with
    | some x8 =>
        (((x8.toNat : Int) == 93) || ((x8.toNat : Int) == 94)) &&
          bv_eqb (ms_gpr ms 0) code
    | none =>
      match RiscvSemantics.step segs ms with
      | .MachineOk ms' => sim_c segs code fuel ms'
      | .MachineFault => false
      | .MachineUnmodeled => false

theorem sim_c_to_exit (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state),
      sim_c segs code fuel ms = true → to_exit segs code ms := by
  intro fuel
  induction fuel with
  | zero =>
    intro ms H
    simp only [sim_c] at H
    exact absurd H (by simp)
  | succ fuel ih =>
    intro ms H
    simp only [sim_c] at H
    rcases hsvc : ms.ms_svc_pending with _ | x8
    · simp only [hsvc] at H
      split at H
      · rename_i ms' hstep
        exact to_exit.te_step ms ms' hsvc hstep (ih ms' H)
      · simp at H
      · simp at H
    · simp only [hsvc, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at H
      obtain ⟨Hx8, Hgpr⟩ := H
      refine to_exit.te_here ms x8 hsvc ?_ ?_
      · rcases Hx8 with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact beq_iff_eq.mp (by simpa only [bv_eqb] using Hgpr)

/- =========================================================================
   Propositional-execution bridges into `sim_c`.

   When the source reads argv memory we cannot `decide` `sim_c`
   (argv is symbolic).  Instead we chain the per-instruction `step_*`
   lemmas from `Common.PropExec` one `sim_c` step at a time via `sim_step`,
   and close at the terminating ecall via `sim_ecall_exit`.
   ========================================================================= -/

/-- One executable step: an ordinary (non-syscall) instruction. -/
theorem sim_step (segs : List Segment) (code : word) (fuel : Nat)
    (ms ms' : machine_state) :
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    sim_c segs code fuel ms' = true →
    sim_c segs code (fuel + 1) ms = true := by
  intro Hsvc Hstep Hrec
  simp only [sim_c, Hsvc, Hstep]
  exact Hrec

/-- A configuration whose pending syscall is exit/exit_group with `a0 = code`
    passes `sim_c` immediately.  Scrutinee stays a variable so `simp` does not
    over-reduce the register lookups. -/
theorem sim_c_exit_now (segs : List Segment) (code : word) (fuel : Nat)
    (ms : machine_state) (x8 : word) :
    ms.ms_svc_pending = some x8 →
    (((x8.toNat : Int) == 93) || ((x8.toNat : Int) == 94)) = true →
    bv_eqb (ms_gpr ms 0) code = true →
    sim_c segs code (fuel + 1) ms = true := by
  intro Hsvc Hx8 Hcode
  simp only [sim_c, Hsvc, Hx8, Bool.true_and]
  exact Hcode

/-- Closing the run: at `ms` (svc not pending), the next instruction is the
    `ecall` (0x73); a7 selects exit/exit_group and a0 carries `code`. -/
theorem sim_ecall_exit (segs : List Segment) (code : word) (fuel : Nat)
    (ms : machine_state) :
    ms.ms_svc_pending = none →
    fetch_word segs (ms_pc ms) = some (BitVec.ofInt 32 0x73) →
    (((ms_reg ms 17).toNat : Int) == 93 || ((ms_reg ms 17).toNat : Int) == 94) = true →
    bv_eqb (ms_gpr ms 0) code = true →
    sim_c segs code (fuel + 1 + 1) ms = true := by
  intro Hsvc Hfetch Hcheck Hcode
  have hecall : is_ecall (BitVec.ofInt 32 0x73) = true := by decide
  let ms1 : machine_state := { ms with ms_svc_pending := some (ms_reg ms 17) }
  have hstep : RiscvSemantics.step segs ms = .MachineOk ms1 := by
    show drop_access_report (step_accesses segs ms) = .MachineOk ms1
    simp only [step_accesses, Hfetch, decode_exec_accesses, hecall, ite_eq_left,
      drop_access_report, mkAccessReport]
    rfl
  refine sim_step segs code (fuel + 1) ms ms1 Hsvc hstep ?_
  exact sim_c_exit_now segs code fuel ms1 (ms_reg ms 17) rfl Hcheck Hcode

/- =========================================================================
   One-step inversions of `sstep` on the two kinds of on-path configs.
   ========================================================================= -/

/-- From a non-syscall state that steps to `ms'`, the ONLY transition is the
    deterministic instruction step; no events, no error. -/
theorem sstep_instr_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (evs : List event) (st : step_to) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    sstep segs ⟨ms, model⟩ evs st →
    (evs = [] ∧ st = .SNext ⟨ms', model⟩) := by
  intro Hlazy Hsvc Hstep Hss
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    have hacc' := hacc
    rw [mi_account_step_no_lazy segs ms model Hlazy] at hacc'
    rw [Hstep] at hacc'
    cases hacc'
    exact ⟨rfl, rfl⟩
  | instr_fault ms0 model0 hh hsvc hacc =>
    exfalso
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hacc
    exact nomatch hacc
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
    exfalso
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hacc
    exact nomatch hacc
  | syscall ms0 model0 x8 eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff model1 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | exit ms0 model0 x8 eff model1 evs0 code hh hsvc hspec hh' hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | killed ms0 model0 x8 eff model1 evs0 sig hh hsvc hspec hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_unmodeled ms0 model0 x8 hh hsvc hspec =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)

/-- From an exit ecall config, the ONLY transition is `sstep.exit`: it emits
    the single `ExitEv` and halts the model. -/
theorem sstep_exit_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to) :
    m_halted model = none →
    ms.ms_svc_pending = some x8 →
    is_exit_no x8 →
    sstep segs ⟨ms, model⟩ evs st →
    (evs = [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)] ∧
     st = .SNext ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩) := by
  intro Hh Hsvc Hx8 Hss
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault ms0 model0 hh hsvc hacc =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x8' eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
    -- the syscall arm's post-model is halted, contradicting `hh'`
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    have hxe : is_exit_no (sys_input segs ms x8').in_sysno := by
      rw [in_sysno_sys_input]; exact hx ▸ Hx8
    obtain ⟨-, hm', -⟩ :=
      exit_dispatch_ok_inv (sys_input segs ms x8') model eff model1 evs hxe hspec
    rw [hm'] at hh'
    simp at hh'
  | syscall_materialization_fault ms0 model0 x8' eff model1 evs0 hh hsvc hspec hh' hmat =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    have hxe : is_exit_no (sys_input segs ms x8').in_sysno := by
      rw [in_sysno_sys_input]; exact hx ▸ Hx8
    obtain ⟨-, hm', -⟩ :=
      exit_dispatch_ok_inv (sys_input segs ms x8') model eff model1 evs0 hxe hspec
    rw [hm'] at hh'
    simp at hh'
  | exit ms0 model0 x8' eff model1 evs0 code hh hsvc hspec hh' hk =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    have hxe : is_exit_no (sys_input segs ms x8').in_sysno := by
      rw [in_sysno_sys_input]; exact hx ▸ Hx8
    obtain ⟨-, hm', hevs⟩ :=
      exit_dispatch_ok_inv (sys_input segs ms x8') model eff model1 evs0 hxe hspec
    rw [in_arg0_sys_input] at hm'
    rw [hm'] at hh'
    have hcode : code = (ms_gpr ms 0 &&& BitVec.ofInt 64 255) :=
      (Option.some.inj (by simpa using hh')).symm
    refine ⟨?_, ?_⟩
    · rw [hevs, hcode, hm']
      simp
    · rw [hm']
  | killed ms0 model0 x8' eff model1 evs0 sig hh hsvc hspec hk =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    have hxe : is_exit_no (sys_input segs ms x8').in_sysno := by
      rw [in_sysno_sys_input]; exact hx ▸ Hx8
    obtain ⟨-, hm', -⟩ :=
      exit_dispatch_ok_inv (sys_input segs ms x8') model eff model1 evs0 hxe hspec
    rw [hm'] at hk
    simp at hk
  | syscall_unmodeled ms0 model0 x8' hh hsvc hspec =>
    exfalso
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    exact exit_dispatch_no_unmodeled (sys_input segs ms x8') model (by
      rw [in_sysno_sys_input]; exact hx ▸ Hx8) hspec

/-- A run cannot leave a halted config. -/
theorem star_halted_nil (segs : List Segment) (c : config) (tr : List event)
    (c' : config) :
    m_halted c.cfg_model ≠ none → star segs c tr c' → (tr = [] ∧ c' = c) := by
  intro Hh Hstar
  cases Hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step c1 evs c2 tr0 c3 hss hstar =>
    exact absurd (sstep_from_running segs c evs (.SNext c2) hss) Hh

/- =========================================================================
   The omni reading: one induction over `to_exit` gives the exact trace,
   termination and error-freedom at once.
   ========================================================================= -/

/-- The postcondition of an exit-only run: the trace is exactly the single
    `ExitEv` at the masked code, and the run exits with that code. -/
def exit_post (code : word) (fs : Fs.Fs) : post :=
  fun tr o => tr = [event.ExitEv (code &&& BitVec.ofInt 64 255) fs] ∧
              exits_with (code &&& BitVec.ofInt 64 255) tr o

theorem to_exit_exec (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    to_exit segs code ms →
    exec segs ⟨ms, model⟩ (exit_post code (m_fs model)) := by
  intro Hh Hlazy Hte
  induction Hte with
  | te_here ms0 x8 Hsvc Hx8 Hgpr =>
    -- te_here: the one transition is the exit, into the halted configuration
    refine exec_step_only segs ⟨ms0, model⟩ (exit_post code (m_fs model))
      [event.ExitEv (ms_gpr ms0 0 &&& BitVec.ofInt 64 255)
        (m_fs (with_halted (ms_gpr ms0 0 &&& BitVec.ofInt 64 255) model))]
      ⟨ms0, with_halted (ms_gpr ms0 0 &&& BitVec.ofInt 64 255) model⟩ ?_ ?_ ?_
    · exact sstep.exit ms0 model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms0 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms0 0 &&& BitVec.ofInt 64 255) Hh Hsvc
        (exit_dispatch_ok (sys_input segs ms0 x8) model (by
          rw [in_sysno_sys_input]; exact Hx8)) rfl rfl
    · intro evs st hss
      obtain ⟨h1, h2⟩ :=
        sstep_exit_inv segs ms0 model x8 evs st Hh Hsvc Hx8 hss
      refine ⟨?_, h2⟩
      rw [h1]
      simp [m_fs_with_halted]
    · refine exec_halted segs ⟨ms0, with_halted (ms_gpr ms0 0 &&& BitVec.ofInt 64 255) model⟩
        _ ?_ ?_
      · simp [m_halted_with_halted]
      · refine ⟨?_, ?_, ?_⟩
        · rw [← Hgpr]
          simp [m_fs_with_halted]
        · rw [← Hgpr]
          simp [m_halted_with_halted]
        · simp [m_killed_with_halted]
  | te_step ms0 ms1 Hsvc Hstep Hte' ih =>
    -- te_step: one silent instruction
    refine exec_step_only segs ⟨ms0, model⟩ (exit_post code (m_fs model)) []
      ⟨ms1, model⟩ ?_ ?_ ?_
    · refine sstep.instr ms0 model ms1 model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms0 model Hlazy, Hstep]
    · intro evs st hss
      exact sstep_instr_inv segs ms0 model ms1 evs st Hlazy Hsvc Hstep hss
    · simpa using ih

/-- A derived trace is empty or exactly the single `ExitEv`. -/
private theorem append_eq_singleton {α : Type} {l1 l2 : List α} {a : α}
    (h : l1 ++ l2 = [a]) : l1 = [a] ∨ l1 = [] := by
  cases l1 with
  | nil => exact Or.inr rfl
  | cons x xs =>
    refine Or.inl ?_
    have h' : x :: (xs ++ l2) = a :: [] := h
    injection h' with hx hxs
    have hnil : xs = [] := (List.append_eq_nil_iff.mp hxs).1
    rw [hx, hnil]

theorem to_exit_star_only (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    to_exit segs code ms →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      (tr = [] ∨ tr = [event.ExitEv (code &&& BitVec.ofInt 64 255) (m_fs model)]) := by
  intro Hh Hlazy Hte tr c Hstar
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ tr c
      (to_exit_exec segs code ms model Hh Hlazy Hte) Hstar)
  obtain ⟨Heq, -⟩ := HQ
  rcases append_eq_singleton Heq with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem to_exit_star_admits (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    to_exit segs code ms →
    ∃ c, star segs ⟨ms, model⟩
      [event.ExitEv (code &&& BitVec.ofInt 64 255) (m_fs model)] c := by
  intro Hh Hlazy Hte
  obtain ⟨tr, o, Hm, HQ⟩ :=
    exec_realizes segs _ _ (to_exit_exec segs code ms model Hh Hlazy Hte)
  rcases o with c' | c'
  · obtain ⟨Heq, -⟩ := HQ
    obtain ⟨Hstar, -⟩ := mexec_halt_star segs ⟨ms, model⟩ tr (.OHalt c') Hm c' rfl
    exact ⟨c', by rw [← Heq]; exact Hstar⟩
  · exfalso
    exact HQ.2

/- =========================================================================
   No-error characterization: no reachable config takes the error step.
   ========================================================================= -/

/-- On-path invariant: a reachable config is either still on the straight
    line (model not halted, `to_exit` holds) or already halted. -/
def on_path (segs : List Segment) (code : word) (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧
   to_exit segs code c.cfg_ms)
  ∨ m_halted c.cfg_model ≠ none

theorem on_path_step (segs : List Segment) (code : word) (c : config)
    (evs : List event) (c' : config) :
    on_path segs code c → sstep segs c evs (.SNext c') → on_path segs code c' := by
  intro Hop Hss
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hop with ⟨Hh, Hlazy, Hte⟩ | Hh
  · cases Hte with
    | te_here ms0 x8 Hsvc Hx8 Hgpr =>
      obtain ⟨-, hc'⟩ :=
        sstep_exit_inv segs ms model x8 evs (.SNext ⟨ms', model'⟩) Hh Hsvc Hx8 Hss
      cases hc'
      exact Or.inr (by simp [m_halted_with_halted])
    | te_step ms0 ms0' Hsvc Hstep Hte' =>
      obtain ⟨-, hc'⟩ :=
        sstep_instr_inv segs ms model ms0' evs (.SNext ⟨ms', model'⟩) Hlazy Hsvc Hstep Hss
      cases hc'
      exact Or.inl ⟨Hh, Hlazy, Hte'⟩
  · -- already halted: no sstep possible
    exact absurd (sstep_from_running segs ⟨ms, model⟩ evs (.SNext ⟨ms', model'⟩) Hss) Hh

theorem on_path_no_error (segs : List Segment) (code : word) (c : config)
    (evs : List event) :
    on_path segs code c → ¬ sstep segs c evs .SError := by
  intro Hop Hss
  obtain ⟨ms, model⟩ := c
  rcases Hop with ⟨Hh, Hlazy, Hte⟩ | Hh
  · cases Hte with
    | te_here ms0 x8 Hsvc Hx8 Hgpr =>
      obtain ⟨-, hc⟩ := sstep_exit_inv segs ms model x8 evs .SError Hh Hsvc Hx8 Hss
      simp at hc
    | te_step ms0 ms0' Hsvc Hstep Hte' =>
      obtain ⟨-, hc⟩ :=
        sstep_instr_inv segs ms model ms0' evs .SError Hlazy Hsvc Hstep Hss
      simp at hc
  · exact Hh (sstep_from_running segs ⟨ms, model⟩ evs .SError Hss)

theorem star_on_path (segs : List Segment) (code : word) (c : config)
    (tr : List event) (c' : config) :
    on_path segs code c → star segs c tr c' → on_path segs code c' :=
  star_inv segs (on_path segs code) (on_path_step segs code) c tr c'

theorem to_exit_no_error (segs : List Segment) (code : word) (ms : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    to_exit segs code ms →
    ¬ reaches_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hte
  refine exec_no_error segs ⟨ms, model⟩ ?_
  refine exec_conseq segs ⟨ms, model⟩ (exit_post code (m_fs model)) never_errors
    (to_exit_exec segs code ms model Hh Hlazy Hte) ?_
  intro tr o h
  exact exits_with_never_errors _ _ _ h.2

/- =========================================================================
   Overlay + enumerate: closing `sim_c` for binaries that read only argc.

   The source binary reads argc (the first 8 stack bytes) and branches on
   it.  To let `decide` close `sim_c` for ALL argv, we replace the
   symbolic stack memory by an "overlay": the first 8 bytes are the concrete
   little-endian encoding of `argc`, every other address defers to an
   unevaluated base function.  Enumerating argc over its valid range
   (0..1024, from `valid_argv`) then discharges every case by computation,
   because the binary only ever reads those 8 concrete bytes.  All lemmas are
   image-INDEPENDENT (generic over segs/init_pc/init_sp/argv/envp).

   The address tests are `==` over unsigned values:
   `sp.toNat + k` cannot wrap in `Int`, so the overlay equals the real
   initial memory for EVERY `sp`, including the (unreachable) top-of-address-
   space corner where `sp + k` would wrap under `BitVec` addition.
   ========================================================================= -/

/-- The overlay: `argc`'s eight little-endian bytes at `sp + 0 … sp + 7`,
    and the given base memory everywhere else. -/
def overlay_argc_bytes (sp : word) (argc : Nat)
    (base_mem : word → Option byte) : word → Option byte :=
  let bytes := word_le8 (nat_to_word argc)
  fun addr =>
    if (addr.toNat : Int) == (sp.toNat : Int) then bytes[0]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 1 then bytes[1]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 2 then bytes[2]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 3 then bytes[3]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 4 then bytes[4]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 5 then bytes[5]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 6 then bytes[6]?
    else if (addr.toNat : Int) == (sp.toNat : Int) + 7 then bytes[7]?
    else base_mem addr

/-- Inside the image, at the offset `i`, `stack_to_mem` answers byte `i`. -/
theorem stm_at (sp : word) (bytes : List byte) (addr : word) (i : Nat)
    (Hi : i < bytes.length)
    (Haddr : (addr.toNat : Int) = (sp.toNat : Int) + (i : Int)) :
    stack_to_mem sp bytes addr = bytes[i]? := by
  unfold stack_to_mem
  have hcast : addr.toNat = sp.toNat + i := by omega
  rw [hcast]
  rw [ite_eq_left (Nat.le_add_right sp.toNat i)]
  dsimp only
  have hoff : (((sp.toNat + i : Nat) : Int) - ((sp.toNat : Nat) : Int)) = (i : Int) := by
    push_cast
    omega
  rw [hoff]
  rw [ite_eq_left (by omega : (i : Int) < (bytes.length : Int))]
  simp

/-- The initial stack image starts with the little-endian `argc` word. -/
theorem build_stack_starts_with_argc (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    ∃ rest, build_stack_bytes ph sp argv envp uid hw rnd
      = word_le8 (nat_to_word argv.length) ++ rest := by
  unfold build_stack_bytes
  simp only
  exact ⟨_, rfl⟩

theorem word_le8_length (v : word) : (word_le8 v).length = 8 := rfl

theorem build_stack_min_length (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    8 ≤ (build_stack_bytes ph sp argv envp uid hw rnd).length := by
  obtain ⟨rest, hr⟩ := build_stack_starts_with_argc ph sp argv envp uid hw rnd
  rw [hr, List.length_append, word_le8_length]
  omega

/-- The `i`-th byte of the initial stack memory (i < 8) is the `i`-th byte of
    the little-endian argc.  Goes through this repo's zero-fallback wrapper.
    The address is characterized by its unsigned value (no wrap in `Int`). -/
theorem init_first8 (segs : List Segment) (init_pc : Nat) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argv envp : List (List byte))
    (addr : word) (i : Nat) (uid hw : word) (Hi : i < 8)
    (Haddr : (addr.toNat : Int) = (init_sp.toNat : Int) + (i : Int)) :
    (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem addr
      = (word_le8 (nat_to_word argv.length))[i]? := by
  have hmin : 8 ≤ (build_stack_bytes ph init_sp argv envp uid hw init_rnd).length :=
    build_stack_min_length ph init_sp argv envp uid hw init_rnd
  have Hstk : stack_to_mem init_sp
      (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
      = (word_le8 (nat_to_word argv.length))[i]? := by
    rw [stack_to_mem_image_in_block ph init_sp argv envp uid hw init_rnd addr (by
      unfold entry_block_top
      omega)]
    rw [stm_at init_sp (build_stack_bytes ph init_sp argv envp uid hw init_rnd) addr i
      (by omega) Haddr]
    obtain ⟨rest, hr⟩ := build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd
    rw [hr, List.getElem?_append_left (by rw [word_le8_length]; exact Hi)]
  change (match stack_to_mem init_sp
      (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
    | some b => some b
    | none =>
      if decide ((init_sp.toNat : Int) - stack_max_size ≤ (addr.toNat : Int)) &&
         decide ((addr.toNat : Int) < (init_sp.toNat : Int))
      then some (BitVec.ofInt 8 0) else none) = _
  rw [Hstk]
  cases h : (word_le8 (nat_to_word argv.length))[i]? with
  | none =>
    have hle := List.getElem?_eq_none_iff.mp h
    rw [word_le8_length] at hle
    omega
  | some b => rfl

/-- The real initial memory IS the overlay at `argc := argv.length` with
    itself as the base. -/
theorem actual_mem_is_overlay (segs : List Segment) (init_pc : Nat) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) :
    (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem
      = overlay_argc_bytes init_sp argv.length
          (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem := by
  funext addr
  unfold overlay_argc_bytes
  by_cases h0 : ((addr.toNat : Int) == (init_sp.toNat : Int)) = true
  · rw [ite_eq_left h0]
    exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw (by omega)
      (beq_iff_eq.mp h0)
  · rw [ite_eq_right h0]
    by_cases h1 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 1) = true
    · rw [ite_eq_left h1]
      exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw (by omega)
        (beq_iff_eq.mp h1)
    · rw [ite_eq_right h1]
      by_cases h2 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 2) = true
      · rw [ite_eq_left h2]
        exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw (by omega)
          (beq_iff_eq.mp h2)
      · rw [ite_eq_right h2]
        by_cases h3 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 3) = true
        · rw [ite_eq_left h3]
          exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw (by omega)
            (beq_iff_eq.mp h3)
        · rw [ite_eq_right h3]
          by_cases h4 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 4) = true
          · rw [ite_eq_left h4]
            exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw (by omega)
              (beq_iff_eq.mp h4)
          · rw [ite_eq_right h4]
            by_cases h5 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 5) = true
            · rw [ite_eq_left h5]
              exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw (by omega)
                (beq_iff_eq.mp h5)
            · rw [ite_eq_right h5]
              by_cases h6 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 6) = true
              · rw [ite_eq_left h6]
                exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw (by omega)
                  (beq_iff_eq.mp h6)
              · rw [ite_eq_right h6]
                by_cases h7 : ((addr.toNat : Int) == (init_sp.toNat : Int) + 7) = true
                · rw [ite_eq_left h7]
                  exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw
                    (by omega) (beq_iff_eq.mp h7)
                · rw [ite_eq_right h7]

/-- The machine state is its fields. -/
theorem machine_state_eta (ms : machine_state) :
    ms = { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms.ms_pc_val,
           ms_svc_pending := ms.ms_svc_pending, ms_resv := ms.ms_resv,
           ms_fcsr := ms.ms_fcsr, ms_mem := ms.ms_mem, ms_rom := ms.ms_rom } := by
  cases ms
  rfl

/-- The "enumeration state": structural fields from the (argv-independent)
    initial state, `ms_mem` replaced by an overlay with a FREE `argc`/base. -/
def enum_state (segs : List Segment) (init_pc : Nat) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argc : Nat)
    (base : word → Option byte) (uid hw : word) : machine_state :=
  { ms_regs := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_regs
    ms_fregs := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_fregs
    ms_pc_val := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_pc_val
    ms_svc_pending :=
      (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_svc_pending
    ms_resv := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_resv
    ms_fcsr := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_fcsr
    ms_mem := overlay_argc_bytes init_sp argc base
    ms_rom := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_rom }

/-- Bridge: the real initial state equals the enumeration state at
    `argc := argv.length` and `base := its own memory`. -/
theorem init_eq_enum_state (segs : List Segment) (init_pc : Nat) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) :
    init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw
      = enum_state segs init_pc ph init_sp init_rnd argv.length
          (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem
          uid hw := by
  unfold enum_state
  rw [← actual_mem_is_overlay segs init_pc ph init_sp init_rnd argv envp uid hw]
  rw [machine_state_eta
    (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)]
  rfl

/- =========================================================================
   Run-level packaging: the two facts, and the equivalence glue.
   ========================================================================= -/

/-- The run-level omni judgment of an exit-only binary. -/
theorem exit_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (code : word)
    (inp : ProcInput) (F : Nat) :
    sim_c segs code F
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (exit_post code (in_fs inp)) := by
  intro Hsim
  show exec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (exit_post code (in_fs inp))
  exact to_exit_exec segs code _ _ rfl rfl (sim_c_to_exit segs code F _ Hsim)

theorem exit_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (code : word)
    (inp : ProcInput) (F : Nat) :
    sim_c segs code F
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ is_prefix tr [event.ExitEv (code &&& BitVec.ofInt 64 255) (in_fs inp)] := by
  intro Hsim tr
  refine exec_obs_iff segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    [event.ExitEv (code &&& BitVec.ofInt 64 255) (in_fs inp)] ?_ tr
  refine exec_conseq segs _ _ _ (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) ?_
  intro tr' o h
  exact ⟨h.1, exits_with_never_errors _ _ _ h.2⟩

theorem exit_no_error_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (code : word)
    (inp : ProcInput) (F : Nat) :
    sim_c segs code F
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro Hsim
  refine exec_no_error segs _ ?_
  refine exec_conseq segs _ _ never_errors
    (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) ?_
  intro tr o h
  exact exits_with_never_errors _ _ _ h.2

/-- The code half of `exit_post`, consumed and pinned: the run satisfies
    `MustExit.must_exit_with` at the masked code, and at no other. -/
theorem exit_must_exit_with (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (code : word)
    (inp : ProcInput) (F : Nat) :
    sim_c segs code F
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    must_exit_with (code &&& BitVec.ofInt 64 255) (mkImage segs pc ph) lim
      ⟨sp, brk0, mb, rnd⟩ inp := by
  intro Hsim
  refine (must_exit_with_iff (code &&& BitVec.ofInt 64 255) (mkImage segs pc ph) lim
    ⟨sp, brk0, mb, rnd⟩ inp).mpr ?_
  refine exec_conseq segs _ _ _ (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) ?_
  intro tr o h
  exact h.2

theorem exit_omni_run_code_unique (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (code : word)
    (inp : ProcInput) (F : Nat) (code' : word) :
    sim_c segs code F
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp (exits_with code') →
    code' = (code &&& BitVec.ofInt 64 255) := by
  intro Hsim Hex
  have Hrun := exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim
  obtain ⟨tr, o, Hm, Hq⟩ := exec_realizes segs _ _ Hrun
  have Hx' := exec_sound segs _ _ Hex tr o Hm
  cases o with
  | OHalt c' =>
    obtain ⟨-, hxe⟩ := Hq
    exact Option.some.inj (Hx'.1.symm.trans hxe.1)
  | OError c' =>
    exact Hq.2.elim

/-- The omni equivalence for two exit-only binaries reaching the same
    exit code, at the two role budgets.  Trace agreement is the two
    `exit_obs_iff` instances under `OmniEquivalence.trace_equiv_iff_omni`
    (both runs have the same exact trace); the source's coverage and the
    target's error-freedom are `exit_omni_run` weakened. -/
theorem exit_omni_strong_equiv (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (code : word) (inp : ProcInput)
    (FR FA : Nat) :
    sim_c source_segs code FR
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    sim_c target_segs code FA
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  intro Hsource Htarget
  constructor
  · -- the source is covered: it never errors at all
    refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _ (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit code inp FR Hsource)) ?_
    intro tr o h
    exact never_errors_covered source_segs tr o (exits_with_never_errors _ _ _ h.2)
  · right
    constructor
    · -- trace agreement: both runs have the same exact trace
      refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
        code inp FR Hsource tr).trans
        (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit
          code inp FA Htarget tr).symm
    · refine (error_free_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact exit_no_error_run target_segs apc aph asp abrk amb arnd
        target_alloc_limit code inp FA Htarget

/-- The `Equivalence`-level equivalence for two exit-only binaries reaching
    the same exit code. -/
theorem exit_strong_equiv (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int) (code : word)
    (inp : ProcInput) (FR FA : Nat) :
    sim_c source_segs code FR
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    sim_c target_segs code FA
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) = true →
    (modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
     equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
           (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  intro Hsource Htarget
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource)
  · right
    constructor
    · intro tr
      exact (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR
        Hsource tr).trans
        (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA
          Htarget tr).symm
    · exact exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA
        Htarget

/-!  They are checks, not  lemmas. -/

section Sanity

/-- A machine state whose pending syscall is `x8` and whose `a0` is `code`. -/
private def msAtExit (code x8 : word) : machine_state :=
  { ms_regs := bvmapSet (BitVec.ofInt 5 10) code (bvmap_empty : BvMap word)
    ms_fregs := bvmap_empty
    ms_pc_val := 0
    ms_svc_pending := some x8
    ms_resv := none
    ms_fcsr := 0
    ms_mem := fun _ => none
    ms_rom := fun _ => none }

/-- Fuel 0 never witnesses anything. -/
example : sim_c [] (BitVec.ofInt 64 7) 0 (msAtExit (BitVec.ofInt 64 7) (BitVec.ofInt 64 93))
    = false := by decide

/-- A pending `exit` (93) with `a0 = code` passes immediately. -/
example : sim_c [] (BitVec.ofInt 64 7) 5 (msAtExit (BitVec.ofInt 64 7) (BitVec.ofInt 64 93))
    = true := by decide

/-- `exit_group` (94) does too. -/
example : sim_c [] (BitVec.ofInt 64 7) 5 (msAtExit (BitVec.ofInt 64 7) (BitVec.ofInt 64 94))
    = true := by decide

/-- A DIFFERENT `a0` does not. -/
example : sim_c [] (BitVec.ofInt 64 7) 5 (msAtExit (BitVec.ofInt 64 8) (BitVec.ofInt 64 93))
    = false := by decide

/-- Neither does a different syscall number. -/
example : sim_c [] (BitVec.ofInt 64 7) 5 (msAtExit (BitVec.ofInt 64 7) (BitVec.ofInt 64 63))
    = false := by decide

/-- The little-endian `argc` word is eight bytes, byte 0 lowest. -/
example : (word_le8 (nat_to_word 3)).length = 8 := by decide

example : (word_le8 (nat_to_word 3))[0]? = some (BitVec.ofInt 8 3) := by decide

example : (word_le8 (nat_to_word 3))[1]? = some (BitVec.ofInt 8 0) := by decide

/-- The overlay answers `argc`'s bytes at `sp + 0..7` and defers elsewhere. -/
example : overlay_argc_bytes (BitVec.ofInt 64 100) 3 (fun _ => none)
    (BitVec.ofInt 64 100) = some (BitVec.ofInt 8 3) := by decide

example : overlay_argc_bytes (BitVec.ofInt 64 100) 3 (fun _ => none)
    (BitVec.ofInt 64 101) = some (BitVec.ofInt 8 0) := by decide

example : overlay_argc_bytes (BitVec.ofInt 64 100) 3 (fun _ => none)
    (BitVec.ofInt 64 108) = none := by decide

/-- The offset characterization `stm_at` consumes: below the image, the byte
    is the list's byte. -/
example : stack_to_mem (BitVec.ofInt 64 100)
    (word_le8 (nat_to_word 3)) (BitVec.ofInt 64 101) = some (BitVec.ofInt 8 0) := by decide

/-- Above the image, nothing. -/
example : stack_to_mem (BitVec.ofInt 64 100)
    (word_le8 (nat_to_word 3)) (BitVec.ofInt 64 108) = none := by decide

/-- Below the base, nothing (the image is based AT `sp`). -/
example : stack_to_mem (BitVec.ofInt 64 100)
    (word_le8 (nat_to_word 3)) (BitVec.ofInt 64 99) = none := by decide

end Sanity

end LinuxSem.Common.ExitSim

