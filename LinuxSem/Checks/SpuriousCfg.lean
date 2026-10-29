/-
  * LinuxProcessSem.Checks.SpuriousCfg — the forced-only filter, on cases chosen by hand

  Not part of the trusted specification: this file is QA on
  [Run.SpuriousCfg], [Run.spurious_refusal_cfg] and [Run.sstep_cfg],
  written to be READ, in the manner of [Checks.Examples] and under the
  four admission reasons its header lists.  Every case here is one a
  single real run cannot show, and for one reason above all: a fold
  of the checker sees what the kernel DID, and the filter is
  a statement about what the kernel COULD HAVE DONE instead — whether
  a refusal was avoidable — which is not an observation of any one
  run (reason 4, and reason 3 where a fixture's budget or ledger is
  named).

  ** What is pinned, family by family

  - fs, never forced: [getcwd]'s -ENOMEM is spurious under forced-only
    and kept under may-fail; its -ERANGE, the answer the state
    determines, is kept under both.  At the STEP level this is the
    subset lemma's negative twin — [Run.sstep] admits the -ENOMEM
    step and [Run.sstep_cfg Run.forced_only_cfg] refuses it — with
    the -ERANGE step admitted on both sides as the positive twin.
  - cred, keyed on state: [setsid]'s -EPERM is spurious before a
    success and FORCED after one, because [Kernel.Sys.setsid_spec]
    answers it deterministically once [State.m_setsid_succeeded] is
    set.
  - alloc, keyed on the budget: an anonymous [mmap] within budget has
    its -ENOMEM removed; one beyond the budget keeps it, because the
    grant's [choose] has no witness there.  And an -ENOMEM the ARGUMENT
    gate determines — the overflowing MAP_FIXED length of
    [Checks.Cases.Mm.Mmap.mmap_fixed_overflowing_len_is_enomem] — is
    kept although it is in [Mmap.mmap_errnos], which is the exactness
    argument of [Run]'s spurious-failure header made concrete: the
    filter never removes an answer the state determines, whatever the
    list says.
  - the table itself: sorted, and every number in it dispatches.
  - run level: the exit-0 image must-exits under forced-only exactly
    as it does under may-fail, and the undecodable image refutes the
    predicate under forced-only as it does under may-fail — the two
    witnesses [MustExit]'s header points at, at the other reading.

  ---------------------------------------------------------------------
  FIXTURES PROVIDED.  Two later files are stated
  over fixtures defined HERE and nowhere else:

    getcwd_i         — the [getcwd] syscall input (sysno 17, all args 0)
    getcwd_ms        — the machine state it is taken at
    mmap_overflow_i  — the MAP_FIXED mmap whose length overflows

  [Checks.BudgetPremise] and [Checks.Omni] name these two, so they are
  part of this file's contract, not decoration.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n`, `Z_to_bv n z` is `BitVec.ofInt n z`, and `bv_unsigned a`
  is `a.toNat`.  `Record` fields are reached with dot notation, so
  `eff_ret eff` is `eff.eff_ret`.  `mkEffect r ws zs` is the
  abbreviation of that name (`mkEffectU r ws zs [] [] []`, the same
  three positional fields).  `Example name`
  checks keep their names as Lean `theorem`s.

  THE `Z`/`Nat` SYSCALL-NUMBER SPLIT.  `in_sysno`
  is a `bv 64` and the specification's tables are keyed by `Z`;
  [InjectedArm] (and `Sys.dispatch`) are keyed by `Nat` via `.toNat`, for
  the reason [Run]'s note gives: the unsigned value of a syscall number is
  non-negative.  Every check below is at a concrete number, so the two
  spellings agree.

  Closed computations / `check_eq` / `sys_destruct`.
  `check_eq` is the name for the `by decide` convention on a closed
  computation (see `Checks/Cases/Prelude`'s note); it closes every
  goal whose type has a `DecidableEq` instance.  `machine_result`,
  `config`, `Model` and `machine_state` have function-typed fields and
  no `DecidableEq`, so where those are compared the goal is closed by
  `rfl` instead.  A `sys_destruct` is a case-bash over the
  monadic spec, and it is NOT reproduced here: the `Ok`-inversion is a
  `*_complete_ok` lemma at the CHECKER
  layer (`Checks.Sys.Fs.DPath.check_getcwd_complete_ok`,
  `Checks.Sys.Kernel.Sys.check_setsid_complete_ok`,
  `Checks.Sys.Mm.Mmap.check_mmap_complete_ok`), so each `sys_destruct`
  below is "invert the executable checker at this input" rather than a
  hand-walk of the `alt`/`bind`/`choose` tree.  The one inversion that
  has no checker twin — the FILTERED step relation, whose non-spuriousness
  premise the checker does not carry — is [sstep_cfg_svc_inv], stated once
  and reused by every refusal.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Mm.Mmap
import LinuxSem.Checks.Examples
import LinuxSem.Examples.PatchClassifyDemo.Verdicts

set_option autoImplicit false

namespace LinuxSem.Checks.SpuriousCfg

open LinuxSem.Riscv (word byte bvmap_empty)
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Sys
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Mm.Mmap
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.Examples.PatchClassifyDemo.Verdicts

/-! =========================================================================
    PART 1 — the table
    ========================================================================= -/

/-- Sorted by number, like [Sys.SyscallTable.spec_table], and so with no
    number twice — the property [Run.lookup_injected]'s first-match
    lookup needs to be unambiguous. -/
def strictly_ascending : List Int → Bool
  | a :: b :: r => decide (a < b) && strictly_ascending (b :: r)
  | _ => true

/-- Sorted by number, like [Sys.SyscallTable.spec_table], and so with no
    number twice — the property [Run.lookup_injected]'s first-match
    lookup needs to be unambiguous. -/
theorem injected_table_sorted :
    strictly_ascending (injected_table.map (fun a => a.ia_no)) = true := by
  decide

/-- Every injecting arm names a syscall the dispatcher answers: a number
    here with no arm in [Sys.SyscallTable.spec_table] would be a filter
    on nothing. -/
theorem injected_table_dispatches :
    injected_table.all
      (fun a => (arm_numbers spec_table).any (fun n => n == a.ia_no))
      = true := by
  decide

/-- An effect that answers errno [e] and does nothing else. -/
def errno_eff (e : Int) : SyscallEffect := mkEffect (errno_ret e) [] []

/-- The model every check below starts from: the demo process with an
    empty file system and end of input. -/
def m0 : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-! =========================================================================
    PART 2 — which families a configuration turns off
    ========================================================================= -/

/-- A machine state at a [getcwd] ecall: syscall number 17 pending, every
    register 0 — so [size] is 0, inside the band [DPath.getcwd_spec]
    answers — and no memory at all, which that spec never reads. -/
def getcwd_ms : machine_state where
  ms_regs := bvmap_empty
  ms_fregs := bvmap_empty
  ms_pc_val := BitVec.ofInt 64 0x100
  ms_svc_pending := some (BitVec.ofInt 64 17)
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun _ => none
  ms_rom := fun _ => none

def getcwd_i : SyscallInput := sys_input [] getcwd_ms (BitVec.ofInt 64 17)

theorem getcwd_off_under_forced_only :
    injected_family_off forced_only_cfg getcwd_i = true := by
  decide

theorem getcwd_on_under_may_fail :
    injected_family_off may_fail_cfg getcwd_i = false := by
  decide

/-- The one-switch form [alloc_only_cfg] touches the allocation family
    and nothing else. -/
theorem getcwd_on_under_alloc_only :
    injected_family_off (alloc_only_cfg false) getcwd_i = false := by
  decide

theorem mmap_off_under_alloc_only :
    injected_family_off (alloc_only_cfg false) (mmap_in 4096) = true := by
  decide

/-- A syscall with no injecting arm belongs to no family, whatever the
    configuration: [exit] is never filtered. -/
theorem exit_has_no_family (cfg : SpuriousCfg) :
    injected_family_off cfg
      ⟨BitVec.ofInt 64 93, [0, 0, 0, 0, 0, 0],
       (fun _ => none), (fun _ => none)⟩ = false := by
  rfl

/-! =========================================================================
    PART 3 — fs: getcwd, never forced
    ========================================================================= -/

theorem getcwd_dispatch (m : Model) (o : Outcome SyscallEffect Model event) :
    Specs.syscall_spec getcwd_i m o ↔
      Sys.Fs.DPath.getcwd_spec (in_arg getcwd_i 1) getcwd_i m o :=
  Iff.rfl

theorem getcwd_size_in_band :
    decide (1 < (in_arg getcwd_i 1).toNat) = false := by
  decide

/-- The size band, as a `Prop`: `getcwd_i`'s buffer size is 0, so the
    spec's `if 1 < size` takes the modelled branch. -/
theorem getcwd_band : ¬ 1 < (in_arg getcwd_i 1).toNat := by
  have h := getcwd_size_in_band
  simp only [decide_eq_false_iff_not] at h
  exact h

/-- `getcwd_admits`: every errno the spec can answer is
    answerable at EVERY model.

    PROOF.  The spec is read directly: `getcwd_spec` never inspects `m`,
    so `getcwd_dispatch` and one `if` put the goal in front of the
    `alt`/`bind`/`choose` tree, and each of the four errnos is one
    introduction rule — `alt_r` for the `-ERANGE` the state determines,
    `alt_l` + `bind_ok` + `choose_ok` for the three the injection picks.
    No case bash is needed in this direction because the goal is
    existential in the tree's choices: naming them IS the proof.
    (`getcwd_only` is the direction that has to invert.) -/
theorem getcwd_admits (m : Model) (e : Int)
    (he : e ∈ ERANGE :: Sys.Fs.DPath.getcwd_errnos) :
    Specs.syscall_spec getcwd_i m (.ok (errno_eff e) m []) := by
  rw [getcwd_dispatch]
  unfold Sys.Fs.DPath.getcwd_spec
  rw [ite_eq_right getcwd_band]
  rcases List.mem_cons.mp he with rfl | hmem
  · refine alt_r _ _ _ _ _ ?_
    unfold Syscall.err_ret Syscall.ret_only LinuxSem.LinuxProcessSem.pure errno_eff
    rfl
  · refine alt_l _ _ _ _ _ ?_
    refine bind_ok _ (fun e => Syscall.err_ret e) getcwd_i m e m [] (errno_eff e) m [] ?_ ?_
    · exact choose_ok (fun e => e ∈ Sys.Fs.DPath.getcwd_errnos) e _ _ hmem
    · unfold Syscall.err_ret Syscall.ret_only LinuxSem.LinuxProcessSem.pure errno_eff
      rfl

/-- `getcwd_only`: the OTHER direction, and the one that
    has to invert: every `Ok` the spec admits at `getcwd_i` is one of the
    four errno returns, and it moves neither the model nor the events.

    PROOF.  By `Checks.Sys.Fs.DPath.check_getcwd_complete_ok` the spec
    hypothesis is an EQUATION of the executable checker, and the checker
    is a three-leaf decision on values — so the inversion is a case bash
    over the checker's own leaves rather than over the monad: the 31
    effect shapes with a non-empty ledger are `CheckReject` (a `nomatch`),
    and the two accepting leaves name the errno outright, `errno_ret_in`'s
    membership witness or the `-ERANGE` return. -/
theorem getcwd_only (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : Specs.syscall_spec getcwd_i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧
      ∃ e, e ∈ ERANGE :: Sys.Fs.DPath.getcwd_errnos ∧ eff = errno_eff e := by
  rw [getcwd_dispatch] at H
  have hc := Checks.Sys.Fs.DPath.check_getcwd_complete_ok (in_arg getcwd_i 1) eff m m' evs
    getcwd_i H
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  unfold Checks.Sys.Fs.DPath.check_getcwd at hc
  rw [ite_eq_right getcwd_band] at hc
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
  case nil.nil.nil.nil.nil =>
    by_cases hin : Checks.Sys.Prelude.errno_ret_in Sys.Fs.DPath.getcwd_errnos ret = true
    · rw [ite_eq_left hin] at hc
      simp only [Sys.Prelude.check_result.CheckOk.injEq] at hc
      obtain ⟨hm, hevs⟩ := hc
      obtain ⟨er, hmem, hret⟩ := (Checks.Sys.Prelude.errno_ret_in_true _ ret).mp hin
      refine ⟨hm.symm, hevs.symm, er, List.mem_cons_of_mem ERANGE hmem, ?_⟩
      rw [hret]
      rfl
    · rw [ite_eq_right hin] at hc
      by_cases heq : Riscv.bv_eqb ret (errno_ret ERANGE) = true
      · rw [ite_eq_left heq] at hc
        simp only [Sys.Prelude.check_result.CheckOk.injEq] at hc
        obtain ⟨hm, hevs⟩ := hc
        have hret : ret = errno_ret ERANGE := (Fs.bv_eqb_eq ret _).mp heq
        refine ⟨hm.symm, hevs.symm, ERANGE, List.mem_cons_self, ?_⟩
        rw [hret]
        rfl
      · rw [ite_eq_right heq] at hc
        exact absurd hc (by simp)
  all_goals exact absurd hc (by simp)

/-- The -ENOMEM is spurious under forced-only: -ERANGE was available. -/
theorem getcwd_enomem_spurious_under_forced_only :
    spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ENOMEM) := by
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨errno_eff ERANGE, m0, [],
    check_syscall_sound_ok getcwd_i (errno_eff ERANGE) m0 m0 [] (by rfl),
    by decide⟩

/-- ... and kept under may-fail. -/
theorem getcwd_enomem_kept_under_may_fail :
    ¬ spurious_refusal_cfg may_fail_cfg getcwd_i m0 (errno_eff ENOMEM) :=
  spurious_refusal_may_fail getcwd_i m0 (errno_eff ENOMEM)

/-- ... and under a configuration that turns only the allocation family
    off. -/
theorem getcwd_enomem_kept_under_alloc_only :
    ¬ spurious_refusal_cfg (alloc_only_cfg false) getcwd_i m0
        (errno_eff ENOMEM) :=
  spurious_refusal_family_on (alloc_only_cfg false) getcwd_i m0
    (errno_eff ENOMEM) (by decide)

/-- The answer the state determines is never spurious. -/
theorem getcwd_erange_kept_under_forced_only :
    ¬ spurious_refusal_cfg forced_only_cfg getcwd_i m0 (errno_eff ERANGE) :=
  spurious_refusal_not_refusal forced_only_cfg getcwd_i m0 (errno_eff ERANGE)
    (by decide)

/-- The filter's question is answered here, in the affirmative. -/
theorem getcwd_decided : refusal_decided forced_only_cfg getcwd_i m0 := by
  intro _
  exact Or.inl ⟨errno_eff ERANGE, m0, [],
    check_syscall_sound_ok getcwd_i (errno_eff ERANGE) m0 m0 [] (by rfl),
    by decide⟩

/-! ** The step level of PART 3

    Two local tools first — the successor-shape facts every refusal
    below needs — then the four declarations. -/

/-- What an errno return's successor keeps: `apply_effect` writes a0 (x10)
    and, on an effect with five empty ledgers, NOTHING else, so the only
    field a state comparison can distinguish here is that register. -/
theorem ms_gpr_apply_effect_errno (ms : machine_state) (e : Int) :
    ms_gpr (advance_past_svc (apply_effect ms (errno_eff e))) 0 = errno_ret e := by
  have h10 : Riscv.bv_eqb (10 : Riscv.reg) (0 : Riscv.reg) = false := by decide
  have hk : BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : Riscv.reg) := by decide
  simp only [ms_gpr, advance_past_svc, apply_effect, errno_eff, mkEffect, set_reg, h10,
    Bool.false_eq_true, ite_false, Riscv.bvmapSet, Riscv.bvmapGet, Riscv.reg_get, hk,
    Riscv.bvmap_get_set_same, Option.getD_some]

/-- ... so two DIFFERENT errno returns lead to two different successor
    configurations.  This is what makes a refusal an observation about
    the successor rather than about the event list: `machine_state` has
    no `DecidableEq` (its memory fields are functions), which is why the
    argument goes through one register projection. -/
theorem advance_errno_eff_ne (e1 e2 : Int) (h : errno_ret e1 ≠ errno_ret e2)
    (ms : machine_state) :
    advance_past_svc (apply_effect ms (errno_eff e1))
      ≠ advance_past_svc (apply_effect ms (errno_eff e2)) := by
  intro heq
  exact h (by
    have := congrArg (fun st : machine_state => ms_gpr st 0) heq
    rwa [ms_gpr_apply_effect_errno, ms_gpr_apply_effect_errno] at this)

/-- `SNext` is injective, so a successor equality is a configuration
    equality. -/
theorem snext_inj {c1 c2 : config} (h : step_to.SNext c1 = step_to.SNext c2) : c1 = c2 := by
  injection h

/-- ... and the machine state is a projection of it. -/
theorem snext_cfg_ms {c1 c2 : config} (h : step_to.SNext c1 = step_to.SNext c2) :
    c1.cfg_ms = c2.cfg_ms := by
  cases snext_inj h
  rfl

/-- ** Inverting ONE filtered transition at a pending syscall.**

    The five surviving shapes, with the non-spuriousness premise kept on
    the two that carry one.  [Common.LibWritev.sstep_svc_inv] is the same
    inversion at [Run.sstep] and is phrased through the checker; this one
    is at [Run.sstep_cfg] and phrased through the SPEC, because the three
    refusals below all have their spec inversion already
    ([getcwd_only], `setsid_spec`, `mmap_spec`) and none of them has a
    checker one that survives the filter's premise.

    The premise is what the raw `cases` on a CONCRETE successor cannot
    do: the claimed successor's `ms` and `eff` are fixed, and dependent
    elimination then has to solve `errno_ret ENOMEM = eff.eff_ret` for
    the constructor's own variable, which fails.  Stating the inversion
    over a free `st` (the `inversion Hss` step with the conclusion
    generalized) is the fix. -/
theorem sstep_cfg_svc_inv (segs : List Segment) (cfg : SpuriousCfg)
    (ms : machine_state) (model : Model) (x8 : word) (evs : List event) (st : step_to)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hss : sstep_cfg segs cfg ⟨ms, model⟩ evs st) :
    (∃ eff model' evs',
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs') ∧
        ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ∧
        ((∃ model'', m_halted model' = none ∧ evs = evs' ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' ∧
            st = .SNext ⟨advance_past_svc (apply_effect ms eff), model''⟩)
         ∨ (m_halted model' = none ∧ evs = [] ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = none ∧
            st = .SError)))
    ∨ (∃ eff model' evs', Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs') ∧
        (∃ code, m_halted model' = some code ∧
          evs = evs' ++ [event.ExitEv code (m_fs model')] ∧ st = .SNext ⟨ms, model'⟩))
    ∨ (∃ eff model' evs', Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs') ∧
        (∃ sig, m_killed model' = some sig ∧
          evs = evs' ++ [event.KillEv sig (m_fs model')] ∧ st = .SNext ⟨ms, model'⟩))
    ∨ (Specs.syscall_spec (sys_input segs ms x8) model .unmodeled ∧
        evs = [] ∧ st = .SError) := by
  cases Hss with
  | instr a b c d p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_fault a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_unmodeled a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | syscall a b c d mp mpp evs1 p8 p9 hspec hns p11 hmat =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      exact Or.inl ⟨d, mp, evs, hspec, hns, Or.inl ⟨mpp, p11, rfl, hmat, rfl⟩⟩
  | syscall_materialization_fault a b c d mp evs1 p7 p8 hspec hns p10 hmat =>
      rw [Hsvc] at p8
      obtain rfl := Option.some.inj p8
      exact Or.inl ⟨d, mp, evs1, hspec, hns, Or.inr ⟨p10, rfl, hmat, rfl⟩⟩
  | exit a b c d mp evs1 code p8 p9 hspec p11 hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      exact Or.inr (Or.inl ⟨d, mp, evs1, hspec, code, p11, rfl, rfl⟩)
  | killed a b c d mp evs1 sig p8 p9 hspec hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      exact Or.inr (Or.inr (Or.inl ⟨d, mp, evs1, hspec, sig, hk, rfl, rfl⟩))
  | syscall_unmodeled a b c p4 p5 hspec =>
      rw [Hsvc] at p5
      obtain rfl := Option.some.inj p5
      exact Or.inr (Or.inr (Or.inr ⟨hspec, rfl, rfl⟩))

/-- `getcwd_step_from`: every errno the spec admits is a
    TRANSITION out of [getcwd_ms], on the bare relation.

    PROOF.  [Run.sstep]'s syscall rule, with the four premises named:
    [getcwd_admits] for the spec witness, `getcwd_ms`'s own
    `ms_svc_pending = some 17` for the pending slot, the model's
    `m_halted = none` (before and after, the spec leaves the model
    alone), and `materialize_model_accesses_no_lazy` for the empty
    access list.  No case analysis: this is the rule APPLIED. -/
theorem getcwd_step_from (e : Int) (he : e ∈ ERANGE :: Sys.Fs.DPath.getcwd_errnos) :
    sstep [] ⟨getcwd_ms, m0⟩ []
      (.SNext ⟨advance_past_svc (apply_effect getcwd_ms (errno_eff e)), m0⟩) :=
  sstep.syscall (ms := getcwd_ms) (model := m0) (x8 := BitVec.ofInt 64 17)
    (eff := errno_eff e) (model' := m0) (model'' := m0) (evs := [])
    (m_halted_init_model _ _ _ _ _ _) rfl (getcwd_admits m0 e he)
    (m_halted_init_model _ _ _ _ _ _)
    (materialize_model_accesses_no_lazy _ _ (init_model_no_lazy _ _ _ _ _ _))

/-- `getcwd_enomem_step_admitted`: the -ENOMEM is one
    of the four, so it is a transition. -/
theorem getcwd_enomem_step_admitted :
    sstep [] ⟨getcwd_ms, m0⟩ []
      (.SNext ⟨advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM)), m0⟩) :=
  getcwd_step_from ENOMEM (List.mem_cons_of_mem ERANGE (by simp [Sys.Fs.DPath.getcwd_errnos]))

/-- `getcwd_enomem_step_refused`: and the FILTER refuses
    it, because -ERANGE was available at the same input and model.

    PROOF.  [sstep_cfg_svc_inv] reduces the filtered step to its five
    shapes.  Two are `SError` claims, which a `SNext` successor refutes;
    the exit and kill shapes land on the UNCHANGED machine state, whose
    `ms_svc_pending` is `none` after an ecall and `some 17` before it;
    and the surviving syscall shape carries [getcwd_only]'s inversion —
    the effect is `errno_eff e` for one of the four errnos.  `-ENOMEM`
    contradicts the refusal's own non-spuriousness premise
    ([getcwd_enomem_spurious_under_forced_only]), the two other
    injectables contradict it by exhibiting `-ERANGE` as the non-refusal
    answer, and `-ERANGE` itself is a DIFFERENT successor configuration
    ([advance_errno_eff_ne]), which the claimed equality forbids. -/
theorem getcwd_enomem_step_refused :
    ¬ sstep_cfg [] forced_only_cfg ⟨getcwd_ms, m0⟩ []
        (.SNext ⟨advance_past_svc (apply_effect getcwd_ms (errno_eff ENOMEM)), m0⟩) := by
  intro hss
  rcases sstep_cfg_svc_inv [] forced_only_cfg getcwd_ms m0 (BitVec.ofInt 64 17) [] _ rfl hss with
    ⟨eff, model', evs', hspec, hns, harm⟩ | ⟨eff, model', evs', hspec, code, hh, hev, hst⟩
    | ⟨eff, model', evs', hspec, sig, hk, hev, hst⟩ | ⟨hspec, hev, hst⟩
  · rcases harm with ⟨m'', -, hev, hmat, hst⟩ | ⟨hh, hev, hmat, hst⟩
    · obtain ⟨rfl, -, e, hmem, heff⟩ := getcwd_only m0 eff model' evs' hspec
      subst heff
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · exact absurd (snext_cfg_ms hst)
          (advance_errno_eff_ne ENOMEM ERANGE (by decide) getcwd_ms)
      · simp only [Sys.Fs.DPath.getcwd_errnos, List.mem_cons, List.not_mem_nil,
          or_false] at hmem2
        rcases hmem2 with rfl | rfl | rfl
        · exact absurd getcwd_enomem_spurious_under_forced_only hns
        · exact absurd ⟨by decide, by decide, ⟨errno_eff ERANGE, m0, [],
              check_syscall_sound_ok getcwd_i (errno_eff ERANGE) m0 m0 [] (by rfl),
              by decide⟩⟩ hns
        · exact absurd ⟨by decide, by decide, ⟨errno_eff ERANGE, m0, [],
              check_syscall_sound_ok getcwd_i (errno_eff ERANGE) m0 m0 [] (by rfl),
              by decide⟩⟩ hns
    · cases hst
  · have hlen := congrArg List.length hev
    simp at hlen
  · have hlen := congrArg List.length hev
    simp at hlen
  · cases hst

/-- `getcwd_erange_step_admitted_under_forced_only`:
    the state-determined answer passes the filter: the exit-1 twin.

    PROOF.  [Run.sstep_cfg]'s syscall rule is [getcwd_step_from]'s step
    plus the filter's premise, and that premise is exactly
    [getcwd_erange_kept_under_forced_only]. -/
theorem getcwd_erange_step_admitted_under_forced_only :
    sstep_cfg [] forced_only_cfg ⟨getcwd_ms, m0⟩ []
      (.SNext ⟨advance_past_svc (apply_effect getcwd_ms (errno_eff ERANGE)), m0⟩) :=
  sstep_cfg.syscall (ms := getcwd_ms) (model := m0) (x8 := BitVec.ofInt 64 17)
    (eff := errno_eff ERANGE) (model' := m0) (model'' := m0) (evs := [])
    (m_halted_init_model _ _ _ _ _ _) rfl
    (getcwd_admits m0 ERANGE List.mem_cons_self)
    getcwd_erange_kept_under_forced_only
    (m_halted_init_model _ _ _ _ _ _)
    (materialize_model_accesses_no_lazy _ _ (init_model_no_lazy _ _ _ _ _ _))

/-! =========================================================================
    PART 4 — cred: setsid, forced by state
    ========================================================================= -/

def setsid_i : SyscallInput :=
  ⟨157, [0, 0, 0, 0, 0, 0], (fun _ => none), (fun _ => none)⟩

theorem setsid_dispatch (m : Model) (o : Outcome SyscallEffect Model event) :
    Specs.syscall_spec setsid_i m o ↔
      Sys.Kernel.Sys.setsid_spec setsid_i m o :=
  Iff.rfl

/-- Before any success, -EPERM is spurious: the session can be made. -/
theorem setsid_eperm_spurious_before_success :
    spurious_refusal_cfg forced_only_cfg setsid_i m0 (errno_eff EPERM) := by
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨mkEffect 1 [] [], with_setsid_succeeded (with_tid 1 m0), [],
    check_syscall_sound_ok setsid_i (mkEffect 1 [] []) m0
      (with_setsid_succeeded (with_tid 1 m0)) [] (by rfl),
    by decide⟩

/-- `setsid_eperm_forced_after_success`: once
    [State.m_setsid_succeeded] is set the -EPERM is FORCED: the spec
    answers it deterministically, so no non-refusal outcome exists at
    that model and the filter has nothing to remove.

    PROOF.  Negating the filter's third conjunct is a claim about ALL
    admissible outcomes, so this is the spec inversion
    [check_setsid_complete_ok] of `Checks.Sys.Kernel.Sys` at the one
    model where the state bit is set: the checker's leading
    `if bv_eqb ret (errno_ret EPERM)` is then the ONLY accepting leaf
    (`CheckReject` otherwise), so the claimed effect's return IS
    `-EPERM` — and `refusal_b` reads `-EPERM` as a refusal of the `cred`
    family, which is exactly what the filter's second conjunct denies. -/
theorem setsid_eperm_forced_after_success :
    ¬ spurious_refusal_cfg forced_only_cfg setsid_i
        (with_setsid_succeeded m0) (errno_eff EPERM) := by
  rintro ⟨-, -, eff, m', evs', hspec, hnr⟩
  have hs : Sys.Kernel.Sys.setsid_spec setsid_i (with_setsid_succeeded m0)
      (Outcome.ok eff m' evs') := (setsid_dispatch _ _).mp hspec
  have hc := Checks.Sys.Kernel.Sys.check_setsid_complete_ok eff (with_setsid_succeeded m0)
    m' evs' setsid_i hs
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    dsimp only [Checks.Sys.Kernel.Sys.check_setsid] at hc
  case nil.nil.nil.nil.nil =>
    by_cases hp : Riscv.bv_eqb ret (errno_ret EPERM) = true
    · rw [ite_eq_left hp] at hc
      have hret : ret = errno_ret EPERM := (Fs.bv_eqb_eq ret _).mp hp
      simp only [Sys.Prelude.check_result.CheckOk.injEq] at hc
      obtain ⟨-, -⟩ := hc
      rw [hret] at hnr
      have htrue : refusal_b setsid_i (with_setsid_succeeded m0) (errno_ret EPERM) = true := by
        decide
      rw [htrue] at hnr
      exact absurd hnr (by simp)
    · rw [ite_eq_right hp] at hc
      rw [ite_eq_left (m_setsid_succeeded_with_setsid_succeeded m0)] at hc
      exact absurd hc (by simp)
  all_goals exact absurd hc (by simp)

/-! =========================================================================
    PART 5 — alloc: mmap, forced by the budget; and the argument gate
    ========================================================================= -/

theorem mmap_dispatch (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (h : i.in_sysno.toNat = 222) :
    Specs.syscall_spec i m o ↔
      Sys.Mm.Mmap.mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)
        (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := by
  simp only [Specs.syscall_spec, Sys.Dispatch.dispatch, h]
  rfl

/-- Within budget the -ENOMEM is spurious: the grant
    [Checks.Cases.Mm.Mmap.mmap_within_budget_grants] admits is the
    non-refusal answer. -/
theorem mmap_enomem_spurious_within_budget :
    spurious_refusal_cfg forced_only_cfg (mmap_in 4096) tight_model
      (errno_eff ENOMEM) := by
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨mkEffect 131072 [] [(131072, 4096)],
    with_vmmaps (mkVmMaps [] [(131072, 4096), (65536, 4096)] 0 0 8192)
      tight_model,
    [], check_syscall_sound_ok _ _ _ _ _ mmap_within_budget_grants,
    by decide⟩

/-- An -ENOMEM the ARGUMENT GATE determines is kept although -ENOMEM is
    the one member of [Mmap.mmap_errnos]: at this input the gate's
    [err_ret ENOMEM] is the whole spec, so no non-refusal outcome
    exists and the filter has nothing to remove.  This is the exactness
    claim of [Run]'s spurious-failure header at the one place a
    list-driven filter would have got it wrong. -/
def mmap_overflow_i : SyscallInput :=
  ⟨222, [4097, 18446744073709551615, 0, 50,
         Sys.Mm.Mmap.mmap_fd_none, 0],
   (fun _ => none), (fun _ => none)⟩

/-- [refusal_b] at the mmap number IS the `-ENOMEM`-or-not test: the
    injected arm's errno list is `Mmap.mmap_errnos` itself, so the filter's
    "is this answer a refusal" and the checker's "is this errno one the
    spec injects" are the same boolean.  The proofs that need it get it
    by `unfold` at the concrete number. -/
theorem refusal_b_mmap (m : Model) (r : word) :
    refusal_b (mmap_in 8192) m r
      = Checks.Sys.Prelude.errno_ret_in Mm.Mmap.mmap_errnos r := by
  rfl

/-- `mmap_enomem_forced_beyond_budget`: over the budget
    the -ENOMEM is FORCED: the grant's own budget gate is shut, so the
    only admissible answer is the errno.

    PROOF.  [mmap_dispatch] + [Checks.Sys.Mm.Mmap.check_mmap_complete_ok]
    turn the spec hypothesis into the executable checker's equation, and
    the checker is then read at this input: the four argument gates are
    decided (`mmap_in 8192` is aligned, anonymous, non-zero and modelled),
    which leaves its two leaves.  On the `errno_ret_in mmap_errnos` leaf
    the answer IS the refusal (`refusal_b` reads exactly that list for
    number 222), and on the grant leaf the `&&` chain contains
    `mmap_noreserve_backed_ok`, which is `false` here — 4096 bytes of
    budget against an 8192-byte request — so the checker answers
    `.CheckReject` and the equation is a constructor mismatch.

    The `mmap_modeled_b` / `w_is0` test and then the budget conjunct are
    what close this, and the budget conjunct is why no case on `m` is
    needed: the model is the CONCRETE [tight_model], so the gate is a
    literal. -/
theorem mmap_enomem_forced_beyond_budget :
    ¬ spurious_refusal_cfg forced_only_cfg (mmap_in 8192) tight_model
        (errno_eff ENOMEM) := by
  rintro ⟨-, -, eff, m', evs', hspec, hnr⟩
  have hspec' := (mmap_dispatch (mmap_in 8192) tight_model _ (by decide)).mp hspec
  have hc := Checks.Sys.Mm.Mmap.check_mmap_complete_ok
    (in_arg (mmap_in 8192) 0) (in_arg (mmap_in 8192) 1) (in_arg (mmap_in 8192) 2)
    (in_arg (mmap_in 8192) 3) (in_arg (mmap_in 8192) 4) (in_arg (mmap_in 8192) 5)
    eff tight_model m' evs' (mmap_in 8192) hspec'
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  dsimp only [Checks.Sys.Mm.Mmap.check_mmap] at hc
  rw [ite_eq_right (by decide : ¬((!(Mm.Mmap.mmap_off_aligned_b (in_arg (mmap_in 8192) 5))) = true)),
      ite_eq_right (by decide : ¬((!(Mm.Mmap.mmap_anon_b (in_arg (mmap_in 8192) 3))) = true)),
      ite_eq_right (by decide : ¬(Syscall.w_is0 (in_arg (mmap_in 8192) 1) = true)),
      ite_eq_left (by decide : Mm.Mmap.mmap_modeled_b (in_arg (mmap_in 8192) 2)
        (in_arg (mmap_in 8192) 3) (in_arg (mmap_in 8192) 5) = true)] at hc
  cases ws <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
  case nil.nil.nil.nil =>
    by_cases herr : Checks.Sys.Prelude.errno_ret_in Mm.Mmap.mmap_errnos ret = true
    · have href : refusal_b (mmap_in 8192) tight_model ret = true := by
        rw [refusal_b_mmap]
        exact herr
      rw [href] at hnr
      exact absurd hnr (by simp)
    · rw [ite_eq_right herr] at hc
      split at hc
      next hchain =>
        have hnores : Mm.Mmap.mmap_noreserve_backed_ok (in_arg (mmap_in 8192) 3) tight_model
            (page_round_up_Z ((in_arg (mmap_in 8192) 1).toNat : Int)) = false := by
          decide
        rw [hnores] at hchain
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at hchain
        simp at hchain
      next hchain => exact nomatch hc
  all_goals exact absurd hc (by simp)

/-- `mmap_gate_enomem_kept_under_forced_only`: the
    ARGUMENT gate's -ENOMEM is kept although -ENOMEM is the one member of
    [Mmap.mmap_errnos]: at this input the gate's `check_ret_only` is the
    whole spec, so every admissible outcome IS the refusal and the filter
    has nothing to remove.

    PROOF.  Same route; the difference is the leaf.  `mmap_overflow_i` is
    a MAP_FIXED PROT_NONE request whose LENGTH overflows the address
    space, so the checker's `two_pow_64 <=? addr + nZ` test is the
    accepting one and it answers `check_ret_only eff (errno_ret ENOMEM)
    m []` — the effect is pinned by [check_ret_only_ok_iff], and
    `refusal_b` reads `-ENOMEM` as a refusal of the `alloc` family. -/
theorem mmap_gate_enomem_kept_under_forced_only :
    ¬ spurious_refusal_cfg forced_only_cfg mmap_overflow_i noaccess_base
        (errno_eff ENOMEM) := by
  rintro ⟨-, -, eff, m', evs', hspec, hnr⟩
  have hspec' := (mmap_dispatch mmap_overflow_i noaccess_base _ (by decide)).mp hspec
  have hc := Checks.Sys.Mm.Mmap.check_mmap_complete_ok
    (in_arg mmap_overflow_i 0) (in_arg mmap_overflow_i 1) (in_arg mmap_overflow_i 2)
    (in_arg mmap_overflow_i 3) (in_arg mmap_overflow_i 4) (in_arg mmap_overflow_i 5)
    eff noaccess_base m' evs' mmap_overflow_i hspec'
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  dsimp only [Checks.Sys.Mm.Mmap.check_mmap] at hc
  rw [ite_eq_right (by decide : ¬((!(Mm.Mmap.mmap_off_aligned_b (in_arg mmap_overflow_i 5))) = true)),
      ite_eq_right (by decide : ¬((!(Mm.Mmap.mmap_anon_b (in_arg mmap_overflow_i 3))) = true)),
      ite_eq_right (by decide : ¬(Syscall.w_is0 (in_arg mmap_overflow_i 1) = true)),
      ite_eq_right (by decide : ¬(Mm.Mmap.mmap_modeled_b (in_arg mmap_overflow_i 2)
        (in_arg mmap_overflow_i 3) (in_arg mmap_overflow_i 5) = true)),
      ite_eq_right (by decide : ¬(Mm.Mmap.mmap_noaccess_b (in_arg mmap_overflow_i 2)
        (in_arg mmap_overflow_i 3) (in_arg mmap_overflow_i 5) = true)),
      ite_eq_left (by decide : Mm.Mmap.mmap_fixed_noaccess_b (in_arg mmap_overflow_i 2)
        (in_arg mmap_overflow_i 3) (in_arg mmap_overflow_i 5) = true),
      ite_eq_left (by decide : two_pow_64 ≤ ((in_arg mmap_overflow_i 0).toNat : Int)
        + page_round_up_Z ((in_arg mmap_overflow_i 1).toNat : Int))] at hc
  obtain ⟨heff, -, -⟩ := (Checks.Sys.Prelude.check_ret_only_ok_iff _ (errno_ret ENOMEM)
    noaccess_base [] m' evs').mp hc
  rw [heff] at hnr
  have href : refusal_b mmap_overflow_i noaccess_base (errno_ret ENOMEM) = true := by
    rw [show refusal_b mmap_overflow_i noaccess_base (errno_ret ENOMEM)
          = refusal_b (mmap_in 8192) noaccess_base (errno_ret ENOMEM) from rfl,
      refusal_b_mmap]
    exact Checks.Sys.Prelude.errno_ret_in_intro _ ENOMEM (by simp [Mm.Mmap.mmap_errnos])
  rw [href] at hnr
  exact absurd hnr (by simp)

/-! =========================================================================
    PART 6 — run level
    ========================================================================= -/

/-! ** The step-level inversions the walk needs

    The `inversion Hss; subst` step inside an `induction fuel`, twice: at
    an instruction state and at the terminating ecall.  Stated once each, so
    the `exits_c` walk below reads like `Checks/Omni`'s rather than like a
    nine-way case bash. -/

/-- At a configuration with no pending syscall whose accounted step is the
    function answer `MachineOk`, the ONLY filtered transition is that step,
    silently (`Common/ExitSim`'s `sstep_instr_inv`, at `sstep_cfg`). -/
theorem sstep_cfg_instr_only (segs : List Segment) (cfg : SpuriousCfg)
    (ms : machine_state) (model : Model) (ms' : machine_state)
    (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    ∀ evs st, sstep_cfg segs cfg ⟨ms, model⟩ evs st → evs = [] ∧ st = .SNext ⟨ms', model⟩ := by
  intro evs st hss
  cases hss with
  | instr ms0 model0 ms1 model1 hh0 hsvc0 hstep =>
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
      simp only [machine_result.MachineOk.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨rfl, rfl⟩
  | instr_fault ms0 model0 hh0 hsvc0 hstep =>
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
      exact absurd hstep (by simp)
  | instr_unmodeled ms0 model0 hh0 hsvc0 hstep =>
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hstep
      exact absurd hstep (by simp)
  | syscall ms0 model0 x8 eff model' model'' evs0 hh0 hsvc0 _ _ _ _ =>
      rw [Hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff model' evs0 hh0 hsvc0 _ _ _ _ =>
      rw [Hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | exit ms0 model0 x8 eff model' evs0 code hh0 hsvc0 _ _ _ =>
      rw [Hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | killed ms0 model0 x8 eff model' evs0 sig hh0 hsvc0 _ _ =>
      rw [Hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | syscall_unmodeled ms0 model0 x8 hh0 hsvc0 _ =>
      rw [Hsvc] at hsvc0
      exact absurd hsvc0 (by simp)

/-- At a configuration whose pending syscall is an exit carrying `code`,
    the ONLY filtered transition is the exit itself, and it lands on the
    halted model — `Checks.Omni.sstep_exit_only`'s twin for the filtered
    relation, through the same four exit normal-form facts. -/
theorem sstep_cfg_exit_only (segs : List Segment) (cfg : SpuriousCfg)
    (ms : machine_state) (model : Model) (x8 code : word)
    (hsvc : ms.ms_svc_pending = some x8)
    (hno : exit_number (sys_input segs ms x8).in_sysno)
    (hcode : ms_gpr ms 0 &&& BitVec.ofInt 64 255 = code) :
    ∀ evs st, sstep_cfg segs cfg ⟨ms, model⟩ evs st →
      ∃ m', st = .SNext ⟨ms, m'⟩ ∧ m_halted m' = some code ∧ m_killed m' = none := by
  intro evs st hss
  cases hss with
  | instr ms0 model0 ms1 model1 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | instr_fault ms0 model0 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | instr_unmodeled ms0 model0 hh0 hsvc0 hstep =>
      rw [hsvc] at hsvc0
      exact absurd hsvc0 (by simp)
  | syscall ms0 model0 x8' eff m' m'' evs0 hh0 hsvc0 hspec hns hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [exit_outcome_halts _ _ _ _ _ hno hspec] at hh'
      exact absurd hh' (by simp)
  | syscall_materialization_fault ms0 model0 x8' eff m' evs0 hh0 hsvc0 hspec hns hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [exit_outcome_halts _ _ _ _ _ hno hspec] at hh'
      exact absurd hh' (by simp)
  | exit ms0 model0 x8' eff m' evs0 code' hh0 hsvc0 hspec hh' hk =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      have hcode' : code' = code := by
        have h1 := hh'
        rw [exit_outcome_halts _ _ _ _ _ hno hspec, sys_input_arg0, hcode] at h1
        exact (Option.some.inj h1).symm
      rw [hcode'] at hh'
      exact ⟨m', rfl, hh', hk⟩
  | killed ms0 model0 x8' eff m' evs0 sig hh0 hsvc0 hspec hk =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      rw [exit_outcome_not_killed _ _ _ _ _ hno hspec] at hk
      exact absurd hk (by simp)
  | syscall_unmodeled ms0 model0 x8' hh0 hsvc0 hspec =>
      have hx : x8' = x8 := Option.some.inj (hsvc0.symm.trans hsvc)
      rw [hx] at hspec
      exact absurd hspec (exit_spec_not_unmodeled _ _ hno)

/-- ** The reflective evaluator, under a configuration.**

    The same induction on `fuel` as `Checks.Examples.exits_c_must_exit_at`,
    with `must_exit_at` replaced by its filtered twin: at the terminating
    ecall the filter has nothing to remove (an exit is never a refusal, and
    `Run.sstep_cfg`'s exit constructor carries no non-spuriousness premise),
    and at an instruction step the filter's step is the unfiltered one
    because the model does not change (`mi_account_step_no_lazy`).

    The two `sstep_cfg` premises of `must_exit_at_cfg.running` are read off
    the inversions above, so no case bash over the nine constructors
    appears here. -/
theorem exits_c_must_exit_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      m_halted model = none → m_vm_lazy model = [] →
      exits_c segs code fuel ms = true →
      must_exit_at_cfg cfg segs code ⟨ms, model⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms model _ _ h
      simp only [exits_c] at h
      exact absurd h (by simp)
  | succ n ih =>
      intro ms model hh hlazy h
      cases hp : ms.ms_svc_pending with
      | some x8 =>
          have h' : ((decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
              && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)) = true := by
            simpa only [exits_c, hp] using h
          rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq,
            beq_iff_eq] at h'
          obtain ⟨hno, hcode⟩ := h'
          have hno' : exit_number (sys_input segs ms x8).in_sysno := hno
          have hspec := exit_spec_at segs ms model x8 hno'
          have hhalt : m_halted (with_halted
              (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model) = some code := by
            rw [m_halted_with_halted, sys_input_arg0, hcode]
          have hnk : m_killed (with_halted
              (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model) = none := by
            rw [m_killed_with_halted]
          refine must_exit_at_cfg.running ⟨ms, model⟩ hh
            ⟨_, _, sstep_cfg.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
              (with_halted (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model) []
              code hh hp hspec hhalt hnk⟩ ?_ ?_
          · intro evs herr
            obtain ⟨m', hst, -, -⟩ :=
              sstep_cfg_exit_only segs cfg ms model x8 code hp hno' hcode evs .SError herr
            cases hst
          · intro evs c' hss
            obtain ⟨m', hst, hhalt', hnk'⟩ :=
              sstep_cfg_exit_only segs cfg ms model x8 code hp hno' hcode evs (.SNext c') hss
            cases hst
            exact must_exit_at_cfg.halted _ hhalt' hnk'
      | none =>
          cases hstep : RiscvSemantics.step segs ms with
          | MachineOk ms' =>
              have hrec : exits_c segs code n ms' = true := by
                simp only [exits_c, hp, hstep] at h
                exact h
              have hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
                rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
              refine must_exit_at_cfg.running ⟨ms, model⟩ hh
                ⟨[], .SNext ⟨ms', model⟩, sstep_cfg.instr ms model ms' model hh hp hacc⟩ ?_ ?_
              · intro evs herr
                obtain ⟨-, hst⟩ :=
                  sstep_cfg_instr_only segs cfg ms model ms' hlazy hp hstep evs .SError herr
                cases hst
              · intro evs c' hss
                obtain ⟨-, hst⟩ :=
                  sstep_cfg_instr_only segs cfg ms model ms' hlazy hp hstep evs (.SNext c') hss
                cases hst
                exact ih ms' model hh hlazy hrec
          | MachineFault =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)
          | MachineUnmodeled =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)

/-! ### The two image checks under forced-only

    Both are corollaries of `exits_c_must_exit_at_cfg` at the image
    fixtures.  They are stated here rather than beside the images because
    the image checks of PART 6 are about the FILTERED relation, and the
    filter is this module's subject.  The fixtures live in
    `Checks.Examples`; this module imports it, and `Checks.Examples` does
    not reach this module, so the edge is acyclic.

    The exit-0 direction is the trace-level lemma at `forced_only_cfg` —
    `exits_c` is never filtered, because an exit carries no avoidable
    refusal — and the undecodable direction is a first step that is
    UNMODELED, which no configuration filters.  Neither statement needs
    the `run_decided` premise the monotonicity route would carry, which
    is why both hold at `forced_only_cfg` directly rather than by
    weakening a may-fail fact. -/

open LinuxSem.Checks.Examples
  LinuxSem.EquivalenceDefinition.Classifier in
/-- The exit-0 image must exit 0 under forced-only, exactly as it does
    under may-fail: the trace-level walk does not consult the filter at
    all on this image's path. -/
theorem exit0_image_must_exit_zero_under_forced_only :
    must_exit_with_scfg forced_only_cfg verdict_accept exit0_image demo_limit
      demo_entry demo_proc_input := by
  show must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit
      demo_proc_input)
  have hexits : LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c
      exit0_segments verdict_accept 8
      (init_machine_state exit0_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
        demo_draw demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
        demo_proc_input.in_hwcap) = true := by
    decide
  exact exits_c_must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl hexits

open LinuxSem.Checks.Examples
  LinuxSem.EquivalenceDefinition.Classifier in
/-- The undecodable image refutes must-exit under forced-only too: its
    first fetch is unmodeled, and the filter never touches that step — it
    only removes avoidable refusals. -/
theorem undecodable_image_refutes_must_exit_under_forced_only :
    ¬ must_exit_with_scfg forced_only_cfg verdict_accept undecodable_image demo_limit
        ⟨BitVec.ofInt 64 65536, BitVec.ofInt 64 1048576,
         BitVec.ofInt 64 mmap_base_max, demo_draw⟩ demo_proc_input := by
  apply must_exit_with_scfg_refuted_by_error
  apply run_scfg_unmodeled_errors
  show reaches_unmodeled_cfg undecodable_segments forced_only_cfg
    (init_config undecodable_segments 0x100 demo_phdrs (BitVec.ofInt 64 65536)
      (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit
      demo_proc_input)
  refine ⟨[], init_config undecodable_segments 0x100 demo_phdrs
      (BitVec.ofInt 64 65536) (BitVec.ofInt 64 1048576)
      (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit demo_proc_input,
    star_cfg.refl _, ?_⟩
  refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [init_config, demo_proc_input, mkProcInput]
  rw [undecodable_step_unmodeled]

end LinuxSem.Checks.SpuriousCfg
