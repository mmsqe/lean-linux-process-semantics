/-
  * LinuxSem.Checks.BudgetPremise — the budget mark, on cases
    chosen by hand

  Not part of the trusted specification: QA on `Run.budget_refused_at`,
  `Run.alloc_budget_refused_b`, the per-arm marks beside the allocation
  specs, and the budget-parameterised statements of
  `Equivalence.SpecBudgets`, written to be READ, in the manner of
  `Checks.Examples` and under the four admission reasons its header
  lists.  Every case here is one a single real run cannot show:
  the mark is a statement about what the BUDGET leaves the kernel
  (reason 3, a model constant and model-internal state), and the
  run-level cases quantify over every execution (reason 1).

  ** What is pinned

  - PART 1, the grant clause, arm by arm.  Each mark fires on the
    arm's own beyond-budget fixture and does not fire within budget,
    on a request an argument gate answers, on a request that consumes
    no backing, or on a query — so a budget refusal is distinguishable
    from every other refusal the arm admits.  Beside the fixtures, the
    SOUNDNESS lemmas at abstract arguments: where the mark fires,
    every outcome the arm admits is a refusal (`Run.refusal_b`) — for
    `brk`, `mmap` and `mprotect` over the whole arm; for `mremap` the
    in-place resolution, under the hypothesis that the grown range
    carries no backing metadata but the source's own, the moved one
    being admitted on a state where the mark fires (the mark's header
    in `Sys/Mm/Mremap` says why that is the safe direction).  Beside
    it, the COMPLETENESS lemmas the two-gate rule of that header
    promises: each of a grow's budget gates, the in-place post-state's
    and the move's at any fresh destination, fires the mark.
  - PART 2, the two first-touch clauses.  A store into a lazy page
    with the budget spent IS budget-refused and is an `SError`
    transition; the same store with a page of budget left is not; and
    a fault the interpreter raises for its own reasons — the `ebreak`
    of `Checks.Omni` — is not, although it takes the same transition.
    A syscall whose copy-in touches a lazy page with the budget spent
    is budget-refused through the effect clause.
  - PART 3, the dispatcher: every `FamAlloc` arm and nothing else
    (`Run.alloc_family_dispatched` makes the enumeration a theorem).
  - PART 4, run level.  The exit-0 image never reaches the mark at ANY
    budget, entry or input, through the same reflective evaluator that
    discharges `MustExit` (`Checks.Examples.exits_c`); a six-instruction
    image that asks for two pages at a one-page budget DOES reach it —
    the premise bites, so the budget family is not the constant-pinned
    family under another name; and the exit-0 pair seals
    `Equivalence.SPEC_ERROR_FREE_BUDGETS` and its abort twin under the
    shipped budgets — the ascription a Checker generated for a flavour
    pair will make.  `tools/gen_checker.py` does not emit it yet, so
    the surface is unconsumed until the generator is taught it.

  A forged budget refusal is not a thing a trace can carry: the mark
  reads the request and the state and never an answer, so "budget
  refused where none occurred" is the within-budget fixture, on which
  the mark is `false` although the -ENOMEM the arm keeps under `alt`
  is admissible.  The forged GRANT beyond budget is the checker's
  `CheckReject`, already pinned by
  `Checks.Cases.Mm.Mmap.mmap_beyond_budget_rejected` and
  `Checks.Cases.Mm.Mmap.brk_grow_beyond_budget_rejects_moving`, and not
  repeated here.

  ** Computing on a machine state without reading it back

  As in `Checks.Omni`: every closed computation below closes a SCALAR — a
  boolean, an access list, a checker verdict — and the run-level image
  is stepped with its memory abstracted (`Checks.Omni.with_mem`).

  ** Contents, part by part

  - PART 1: the three budget marks' fixtures and every `decide` pin
    beside them, including the `region_free`/page-rounding proof kit and
    both directions of the two-gate approximation (`ov_*`, `un_*`,
    `un_inplace_gate_passes`); `mremap_budget_refused_fires_on_inplace_refusal`,
    `mremap_budget_refused_refuses_move` and
    `mremap_budget_refused_refuses_inplace`; the mprotect pins and
    `mprotect_dispatch`; `mmap_overflowing_len_is_not_budget_refused`
    (the -ENOMEM an ARGUMENT GATE determines, over
    `Checks.SpuriousCfg.mmap_overflow_i`); and the three whole-arm
    soundness lemmas `brk_refusal_b_of_mark` /
    `brk_budget_refused_is_refusal`, `mmap_budget_refused_is_refusal` and
    `mprotect_budget_refused_is_refusal`.
  - PART 2: the instruction-side first-touch clauses
    (`touch_segment` … `touch_within_budget_is_not_budget_refused`) and
    the effect-side one (`wtouch_ms` … `wtouch_errors`), plus the
    own-reasons clause `ebreak_fault_is_not_budget_refused`.
  - PART 3: the four `*_is_dispatched` instances of
    `Run.alloc_family_dispatched`, `brk_number_reaches_its_mark`, and the
    two non-allocation syscalls `getcwd_is_never_budget_refused` /
    `exit_is_never_budget_refused`.
  - PART 4: the "premise bites" half — `mm_segment` … `mm_not_within_budget`
    — the reflective evaluator `exits_c_no_budget_refused`,
    `exit0_never_budget_refused`, `exit0_source_within_budget`, the sealed
    unconfigured ascriptions (`exit0_strong_universal_error_free_budgets`
    and its abort twin, `Exit0BudgetsChecked` /
    `Exit0BudgetsAbortChecked`), and `exit0_budgets_from_pinned`; plus the
    `ebreak` refutations.
  - PART 5: the configured family
    (`exit0_must_exit_at_cfg`, `exit0_obs_cfg`,
    `exit0_strong_universal_error_free_budgets_scfg`, the
    `ForcedOnlyCfg` / `Exit0ScfgBudgetsChecked` /
    `Exit0ScfgBudgetsBaselineChecked` seal, the either pair and
    `exit0_source_within_budget_scfg`).
  - PART 6: the abort-declared configured cell (the
    `abrt_input` fixture, `exit0_never_dies_by_signal_cfg`,
    `exit0_strong_universal_error_free_budgets_scfg_abort`, the sealed
    `SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT` /
    `SPEC_SCFG_BUDGETS_ABORT` pair, and the `ebreak` refutation under the
    declaration).

  THE SOUNDNESS ROUTE.  All three whole-arm soundness lemmas take the
  route the `brk` pair takes: `brk_dispatch` /
  `mmap_dispatch` / `mprotect_dispatch` into the arm's spec, the CHECKER's
  completeness lemma (`Checks.Sys.Mm.Mmap.check_brk_complete_ok`,
  `check_mmap_complete_ok`, `Checks.Sys.Mm.Mprotect.check_mprotect_complete_ok`)
  to pin the checker's verdict, then the mark's own `if` chain read against
  the checker's accepting branches.  `mark_is_never_spurious` is the
  three-way membership split (`brk` / `mmap` / `mprotect`),
  and `marked_step_is_configured` the five-constructor `sstep` inversion that
  consumes it.  No `sys_destruct` + `errno_is_refusal` case bash is needed:
  each arm's mark and its checker share their gates line for line, which is
  what makes the walk short.  `mmap_dispatch` is the `mmap` twin of
  `brk_dispatch` / `mprotect_dispatch`.

  ** Two fixtures supplied here

  - `abrt_input` and `abrt_input_valid` are not defined here: they come
    from `LinuxSem.Checks.AbortWitness` and are imported, so
    that PART 6 speaks about the same fixture the abort refutation does.
    The machine state at `abrt_input` is `Checks.Omni.ebreak_ms`
    (`ebreak_config_abort`), because the entry stack image does not read
    the declaration.
  - The first-touch fixtures bind registers with `bvmapSet (10 : reg)`
    rather than by the raw index: `Riscv.bv_key` is `toNat + 1`, so a raw
    index 10 names a different slot.  Without that, `touch_ms` would read
    `a0` as zero and the store would be reported at address 0.
  - `materialize_model_accesses_none_iff` is stated once so that a concrete
    `materialize_model_accesses … = none` is a `decide` on a
    `List word` equality — `Model` has no `DecidableEq`, and a `decide`
    target has to be an equality over a type that has one.

  ** Spelling

  `Z` is `Int`; `bv n`/`word`/`byte` are `BitVec n`/`BitVec 64`/`BitVec 8`;
  `Z_to_bv n z` is `BitVec.ofInt n z`; `bv_unsigned a` is `(a.toNat : Int)`;
  `N` is `Nat`.  `negb`/`andb`/`orb` are `!`/`&&`/`||`;
  `Z.eqb a b` is `a == b`; `Z.ltb a b`/`Z.leb a b` are `decide (a < b)`/
  `decide (a ≤ b)`; `Z.ltb_lt`/`Z.leb_le`/`Z.leb_gt` are the `decide`
  reflection lemmas (`decide_eq_true_iff`/`decide_eq_false_iff_not`) plus
  `omega`; `bv_eqb_eq` is `BitVec.eq_of_toNat_eq`'s `==`-reflection
  `beq_iff_eq`; `mkVmMaps`/`mkVmMapsFull` are `State.mkVmMaps`/
  `State.VmMaps.mkVmMapsFull`; `mkCfg` is the `Run.config` constructor;
  `mkInput` is `State.SyscallInput.mkInput`; `Ok`/`Unmodeled` are
  `.ok`/`.unmodeled`; `CheckOk` is `.CheckOk`.
  A closed computation on a Bool or an access list is `decide`,
  because the goal is a decidable proposition; on a value of a type with
  no `DecidableEq` (a checker verdict, which carries a `Model`) it is
  `rfl`.
-/
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.SpuriousCfg
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Mm.Mmap
import LinuxSem.Checks.Progress
import LinuxSem.Checks.Omni
import LinuxSem.Checks.AbortWitness
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.EquivalenceDefinition.OmniEquivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Omni
open LinuxSem.Checks.AbortWitness (abrt_input abrt_input_valid)
open LinuxSem.Checks.Cases.Mm.Mmap
open LinuxSem.Checks.Examples (demo_entry exit_sysno exit0_segments
  exit0_image undecodable_image)
open LinuxSem.Checks.SpuriousCfg (mmap_overflow_i getcwd_i)
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Checks.BudgetPremise

open LinuxSem.Checks.Sys.Prelude (errno_ret_in listNN_eqb)
open LinuxSem.LinuxProcessSem.Sys.Syscall (w_is0)

-- The specs' `if` chains and the page arithmetic below are deeper than
-- the default recursion budget admits.
set_option maxRecDepth 1000000

/- =========================================================================
   PART 1 — the grant clause, arm by arm
   ========================================================================= -/

/-! ** brk

    `Checks.Cases.Mm.Mmap.m_tight_brk`: a fresh process with a one-page
    budget and its break at 65536.  A two-page grow is refused for
    budget; a one-page grow fits; the query is not a request. -/

theorem brk_two_pages_is_budget_refused :
    brk_budget_refused_b m_tight_brk 73728 = true := by decide

theorem brk_one_page_is_not_budget_refused :
    brk_budget_refused_b m_tight_brk 69632 = false := by decide

theorem brk_query_is_not_budget_refused :
    brk_budget_refused_b m_tight_brk 0 = false := by decide

/-- After the one-page grow the budget is spent: a single further byte
    is refused, and a shrink back is not a budget refusal (it releases). -/
def m_tight_brk_grown : Model :=
  with_vmmaps (mkVmMaps brk_reserved [(65536, 4096)] 65536 69632 4096) m_tight_brk

theorem brk_one_byte_on_spent_budget_is_budget_refused :
    brk_budget_refused_b m_tight_brk_grown 69633 = true := by decide

theorem brk_shrink_is_not_budget_refused :
    brk_budget_refused_b m_tight_brk_grown 65536 = false := by decide

/-- SOUNDNESS, abstract: where the mark fires, `Mmap.brk_r_ok` admits
    only the unmoved break. -/
theorem brk_budget_refused_forces (m : Model) (req r : word)
    (Hmark : brk_budget_refused_b m req = true) (Hok : brk_r_ok m req r = true) :
    r = (m_vmmaps m).vm_brk := by
  -- The mark's four conjuncts, in the mark's order: the query-or-invalid
  -- gate is `false`, then the break is above zero and below the request,
  -- then the budget gate refuses.
  unfold brk_budget_refused_b at Hmark
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at Hmark
  obtain ⟨⟨⟨Hq, Hc⟩, Hd⟩, Hbud⟩ := Hmark
  rw [Bool.or_eq_false_iff] at Hq
  obtain ⟨Hq0, Hq1⟩ := Hq
  rw [decide_eq_false_iff_not] at Hq1
  have Hc' : 0 < ((m_vmmaps m).vm_brk.toNat : Int) := by simpa using Hc
  have Hd' : ((m_vmmaps m).vm_brk.toNat : Int) < (req.toNat : Int) := by simpa using Hd
  -- `brk_r_ok`'s two leading gates are therefore `false`, so the only
  -- resolution left is the GROW shape.
  unfold brk_r_ok at Hok
  dsimp only at Hok
  rw [ite_eq_right (by simp [Hq0]; omega)] at Hok
  rw [ite_eq_right (by simp; omega)] at Hok
  simp only [Bool.and_eq_true] at Hok
  obtain ⟨Hr, Hgrow⟩ := Hok
  rw [Bool.or_eq_true] at Hr
  rcases Hr with Hr | Hr
  · -- the grow-to-`req` resolution: the mark's own budget conjunct refutes it
    have hr : r = req := (beq_iff_eq).mp Hr
    subst hr
    unfold brk_grow_ok at Hgrow
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Hc', Hd'⟩)] at Hgrow
    simp only [Bool.and_eq_true] at Hgrow
    exact absurd Hgrow.2 (by simp [Hbud])
  · exact (beq_iff_eq).mp Hr

/-- The dispatcher at the brk number IS `Mmap.brk_spec`.  The hypothesis
    is stated in `Nat` — `i.in_sysno.toNat = 214` — because
    `Run.alloc_budget_refused_b` compares `in_sysno.toNat` (a `Nat`)
    against `214`, so the `Nat` spelling is the one that composes with
    `Run.alloc_mark_sysnos_dispatched` and is used throughout. -/
theorem brk_dispatch (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hE : i.in_sysno.toNat = 214) :
    Specs.syscall_spec i m o ↔ brk_spec (in_arg i 0) i m o := by
  rw [Specs.syscall_spec, Sys.Dispatch.dispatch, hE]
  rfl

/-- The mark and `brk_refusal_b` agree: where the budget refuses the
    REQUEST, the answer that reports the old break IS a refusal.  This is
    the `refusal_b` half of the whole-arm soundness lemma below, and it is
    where the mark's own conjuncts are read: a real request, above
    `Mmap.min_brk`, that moves the break up. -/
theorem brk_refusal_b_of_mark (m : Model) (req : word)
    (Hmark : brk_budget_refused_b m req = true) :
    brk_refusal_b m req (m_vmmaps m).vm_brk = true := by
  unfold brk_budget_refused_b at Hmark
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at Hmark
  obtain ⟨⟨⟨Hq, Hc⟩, Hd⟩, Hbud⟩ := Hmark
  rw [Bool.or_eq_false_iff] at Hq
  obtain ⟨Hq0, Hq1⟩ := Hq
  rw [decide_eq_false_iff_not] at Hq1
  have Hd' : ((m_vmmaps m).vm_brk.toNat : Int) < (req.toNat : Int) := by simpa using Hd
  have hne : req ≠ (m_vmmaps m).vm_brk := by
    intro h
    rw [h] at Hd'
    omega
  unfold brk_refusal_b
  simp only [Bool.and_eq_true, Bool.not_eq_true', bv_eqb, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, trivial⟩
  · exact Hq0
  · rw [decide_eq_false_iff_not]; exact Hq1
  · simpa [beq_iff_eq] using hne

/-- SOUNDNESS, arm level: where the mark fires, every `brk_spec` outcome is
    one of `Run.refusal_b`'s refusals.  The inversion of the arm's own
    `choose` is `Checks.Sys.Mm.Mmap.check_brk_complete_ok` — the checker
    reads the accepted resolution off `syscall_spec` in one step — so what
    is left is `brk_budget_refused_forces` (the resolution the mark leaves
    is the unmoved break) and `brk_refusal_b_of_mark` (and that answer is
    a refusal).  A `sys_destruct` + `errno_is_refusal` case bash would do
    the same work. -/
theorem brk_budget_refused_is_refusal (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (hE : i.in_sysno.toNat = 214)
    (Hmark : alloc_budget_refused_b i m = true)
    (Hspec : Specs.syscall_spec i m (.ok eff m' evs)) :
    refusal_b i m eff.eff_ret = true := by
  have hmark : brk_budget_refused_b m (in_arg i 0) = true := by
    simpa only [alloc_budget_refused_b, hE, ite_true] using Hmark
  have hspec : brk_spec (in_arg i 0) i m (.ok eff m' evs) := (brk_dispatch i m _ hE).mp Hspec
  have hchk := LinuxSem.Checks.Sys.Mm.Mmap.check_brk_complete_ok
    (in_arg i 0) eff m m' evs i hspec
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_brk at hchk
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases cs <;> cases ci <;> dsimp only at hchk
  · by_cases hok : (brk_r_ok m (in_arg i 0) r &&
        LinuxSem.Checks.Sys.Prelude.listNN_eqb zs
          (brk_zeros (in_arg i 0) r (m_vmmaps m).vm_brk) &&
        LinuxSem.Checks.Sys.Prelude.listNN_eqb us
          (brk_unmaps r (m_vmmaps m).vm_brk)) = true
    · rw [ite_eq_left hok] at hchk
      have h1 : (brk_r_ok m (in_arg i 0) r &&
          LinuxSem.Checks.Sys.Prelude.listNN_eqb zs
            (brk_zeros (in_arg i 0) r (m_vmmaps m).vm_brk)) = true :=
        ((Bool.and_eq_true ..).mp hok).1
      have hrok : brk_r_ok m (in_arg i 0) r = true := ((Bool.and_eq_true ..).mp h1).1
      have hr : r = (m_vmmaps m).vm_brk :=
        brk_budget_refused_forces m (in_arg i 0) r hmark hrok
      rw [hr]
      change refusal_b i m (m_vmmaps m).vm_brk = true
      simp only [refusal_b, hE, ite_true]
      exact brk_refusal_b_of_mark m (in_arg i 0) hmark
    · rw [ite_eq_right hok] at hchk
      exact absurd hchk (by simp)
  all_goals (exact absurd hchk (by simp))

/-! ** mmap

    `Checks.Cases.Prelude.tight_model`: budget 8192, one live page —
    one page of budget left.  `Checks.Cases.Mm.Mmap.mmap_in` is the
    hint-placed rw anonymous request. -/

theorem mmap_two_pages_is_budget_refused :
    alloc_budget_refused_b (mmap_in 8192) tight_model = true := by decide

/-- Within budget the mark is `false` — although the -ENOMEM is still
    admissible there (`Checks.SpuriousCfg.mmap_enomem_spurious_within_budget`):
    that is the "forged budget refusal", and the mark does not carry it. -/
theorem mmap_one_page_is_not_budget_refused :
    alloc_budget_refused_b (mmap_in 4096) tight_model = false := by decide

/-- A MAP_NORESERVE request beyond the budget is free at grant time
    and so not a budget refusal; its pages are charged on first touch
    (PART 2). -/
def mmap_noreserve_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 3, 16418, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

theorem mmap_noreserve_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreserve_in 8192) tight_model = false := by decide

/-- A PROT_NONE reservation consumes no backing. -/
def mmap_noaccess_in (len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [0, len, 0, 34, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

theorem mmap_prot_none_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noaccess_in 8192) tight_model = false := by decide

/-- The contained MAP_FIXED rw commit, exposing a PROT_NONE page: on a
    spent budget it is refused; with a page left it is not. -/
def fixed_rw_model (lim : Int) : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 lim
       (BitVec.ofInt 64 0) (BitVec.ofInt 64 sp_window_lo))
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

def mmap_fixed_rw_in : SyscallInput :=
  SyscallInput.mkInput 222 [65536, 4096, 3, 50, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

theorem mmap_fixed_commit_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 0) = true := by decide

theorem mmap_fixed_commit_within_budget_is_not_budget_refused :
    alloc_budget_refused_b mmap_fixed_rw_in (fixed_rw_model 4096) = false := by decide

/-- The MAP_FIXED_NOREPLACE rw grant over a free range charges like any
    grant: beyond the remaining budget it is refused, within it not;
    the PROT_NONE spelling consumes nothing. -/
def mmap_noreplace_in (prot len : word) : SyscallInput :=
  SyscallInput.mkInput 222 [131072, len, prot, 1048610, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

theorem mmap_noreplace_two_pages_is_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 3 8192) tight_model = true := by decide

theorem mmap_noreplace_one_page_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 3 4096) tight_model = false := by decide

theorem mmap_noreplace_prot_none_is_not_budget_refused :
    alloc_budget_refused_b (mmap_noreplace_in 0 8192) tight_model = false := by decide

/-- The premise bites at 2 GiB too, not only at the shipped tight
    fixtures above: a FRESH model (no live grant) under the
    `Equivalence.sanitizer_source_limit` budget refuses an
    anonymous private request one page over that budget, and grants
    one of exactly that budget.  The ledger's arithmetic
    (`page_round_up_Z` against a plain `Int` comparison) is on
    page-rounded BYTE sizes, not a page count, but `Int` is binary, so
    the check closes at this ~2 GiB magnitude in about the same
    time as the tight fixtures above; if that stops being true at a
    larger sealed budget, the check to change is this one, not the
    ledger. -/
def sanitizer_budget_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 lim)
    (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

theorem mmap_sanitizer_budget_plus_page_is_budget_refused :
    alloc_budget_refused_b
      (mmap_in (BitVec.ofInt 64 (LinuxSem.EquivalenceDefinition.Equivalence.sanitizer_source_limit + page_size)))
      (sanitizer_budget_model LinuxSem.EquivalenceDefinition.Equivalence.sanitizer_source_limit) = true := by decide

theorem mmap_sanitizer_budget_exact_is_not_budget_refused :
    alloc_budget_refused_b
      (mmap_in (BitVec.ofInt 64 LinuxSem.EquivalenceDefinition.Equivalence.sanitizer_source_limit))
      (sanitizer_budget_model LinuxSem.EquivalenceDefinition.Equivalence.sanitizer_source_limit) = false := by decide

/-! ### SOUNDNESS over the mmap arm — the whole-arm refusal lemma

    A `sys_destruct` over `mmap_spec`'s `alt`/`bind`
    tree, with `errno_is_refusal` reading each errno branch, would prove it
    too.  The route this file's `brk` pair already uses is shorter and names
    no tactic: the CHECKER's completeness lemma turns the admitted outcome
    into `check_mmap … = .CheckOk`, the mark's own `if` chain is walked once
    to learn which gates it passed and which charging gate it closed, and the
    checker's accepting branches are then inverted under those facts.

    WHAT THE WALK YIELDS.  The mark has six FALSE leaves (an argument gate,
    the PROT_NONE shapes, the noreplace-PROT_NONE shape, and two dead ends)
    and five charging leaves, each of which says one of
    `mmap_noreserve_backed_ok`, `mmap_fixed_rw_budget_ok` or
    `mmap_fixed_rw_span_budget_ok` is `false`.  Every non-errno accepting
    branch of `check_mmap` conjoins one of those three, and each of the four
    errno arms `check_ret_only`s an `errno_ret` from `mmap_errnos`.  So an
    accepted outcome under the mark is an errno answer, which is the
    `refusal_b` this file is about. -/

/-- The dispatcher at the mmap number IS `Mmap.mmap_spec`, the same fact
    `brk_dispatch` and `mprotect_dispatch` state at their numbers.  This
    is the `mmap` dispatch the two soundness lemmas below need; the number
    is compared in `Nat` for the reason `brk_dispatch`'s header gives. -/
theorem mmap_dispatch (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hE : i.in_sysno.toNat = 222) :
    Specs.syscall_spec i m o ↔ mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := by
  rw [Specs.syscall_spec, Sys.Dispatch.dispatch, hE]
  rfl

theorem mmap_budget_refused_is_refusal (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hE : i.in_sysno.toNat = 222)
    (Hmark : alloc_budget_refused_b i m = true)
    (Hspec : Specs.syscall_spec i m (.ok eff m' evs)) :
    refusal_b i m eff.eff_ret = true := by
  have hmark : mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) (in_arg i 4) (in_arg i 5) m = true := by
    simp only [alloc_budget_refused_b, hE] at Hmark
    simpa using Hmark
  have hspec : mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      (in_arg i 4) (in_arg i 5) i m (.ok eff m' evs) :=
    (mmap_dispatch i m _ hE).mp Hspec
  have hchk := LinuxSem.Checks.Sys.Mm.Mmap.check_mmap_complete_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)
    eff m m' evs i hspec
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  have hFacts : (mmap_off_aligned_b (in_arg i 5) = true)
      ∧ (mmap_anon_b (in_arg i 3) = true)
      ∧ (w_is0 (in_arg i 1) = false) := by
    unfold mmap_budget_refused_b at hmark
    by_cases h1 : (!(mmap_off_aligned_b (in_arg i 5))) = true
    · rw [ite_eq_left h1] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h1] at hmark
    by_cases h2 : (!(mmap_anon_b (in_arg i 3))) = true
    · rw [ite_eq_left h2] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h2] at hmark
    by_cases h3 : w_is0 (in_arg i 1) = true
    · rw [ite_eq_left h3] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h3] at hmark
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  obtain ⟨hoff, hanon, hlen⟩ := hFacts
  have herrno : LinuxSem.Checks.Sys.Prelude.errno_ret_in mmap_errnos r = true := by
    by_cases h : LinuxSem.Checks.Sys.Prelude.errno_ret_in mmap_errnos r = true
    · exact h
    · unfold mmap_budget_refused_b at hmark
      by_cases h1 : (!(mmap_off_aligned_b (in_arg i 5))) = true
      · rw [ite_eq_left h1] at hmark; exact absurd hmark (by simp)
      rw [ite_eq_right h1] at hmark
      by_cases h2 : (!(mmap_anon_b (in_arg i 3))) = true
      · rw [ite_eq_left h2] at hmark; exact absurd hmark (by simp)
      rw [ite_eq_right h2] at hmark
      by_cases h3 : w_is0 (in_arg i 1) = true
      · rw [ite_eq_left h3] at hmark; exact absurd hmark (by simp)
      rw [ite_eq_right h3] at hmark
      by_cases hmod : mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
      · -- L1
        rw [ite_eq_left hmod] at hmark
        have hnr : mmap_noreserve_backed_ok (in_arg i 3) m
            (page_round_up_Z ((in_arg i 1).toNat : Int)) = false := by
          simpa using hmark
        have hc := hchk
        unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap at hc
        rw [ite_eq_right (by rw [hoff]; simp), ite_eq_right (by rw [hanon]; simp),
            ite_eq_right (by rw [hlen]; simp), ite_eq_left hmod] at hc
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
        all_goals (simp only [h, hnr, Bool.and_false, ite_false,
          reduceCtorEq, Bool.false_eq_true] at hc)
        all_goals (exact absurd hc (by simp))
      · rw [ite_eq_right hmod] at hmark
        by_cases hna : mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
        · rw [ite_eq_left hna] at hmark; exact absurd hmark (by simp)
        rw [ite_eq_right hna] at hmark
        by_cases hfna : mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
        · rw [ite_eq_left hfna] at hmark; exact absurd hmark (by simp)
        rw [ite_eq_right hfna] at hmark
        by_cases hfix : mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
        · -- the fixed_rw family
          rw [ite_eq_left hfix] at hmark
          by_cases hbig : two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)
          · rw [ite_eq_left hbig] at hmark; exact absurd hmark (by simp)
          rw [ite_eq_right hbig] at hmark
          by_cases htop : ¬ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)
              ≤ alloc_top (m_vmmaps m)
          · rw [ite_eq_left htop] at hmark; exact absurd hmark (by simp)
          rw [ite_eq_right htop] at hmark
          by_cases halign : (!(((in_arg i 0).toNat : Int) % page_size) == 0) = true
          · rw [ite_eq_left halign] at hmark; exact absurd hmark (by simp)
          rw [ite_eq_right halign] at hmark
          by_cases hpos : ¬ (0 < ((in_arg i 0).toNat : Int))
          · rw [ite_eq_left hpos] at hmark; exact absurd hmark (by simp)
          rw [ite_eq_right hpos] at hmark
          by_cases hcont : (region_free (m_vmmaps m).vm_reserved (in_arg i 0)
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
            map_contains (m_vmmaps m).vm_maps (in_arg i 0)
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))) = true
          · -- contained: fixed_rw_budget_ok is false
            rw [ite_eq_left hcont] at hmark
            have hbud : mmap_fixed_rw_budget_ok (in_arg i 3) m (in_arg i 0)
                (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = false := by
              simpa using hmark
            have hc := hchk
            unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap at hc
            rw [ite_eq_right (by rw [hoff]; simp), ite_eq_right (by rw [hanon]; simp),
                ite_eq_right (by rw [hlen]; simp), ite_eq_right hmod, ite_eq_right hna, ite_eq_right hfna,
                ite_eq_left hfix, ite_eq_right hbig, ite_eq_right htop,
                ite_eq_right (by simpa using halign), ite_eq_right hpos, ite_eq_left hcont] at hc
            cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
            all_goals (simp only [h, hbud, Bool.and_false, ite_false,
              reduceCtorEq, Bool.false_eq_true] at hc)
            all_goals (exact absurd hc (by simp))
          · rw [ite_eq_right hcont] at hmark
            by_cases hfreeall : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
                (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
            · -- second arm: noreserve_ok false
              rw [ite_eq_left hfreeall] at hmark
              have hnr : mmap_noreserve_backed_ok (in_arg i 3) m
                  (page_round_up_Z ((in_arg i 1).toNat : Int)) = false := by
                simpa using hmark
              have hc := hchk
              unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap at hc
              rw [ite_eq_right (by rw [hoff]; simp), ite_eq_right (by rw [hanon]; simp),
                  ite_eq_right (by rw [hlen]; simp), ite_eq_right hmod, ite_eq_right hna, ite_eq_right hfna,
                  ite_eq_left hfix, ite_eq_right hbig, ite_eq_right htop,
                  ite_eq_right (by simpa using halign), ite_eq_right hpos, ite_eq_right hcont, ite_eq_left hfreeall] at hc
              cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
              all_goals (simp only [h, hnr, Bool.and_false, ite_false,
                reduceCtorEq, Bool.false_eq_true] at hc)
              all_goals (exact absurd hc (by simp))
            · rw [ite_eq_right hfreeall] at hmark
              by_cases hfreeres : region_free (m_vmmaps m).vm_reserved (in_arg i 0)
                  (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
              · -- third arm: span_budget_ok false
                rw [ite_eq_left hfreeres] at hmark
                have hspan : mmap_fixed_rw_span_budget_ok (in_arg i 3) m (in_arg i 0)
                    (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = false := by
                  simpa using hmark
                have hc := hchk
                unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap at hc
                rw [ite_eq_right (by rw [hoff]; simp), ite_eq_right (by rw [hanon]; simp),
                    ite_eq_right (by rw [hlen]; simp), ite_eq_right hmod, ite_eq_right hna, ite_eq_right hfna,
                    ite_eq_left hfix, ite_eq_right hbig, ite_eq_right htop,
                    ite_eq_right (by simpa using halign), ite_eq_right hpos, ite_eq_right hcont,
                    ite_eq_right hfreeall, ite_eq_left hfreeres] at hc
                cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
                all_goals (simp only [h, hspan, Bool.and_false, ite_false,
                  reduceCtorEq, Bool.false_eq_true] at hc)
                all_goals (exact absurd hc (by simp))
              · rw [ite_eq_right hfreeres] at hmark
                exact absurd hmark (by simp)
        · -- the noreplace family
          rw [ite_eq_right hfix] at hmark
          by_cases hnrna : mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
          · rw [ite_eq_left hnrna] at hmark; exact absurd hmark (by simp)
          rw [ite_eq_right hnrna] at hmark
          by_cases hnrrw : mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
          · rw [ite_eq_left hnrrw] at hmark
            by_cases hbig : two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)
            · rw [ite_eq_left hbig] at hmark; exact absurd hmark (by simp)
            rw [ite_eq_right hbig] at hmark
            by_cases htop : ¬ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)
                ≤ alloc_top (m_vmmaps m)
            · rw [ite_eq_left htop] at hmark; exact absurd hmark (by simp)
            rw [ite_eq_right htop] at hmark
            by_cases halign : (!(((in_arg i 0).toNat : Int) % page_size) == 0) = true
            · rw [ite_eq_left halign] at hmark; exact absurd hmark (by simp)
            rw [ite_eq_right halign] at hmark
            by_cases hpos : ¬ (0 < ((in_arg i 0).toNat : Int))
            · rw [ite_eq_left hpos] at hmark; exact absurd hmark (by simp)
            rw [ite_eq_right hpos] at hmark
            by_cases hfreeall : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
                (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
            · rw [ite_eq_left hfreeall] at hmark
              have hnr : mmap_noreserve_backed_ok (in_arg i 3) m
                  (page_round_up_Z ((in_arg i 1).toNat : Int)) = false := by
                simpa using hmark
              have hc := hchk
              unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap at hc
              rw [ite_eq_right (by rw [hoff]; simp), ite_eq_right (by rw [hanon]; simp),
                  ite_eq_right (by rw [hlen]; simp), ite_eq_right hmod, ite_eq_right hna, ite_eq_right hfna,
                  ite_eq_right hfix, ite_eq_right hnrna, ite_eq_left hnrrw, ite_eq_right hbig, ite_eq_right htop,
                  ite_eq_right (by simpa using halign), ite_eq_right hpos, ite_eq_left hfreeall] at hc
              cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hc
              all_goals (simp only [h, hnr, Bool.and_false, ite_false,
                reduceCtorEq, Bool.false_eq_true] at hc)
              all_goals (exact absurd hc (by simp))
            · rw [ite_eq_right hfreeall] at hmark
              exact absurd hmark (by simp)
          · rw [ite_eq_right hnrrw] at hmark
            exact absurd hmark (by simp)
  have hret : ret_in_errnos mmap_errnos r = true := by
    simpa only [ret_in_errnos,
      LinuxSem.Checks.Sys.Prelude.errno_ret_in] using herrno
  have harm : injected_arm 222 = some ⟨222, .FamAlloc, mmap_errnos⟩ := by decide
  simp only [refusal_b, hE, harm, ret_in_errnos]
  exact hret

/-! ** mremap

    One live eager page at 65536 on a one-page budget, fully spent: a
    grow to two pages is refused; the equal-size answer is not a
    request the budget sees; a shrink releases. -/
def mremap_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 lim)
              (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

def mremap_in (old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [65536, old_size, new_size, 1, 0, 0]
    (fun _ => none) (fun _ => none)

theorem mremap_grow_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 4096) = true := by decide

theorem mremap_grow_within_budget_is_not_budget_refused :
    alloc_budget_refused_b (mremap_in 4096 8192) (mremap_model 8192) = false := by decide

theorem mremap_equal_size_is_not_budget_refused :
    alloc_budget_refused_b (mremap_in 4096 4096) (mremap_model 4096) = false := by decide

def mremap_two_page_model (lim : Int) : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 lim)
              (init_model [] 0 0 demo_sp lim (demo_input [] IEof))

theorem mremap_shrink_is_not_budget_refused :
    alloc_budget_refused_b (mremap_in 8192 4096) (mremap_two_page_model 8192) = false := by decide

/-- BOTH DIRECTIONS OF THE APPROXIMATION, each on a reachable state.
    The mark tests both of a grow's budget gates — the in-place
    post-state's and the move's, the latter through
    `Mremap.mremap_move_budget_b` — because the two charges are ordered
    neither way on every state; the header of `Sys/Mm/Mremap` carries
    the argument, and the two states below pin one direction each.

    OVER: an eager page-sized source at 0x10000, a MAP_NORESERVE
    neighbour at 0x11000 with its first page touched, and a budget the
    pre-state half fills.  A grow of the source over the neighbour's
    first page: the mark fires, because the in-place post-state would
    clear the neighbour's lazy metadata under the tail and charge it
    eagerly, past the budget; the in-place resolution is not even
    available (the tail is occupied); and a move to a free destination
    FITS, exactly at the budget.  Linux moves and
    succeeds; the premise excludes the input anyway.  Over-approximation,
    the safe direction — and pinned so that a later change cannot
    restate the mark on the move's gate alone and silently turn it into
    an under-approximation. -/
def ov_model : Model :=
  with_vm_backing [(BitVec.ofInt 64 0x11000, BitVec.ofInt 64 8192)]
    [BitVec.ofInt 64 0x11000]
    (with_vmmaps (mkVmMaps [] [(0x10000, 4096), (0x11000, 8192)] 0 0 16384)
      (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof)))

theorem ov_pre_state_within_budget : vm_backing_within_limit ov_model = true := by decide

theorem ov_mark_fires_while_a_move_fits :
    mremap_budget_refused_b 0x10000 4096 12288 1 ov_model = true
    ∧ mremap_inplace_grow_b ov_model 0x10000 4096 12288 4096 12288 = false
    ∧ mremap_fresh_b ov_model 4096 12288 0x10000 4096 0x100000 12288 = true := by
  decide

/-- The charges behind it: the in-place post-state is over the budget,
    the moved one is exactly at it, and the destination-free charge the
    mark reads is the moved one's. -/
theorem ov_charges :
    vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x10000 12288) = 20480
    ∧ vm_backing_used (mremap_model_next ov_model 0x10000 4096 0x100000 12288) = 16384
    ∧ mremap_move_charge ov_model 0x10000 4096 12288 = 16384 := by
  decide

/-- UNDER: an eager page-sized source at
    0x10000 and a PROT_NONE mapping directly above it at 0x11000 —
    recorded in `vm_maps` AND `vm_noaccess`, as the NULL-hint PROT_NONE
    arm of `Mmap.mmap_spec` records it, so the state is a pair of
    ordinary mmaps away from a fresh process — on a budget the source
    alone half fills (the PROT_NONE bytes are subtracted from the backed
    charge).  A grow of the source over the whole neighbour: in-place
    growth is unavailable (the tail meets the neighbour), and the
    in-place post-state is charged no more than the source was, because
    the tail's bytes lie under `vm_noaccess` and `State.vm_backed_maps`
    subtracts them — so a mark stated on that post-state is silent for
    every limit that admitted the pre-state.  A move re-creates the
    whole grown mapping at a fresh destination and is charged every byte
    of it, over the budget, at every such destination: the only
    non-errno resolution is budget-refused.
    The mark fires, because it tests the move's gate as well.  A mark
    that read the in-place gate alone would not, and
    `Run.source_within_budget` would hold of an input whose source is
    refused. -/
def un_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(0x10000, 4096), (0x11000, 8192)] [(0x11000, 8192)]
       0 0 8192 (BitVec.ofInt 64 0) (BitVec.ofInt 64 sp_window_lo))
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem un_pre_state_within_budget : vm_backing_within_limit un_model = true := by decide

theorem un_mark_fires_on_the_move_refusal :
    mremap_budget_refused_b 0x10000 4096 12288 1 un_model = true
    ∧ mremap_inplace_grow_b un_model 0x10000 4096 12288 4096 12288 = false
    ∧ mremap_fresh_b un_model 4096 12288 0x10000 4096 0x100000 12288 = false := by
  decide

/-- The charges behind it: the in-place post-state is within the
    budget, the moved one is over it, and the destination-free charge
    the mark reads is the moved one's. -/
theorem un_charges :
    vm_backing_used (mremap_model_next un_model 0x10000 4096 0x10000 12288) = 4096
    ∧ vm_backing_used (mremap_model_next un_model 0x10000 4096 0x100000 12288) = 12288
    ∧ mremap_move_charge un_model 0x10000 4096 12288 = 12288 := by
  decide

/-- ...and the in-place gate alone passes on this state, which is the
    silence the witness exposes. -/
theorem un_inplace_gate_passes :
    mremap_final_budget_b un_model 0x10000 4096 0x10000 12288 = true := by decide

theorem region_free_map_remove (maps : List (word × word)) (old lo n : word)
    (H : region_free maps lo n = true) : region_free (map_remove maps old) lo n = true := by
  apply region_free_intro
  intro a sz Hin
  exact region_free_In _ _ _ _ _ H (List.mem_filter.mp Hin).1

/-- The rounded request as the spec computes it: page sized, and a word
    whenever `page_align_is0_b` passed it. -/
theorem page_round_up_Z_mod (z : Int) : page_round_up_Z z % page_size = 0 := by
  unfold page_round_up_Z
  exact Int.emod_eq_zero_of_dvd ⟨_, by rw [Int.mul_comm]⟩

theorem page_round_up_Z_nonneg (z : Int) (Hz : 0 ≤ z) : 0 ≤ page_round_up_Z z := by
  unfold page_round_up_Z
  have h1 : 0 ≤ z + page_size - 1 := by
    have : (0 : Int) < page_size := by decide
    omega
  have h2 : (0 : Int) < page_size := by decide
  exact Int.mul_nonneg (Int.ediv_nonneg h1 (Int.le_of_lt h2)) (Int.le_of_lt h2)

theorem page_align_is0_b_false_word (len : word) (H : page_align_is0_b len = false) :
    (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))).toNat
      = page_round_up_Z (len.toNat : Int) := by
  unfold page_align_is0_b at H
  rw [Bool.or_eq_false_iff] at H
  obtain ⟨-, H⟩ := H
  rw [decide_eq_false_iff_not] at H
  apply mremap_u64
  exact ⟨page_round_up_Z_nonneg _ (bv_unsigned_range_u64 len).1, by omega⟩

/-- The limit is carried across the resize unchanged. -/
theorem mremap_model_next_limit (m : Model) (old old_n dst new_n : word) :
    (m_vmmaps (mremap_model_next m old old_n dst new_n)).vm_limit
      = (m_vmmaps m).vm_limit := rfl

/-- THE TWO-GATE RULE, abstract.  Each of a grow's budget gates fires
    the mark: the in-place post-state's, with no side condition, and
    the move's at any fresh destination that carries no backing
    metadata, through `Mremap.mremap_move_charge_at_fresh`.  The
    hypotheses of both are the mark's own argument gates, passed. -/
theorem mremap_budget_refused_fires_on_inplace_refusal
    (old old_size new_size flags : word) (m : Model)
    (Hflags : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : ((old.toNat : Int) % page_size == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : (mremap_source_b (m_vmmaps m) old
               (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
               (page_round_up_Z (old_size.toNat : Int))
             && mremap_backing_uniform_b m old
                  (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true)
    (Hgrow : page_round_up_Z (old_size.toNat : Int)
               < page_round_up_Z (new_size.toNat : Int))
    (Hgate : mremap_final_budget_b m old
               (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) old
               (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = false) :
    mremap_budget_refused_b old old_size new_size flags m = true := by
  unfold mremap_budget_refused_b
  dsimp only
  rw [ite_eq_right (by simp [Hflags]), ite_eq_right (by simp [Halign]),
      ite_eq_right (by simp [Hnew]), ite_eq_right (by simp [Hold]),
      ite_eq_right (by simp [Hsrc])]
  rw [ite_eq_right (by omega)]
  simp [Hgate]

/-- COMPLETENESS for the move, abstract: a grow whose move gate refuses
    at a fresh destination fires the mark.  `mremap_move_charge_at_fresh`
    reads the move's charge off the in-place post-state's ledger
    arithmetic, so the mark's `mremap_move_budget_b` conjunct is the
    same `decide` as the `mremap_final_budget_b` the hypothesis refuses
    — which is what lets a caller that has already resolved the move
    conclude the budget declined it. -/
theorem mremap_budget_refused_refuses_move (old old_size new_size flags : word) (m : Model) (dst : word)
    (Hflags : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : ((old.toNat : Int) % page_size == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : (mremap_source_b (m_vmmaps m) old (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
               (page_round_up_Z (old_size.toNat : Int))
             && mremap_backing_uniform_b m old (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true)
    (Hgrow : page_round_up_Z (old_size.toNat : Int) < page_round_up_Z (new_size.toNat : Int))
    (Hdalign : (dst.toNat : Int) % page_size = 0)
    (Hdtop : (dst.toNat : Int) + page_round_up_Z (new_size.toNat : Int)
               ≤ alloc_top (m_vmmaps m))
    (Hdfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true)
    (Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hnoacc : region_free (m_vmmaps m).vm_noaccess dst (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true)
    (Hlazy : maps_subtract
        (maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
        (dst.toNat : Int) ((dst.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat)
      = maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
    (Hpages : List.filter (page_outside_range (dst.toNat : Int)
          ((dst.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat))
        (List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat)) (m_vm_materialized m))
      = List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat)) (m_vm_materialized m))
    (Hgate : mremap_final_budget_b m old (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) dst (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = false) :
    mremap_budget_refused_b old old_size new_size flags m = true := by
  let ON : word := (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
  let NN : word := (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))
  have hNNn : NN.toNat = page_round_up_Z (new_size.toNat : Int) :=
    page_align_is0_b_false_word new_size Hnew
  have hbase : (0 : Int) ≤ page_round_up_Z (old_size.toNat : Int) :=
    page_round_up_Z_nonneg _ (bv_unsigned_range_u64 old_size).1
  have hpos : (0 : Int) < (NN.toNat : Int) := by rw [hNNn]; omega
  have hend : (dst.toNat : Int) + (NN.toNat : Int) < two_pow_64 := by
    rw [hNNn]
    have := alloc_top_lt (m_vmmaps m)
    omega
  have hmaps : region_free (map_remove (m_vmmaps m).vm_maps old) dst NN = true :=
    region_free_map_remove (m_vmmaps m).vm_maps old dst NN
      (region_free_app_r _ _ dst NN Hdfree)
  have hfalse : mremap_move_budget_b m old ON NN = false := by
    have hch := mremap_move_charge_at_fresh m old ON dst NN
      Hdalign (by rw [hNNn]; exact page_round_up_Z_mod _) hpos hend Hfit hmaps
      Hnoacc Hlazy Hpages
    unfold mremap_move_budget_b
    unfold mremap_final_budget_b vm_backing_within_limit at Hgate
    rw [← hch]
    exact Hgate
  unfold mremap_budget_refused_b
  dsimp only
  rw [ite_eq_right (by simp [Hflags]), ite_eq_right (by simp [Halign]),
      ite_eq_right (by simp [Hnew]), ite_eq_right (by simp [Hold]),
      ite_eq_right (by rw [Hsrc]; simp), ite_eq_right (by omega)]
  rw [hfalse]
  simp

/-- SOUNDNESS for the in-place resolution, abstract, kept from the
    one-gate mark: where the mark fires, `Mremap.mremap_inplace_grow_b`
    is `false`.  Under the two-gate mark the proof goes through the
    grown range `[old, old+new_n)` carrying no backing metadata but the
    source's own — the metadata hypotheses of
    `mremap_budget_refused_refuses_move`, at `dst = old` — because then
    the two post-states are charged alike
    (`Mremap.mremap_move_charge_at_fresh` at the source's own address),
    so a mark that fires is an in-place gate that refuses.

    THE HYPOTHESES ARE NOT A RESTRICTION OF THE LEMMA.  Each is an
    instance, at the grown range, of a ledger invariant every reachable
    state satisfies: the protected half is `State.noaccess_pages_owned`
    (every protected byte lies on a page some live mapping touches —
    stated in `State`'s purpose (c), checked on the brk-orphan state by
    `Checks/Cases/Mm/Mmap`'s `noaccess_pages_owned_brk_orphan`, and the
    hypothesis `Mremap.mremap_fresh_avoids_noaccess` already consumes),
    together with `Mremap.mremap_source_b`'s own freeness of the source;
    the lazy and materialized halves are the reservation-under-live-
    mapping invariant of `vm_lazy` and `vm_materialized` that
    `Sys/Mm/Mremap`'s charge header names, which the tree states in
    prose but has not yet proved preserved.  A free tail (the in-place
    region_free conjunct) therefore carries none of them on a
    reachable state, and the hypotheses hold.  The state on which the
    hypothesis-free statement fails — a protected page above the
    source that no live mapping touches, so the in-place post-state is
    cheaper than a move and the mark fires on the move's refusal while
    in-place growth is admitted — violates `noaccess_pages_owned` and is
    unreachable.  Discharging the protected half from the invariant, as
    `mremap_fresh_avoids_noaccess` does for a moved destination, is a
    follow-up. -/
theorem mremap_budget_refused_refuses_inplace (old old_size new_size flags : word) (m : Model)
    (Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hnoacc : region_free (m_vmmaps m).vm_noaccess old
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true)
    (Hlazy : maps_subtract
        (maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int)
           + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
        (old.toNat : Int)
        ((old.toNat : Int)
         + (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat)
      = maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int)
           + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
    (Hpages : List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int)
           + (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat))
        (List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int)
           + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
          (m_vm_materialized m))
      = List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int)
           + (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
          (m_vm_materialized m))
    (Hmark : mremap_budget_refused_b old old_size new_size flags m = true) :
    mremap_inplace_grow_b m old
      (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))
      (page_round_up_Z (old_size.toNat : Int))
      (page_round_up_Z (new_size.toNat : Int)) = false := by
  let ON : word := BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))
  let NN : word := BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))
  unfold mremap_budget_refused_b at Hmark
  dsimp only at Hmark
  by_cases h1 : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true
  · rw [ite_eq_right (by simp [h1])] at Hmark
    by_cases h2 : ((old.toNat : Int) % page_size == 0) = true
    · rw [ite_eq_right (by simp [h2])] at Hmark
      by_cases h3 : page_align_is0_b new_size = false
      · rw [ite_eq_right (by simp [h3])] at Hmark
        by_cases h4 : page_align_is0_b old_size = false
        · rw [ite_eq_right (by simp [h4])] at Hmark
          by_cases h5 : (mremap_source_b (m_vmmaps m) old
                           (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
                           (page_round_up_Z (old_size.toNat : Int))
                         && mremap_backing_uniform_b m old
                              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true
          · rw [ite_eq_right (by rw [h5]; simp)] at Hmark
            by_cases h6 : page_round_up_Z (new_size.toNat : Int)
                          ≤ page_round_up_Z (old_size.toNat : Int)
            · rw [ite_eq_left (by simp [h6])] at Hmark
              simp at Hmark
            · rw [ite_eq_right (by simp [h6])] at Hmark
              change mremap_inplace_grow_b m old ON NN
                (page_round_up_Z (old_size.toNat : Int))
                (page_round_up_Z (new_size.toNat : Int)) = false
              cases hv : mremap_inplace_grow_b m old ON NN
                  (page_round_up_Z (old_size.toNat : Int))
                  (page_round_up_Z (new_size.toNat : Int)) with
              | false => rfl
              | true =>
                exfalso
                unfold mremap_inplace_grow_b at hv
                dsimp only at hv
                rw [Bool.and_eq_true, Bool.and_eq_true] at hv
                obtain ⟨⟨Htop, Hfree⟩, Hgate⟩ := hv
                rw [decide_eq_true_eq] at Htop
                have hONn : ON.toNat = page_round_up_Z (old_size.toNat : Int) :=
                  page_align_is0_b_false_word old_size h4
                have hNNn : NN.toNat = page_round_up_Z (new_size.toNat : Int) :=
                  page_align_is0_b_false_word new_size h3
                have hmain : (old.toNat : Int) % page_size = 0 := (beq_iff_eq).mp h2
                have hnmod : (page_round_up_Z (new_size.toNat : Int)) % page_size = 0 :=
                  page_round_up_Z_mod _
                have hbase : (0 : Int) ≤ page_round_up_Z (old_size.toNat : Int) :=
                  page_round_up_Z_nonneg _ (bv_unsigned_range_u64 old_size).1
                have hpos : (0 : Int) < (NN.toNat : Int) := by
                  rw [hNNn]; omega
                have hend : (old.toNat : Int) + (NN.toNat : Int) < two_pow_64 := by
                  rw [hNNn]
                  have := alloc_top_lt (m_vmmaps m)
                  omega
                have hmaps : region_free (map_remove (m_vmmaps m).vm_maps old) old NN = true :=
                  region_free_app_r _ _ old NN Hfree
                have hch := mremap_move_charge_at_fresh m old ON old NN
                  hmain (by rw [hNNn]; exact hnmod) hpos hend Hfit hmaps Hnoacc Hlazy Hpages
                have heq : mremap_move_budget_b m old ON NN
                    = mremap_final_budget_b m old ON old NN := by
                  unfold mremap_move_budget_b mremap_final_budget_b vm_backing_within_limit
                  rw [hch]
                  rfl
                rw [heq] at Hmark
                rw [Hgate] at Hmark
                exact absurd Hmark (by simp)
          · have hfalse : (mremap_source_b (m_vmmaps m) old
                             (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
                             (page_round_up_Z (old_size.toNat : Int))
                           && mremap_backing_uniform_b m old
                                (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = false := by
              cases hb : (mremap_source_b (m_vmmaps m) old
                             (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
                             (page_round_up_Z (old_size.toNat : Int))
                           && mremap_backing_uniform_b m old
                                (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) with
              | false => rfl
              | true => exact absurd hb h5
            rw [ite_eq_left (by rw [hfalse]; simp)] at Hmark
            simp at Hmark
        · rw [ite_eq_left (by simp [h4])] at Hmark
          simp at Hmark
      · rw [ite_eq_left (by simp [h3])] at Hmark
        simp at Hmark
    · rw [ite_eq_left (by simp [h2])] at Hmark
      simp at Hmark
  · rw [ite_eq_left (by simp [h1])] at Hmark
    simp at Hmark

/-- ** mprotect

    The reserve-then-commit idiom: a PROT_NONE page inside a live
    mapping, exposed rw.  On a spent budget the exposure is refused;
    with a page left it is not; exposing an already-rw page charges
    nothing. -/
def mprotect_in (addr len prot : word) : SyscallInput :=
  SyscallInput.mkInput 226 [addr, len, prot, 0, 0, 0]
    (fun _ => none) (fun _ => none)

theorem mprotect_expose_on_spent_budget_is_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 0) = true := by decide

theorem mprotect_expose_within_budget_is_not_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) (fixed_rw_model 4096) = false := by
  decide

theorem mprotect_already_rw_is_not_budget_refused :
    alloc_budget_refused_b (mprotect_in 65536 4096 3) (mremap_model 4096) = false := by decide

theorem mprotect_dispatch (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hE : i.in_sysno.toNat = 226) :
    Specs.syscall_spec i m o ↔ mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := by
  rw [Specs.syscall_spec, Sys.Dispatch.dispatch, hE]
  rfl

/-- SOUNDNESS over the whole mprotect arm, abstract: where the mark fires,
    every admitted outcome is a refusal.  Same route as the mmap lemma above
    — dispatch, then `check_mprotect_complete_ok`, then the mark's conjuncts
    against the checker's accepting branches — and shorter, because the
    mprotect mark has ONE charging leaf (`mprotect_budget_ok`) and the
    checker one accepting grant that conjoins it. -/
theorem mprotect_budget_refused_is_refusal (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hE : i.in_sysno.toNat = 226)
    (Hmark : alloc_budget_refused_b i m = true)
    (Hspec : Specs.syscall_spec i m (.ok eff m' evs)) :
    refusal_b i m eff.eff_ret = true := by
  have hmark : mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m = true := by
    simp only [alloc_budget_refused_b, hE] at Hmark
    simpa using Hmark
  have hspec : mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m
      (.ok eff m' evs) :=
    (mprotect_dispatch i m _ hE).mp Hspec
  have hchk := LinuxSem.Checks.Sys.Mm.Mprotect.check_mprotect_complete_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i hspec
  have hFacts : (mprotect_grows_conflict_b (in_arg i 2) = false)
      ∧ (!(((in_arg i 0).toNat : Int) % page_size) == 0) = false
      ∧ w_is0 (in_arg i 1) = false
      ∧ ¬ (two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int))
      ∧ mprotect_modeled_b (in_arg i 2) = true
      ∧ (map_contains (m_vmmaps m).vm_noaccess (in_arg i 0)
           (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
         map_contains (m_vmmaps m).vm_maps (in_arg i 0)
           (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))) = true
      ∧ mprotect_budget_ok m (in_arg i 0)
           (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = false := by
    unfold mprotect_budget_refused_b at hmark
    by_cases h1 : mprotect_grows_conflict_b (in_arg i 2) = true
    · rw [ite_eq_left h1] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h1] at hmark
    by_cases h2 : (!(((in_arg i 0).toNat : Int) % page_size) == 0) = true
    · rw [ite_eq_left h2] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h2] at hmark
    by_cases h3 : w_is0 (in_arg i 1) = true
    · rw [ite_eq_left h3] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h3] at hmark
    by_cases h4 : two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)
    · rw [ite_eq_left h4] at hmark; exact absurd hmark (by simp)
    rw [ite_eq_right h4] at hmark
    by_cases h5 : mprotect_modeled_b (in_arg i 2) = true
    · rw [ite_eq_left h5] at hmark
      by_cases h6 : (map_contains (m_vmmaps m).vm_noaccess (in_arg i 0)
            (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
          map_contains (m_vmmaps m).vm_maps (in_arg i 0)
            (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))) = true
      · rw [ite_eq_left h6] at hmark
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3,
          by simpa using h4, h5, h6, by simpa using hmark⟩
      · rw [ite_eq_right h6] at hmark; exact absurd hmark (by simp)
    · rw [ite_eq_right h5] at hmark; exact absurd hmark (by simp)
  obtain ⟨hgrows, halign, hlen, hbig, hmod, hcontains, hbudget⟩ := hFacts
  have hchk' := hchk
  unfold LinuxSem.Checks.Sys.Mm.Mprotect.check_mprotect at hchk'
  rw [ite_eq_right (by rw [hgrows]; simp)] at hchk'
  rw [ite_eq_right (by rw [halign]; simp)] at hchk'
  rw [ite_eq_right (by rw [hlen]; simp)] at hchk'
  rw [ite_eq_right hbig] at hchk'
  rw [ite_eq_right (by rw [hmod]; simp)] at hchk'
  rw [ite_eq_left hcontains] at hchk'
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases us <;> cases cs <;> cases ci <;> dsimp only at hchk'
  · by_cases herrno : errno_ret_in mprotect_errnos r = true
    · have hret : ret_in_errnos mprotect_errnos r = true := by
        simpa only [ret_in_errnos,
          LinuxSem.Checks.Sys.Prelude.errno_ret_in] using herrno
      have harm : injected_arm 226
          = some ⟨226, .FamAlloc, mprotect_errnos⟩ := by decide
      simp only [refusal_b, hE, harm, ret_in_errnos]
      exact hret
    · rw [ite_eq_right (by simpa using herrno)] at hchk'
      by_cases h2 : (mprotect_budget_ok m (in_arg i 0)
            (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
          w_is0 r &&
          listNN_eqb zs [(in_arg i 0,
            BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))]) = true
      · rw [ite_eq_left h2] at hchk'
        have hb : mprotect_budget_ok m (in_arg i 0)
            (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true := by
          simp only [Bool.and_eq_true] at h2
          exact h2.1.1
        rw [hbudget] at hb
        exact absurd hb (by simp)
      · rw [ite_eq_right h2] at hchk'
        exact absurd hchk' (by simp)
  all_goals (exact absurd hchk' (by simp))
/- =========================================================================
   PART 3 — the dispatcher: every allocation arm and nothing else
   ========================================================================= -/

theorem brk_dispatches_to_its_mark :
    alloc_budget_refused_b (brk_in 73728) m_tight_brk = true := by decide

/-- A syscall with no allocation arm is never budget-refused, whatever
    its state: `getcwd` (`Checks.SpuriousCfg.getcwd_i`) and the two exit
    numbers; and, off the whole list, `Run.alloc_budget_refused_b_outside`.
    `Run.alloc_family_dispatched` is the other half — every `FamAlloc`
    number IS on the list — instantiated here on each arm the table
    registers. -/
theorem brk_is_dispatched : 214 ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 214 ⟨214, .FamAlloc, []⟩ rfl rfl

theorem mremap_is_dispatched : 216 ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 216 ⟨216, .FamAlloc, mremap_errnos⟩ rfl rfl

theorem mmap_is_dispatched : 222 ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 222 ⟨222, .FamAlloc, mmap_errnos⟩ rfl rfl

theorem mprotect_is_dispatched : 226 ∈ alloc_mark_sysnos :=
  alloc_family_dispatched 226 ⟨226, .FamAlloc, mprotect_errnos⟩ rfl rfl

/-- Each number on the list reaches its arm's mark:
    `Run.alloc_mark_sysnos_dispatched`, instantiated on the brk number. -/
theorem brk_number_reaches_its_mark (i : SyscallInput) (m : Model)
    (hE : i.in_sysno.toNat = 214) :
    alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0) :=
  (alloc_mark_sysnos_dispatched i m).1 hE

/- =========================================================================
   PART 2 (one clause) — a fault the interpreter raises for ITS OWN reasons
   ========================================================================= -/

/-- A fault the interpreter raises for ITS OWN reasons is not a budget
    refusal: `Checks.Omni.ebreak_ms` faults (`Checks.Omni.ebreak_faults`)
    and takes the same `SError` transition, and the mark is false on it
    at every budget. -/
theorem ebreak_fault_is_not_budget_refused (lim : Int) :
    ¬ budget_refused_at ebreak_segments ⟨ebreak_ms, ebreak_model lim⟩ := by
  rintro ⟨-, hD⟩
  rcases hD with ⟨hsvc, r, hacc, hmat⟩ | ⟨x8, hx8, -⟩
  · have hd := drop_step_accesses ebreak_segments ebreak_ms
    rw [hacc, ebreak_faults] at hd
    simp [drop_access_report] at hd
  · have hnone : ebreak_ms.ms_svc_pending = none := rfl
    exact absurd hx8 (by rw [hnone]; simp)

/- =========================================================================
   PART 3 (the rest) — the two non-allocation syscalls
   ========================================================================= -/

/-- A syscall with no allocation arm is never budget-refused, whatever
    its state: `getcwd` (`Checks.SpuriousCfg.getcwd_i`).  The other half,
    `Run.alloc_family_dispatched`, is the four `*_is_dispatched` instances
    above. -/
theorem getcwd_is_never_budget_refused (m : Model) :
    alloc_budget_refused_b getcwd_i m = false := rfl

theorem exit_is_never_budget_refused (i : SyscallInput) (m : Model)
    (H : exit_sysno i.in_sysno) : alloc_budget_refused_b i m = false := by
  rcases H with E | E
  · unfold alloc_budget_refused_b
    have h : i.in_sysno.toNat = 93 := by omega
    rw [h]
    rfl
  · unfold alloc_budget_refused_b
    have h : i.in_sysno.toNat = 94 := by omega
    rw [h]
    rfl

/- =========================================================================
   PART 1 (the rest) — an -ENOMEM an ARGUMENT GATE determines
   ========================================================================= -/

/-- The -ENOMEM an ARGUMENT GATE determines — the overflowing `MAP_FIXED`
    length of `Checks.SpuriousCfg.mmap_overflow_i` — is not a budget
    refusal either, although it is in `Mmap.mmap_errnos`. -/
theorem mmap_overflowing_len_is_not_budget_refused :
    alloc_budget_refused_b mmap_overflow_i noaccess_base = false := by decide

/- =========================================================================
   PART 4 — run level: the premise bites
   ========================================================================= -/

/-- Six instructions at 0x100 — `addi a7, x0, 222; lui a1, 2; addi a2, x0,
    3; addi a3, x0, 34; addi a4, x0, -1; ecall` — an
    `mmap(0, 8192, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)`
    (`a0` and `a5` are zero at entry). -/
def mm_segment : Segment where
  seg_base := 0x100
  seg_size := 24
  seg_perms := "r-x"
  seg_bytes := ["9308e00db725000013063000930620021307f0ff73000000"]

def mm_segments : List Segment := [mm_segment]

def mm_image : Image :=
  LinuxSem.EquivalenceDefinition.Equivalence.mkImage mm_segments 0x100
    demo_phdrs

def mm_budget : Int := page_size

def mm_ms0 : machine_state :=
  init_machine_state mm_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    demo_proc_input.in_argv demo_proc_input.in_envp demo_proc_input.in_uid
    demo_proc_input.in_hwcap

def mm_msk (k : Nat) : machine_state :=
  match run_steps k mm_segments mm_ms0 with
  | some ms => ms
  | none => mm_ms0

def mm_s (k : Nat) : machine_state := with_mem (mm_msk k) mm_ms0.ms_mem

def mm_model : Model :=
  init_model (segments_reserved mm_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) mm_budget
    demo_proc_input

def mm_c : config := ⟨mm_s 0, mm_model⟩

theorem mm_config :
    init_config mm_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw mm_budget
      demo_proc_input = mm_c := by
  simp only [mm_c, mm_s, mm_msk, run_steps, mm_budget]
  rw [← with_mem_eta mm_ms0]
  rfl

/-- The six instruction steps, at every placement of the memory: the
    image touches no memory but its own fetch, which reads the segment
    image. -/
theorem mm_step : ∀ k, k < 6 → ∀ mem,
    RiscvSemantics.step mm_segments (with_mem (mm_msk k) mem)
      = .MachineOk (with_mem (mm_msk (k + 1)) mem) := by
  intro k Hk mem
  rcases k with _ | _ | _ | _ | _ | _ | k <;> first | istep | omega

theorem mm_svc_none (k : Nat) (Hk : k < 6) : (mm_s k).ms_svc_pending = none := by
  rcases k with _ | _ | _ | _ | _ | _ | k <;> first | decide | omega

theorem mm_instr_sstep (k : Nat) (Hk : k < 6) :
    sstep mm_segments ⟨mm_s k, mm_model⟩ [] (.SNext ⟨mm_s (k + 1), mm_model⟩) := by
  have hstep : mi_account_step mm_segments (mm_s k) mm_model
      = .MachineOk (mm_s (k + 1), mm_model) := by
    no_lazy
    simp only [mm_s]
    rw [mm_step k Hk mm_ms0.ms_mem]
  exact sstep.instr _ _ _ _ rfl (mm_svc_none k Hk) hstep

theorem mm_star : star mm_segments mm_c [] ⟨mm_s 6, mm_model⟩ := by
  unfold mm_c
  exact star.step _ _ _ _ _ (mm_instr_sstep 0 (by omega))
    (star.step _ _ _ _ _ (mm_instr_sstep 1 (by omega))
      (star.step _ _ _ _ _ (mm_instr_sstep 2 (by omega))
        (star.step _ _ _ _ _ (mm_instr_sstep 3 (by omega))
          (star.step _ _ _ _ _ (mm_instr_sstep 4 (by omega))
            (star.step _ _ _ _ _ (mm_instr_sstep 5 (by omega)) (star.refl _))))))

theorem mm_svc6 : (mm_s 6).ms_svc_pending = some (BitVec.ofInt 64 222) := by
  decide

/-- At the ecall the mark fires: the grant clause, by computation.  One
    page of budget, a two-page anonymous rw request. -/
theorem mm_ecall_is_budget_refused :
    budget_refused_at mm_segments ⟨mm_s 6, mm_model⟩ := by
  refine ⟨rfl, Or.inr ⟨BitVec.ofInt 64 222, mm_svc6, Or.inl ?_⟩⟩
  decide

theorem mm_run_budget_refused :
    run_budget_refused mm_image mm_budget demo_entry demo_proc_input := by
  unfold run_budget_refused
  simp only [mm_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [mm_config]
  exact reaches_budget_refused_star mm_segments mm_c [] ⟨mm_s 6, mm_model⟩ mm_star
    (reaches_budget_refused_intro _ _ mm_ecall_is_budget_refused)

/-- ... so the premise excludes it: the budget family is not the
    constant-pinned family under another name. -/
theorem mm_not_within_budget :
    ¬ source_within_budget mm_budget mm_image demo_entry demo_proc_input := by
  intro H
  exact H mm_run_budget_refused

/-! =========================================================================
   PART 2 — the first-touch clauses
   ========================================================================= -/

/-! ** An instruction that touches a lazy page

    One instruction at 0x100, `sd x0, 0(a0)` (0x00053023), with `a0`
    pointing at a page that is writable in the machine and recorded LAZY
    in the model — a MAP_NORESERVE grant the process has not yet touched.
    The machine state is built by hand so that its memory is a small
    function rather than an entry stack image.  The model: the page is a
    lazy reservation and nothing is charged yet, at budget `lim`.
    SYNTHETIC — the lazy range has no `vm_maps` entry, which no grant
    produces; the state exercises clause A of the mark, not the
    allocator.

    The register file is keyed by `Riscv.bv_key`, which is `toNat + 1`,
    so a register is bound with `bvmapSet (10 : reg)` rather than by the
    raw index 10. -/

open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.Examples.PatchClassifyDemo.Verdicts
open LinuxSem.Checks.Sys.Fs.ReadWrite (check_write)
open LinuxSem.Checks.Sys.DispatchCompute (check_syscall_write)

theorem materialize_model_accesses_none_iff (m : Model) (acc : List (word × Nat)) :
    materialize_model_accesses m acc = none ↔
      materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m)
        ((m_vmmaps m).vm_limit) acc = none := by
  unfold materialize_model_accesses
  cases h : materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m)
      ((m_vmmaps m).vm_limit) acc with
  | none => simp
  | some p => simp

def touch_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["23300500"]

def touch_segments : List Segment := [touch_segment]

def touch_page : Int := 0x10000

def touch_ms : machine_state where
  ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 touch_page) bvmap_empty
  ms_fregs := bvmap_empty
  ms_pc_val := BitVec.ofInt 64 0x100
  ms_svc_pending := none
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun a =>
    if decide (touch_page ≤ (a.toNat : Int)) && decide ((a.toNat : Int) < touch_page + page_size)
    then some (BitVec.ofInt 8 0) else none
  ms_rom := fun addr =>
    match memory_read touch_segments addr 1 with
    | some (b :: _) => some b
    | _ => none

def touch_model (lim : Int) : Model :=
  with_vm_backing [(BitVec.ofInt 64 touch_page, BitVec.ofInt 64 page_size)] []
    (init_model (segments_reserved touch_segments) 0 0 demo_sp lim (demo_input [] IEof))

def touch_accesses : Option (List memory_access) :=
  match RiscvSemantics.step_accesses touch_segments touch_ms with
  | .MachineOk r => some r.accessed_ranges
  | .MachineFault | .MachineUnmodeled => none

theorem touch_store_reports_the_page :
    touch_accesses = some [(BitVec.ofInt 64 touch_page, 8)] := by
  decide

theorem touch_report : ∃ r : access_report machine_state,
    RiscvSemantics.step_accesses touch_segments touch_ms = .MachineOk r
    ∧ r.accessed_ranges = [(BitVec.ofInt 64 touch_page, 8)] := by
  have h := touch_store_reports_the_page
  unfold touch_accesses at h
  cases hx : RiscvSemantics.step_accesses touch_segments touch_ms with
  | MachineOk r =>
      rw [hx] at h
      exact ⟨r, rfl, Option.some.inj h⟩
  | MachineFault => rw [hx] at h; exact absurd h (by simp)
  | MachineUnmodeled => rw [hx] at h; exact absurd h (by simp)

theorem touch_spent_materialization_fails :
    materialize_model_accesses (touch_model 0) [(BitVec.ofInt 64 touch_page, 8)] = none :=
  (materialize_model_accesses_none_iff _ _).mpr (by decide)

theorem touch_within_budget_materialization_succeeds :
    materialize_model_accesses (touch_model page_size)
      [(BitVec.ofInt 64 touch_page, 8)] ≠ none :=
  fun h => absurd ((materialize_model_accesses_none_iff _ _).mp h) (by decide)

theorem touch_on_spent_budget_is_budget_refused :
    budget_refused_at touch_segments ⟨touch_ms, touch_model 0⟩ := by
  obtain ⟨r, hstep, hranges⟩ := touch_report
  refine ⟨rfl, Or.inl ⟨rfl, r, hstep, ?_⟩⟩
  rw [hranges]
  exact touch_spent_materialization_fails

theorem touch_on_spent_budget_errors :
    sstep touch_segments ⟨touch_ms, touch_model 0⟩ [] .SError := by
  obtain ⟨r, hstep, hranges⟩ := touch_report
  refine budget_fault_instr_sstep_error touch_segments touch_ms (touch_model 0) r
    rfl rfl hstep ?_
  rw [hranges]
  exact touch_spent_materialization_fails

theorem touch_within_budget_is_not_budget_refused :
    ¬ budget_refused_at touch_segments ⟨touch_ms, touch_model page_size⟩ := by
  rintro ⟨-, h | h⟩
  · obtain ⟨-, r, hstep, hmat⟩ := h
    obtain ⟨r', hstep', hranges⟩ := touch_report
    rw [hstep] at hstep'
    obtain rfl := machine_result.MachineOk.inj hstep'
    rw [hranges] at hmat
    exact touch_within_budget_materialization_succeeds hmat
  · obtain ⟨x8, hx8, -⟩ := h
    rw [show touch_ms.ms_svc_pending = none from rfl] at hx8
    exact absurd hx8 (by simp)

/-! ** A syscall whose copy-in touches a lazy page

    `write(1, 0x1000, 1)` from a process whose lazy reservation covers the
    first two pages, page 0 already charged, budget one page. -/

def wtouch_ms : machine_state where
  ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 1)
    (bvmapSet (11 : reg) (BitVec.ofInt 64 0x1000)
      (bvmapSet (12 : reg) (BitVec.ofInt 64 1) bvmap_empty))
  ms_fregs := bvmap_empty
  ms_pc_val := BitVec.ofInt 64 0x100
  ms_svc_pending := some (BitVec.ofInt 64 64)
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun a => if bv_eqb a (BitVec.ofInt 64 0x1000) then some (BitVec.ofInt 8 0) else none
  ms_rom := fun _ => none

def wtouch_model : Model :=
  with_vm_backing [(0, 0x2000)] [0]
    (init_model [] 0 0 demo_sp 0x1000 (demo_input [] IEof))

def wtouch_eff : SyscallEffect :=
  SyscallEffect.mkEffectU 1 [] [] [] [] [(BitVec.ofInt 64 0x1000, 1)]

abbrev wtouch_i : SyscallInput := sys_input [] wtouch_ms (BitVec.ofInt 64 64)

theorem wtouch_fd :
    fd_lookup (m_fds wtouch_model) (Sys.Syscall.fd32 (in_arg wtouch_i 0))
      = some (FdEntry.FdChannel (BitVec.ofInt 64 1)) := rfl

theorem wtouch_chan : Sys.Syscall.w_is0 (1#64) = false := by decide

theorem wtouch_range : modeled_rw_range (in_arg wtouch_i 1) (in_arg wtouch_i 2) = true := by
  decide

theorem wtouch_count : Sys.Syscall.w_is0 (in_arg wtouch_i 2) = false := by decide

theorem wtouch_source : write_source wtouch_i.in_mem (in_arg wtouch_i 1) (in_arg wtouch_i 2)
    = [BitVec.ofInt 8 0] := by decide

theorem check_write_wtouch_walk (eff : SyscallEffect) :
    check_write wtouch_i (Sys.Syscall.fd32 (in_arg wtouch_i 0)) (in_arg wtouch_i 1) (in_arg wtouch_i 2)
      eff wtouch_model
    = (match eff with
       | ⟨ret, [], [], [], [], copyins⟩ =>
           if decide (1 ≤ (ret.toNat : Int)) && decide ((ret.toNat : Int) ≤ 1) then
             if LinuxSem.Checks.Sys.Prelude.access_ranges_eqb copyins
                  [(in_arg wtouch_i 1, ret.toNat)] then
               .CheckOk wtouch_model
                 (List.map (event.WriteEv (BitVec.ofInt 64 1)) (List.take ret.toNat
                   [BitVec.ofInt 8 0]))
             else .CheckReject
           else .CheckReject
       | _ => .CheckReject) := by
  simp [check_write, wtouch_fd, wtouch_chan, wtouch_range, wtouch_count, wtouch_source]
  rfl

theorem wtouch_checker :
    check_syscall wtouch_i wtouch_eff wtouch_model
      = .CheckOk wtouch_model [event.WriteEv (BitVec.ofInt 64 1) (BitVec.ofInt 8 0)] := by
  rw [check_syscall_write wtouch_i wtouch_eff wtouch_model (by decide)]
  rw [check_write_wtouch_walk wtouch_eff]
  simp [wtouch_eff]
  rfl

theorem wtouch_materialization_fails :
    materialize_model_accesses wtouch_model (syscall_effect_accesses wtouch_eff) = none := by
  refine (materialize_model_accesses_none_iff _ _).mpr ?_
  show materialize_accesses (m_vm_lazy wtouch_model) (m_vm_materialized wtouch_model)
    (vm_backing_used wtouch_model) ((m_vmmaps wtouch_model).vm_limit)
    [(BitVec.ofInt 64 0x1000, 1)] = none
  decide

theorem wtouch_is_budget_refused :
    budget_refused_at [] ⟨wtouch_ms, wtouch_model⟩ := by
  refine ⟨rfl, Or.inr ⟨BitVec.ofInt 64 64, rfl, Or.inr ?_⟩⟩
  exact ⟨wtouch_eff, wtouch_model,
    [event.WriteEv (BitVec.ofInt 64 1) (BitVec.ofInt 8 0)],
    check_syscall_sound_ok _ _ _ _ _ wtouch_checker, rfl,
    wtouch_materialization_fails⟩

theorem wtouch_errors :
    sstep [] ⟨wtouch_ms, wtouch_model⟩ [] .SError :=
  budget_fault_syscall_sstep_error [] wtouch_ms wtouch_model (BitVec.ofInt 64 64)
    wtouch_eff wtouch_model [event.WriteEv (BitVec.ofInt 64 1) (BitVec.ofInt 8 0)]
    rfl rfl (check_syscall_sound_ok _ _ _ _ _ wtouch_checker) rfl
    wtouch_materialization_fails

/- =========================================================================
   PART 4 — run level: the reflective evaluator discharges the premise
   ========================================================================= -/

theorem exits_c_no_budget_refused (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      m_halted model = none → m_vm_lazy model = [] →
      Examples.exits_c segs code fuel ms = true →
      ¬ reaches_budget_refused segs ⟨ms, model⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms model _ _ hc
      simp only [Examples.exits_c,
        LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c] at hc
      exact absurd hc (by simp)
  | succ n ih =>
      intro ms model hh hlazy hc hbr
      obtain ⟨tr, c, hstar, hb⟩ := hbr
      cases hp : ms.ms_svc_pending with
      | some x8 =>
          have h' : ((decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
              && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)) = true := by
            simpa only [Examples.exits_c,
              LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp] using hc
          rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq,
            beq_iff_eq] at h'
          obtain ⟨hno, hcode⟩ := h'
          have hno' : Examples.exit_sysno (sys_input segs ms x8).in_sysno := by
            rcases hno with hno | hno
            · exact Or.inl hno
            · exact Or.inr hno
          cases hstar with
          | refl =>
              rw [budget_refused_at_no_lazy_syscall segs ms model x8 hh hp ?_] at hb
              · rw [exit_is_never_budget_refused _ _ hno'] at hb
                exact absurd hb (by simp)
              · intro eff model' evs hspec
                obtain ⟨-, hm', -⟩ :=
                  LinuxSem.Checks.Examples.exit_dispatch_forced
                    (sys_input segs ms x8) model eff model' evs hno' hspec
                rw [hm']
                exact hlazy
          | step =>
              obtain ⟨m', hst, -, hhalt, -⟩ :=
                sstep_exit_only segs ms model x8 code hp hno' hcode _ (.SNext _) ‹_›
              cases hst
              obtain ⟨-, rfl⟩ :=
                star_from_halted segs ⟨ms, m'⟩ _ _ ‹_› (by rw [hhalt]; simp)
              exact absurd hb.1 (by rw [hhalt]; simp)
      | none =>
          cases hstep : RiscvSemantics.step segs ms with
          | MachineOk ms' =>
              have hrec : Examples.exits_c segs code n ms' = true := by
                simp only [Examples.exits_c,
                  LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at hc
                exact hc
              cases hstar with
              | refl => exact budget_refused_at_no_lazy_instr segs ms model hlazy hp hb
              | step =>
                  obtain ⟨-, hst⟩ :=
                    sstep_instr_only segs ms model ms' hlazy hp hstep _ (.SNext _) ‹_›
                  cases hst
                  exact ih ms' model hh hlazy hrec ⟨_, _, ‹_›, hb⟩
          | MachineFault =>
              simp only [Examples.exits_c,
                LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at hc
              exact absurd hc (by simp)
          | MachineUnmodeled =>
              simp only [Examples.exits_c,
                LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c, hp, hstep] at hc
              exact absurd hc (by simp)

theorem exit0_never_budget_refused (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ run_budget_refused exit0_image lim en inp := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  unfold run_budget_refused
  exact exits_c_no_budget_refused exit0_segments verdict_accept 8
    (init_machine_state exit0_segments 0x100 demo_phdrs sp rnd
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
    (init_model (segments_reserved exit0_segments) brk0 mbase sp lim inp)
    (m_halted_init_model _ _ _ _ _ _) (init_model_no_lazy _ _ _ _ _ _)
    (exit0_exits_c sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)

theorem exit0_source_within_budget (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    source_within_budget lim exit0_image en inp :=
  exit0_never_budget_refused lim en inp

/-- The sealed ascription: the exit-0 pair satisfies the error-free budget
    statement at EVERY pair of budgets — the image never touches the heap. -/
theorem exit0_strong_universal_error_free_budgets (lim_source lim_target : Int) :
    strong_universal_error_free_T_budgets lim_source lim_target exit0_image exit0_image := by
  intro en_s en_t inp _ _ _ _
  unfold strong_equiv_error_free_budgets
  refine ⟨?_, ?_, ?_⟩
  · rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp
  · rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp
  · intro tr
    simp only [run, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [exit0_obs en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw lim_source inp tr,
      exit0_obs en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw lim_target inp tr]

/-- The sealed surface `SPEC_ERROR_FREE_BUDGETS`, as a structure instance —
    the way `Checks.Omni` seals its surfaces (`Exit0Checked`,
    `Exit0ScfgAbortChecked`, …). -/
theorem Exit0BudgetsChecked : SPEC_ERROR_FREE_BUDGETS ShippedBudgets Exit0Image Exit0Image where
  strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets
      ShippedBudgets.lim_source ShippedBudgets.lim_target

/-- The abort twin: the exit-0 image is never killed — its trace set is the
    prefixes of one exit event. -/
theorem exit0_never_dies_by_signal (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ dies_by_signal (run exit0_image lim en inp) :=
  exit0_not_dies_by_signal lim en inp

theorem exit0_strong_universal_error_free_budgets_abort (lim_source lim_target : Int) :
    strong_universal_error_free_T_budgets_abort lim_source lim_target
      exit0_image exit0_image := by
  intro en_s en_t inp _ _ _ _
  unfold strong_equiv_error_free_budgets_abort error_free_unkilled
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp
  · exact exit0_never_dies_by_signal lim_source en_s inp
  · rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp
  · exact exit0_never_dies_by_signal lim_target en_t inp
  · intro tr
    simp only [run, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [exit0_obs en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw lim_source inp tr,
      exit0_obs en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw lim_target inp tr]

theorem Exit0BudgetsAbortChecked :
    SPEC_ERROR_FREE_BUDGETS_ABORT ShippedBudgets Exit0Image Exit0Image where
  strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_abort
      ShippedBudgets.lim_source ShippedBudgets.lim_target

/-- And the constant-pinned error-free statement hands over the budget one
    at the shipped constants without a new proof. -/
theorem exit0_budgets_from_pinned (H : strong_universal_error_free_T exit0_image exit0_image) :
    strong_universal_error_free_T_budgets source_alloc_limit target_alloc_limit
      exit0_image exit0_image :=
  strong_universal_error_free_T_budgets_of_pinned _ _ H

/- =========================================================================
   PART 5 — the configured family and the either pair, on the exit-0 pair
   ========================================================================= -/

theorem exit0_must_exit_at_cfg (cfg : SpuriousCfg) (sp brk0 mbase : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    must_exit_at_cfg cfg exit0_segments verdict_accept
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) := by
  unfold init_config
  exact LinuxSem.Checks.SpuriousCfg.exits_c_must_exit_at_cfg cfg exit0_segments
    verdict_accept 8 _ _ (m_halted_init_model _ _ _ _ _ _)
    (init_model_no_lazy _ _ _ _ _ _)
    (exit0_exits_c sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)

/-- A prefix of a one-element list appends to nothing: the only way
    `l ++ [a]` is a prefix of `[b]` is `l = []` and `a = b`. -/
theorem is_prefix_append_singleton {A : Type} {l : List A} {a b : A}
    (h : is_prefix (l ++ [a]) [b]) : l = [] ∧ a = b := by
  cases l with
  | nil =>
      simp only [List.nil_append, is_prefix] at h
      exact ⟨rfl, h.1⟩
  | cons x xs =>
      rw [List.cons_append] at h
      obtain ⟨-, h2⟩ := h
      cases xs <;> simp [is_prefix] at h2

theorem exit0_obs_cfg (cfg : SpuriousCfg) (sp brk0 mbase : word) (rnd : EntryDraw)
    (lim : Int) (inp : ProcInput) (tr : List event) :
    obs_trace_cfg exit0_segments cfg
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) tr
    <-> is_prefix tr [event.ExitEv verdict_accept (in_fs inp)] := by
  constructor
  · intro H
    exact (exit0_obs sp brk0 mbase rnd lim inp tr).mp
      (obs_trace_cfg_sub exit0_segments cfg _ _ H)
  · intro Hp
    obtain ⟨tr0, fs, c', hstar, -⟩ :=
      must_exit_at_cfg_realizes cfg exit0_segments verdict_accept _
        (exit0_must_exit_at_cfg cfg sp brk0 mbase rnd lim inp) rfl
    have hfull : obs_trace_cfg exit0_segments cfg
        (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp)
        (tr0 ++ [event.ExitEv verdict_accept fs]) :=
      ⟨_, _, hstar, is_prefix_refl _⟩
    have hpre := (exit0_obs sp brk0 mbase rnd lim inp _).mp
      (obs_trace_cfg_sub exit0_segments cfg _ _ hfull)
    obtain ⟨rfl, hev⟩ := is_prefix_append_singleton hpre
    rw [← hev] at Hp
    exact ⟨[event.ExitEv verdict_accept fs], c', hstar, Hp⟩

theorem exit0_strong_universal_error_free_budgets_scfg (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target
      exit0_image exit0_image := by
  intro en_s en_t inp _ _ _ _
  unfold strong_equiv_error_free_budgets_scfg
  refine ⟨?_, ?_, ?_⟩
  · apply error_free_scfg_of_error_free
    rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp
  · apply error_free_scfg_of_error_free
    rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp
  · intro tr
    simp only [run_scfg, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [exit0_obs_cfg cfg en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp tr,
      exit0_obs_cfg cfg en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp tr]

/-- The sealed surface `SPURIOUS_CFG`, as a structure instance. -/
def ForcedOnlyCfg : SPURIOUS_CFG := ⟨forced_only_cfg⟩

theorem Exit0ScfgBudgetsChecked :
    SPEC_ERROR_FREE_SCFG_BUDGETS ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image where
  strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_scfg ForcedOnlyCfg.cfg
      ShippedBudgets.lim_source ShippedBudgets.lim_target

theorem Exit0ScfgBudgetsBaselineChecked :
    SPEC_SCFG_BUDGETS ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image where
  strong_universal :=
    strong_universal_error_free_T_scfg_budgets_implies _ _ _ _ _
      Exit0ScfgBudgetsChecked.strong_universal_error_free

theorem exit0_source_within_budget_scfg (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : source_within_budget_scfg cfg lim exit0_image en inp :=
  source_within_budget_scfg_of_source_within_budget cfg lim exit0_image en inp
    (exit0_source_within_budget lim en inp)

theorem Exit0BudgetsEitherChecked :
    SPEC_ERROR_FREE_BUDGETS_EITHER ShippedBudgets Exit0Image Exit0Image where
  strong_universal_error_free :=
    ⟨exit0_strong_universal_error_free_budgets
        ShippedBudgets.lim_source ShippedBudgets.lim_target,
      exit0_strong_universal_error_free_budgets_abort
        ShippedBudgets.lim_source ShippedBudgets.lim_target⟩

theorem Exit0BudgetsEitherBaselineChecked :
    SPEC_BUDGETS_EITHER ShippedBudgets Exit0Image Exit0Image where
  strong_universal :=
    strong_universal_error_free_T_budgets_either_implies _ _ _ _
      Exit0BudgetsEitherChecked.strong_universal_error_free

/- ** The refutations, fired

    `Checks.Omni.ebreak_image` never allocates — its one instruction
    faults — so it satisfies the premise at every budget. -/

theorem demo_entry_valid_ebreak (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry ebreak_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk ebreak_image ebreak_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem ebreak_source_within_budget (lim : Int) :
    source_within_budget lim ebreak_image demo_entry demo_proc_input := by
  unfold source_within_budget run_budget_refused
  simp only [ebreak_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [ebreak_config]
  apply never_budget_refused_ind ebreak_segments
    (fun c => c = (⟨ebreak_ms, ebreak_model lim⟩ : config)) _ rfl
  · intro c evs c' hI hss
    rw [hI] at hss
    exact absurd (ebreak_only lim evs (.SNext c') hss).2 (by simp)
  · intro c hI hb
    rw [hI] at hb
    exact ebreak_fault_is_not_budget_refused lim hb

theorem ebreak_errors (lim : Int) :
    (run ebreak_image lim demo_entry demo_proc_input).bh_errors := by
  show reaches_error ebreak_segments
    (init_config ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim
      demo_proc_input)
  rw [ebreak_config]
  exact ⟨[], _, [], star.refl _,
    sstep.instr_fault _ _ rfl rfl (by no_lazy; rw [ebreak_faults])⟩

theorem ebreak_errors_cfg (cfg : SpuriousCfg) (lim : Int) :
    (run_scfg cfg ebreak_image lim demo_entry demo_proc_input).bh_errors := by
  show reaches_error_cfg ebreak_segments cfg
    (init_config ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim
      demo_proc_input)
  rw [ebreak_config]
  exact ⟨[], _, [], star_cfg.refl _,
    sstep_cfg.instr_fault _ _ rfl rfl (by no_lazy; rw [ebreak_faults])⟩

theorem ebreak_refutes_error_free_budgets (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_budgets lim_source lim_target
        ebreak_image exit0_image := by
  apply strong_universal_error_free_T_budgets_refuted_by_source_error
    _ _ _ _ demo_entry demo_entry demo_proc_input
  · apply demo_entry_valid_ebreak
    exact LinuxSem.Checks.Examples.demo_input_valid
  · apply LinuxSem.Checks.Examples.demo_entry_valid_exit0
    exact LinuxSem.Checks.Examples.demo_input_valid
  · exact LinuxSem.Checks.Examples.demo_input_valid
  · apply ebreak_source_within_budget
  · apply ebreak_errors

theorem ebreak_refutes_error_free_scfg_budgets (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets cfg lim_source lim_target
        ebreak_image exit0_image := by
  apply strong_universal_error_free_T_scfg_budgets_refuted_by_source_error
    _ _ _ _ _ demo_entry demo_entry demo_proc_input
  · apply demo_entry_valid_ebreak
    exact LinuxSem.Checks.Examples.demo_input_valid
  · apply LinuxSem.Checks.Examples.demo_entry_valid_exit0
    exact LinuxSem.Checks.Examples.demo_input_valid
  · exact LinuxSem.Checks.Examples.demo_input_valid
  · apply source_within_budget_scfg_of_source_within_budget
    apply ebreak_source_within_budget
  · apply ebreak_errors_cfg

/- =========================================================================
   PART 6 — the abort-declared configured budget cell
   ========================================================================= -/

/-- `abrt_input` and `abrt_input_valid` come from `Checks.AbortWitness`
    (imported), not from local copies: the fixture is shared so that PART 6
    speaks about the same input the abort refutation does.  The machine
    state at it is `Checks.Omni.ebreak_ms` (`ebreak_config_abort`), because
    the entry stack image does not read the declaration. -/

theorem demo_entry_valid_exit0_abort (inp : ProcInput) (Hvalid : valid_input_abort inp) :
    valid_entry exit0_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk exit0_image exit0_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem exit0_never_dies_by_signal_cfg (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : ¬ dies_by_signal (run_scfg cfg exit0_image lim en inp) := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  rintro ⟨tr, sig, fs, Hobs, Hin⟩
  simp only [run_scfg, exit0_image,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at Hobs
  rw [exit0_obs_cfg cfg sp brk0 mbase rnd lim inp tr] at Hobs
  cases tr with
  | nil => simp only [List.not_mem_nil] at Hin
  | cons e tr' =>
      obtain ⟨rfl, hp⟩ := Hobs
      cases tr' with
      | nil =>
          simp only [List.mem_singleton] at Hin
          cases Hin
      | cons e' tr'' => exact hp

theorem exit0_strong_universal_error_free_budgets_scfg_abort (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
      exit0_image exit0_image := by
  intro en_s en_t inp _ _ _ _
  unfold strong_equiv_error_free_budgets_scfg_abort error_free_unkilled
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · apply error_free_scfg_of_error_free
    rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp
  · exact exit0_never_dies_by_signal_cfg cfg lim_source en_s inp
  · apply error_free_scfg_of_error_free
    rw [error_free_iff]
    simpa only [LinuxSem.LinuxProcessSem.OmniRun.omni_corun, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
      using exit0_never_errors en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp
  · exact exit0_never_dies_by_signal_cfg cfg lim_target en_t inp
  · intro tr
    simp only [run_scfg, exit0_image,
      LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
    rw [exit0_obs_cfg cfg en_s.en_sp en_s.en_brk en_s.en_mmap_base en_s.en_draw
        lim_source inp tr,
      exit0_obs_cfg cfg en_t.en_sp en_t.en_brk en_t.en_mmap_base en_t.en_draw
        lim_target inp tr]

theorem Exit0ScfgBudgetsAbortChecked :
    SPEC_ERROR_FREE_SCFG_BUDGETS_ABORT ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image where
  strong_universal_error_free :=
    exit0_strong_universal_error_free_budgets_scfg_abort ForcedOnlyCfg.cfg
      ShippedBudgets.lim_source ShippedBudgets.lim_target

theorem Exit0ScfgBudgetsAbortBaselineChecked :
    SPEC_SCFG_BUDGETS_ABORT ForcedOnlyCfg ShippedBudgets Exit0Image Exit0Image where
  strong_universal :=
    strong_universal_error_free_T_scfg_budgets_abort_implies _ _ _ _ _
      Exit0ScfgBudgetsAbortChecked.strong_universal_error_free

/-! ** The refutation, fired under the abort declaration -/

def ebreak_model_abort (lim : Int) : Model :=
  init_model (segments_reserved ebreak_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) lim abrt_input

theorem ebreak_config_abort (lim : Int) :
    init_config ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim abrt_input
    = (⟨ebreak_ms, ebreak_model_abort lim⟩ : config) := rfl

theorem ebreak_only_abort (lim : Int) (evs : List event) (st : step_to)
    (hss : sstep ebreak_segments ⟨ebreak_ms, ebreak_model_abort lim⟩ evs st) :
    evs = [] ∧ st = .SError :=
  sstep_fault_only ebreak_segments ebreak_ms (ebreak_model_abort lim) rfl rfl
    ebreak_faults evs st hss

theorem ebreak_fault_is_not_budget_refused_any (model : Model) :
    ¬ budget_refused_at ebreak_segments ⟨ebreak_ms, model⟩ := by
  rintro ⟨-, hD⟩
  rcases hD with ⟨hsvc, r, hacc, hmat⟩ | ⟨x8, hx8, -⟩
  · have hd := drop_step_accesses ebreak_segments ebreak_ms
    rw [hacc, ebreak_faults] at hd
    simp [drop_access_report] at hd
  · rw [show ebreak_ms.ms_svc_pending = none from rfl] at hx8
    exact absurd hx8 (by simp)

theorem demo_entry_valid_ebreak_abort (inp : ProcInput) (Hvalid : valid_input_abort inp) :
    valid_entry ebreak_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk ebreak_image ebreak_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem ebreak_source_within_budget_abort (lim : Int) :
    source_within_budget lim ebreak_image demo_entry abrt_input := by
  unfold source_within_budget run_budget_refused
  simp only [ebreak_image, demo_entry,
    LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [ebreak_config_abort]
  apply never_budget_refused_ind ebreak_segments
    (fun c => c = (⟨ebreak_ms, ebreak_model_abort lim⟩ : config)) _ rfl
  · intro c evs c' hI hss
    rw [hI] at hss
    exact absurd (ebreak_only_abort lim evs (.SNext c') hss).2 (by simp)
  · intro c hI hb
    rw [hI] at hb
    exact ebreak_fault_is_not_budget_refused_any _ hb

theorem ebreak_errors_cfg_abort (cfg : SpuriousCfg) (lim : Int) :
    (run_scfg cfg ebreak_image lim demo_entry abrt_input).bh_errors := by
  show reaches_error_cfg ebreak_segments cfg
    (init_config ebreak_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim abrt_input)
  rw [ebreak_config_abort]
  exact ⟨[], _, [], star_cfg.refl _,
    sstep_cfg.instr_fault _ _ rfl rfl (by no_lazy; rw [ebreak_faults])⟩

theorem ebreak_refutes_error_free_scfg_budgets_abort (cfg : SpuriousCfg)
    (lim_source lim_target : Int) :
    ¬ strong_universal_error_free_T_scfg_budgets_abort cfg lim_source lim_target
        ebreak_image exit0_image := by
  apply strong_universal_error_free_T_scfg_budgets_abort_refuted_by_source_error
    _ _ _ _ _ demo_entry demo_entry abrt_input
  · apply demo_entry_valid_ebreak_abort
    exact abrt_input_valid
  · apply demo_entry_valid_exit0_abort
    exact abrt_input_valid
  · exact abrt_input_valid
  · apply source_within_budget_scfg_of_source_within_budget
    apply ebreak_source_within_budget_abort
  · apply ebreak_errors_cfg_abort

/- =========================================================================
   The mark and the filter agree
   ========================================================================= -/

/-- A configuration removes a refusal only where a non-refusal is also
    admitted (`Run.spurious_refusal_cfg`).  Where the mark fires, every
    admitted outcome IS a refusal (the soundness lemmas of PART 1), so
    nothing at that configuration is spurious and the configured step
    relation admits exactly the unfiltered steps: the mark is about a
    step no configuration can remove.  Stated for the arms whose
    soundness lemma covers the whole arm; mremap's mark can fire where
    a move is still admitted (`ov_mark_fires_while_a_move_fits`), so it
    is left out here.

    The number set is stated in `Nat` — `[214, 222, 226]` — because
    `Run.alloc_budget_refused_b` compares `in_sysno.toNat` (a `Nat`); that
    is the spelling that composes with `Run.alloc_mark_sysnos`, and the
    three-way split is `List.mem_cons`. -/
theorem mark_is_never_spurious (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect)
    (hno : i.in_sysno.toNat ∈ [214, 222, 226])
    (hmark : alloc_budget_refused_b i m = true) :
    ¬ spurious_refusal_cfg cfg i m eff := by
  rintro ⟨-, -, eff', m', evs', Hspec, Hnr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
  rcases hno with h214 | h222 | h226
  · rw [brk_budget_refused_is_refusal i m eff' m' evs' h214 hmark Hspec] at Hnr
    exact absurd Hnr (by simp)
  · rw [mmap_budget_refused_is_refusal i m eff' m' evs' h222 hmark Hspec] at Hnr
    exact absurd Hnr (by simp)
  · rw [mprotect_budget_refused_is_refusal i m eff' m' evs' h226 hmark Hspec] at Hnr
    exact absurd Hnr (by simp)

/-- The step-level corollary: at a pending allocation syscall whose mark
    fires, the CONFIGURED step relation admits every unfiltered step, so a
    step that would be dropped as a spurious refusal survives the filter.
    The five syscall-ending constructors are the five that can consume an
    outcome; only `syscall` and `syscall_materialization_fault` carry the
    non-spuriousness premise, and it is `mark_is_never_spurious` there.

    The `hx` below does what a `unify_svc` step would — it rewrites the
    branch's pending-number to the statement's — from the two `some`
    equalities the constructor and the hypothesis give. -/
theorem marked_step_is_configured (cfg : SpuriousCfg) (segs : List Segment)
    (ms : machine_state) (model : Model) (x8 : word) (evs : List event) (st : step_to)
    (hsvc : ms.ms_svc_pending = some x8)
    (hno : x8.toNat ∈ [214, 222, 226])
    (hmark : alloc_budget_refused_b (sys_input segs ms x8) model = true)
    (hss : sstep segs ⟨ms, model⟩ evs st) :
    sstep_cfg segs cfg ⟨ms, model⟩ evs st := by
  cases hss with
  | instr ms model ms' model' hh hsvc0 hstep =>
      exact sstep_cfg.instr _ _ _ _ hh hsvc0 hstep
  | instr_fault ms model hh hsvc0 hstep =>
      exact sstep_cfg.instr_fault _ _ hh hsvc0 hstep
  | instr_unmodeled ms model hh hsvc0 hstep =>
      exact sstep_cfg.instr_unmodeled _ _ hh hsvc0 hstep
  | syscall ms model x8' eff model' model'' evs' hh hsvc0 hspec hh' hmat =>
      have hx : x8' = x8 := by
        rw [hsvc] at hsvc0
        exact (Option.some.inj hsvc0).symm
      have hno' : x8'.toNat ∈ [214, 222, 226] := by rw [hx]; exact hno
      have hmark' : alloc_budget_refused_b (sys_input segs ms x8') model = true := by
        rw [hx]; exact hmark
      exact sstep_cfg.syscall _ _ _ _ _ _ _ hh hsvc0 hspec
        (mark_is_never_spurious cfg (sys_input segs ms x8') model eff hno' hmark') hh' hmat
  | syscall_materialization_fault ms model x8' eff model' evs' hh hsvc0 hspec hh' hmat =>
      have hx : x8' = x8 := by
        rw [hsvc] at hsvc0
        exact (Option.some.inj hsvc0).symm
      have hno' : x8'.toNat ∈ [214, 222, 226] := by rw [hx]; exact hno
      have hmark' : alloc_budget_refused_b (sys_input segs ms x8') model = true := by
        rw [hx]; exact hmark
      exact sstep_cfg.syscall_materialization_fault _ _ _ _ _ _ hh hsvc0 hspec
        (mark_is_never_spurious cfg (sys_input segs ms x8') model eff hno' hmark') hh' hmat
  | exit ms model x8' eff model' evs' code hh hsvc0 hspec hh' hk =>
      exact sstep_cfg.exit _ _ _ _ _ _ _ hh hsvc0 hspec hh' hk
  | killed ms model x8' eff model' evs' sig hh hsvc0 hspec hk =>
      exact sstep_cfg.killed _ _ _ _ _ _ _ hh hsvc0 hspec hk
  | syscall_unmodeled ms model x8' hh hsvc0 hspec =>
      exact sstep_cfg.syscall_unmodeled _ _ _ hh hsvc0 hspec

end LinuxSem.Checks.BudgetPremise
