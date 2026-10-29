/-
  * Common.NoReserve — the MAP_NORESERVE mmap node, lazy-tolerant
    syscall nodes, and the chained disjoint straight line

    TRUST BOUNDARY: image-INDEPENDENT proof library, like [ShapeAlg] /
    [SpinAlg] (which this file extends) and [LazyFrame] / [DivergeSim]
    (whose machinery it consumes).  Nothing here is part of the trusted
    specification.

    This file closes the three residuals [SpinAlg]'s header enumerates —
    the last proof-infrastructure tier before a full ASan equivalence
    skeleton is writable with node applications only:

    RESIDUAL 1 — THE NORESERVE-SHAPED MMAP NODE.  [mmap_args_ok] pins
    flags = MAP_PRIVATE|MAP_ANONYMOUS (34), so ASan's shadow reservation
    (34 | 0x4000 = MAP_NORESERVE, i.e. 16418) had no node.
    [mmap_args_ok_noreserve] pins the NORESERVE spelling of the same
    modeled shape ([Mmap.mmap_flags_core] masks exactly that bit before
    the shape match, Mmap:335-336/796-799), and the node family
    ([node_mmap_noreserve], [srz_mmap_noreserve], [srz_mmap_spin_noreserve],
    with the inversion [sstep_mmap_inv_noreserve]) mirrors [SpinAlg]'s,
    with two deliberate differences:
      - the grant successor wraps the model with [vm_add_lazy] (the
        [with_mmap_backing] path, Mmap:341-342/944): [mmap_model_noreserve]
        = [vm_add_lazy a n (mmap_model a n model)], so after a grant
        [m_vm_lazy] is NON-EMPTY (State:2307-2317 — the interior of a
        page-aligned, page-rounded nonzero grant is the singleton
        [(a, n)]);
      - the grant condition [grant_ok_nr] has NO budget conjunct: the
        reservation is granted regardless of remaining backed budget
        ([mmap_noreserve_backed_ok], Mmap:873-876, unconditionally
        [true] for a NORESERVE call — pages charge on first touch inside
        [mi_account_step], Run:277-287).
    The refusal arm is RETAINED (failure-anytime stays, by ruling): the
    plain node keeps both arms, and the spin-armed node discharges each
    refusal by [DivergeSim.to_spin] exactly as [SpinAlg.srz_mmap_spin].

    RESIDUAL 2 — LAZY-TOLERANT SYSCALL NODES.  After a NORESERVE grant,
    every [m_vm_lazy model = []] premise is dead for the rest of the run
    on the grant path.  The nodes the ASan skeleton needs are re-derived
    without it:
      - mmap / munmap / exit have EMPTY effect access lists
        ([State.syscall_effect_accesses]: no [eff_writes], no
        [eff_copyins]), so [DivergeSim.materialize_model_accesses_nil]
        replaces [materialize_model_accesses_no_lazy] and the premise
        just DROPS: [node_mmap_lazy] / [srz_mmap_lazy] /
        [srz_mmap_spin_lazy], [node_munmap_lazy] / [srz_munmap_lazy]
        (with inversions [sstep_mmap_inv_lazy] / [sstep_munmap_inv_lazy]).
        [SpinAlg.srz_exit] never had the premise — exit needs nothing.
      - write(1, buf, n) is the one node whose effect DOES carry an
        access ([eff_copyins = [(buf, n)]] — the syscall READS user
        memory, and a read materializes lazy pages like any access), so
        its lazy-tolerant form takes the [LazyFrame] DISJOINTNESS
        hypothesis instead — the buffer lies outside every lazy range
        ([node_write1_disjoint] / [srz_write1_disjoint], inversions
        [sstep_write_next_inv_disjoint] / [sstep_write_inv_disjoint]).
        In an ASan binary that hypothesis is real and discharged by the
        placement gate: the buffer lives in the binary's data/stack
        segments, and [grant_ok]/[grant_ok_nr]'s [region_free] keeps
        every reservation disjoint from the image.

    RESIDUAL 3 — THE CHAINED DISJOINT STRAIGHT LINE.  [msteps_acc], the
    [msteps] analog that CARRIES the per-step access reports, with
    [srz_msteps_disjoint] / [rz_msteps_disjoint] / [ts_msteps_disjoint]:
    a straight line of instructions whose accumulated report is disjoint
    from every lazy range walks any [srealizes]/[realizes]/[to_spin]
    obligation through a non-empty ledger.  The per-instruction
    [stepacc_*] lemmas mirror [PropExec]'s step inventory at the
    [step_accesses] level (same hypotheses, conclusion carries the access
    report): the generic ALU/branch/jump/ecall forms report [] and the
    seven load forms report their single read range.  PropExec has no
    store lemmas, so none are mirrored here (same scope, one level down).

    The worked example [AsanInitReal] at the bottom is the full ASan-init
    shape in miniature: a NORESERVE reservation (refusal spins; grant
    makes the ledger non-empty), a plain rw mmap THROUGH the non-empty
    ledger (refusal spins; grant continues), a write(1) of a
    ledger-disjoint buffer, and an exit — concluding the standard
    obs_iff / no_error pair with a proof that is node applications and
    leaves only.


  V` (1,898 lines).

  — WHAT IS HERE AND WHAT IS NOT.  This tree proceeded in
  dependency order against the modules that exist in the tree.  Everything
  below that needs only `RiscvSem`, `RiscvSemantics`, `State`/`StateVm`/
  `StateLedger`, `Sys/Mm/Mmap`, `Common/PropExec`, `Common/MmapSim`,
  `Common/DivergeSim`, `Common/SpinAlg`, `Common/LazyFrame`,
  `Common/ExitSim` and `Checks/Sys/{Prelude,Mm/Mmap}` is stated and
  checked here.  **Nothing in this file is deferred**, and there is no
  `DEFERRED` block: the declarations that once waited on a module now in
  the tree have landed .  Nothing
  here is stubbed, weakened, or axiomatized.
  WHAT IS IN.   - RESIDUAL 2, the lazy-tolerant syscall nodes: `sstep_mmap_inv_lazy` /
    `node_mmap_lazy` / `srz_mmap_lazy` / `srz_mmap_spin_lazy` (the
    `m_vm_lazy model = []` premise DROPPED — both resolutions' effects
    name no access, so `materialize_syscall_effect_nil` applies on any
    ledger), `sstep_munmap_inv_lazy` / `node_munmap_lazy` /
    `srz_munmap_lazy`, and the write(1) family
    `sstep_write_next_inv_disjoint` / `sstep_write_inv_disjoint` /
    `node_write1_disjoint` / `srz_write1_disjoint` (disjointness, not an
    empty ledger, via `materialize_syscall_effect_copyin_disjoint`).
    `SpinAlg.srz_exit` needed no re-derivation.
  - RESIDUAL 3, the chained disjoint straight line: `msteps_acc` with
    `msteps_acc_one` / `msteps_acc_trans`, the three consumers
    `srz_msteps_disjoint` / `rz_msteps_disjoint` / `ts_msteps_disjoint`,
    and the twenty-two per-instruction `stepacc_*` forms.
  - the worked example (`Section AsanInitReal`), all three theorems:
    `asan_init_srealizes`, `asan_init_obs_iff`, `asan_init_no_error`.
  TWO DECISIONS the reader should know about:
  1. the five disjointness-plumbing lemmas
     (`access_outside_range_mono`, `accesses_outside_lazy_incl` /
     `_app_l` / `_app_r` / `_shrink`) are NOT restated here:
     `Common/LazyFrame.lean` owns the two predicates they are about and
     owns them next to them, and this file OPENS that module.  See the
     "Disjointness plumbing" section of this file.
  2. four declarations whose home is a DIFFERENT module are carried here
     with their own notes: all four are now EXACT
     DUPLICATES of a landed declaration, kept because this file's own
     proofs use the local names.  Referrers, so a cleanup can be scoped
     (by name, not line: the lines move):
       - `node_instr_disjoint` — its only referrers are the local
         `rz_step_disjoint` and `srz_step_disjoint` just below it; no
         referrer outside this file.
       - `rz_step_disjoint` / `srz_step_disjoint` — the two `msteps_acc`
         consumers below; no referrer outside this file.
       - `t_writes_ch_pick_exit_iff` — `asan_init_obs_iff` below; no
         referrer outside this file.
     `Common/NoReserve.lean` imports `SpinAlg` and `ShapeAlg`, so the
     landed names are already in scope (qualified); nothing imports
     `NoReserve` except `Common/AsanNodesMmLib.lean`.
 `srealizes`, `node_ok` and `TSet` likewise all take
  `segs` explicitly.  The `sstep_*_inv_*` inversions of RESIDUAL 1/2 are
  this file's own work and are all proved above.
  — VOCABULARY. -/

import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.Common.PropExec
import LinuxSem.Common.DivergeSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.SpinAlg
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.LazyFrame
import LinuxSem.Common.ExitSim
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Mm.Mmap
import LinuxSem.Common.SharedFacts

namespace LinuxSem.Common.NoReserve

open LinuxSem.Common.SharedFacts (materialize_model_accesses_nil)

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Prelude (errno_ret_in errno_ret_in_below errno_ret_in_true
  errno_ret_in_intro listNN_eqb listNN_eqb_eq check_result)
open LinuxSem.Common.PropExec
open LinuxSem.Common.DivergeSim (to_spin)
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.LazyFrame
open LinuxSem.Common.ExitSim (is_exit_no)
open LinuxSem.Common.MmapSim (mmap_model grant_ok mmap_args_ok mmap_args_ok_gates
  syscall_spec_mmap mmap_fail_ok mmap_succ_ok mmap_ok_inv mmap_no_unmodeled munmap_eff munmap_model
  munmap_ok munmap_ok_inv grant_ok_unpack grant_not_errno munmap_model_halted mmap_model_halted
  munmap_args_ok munmap_no_unmodeled ENOMEM_in_mmap_errnos page_round_up)
open LinuxSem.Common.CatSim (apply_effect_no_write apply_effect_copyins_no_write
  fd1chan msteps buf_modeled write1_ok_n write1_ok_inv write1_no_unmodeled
  sstep_write_inv sstep_write_next_inv wpick wevents_ch wpick_wevents)

/-  `{fx : FPState}` context: every lemma in the file is
    polymorphic in the (integer-instruction-preserved) FP state, and the
    `PropExec`/`MmapSim` lemmas this file cites carry the same implicit
    argument, so it has to be in scope throughout.  Most of the lemmas
    below never mention it, hence the linter setting — the same one
    `Common/PropExec.lean` and `Common/MmapSim.lean` use. -/
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable [fx : FPState]

/- ================================================================= -/
/- Materialization plumbing: the two wrappers every node below uses    -/
/- ================================================================= -/

/-- A syscall effect with no writes and no copyins names no user-memory
    access: materializing it is the identity on ANY model (the
    `DivergeSim.materialize_model_accesses_nil` instance, stated at the
    effect so the node proofs can rewrite without normalizing
    `syscall_effect_accesses` first).  This covers every effect the mmap
    / munmap / exit nodes produce. -/
theorem materialize_syscall_effect_nil (m : Model) (r : word)
    (zs us : List (word × word)) :
    materialize_model_accesses m
      (syscall_effect_accesses (SyscallEffect.mkEffectU r [] zs us [] [])) = some m := by
  simp only [syscall_effect_accesses, write_accesses]
  exact materialize_model_accesses_nil m

/-- The munmap-effect spelling of the same fact (`munmap_eff` is a
    definition, so the `mkEffectU` pattern above does not match it
    syntactically). -/
theorem materialize_munmap_eff_nil (m : Model) (ms : machine_state) :
    materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms)) = some m := by
  simp only [munmap_eff, syscall_effect_accesses, write_accesses]
  exact materialize_model_accesses_nil m

/-- The write effect's single copyin range, materialized through a
    disjoint ledger: the identity ([LazyFrame]'s
    [materialize_model_accesses_disjoint] instance at the effect,
    NoReserve:98-108). -/
theorem materialize_syscall_effect_copyin_disjoint (m : Model) (r a : word) (n : Nat)
    (Hout : accesses_outside_lazy [(a, n)] (m_vm_lazy m)) :
    materialize_model_accesses m
      (syscall_effect_accesses (with_copyins [(a, n)] (mkEffect r [] []))) = some m := by
  simp only [syscall_effect_accesses, with_copyins, mkEffect, write_accesses,
    List.append_nil]
  exact materialize_model_accesses_disjoint m [(a, n)] Hout

/- ================================================================= -/
/- Disjointness plumbing                                            -/
/- ================================================================= -/

/- — the disjointness plumbing is NOT restated here.
 Restating them here would duplicate `Common/LazyFrame`'s
    definitions, so this file only OPENS `Common.LazyFrame`: every
    consumer below gets `access_outside_range_mono` /
    `accesses_outside_lazy_incl` / `_app_l` / `_app_r` / `_shrink`
    unqualified from there. -/

/- ================================================================= -/
/- The NORESERVE model transformer and its frame                      -/
/- ================================================================= -/

/-- State after a granted NORESERVE reservation: the ordinary grant
    ledger entry plus the lazy-backing record — exactly the
    `with_mmap_backing flags a n (with_vmmaps ... m)` the spec's grant
    branch applies when the NORESERVE bit is set (Mmap:941-948,
    341-342). -/
def mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m)

theorem mmap_model_noreserve_halted (a n : word) (m : Model) :
    m_halted (mmap_model_noreserve a n m) = m_halted m := by
  simp only [mmap_model_noreserve, mmap_model, vm_add_lazy, with_vm_backing, with_vmmaps,
    m_halted]

theorem mmap_model_noreserve_fs (a n : word) (m : Model) :
    m_fs (mmap_model_noreserve a n m) = m_fs m := by
  simp only [mmap_model_noreserve, mmap_model, vm_add_lazy, with_vm_backing, with_vmmaps, m_fs]

theorem mmap_model_noreserve_fd1chan (a n : word) (m : Model) (H : fd1chan m) :
    fd1chan (mmap_model_noreserve a n m) := by
  unfold fd1chan at *
  simpa only [mmap_model_noreserve, mmap_model, vm_add_lazy, with_vm_backing, with_vmmaps,
    m_fds] using H

/-- The whole point: the grant's page-aligned interior lands on the
    ledger.  For the modeled grant shape (`a` page-aligned, `n` the
    page-rounded nonzero length) `lazy_interior a n = [(a, n)]`, so the
    ledger is non-empty from here on. -/
theorem mmap_model_noreserve_lazy (a n : word) (m : Model) :
    m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m := by
  simp only [mmap_model_noreserve, mmap_model, vm_add_lazy, with_vm_backing, with_vmmaps,
    m_vm_lazy]

/- ================================================================= -/
/- RESIDUAL 1 — the NORESERVE-shaped mmap call                        -/
/- ================================================================= -/

/-- The register shape of the ASan shadow reservation: the ONE modeled
    anonymous rw shape (`Mmap.mmap_modeled_b`, which masks the
    NORESERVE bit out via `mmap_flags_core`) with the bit SET:
    flags (a3) = MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE
               = 2 + 32 + 16384 = 16418. -/
def mmap_args_ok_noreserve (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ BitVec.ofInt 64 0 ∧ ms_gpr ms 2 = BitVec.ofInt 64 3
  ∧ ms_gpr ms 3 = BitVec.ofInt 64 16418 ∧ ms_gpr ms 4 = BitVec.ofInt 64 (-1)
  ∧ ms_gpr ms 5 = BitVec.ofInt 64 0

/-- Under `mmap_args_ok_noreserve` the fail-closed gates of
    `check_mmap` / `mmap_spec` are open: the masked shape matches. -/
theorem mmap_args_ok_noreserve_gates (ms : machine_state)
    (h : mmap_args_ok_noreserve ms) :
    mmap_off_aligned_b (ms_gpr ms 5) = true ∧
    mmap_anon_b (ms_gpr ms 3) = true ∧
    w_is0 (ms_gpr ms 1) = false ∧
    mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true := by
  obtain ⟨H1, H2, H3, H4, H5⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mmap_off_aligned_b
    rw [H5]
    decide
  · unfold mmap_anon_b
    rw [H3]
    decide
  · unfold w_is0
    exact bv_eqb_neq _ _ H1
  · unfold mmap_modeled_b
    rw [H2, H3, H5]
    decide

/-- The NORESERVE bit, read back where it changes answers. -/
theorem mmap_noreserve_b_flags : mmap_noreserve_b (BitVec.ofInt 64 16418) = true := by
  decide

/-- May the kernel grant the NORESERVE reservation `[a, a+n)`?
    `MmapSim.grant_ok` minus the backed-budget conjunct: the reservation
    is granted UNCONDITIONALLY on budget (`mmap_noreserve_backed_ok` is
    `true` for a NORESERVE call); pages charge on first touch. -/
def grant_ok_nr (_hint : word) (m : Model) (a : word) (n : Int) : Bool :=
  -- `hint` is the address hint `grant_ok` takes; unused here exactly as
  --  is (the model's placement is nondeterministic).
  decide ((a.toNat : Int) % page_size = 0) && decide (0 < (a.toNat : Int))
  && decide ((a.toNat : Int) + n ≤ alloc_top (m_vmmaps m))
  && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
       (BitVec.ofInt 64 n)

theorem grant_ok_nr_unpack (hint : word) (m : Model) (a : word) (n : Int)
    (h : grant_ok_nr hint m a n = true) :
    (a.toNat : Int) % page_size = 0 ∧ 0 < (a.toNat : Int) ∧
    (a.toNat : Int) + n ≤ alloc_top (m_vmmaps m) ∧
    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
      (BitVec.ofInt 64 n) = true := by
  unfold grant_ok_nr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A budget-free grant is a fortiori not an errno encoding. -/
theorem grant_nr_not_errno (hint : word) (model : Model) (a : word) (n : Int)
    (Hn : 0 ≤ n) (Hg : grant_ok_nr hint model a n = true) :
    errno_ret_in mmap_errnos a = false := by
  obtain ⟨_, _, Hce, _⟩ := grant_ok_nr_unpack hint model a n Hg
  apply errno_ret_in_below
  · decide
  · have hroom := alloc_top_room (m_vmmaps model)
    have hs : stack_max_size = 8388608 := rfl
    have h1 : (a.toNat : Int) ≤ alloc_top (m_vmmaps model) := by omega
    unfold two_pow_64 at *
    omega

/-- The errno resolutions of the NORESERVE call (failure-anytime is
    retained: this arm exists for every modeled mmap shape). -/
theorem mmap_fail_ok_noreserve (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (e : Int) (Hno : (x8.toNat : Int) = 222)
    (Ha : mmap_args_ok_noreserve ms) (HIn : e ∈ mmap_errnos) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (errno_ret e) [] []) model []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_noreserve_gates ms Ha
  apply (syscall_spec_mmap segs ms x8 model _ Hno).mpr
  apply check_mmap_sound_ok
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb]
  simp only []
  rw [errno_ret_in_intro mmap_errnos e HIn]
  simp only [Bool.not_true, Bool.false_eq_true, ite_true, ite_false]

/-- The grant resolutions: any `grant_ok_nr` address, successor model
    `vm_add_lazy`-wrapped. -/
theorem mmap_succ_ok_noreserve (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (a : word) (Hno : (x8.toNat : Int) = 222)
    (Ha : mmap_args_ok_noreserve ms)
    (Hg : grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int))
      = true) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_noreserve_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  apply (syscall_spec_mmap segs ms x8 model _ Hno).mpr
  apply check_mmap_sound_ok
  obtain ⟨Hg1, Hg2, Hg3, Hg4⟩ := grant_ok_nr_unpack (ms_gpr ms 0) model a _ Hg
  unfold check_mmap
  rw [Hoff, Hanon, Hl, Hmb]
  simp only []
  have hn : 0 ≤ page_round_up_Z ((ms_gpr ms 1).toNat : Int) :=
    page_round_up_Z_nonneg _ (Int.natCast_nonneg _)
  rw [grant_nr_not_errno (ms_gpr ms 0) model a _ hn Hg]
  have hcond1 : decide ((a.toNat : Int) % page_size = 0) = true := by
    simp only [decide_eq_true_eq]
    exact Hg1
  have hcond2 : decide (0 < (a.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hg2
  have hcond3 : decide ((a.toNat : Int) + page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤
      alloc_top (m_vmmaps model)) = true := by
    simp only [decide_eq_true_eq]
    exact Hg3
  have hcond4 : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) a
      (BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int))) = true := Hg4
  have hcond5 : mmap_noreserve_backed_ok (ms_gpr ms 3) model
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true := by
    unfold mmap_noreserve_backed_ok
    rw [Hflags, mmap_noreserve_b_flags]
    rfl
  have hcond6 : listNN_eqb [(a, page_round_up (ms_gpr ms 1))]
      [(a, BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int)))] = true := by
    simp only [page_round_up, listNN_eqb_eq]
  rw [hcond1, hcond2, hcond3, hcond4, hcond5, hcond6]
  simp only [Bool.true_and, ite_true]
  unfold with_mmap_backing
  rw [Hflags, mmap_noreserve_b_flags]
  simp only [ite_true]
  unfold mmap_model_noreserve mmap_model page_round_up
  rfl

/-- Inversion: the admissible outcomes of the NORESERVE call are
    EXACTLY the errnos plus the `grant_ok_nr` grants. -/
theorem mmap_ok_inv_noreserve (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok_noreserve ms)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)) :
    evs = [] ∧
    ((∃ e, e ∈ mmap_errnos ∧ eff = mkEffect (errno_ret e) [] [] ∧ model' = model) ∨
     (∃ a, grant_ok_nr (ms_gpr ms 0) model a
          (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true ∧
        eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))] ∧
        model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)) := by
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_noreserve_gates ms Ha
  obtain ⟨_, _, Hflags, _, _⟩ := Ha
  have H2 := (syscall_spec_mmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_mmap_complete_ok (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
    (ms_gpr ms 4) (ms_gpr ms 5) eff model model' evs (sys_input segs ms x8) H2
  unfold check_mmap at H3
  rw [Hoff, Hanon, Hl, Hmb] at H3
  simp only [Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H3
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws with
  | cons _ _ => simp at H3
  | nil =>
    cases us with
    | cons _ _ => simp at H3
    | nil =>
      cases cs with
      | cons _ _ => simp at H3
      | nil =>
        cases ci with
        | cons _ _ => simp at H3
        | nil =>
          simp only [] at H3
          by_cases Herr : errno_ret_in mmap_errnos r = true
          · rw [ite_eq_left Herr] at H3
            cases zs with
            | cons _ _ => simp at H3
            | nil =>
              obtain ⟨hmm, hev⟩ := check_result.CheckOk.inj H3
              obtain ⟨e, hmem, heq⟩ := (errno_ret_in_true mmap_errnos r).mp Herr
              refine ⟨hev.symm, Or.inl ⟨e, hmem, ?_, hmm.symm⟩⟩
              simp only [mkEffect, heq]
          · rw [ite_eq_right Herr] at H3
            split at H3
            · rename_i hcond
              obtain ⟨hmm, hev⟩ := check_result.CheckOk.inj H3
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              obtain ⟨⟨⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩, hg5⟩, hg6⟩ := hcond
              have hz : zs = [(r, BitVec.ofInt 64 (page_round_up_Z ((ms_gpr ms 1).toNat : Int)))] :=
                (listNN_eqb_eq _ _).mp hg6
              have hd1 : decide ((r.toNat : Int) % page_size = 0) = true := by
                simp only [decide_eq_true_eq]
                exact hg1
              have hd2 : decide (0 < (r.toNat : Int)) = true := by
                simp only [decide_eq_true_eq]
                exact hg2
              have hd3 : decide ((r.toNat : Int) +
                  page_round_up_Z ((ms_gpr ms 1).toNat : Int) ≤
                  alloc_top (m_vmmaps model)) = true := by
                simp only [decide_eq_true_eq]
                exact hg3
              refine ⟨hev.symm, Or.inr ⟨r, ?_, ?_, ?_⟩⟩
              · unfold grant_ok_nr
                rw [hd1, hd2, hd3, hg4]
                rfl
              · simp only [mkEffect, page_round_up, hz]
              · rw [hmm.symm, Hflags]
                unfold with_mmap_backing
                rw [mmap_noreserve_b_flags]
                simp only [ite_true]
                unfold mmap_model_noreserve mmap_model page_round_up
                rfl
            · simp at H3

theorem mmap_no_unmodeled_noreserve (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : (x8.toNat : Int) = 222) (Ha : mmap_args_ok_noreserve ms) :
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hspec
  obtain ⟨Hoff, Hanon, Hl, Hmb⟩ := mmap_args_ok_noreserve_gates ms Ha
  have H2 := (syscall_spec_mmap segs ms x8 model _ Hno).mp Hspec
  have H3 := check_mmap_complete_unmodeled (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2)
    (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) model (sys_input segs ms x8)
    (mkEffect (BitVec.ofInt 64 0) [] []) H2
  unfold check_mmap at H3
  rw [Hoff, Hanon, Hl, Hmb] at H3
  simp only [Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H3
  repeat' split at H3
  all_goals simp at H3

/- ----------------------------------------------------------------- -/
/- One-step inversion for the NORESERVE mmap config — LAZY-TOLERANT   -/
/- by construction: both resolutions' effects name no access, so the  -/
/- materialization collapses on ANY ledger.                          -/
/- ----------------------------------------------------------------- -/

/-- Inversion: the admissible outcomes of the NORESERVE call are
    EXACTLY the errnos plus the `grant_ok_nr` grants.  NO ledger
    hypothesis: the materialization step is
    `materialize_syscall_effect_nil`, which holds for every `Model`. -/
theorem sstep_mmap_inv_noreserve (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok_noreserve ms)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    evs = [] ∧
    ((∃ e, e ∈ mmap_errnos ∧
        st = .SNext ⟨advance_past_svc (set_gpr0 ms (errno_ret e)), model⟩) ∨
     (∃ a, grant_ok_nr (ms_gpr ms 0) model a
          (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true ∧
        st = .SNext ⟨advance_past_svc
              (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])),
            mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model⟩)) := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x80 eff model' model'' evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨Hevs, Hcase⟩ :=
      mmap_ok_inv_noreserve segs ms x8 model eff model' _ Hno Hargs hspec
    subst Hevs
    refine ⟨rfl, ?_⟩
    rcases Hcase with ⟨e, He, heff, hmodel⟩ | ⟨a, Hg, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hmat
      have hmm : model'' = model := by
        rw [materialize_syscall_effect_nil] at hmat
        exact (Option.some.inj hmat).symm
      rw [hmm, apply_effect_no_write]
      exact Or.inl ⟨e, He, rfl⟩
    · subst heff
      rw [hmodel] at hmat
      have hmm : model'' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model := by
        rw [materialize_syscall_effect_nil] at hmat
        exact (Option.some.inj hmat).symm
      rw [hmm]
      exact Or.inr ⟨a, Hg, rfl⟩
  | syscall_materialization_fault ms0 model0 x80 eff model' evs0 hh hsvc hspec hh' hmat =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv_noreserve segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_nil] at hmat
      cases hmat
    · subst heff
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_nil] at hmat
      cases hmat
  | exit ms0 model0 x80 eff model' evs0 code hh hsvc hspec hh' hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv_noreserve segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hh'
      rw [Hh] at hh'
      cases hh'
    · subst heff
      rw [hmodel] at hh'
      rw [mmap_model_noreserve_halted, Hh] at hh'
      cases hh'
  | killed ms0 model0 x80 eff model' evs0 sig hh hsvc hspec hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv_noreserve segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hk
      rw [m_killed_of_m_halted_none _ Hh] at hk
      cases hk
    · subst heff
      rw [hmodel] at hk
      rw [m_killed_of_m_halted_none _ (by rw [mmap_model_noreserve_halted]; exact Hh)] at hk
      cases hk
  | syscall_unmodeled ms0 model0 x80 hh hsvc hspec =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    exact mmap_no_unmodeled_noreserve segs ms x8 model Hno Hargs hspec

/-- The index type of a NORESERVE node's resolutions: an errno refusal,
    or a `grant_ok_nr` grantable address. -/
abbrev MmapNrIdx (ms : machine_state) (model : Model) : Type :=
  { e : Int // e ∈ mmap_errnos } ⊕
  { a : word // grant_ok_nr (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }

/-- The successor configuration of a NORESERVE resolution (the grant
    successor's model is `vm_add_lazy`-wrapped). -/
def mmap_nr_next (ms : machine_state) (model : Model) : MmapNrIdx ms model → config
  | .inl e => ⟨advance_past_svc (set_gpr0 ms (errno_ret e.1)), model⟩
  | .inr a => ⟨advance_past_svc
      (apply_effect ms (mkEffect a.1 [] [(a.1, page_round_up (ms_gpr ms 1))])),
      mmap_model_noreserve a.1 (page_round_up (ms_gpr ms 1)) model⟩

/-- The NORESERVE node's interface.  NO ledger hypothesis at all: the
    reservation itself is usable both before (ASan's shadow, empty
    ledger) and after (a second reservation) the ledger fills. -/
theorem node_mmap_noreserve (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok_noreserve ms) :
    node_ok segs (mkCfg ms model) (MmapNrIdx ms model) (fun _ => []) (mmap_nr_next ms model) := by
  constructor
  · rintro (⟨e, He⟩ | ⟨a, Ha⟩)
    · exact sstep.syscall ms model x8 (mkEffect (errno_ret e) [] []) model model []
        Hh Hsvc (mmap_fail_ok_noreserve segs ms x8 model e Hno Hargs He) Hh
        (materialize_syscall_effect_nil _ _ _ _)
    · exact sstep.syscall ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []
        Hh Hsvc (mmap_succ_ok_noreserve segs ms x8 model a Hno Hargs Ha)
        (by rw [mmap_model_noreserve_halted]; exact Hh)
        (materialize_syscall_effect_nil _ _ _ _)
  · intro e st Hss
    obtain ⟨he, hst⟩ := sstep_mmap_inv_noreserve segs ms model x8 e st Hh Hsvc Hno Hargs Hss
    rcases hst with ⟨er, Her, hst⟩ | ⟨a, Ha, hst⟩
    · exact ⟨.inl ⟨er, Her⟩, he, hst⟩
    · exact ⟨.inr ⟨a, Ha⟩, he, hst⟩

/-- The plain two-branch NORESERVE node (both arms continue). -/
theorem srz_mmap_noreserve (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (A B : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok_noreserve ms)
    (HA : ∀ e, e ∈ mmap_errnos →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : ∀ a, grant_ok_nr (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      srealizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok_nr (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    srealizes segs (mkCfg ms model) (t_alt2 A B) := by
  obtain ⟨a0, Ha0⟩ := Hex
  refine srz_alt2 segs (mkCfg ms model) { e : Int // e ∈ mmap_errnos }
    { a : word // grant_ok_nr (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }
    (mmap_nr_next ms model) A B ⟨ENOMEM, ENOMEM_in_mmap_errnos⟩ ⟨a0, Ha0⟩
    (node_mmap_noreserve segs ms model x8 Hh Hsvc Hno Hargs) ?_ ?_
  · rintro ⟨e, He⟩
    exact HA e He
  · rintro ⟨a, Ha⟩
    exact HB a Ha

/-- THE SPIN-ARMED NORESERVE NODE: the shadow-reservation shape ASan
    init actually has.  Every refusal spins (`to_spin`, model
    unchanged — on the FIRST reservation the ledger is still empty
    there, so the no-lazy spellings feed this hypothesis as-is); every
    grant continues as `B` with the ledger non-empty.  The refusal arm
    contributes only `[]`, so the node realizes `B` alone. -/
theorem srz_mmap_spin_noreserve (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (B : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok_noreserve ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (HB : ∀ a, grant_ok_nr (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      srealizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok_nr (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    srealizes segs (mkCfg ms model) B := by
  obtain ⟨a0, Ha0⟩ := Hex
  have HB0 : B [] := srealizes_nonempty segs _ B (HB a0 Ha0)
  have Hnode : node_ok segs (mkCfg ms model) (MmapNrIdx ms model) (fun _ => [])
      (mmap_nr_next ms model) :=
    node_mmap_noreserve segs ms model x8 Hh Hsvc Hno Hargs
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun i : MmapNrIdx ms model =>
      t_emit [] (match i with | .inl _ => t_nil | .inr _ => B))) B ?_ ?_
  · refine srz_node segs (mkCfg ms model) (MmapNrIdx ms model) (fun _ => [])
      (mmap_nr_next ms model)
      (fun i => match i with | .inl _ => t_nil | .inr _ => B) (.inr ⟨a0, Ha0⟩) Hnode ?_
    rintro (⟨e, He⟩ | ⟨a, Ha⟩)
    · exact srz_spin segs _ (Hrefuse e He) Hh
    · exact HB a Ha
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl e => exact (t_emit_nil_eq t_nil rfl tr).1 Hi ▸ HB0
      | inr a => exact (t_emit_nil_eq B HB0 tr).1 Hi
    · intro HBtr
      exact ⟨.inr ⟨a0, Ha0⟩, (t_emit_nil_eq B HB0 tr).2 HBtr⟩

/- ================================================================= -/
/- RESIDUAL 2 — lazy-tolerant re-derivations of the syscall nodes     -/
/- the ASan skeleton needs (mmap, munmap, write(1); exit needs        -/
/- nothing: [SpinAlg.srz_exit] never had a ledger premise)            -/
/- ================================================================= -/

/- ----------------------------------------------------------------- -/
/- mmap (plain rw shape), through a non-empty ledger                  -/
/- ----------------------------------------------------------------- -/

/-- [SpinAlg]'s [sstep_mmap_inv] with the [m_vm_lazy model = []]
    premise DROPPED: both resolutions' effects name no access, so the
    materialization collapses on ANY ledger. -/
theorem sstep_mmap_inv_lazy (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    evs = [] ∧
    ((∃ e, e ∈ mmap_errnos ∧
        st = .SNext ⟨advance_past_svc (set_gpr0 ms (errno_ret e)), model⟩) ∨
     (∃ a, grant_ok (ms_gpr ms 0) model a
          (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true ∧
        st = .SNext ⟨advance_past_svc
              (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])),
            mmap_model a (page_round_up (ms_gpr ms 1)) model⟩)) := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x80 eff model' model'' evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨Hevs, Hcase⟩ :=
      mmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    subst Hevs
    refine ⟨rfl, ?_⟩
    rcases Hcase with ⟨e, He, heff, hmodel⟩ | ⟨a, Hg, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hmat
      have hmm : model'' = model := by
        rw [materialize_syscall_effect_nil] at hmat
        exact (Option.some.inj hmat).symm
      rw [hmm, apply_effect_no_write]
      exact Or.inl ⟨e, He, rfl⟩
    · subst heff
      rw [hmodel] at hmat
      have hmm : model'' = mmap_model a (page_round_up (ms_gpr ms 1)) model := by
        rw [materialize_syscall_effect_nil] at hmat
        exact (Option.some.inj hmat).symm
      rw [hmm]
      exact Or.inr ⟨a, Hg, rfl⟩
  | syscall_materialization_fault ms0 model0 x80 eff model' evs0 hh hsvc hspec hh' hmat =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_nil] at hmat
      cases hmat
    · subst heff
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_nil] at hmat
      cases hmat
  | exit ms0 model0 x80 eff model' evs0 code hh hsvc hspec hh' hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hh'
      rw [Hh] at hh'
      cases hh'
    · subst heff
      rw [hmodel] at hh'
      rw [mmap_model_halted, Hh] at hh'
      cases hh'
  | killed ms0 model0 x80 eff model' evs0 sig hh hsvc hspec hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, Hcase⟩ :=
      mmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    rcases Hcase with ⟨e, -, heff, hmodel⟩ | ⟨a, -, heff, hmodel⟩
    · subst heff
      rw [hmodel] at hk
      rw [m_killed_of_m_halted_none _ Hh] at hk
      cases hk
    · subst heff
      rw [hmodel] at hk
      rw [m_killed_of_m_halted_none _ (by rw [mmap_model_halted]; exact Hh)] at hk
      cases hk
  | syscall_unmodeled ms0 model0 x80 hh hsvc hspec =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    exact mmap_no_unmodeled segs ms x8 model Hno Hargs hspec

/-- [SpinAlg.node_mmap] with the [m_vm_lazy model = []] premise
    DROPPED: both resolutions' effects name no access. -/
theorem node_mmap_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms) :
    node_ok segs (mkCfg ms model) (MmapIdx ms model) (fun _ => []) (mmap_next ms model) := by
  constructor
  · rintro (⟨e, He⟩ | ⟨a, Ha⟩)
    · exact sstep.syscall ms model x8 (mkEffect (errno_ret e) [] []) model model []
        Hh Hsvc (mmap_fail_ok segs ms x8 model e Hno Hargs He) Hh
        (materialize_syscall_effect_nil _ _ _ _)
    · exact sstep.syscall ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) []
        Hh Hsvc (mmap_succ_ok segs ms x8 model a Hno Hargs Ha)
        (by rw [mmap_model_halted]; exact Hh)
        (materialize_syscall_effect_nil _ _ _ _)
  · intro e st Hss
    obtain ⟨he, hst⟩ := sstep_mmap_inv_lazy segs ms model x8 e st Hh Hsvc Hno Hargs Hss
    rcases hst with ⟨er, Her, hst⟩ | ⟨a, Ha, hst⟩
    · exact ⟨.inl ⟨er, Her⟩, he, hst⟩
    · exact ⟨.inr ⟨a, Ha⟩, he, hst⟩

/-- The plain two-branch mmap node, ledger-free. -/
theorem srz_mmap_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (A B : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (HA : ∀ e, e ∈ mmap_errnos →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      srealizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    srealizes segs (mkCfg ms model) (t_alt2 A B) := by
  obtain ⟨a0, Ha0⟩ := Hex
  refine srz_alt2 segs (mkCfg ms model) { e : Int // e ∈ mmap_errnos }
    { a : word // grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }
    (mmap_next ms model) A B ⟨ENOMEM, ENOMEM_in_mmap_errnos⟩ ⟨a0, Ha0⟩
    (node_mmap_lazy segs ms model x8 Hh Hsvc Hno Hargs) ?_ ?_
  · rintro ⟨e, He⟩
    exact HA e He
  · rintro ⟨a, Ha⟩
    exact HB a Ha

/-- The spin-armed mmap node, ledger-free: [SpinAlg.srz_mmap_spin]
    usable AFTER the NORESERVE grant (the ASan skeleton's second
    allocation, standing on a non-empty ledger). -/
theorem srz_mmap_spin_lazy (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (B : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      srealizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    srealizes segs (mkCfg ms model) B := by
  obtain ⟨a0, Ha0⟩ := Hex
  have HB0 : B [] := srealizes_nonempty segs _ B (HB a0 Ha0)
  have Hnode : node_ok segs (mkCfg ms model) (MmapIdx ms model) (fun _ => [])
      (mmap_next ms model) :=
    node_mmap_lazy segs ms model x8 Hh Hsvc Hno Hargs
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun i : MmapIdx ms model =>
      t_emit [] (match i with | .inl _ => t_nil | .inr _ => B))) B ?_ ?_
  · refine srz_node segs (mkCfg ms model) (MmapIdx ms model) (fun _ => [])
      (mmap_next ms model)
      (fun i => match i with | .inl _ => t_nil | .inr _ => B) (.inr ⟨a0, Ha0⟩) Hnode ?_
    rintro (⟨e, He⟩ | ⟨a, Ha⟩)
    · exact srz_spin segs _ (Hrefuse e He) Hh
    · exact HB a Ha
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl e => exact (t_emit_nil_eq t_nil rfl tr).1 Hi ▸ HB0
      | inr a => exact (t_emit_nil_eq B HB0 tr).1 Hi
    · intro HBtr
      exact ⟨.inr ⟨a0, Ha0⟩, (t_emit_nil_eq B HB0 tr).2 HBtr⟩

/- ----------------------------------------------------------------- -/
/- munmap, through a non-empty ledger                                -/
/- ----------------------------------------------------------------- -/

/-- [MmapSim.sstep_munmap_inv] with the [m_vm_lazy model = []] premise
    DROPPED (the munmap effect names no access). -/
theorem sstep_munmap_inv_lazy (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 215) (Hargs : munmap_args_ok ms model)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    evs = [] ∧
    st = .SNext ⟨advance_past_svc (apply_effect ms (munmap_eff ms)),
      munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model⟩ := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x80 eff model' model'' evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, Hevs⟩ :=
      munmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    subst heff
    subst Hevs
    rw [hmodel] at hmat
    have hmm : model'' = munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model := by
      rw [materialize_munmap_eff_nil] at hmat
      exact (Option.some.inj hmat).symm
    rw [hmm]
    exact ⟨rfl, rfl⟩
  | syscall_materialization_fault ms0 model0 x80 eff model' evs0 hh hsvc hspec hh' hmat =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨heff, hmodel, -⟩ :=
      munmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    subst heff
    rw [hmodel] at hmat
    rw [materialize_munmap_eff_nil] at hmat
    cases hmat
  | exit ms0 model0 x80 eff model' evs0 code hh hsvc hspec hh' hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, hmodel, -⟩ :=
      munmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    rw [hmodel] at hh'
    rw [munmap_model_halted, Hh] at hh'
    cases hh'
  | killed ms0 model0 x80 eff model' evs0 sig hh hsvc hspec hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, hmodel, -⟩ :=
      munmap_ok_inv segs ms x8 model eff model' _ Hno Hargs hspec
    rw [hmodel] at hk
    rw [m_killed_of_m_halted_none _ (by rw [munmap_model_halted]; exact Hh)] at hk
    cases hk
  | syscall_unmodeled ms0 model0 x80 hh hsvc hspec =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    exact munmap_no_unmodeled segs ms x8 model Hno Hargs hspec

/-- [SpinAlg.node_munmap] with the ledger premise DROPPED. -/
theorem node_munmap_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 215) (Hargs : munmap_args_ok ms model) :
    node_ok segs (mkCfg ms model) Unit (fun _ => [])
      (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) := by
  constructor
  · intro i
    cases i
    exact sstep.syscall ms model x8 (munmap_eff ms)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
      Hh Hsvc (munmap_ok segs ms x8 model Hno Hargs)
      (by rw [munmap_model_halted]; exact Hh)
      (materialize_munmap_eff_nil _ _)
  · intro e st Hss
    obtain ⟨he, hst⟩ :=
      sstep_munmap_inv_lazy segs ms model x8 e st Hh Hsvc Hno Hargs Hss
    exact ⟨(), he, hst⟩

/-- The munmap node, ledger-free. -/
theorem srz_munmap_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (T : TSet) (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 215) (Hargs : munmap_args_ok ms model)
    (Hc : srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T (node_munmap_lazy segs ms model x8 Hh Hsvc Hno Hargs) Hc


/- ----------------------------------------------------------------- -/
/- write(1, buf, len), through a non-empty ledger — the ONE node      -/
/- whose effect names an access (the copyin of the buffer), so the    -/
/- lazy-tolerant form takes the DISJOINTNESS hypothesis: the whole    -/
/- buffer lies outside every lazy range.                              -/
/- ----------------------------------------------------------------- -/

/-- One-step inversion for a write(1) whose buffer is ledger-disjoint
    (NoReserve).  The materialization step is
    `materialize_syscall_effect_copyin_disjoint` fed by
    `accesses_outside_lazy_shrink` (disjointness of the FULL buffer
    covers every delivered prefix). -/
theorem sstep_write_next_inv_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (evs : List event) (c' : config)
    (Hh : m_halted model = none)
    (Hout : accesses_outside_lazy [(ms_gpr ms 1, buf.length)] (m_vm_lazy model))
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hss : sstep segs ⟨ms, model⟩ evs (.SNext c')) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      evs = List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) ∧
      c' = ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩ := by
  cases Hss with
  | instr _ _ _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x80 eff model' model'' evs0 hh hsvc hspec hh' hmat =>
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨n, Hn1, Hn2, heff, hmodel, Hevs⟩ :=
      write1_ok_inv segs ms x8 model eff model' _ buf Hfd Hno Hg Hr Hnb hspec
    subst heff
    have hmm : model'' = model := by
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_copyin_disjoint model (len_word (buf.take n))
        (ms_gpr ms 1) n
        (accesses_outside_lazy_shrink (ms_gpr ms 1) buf.length n (m_vm_lazy model) Hn2 Hout)]
        at hmat
      exact (Option.some.inj hmat).symm
    refine ⟨n, Hn1, Hn2, Hevs, ?_⟩
    rw [hmm, apply_effect_copyins_no_write]
  | exit ms0 model0 x80 eff model' evs0 code hh hsvc hspec hh' hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, -, -, -, hmodel, -⟩ :=
      write1_ok_inv segs ms x8 model eff model' _ buf Hfd Hno Hg Hr Hnb hspec
    rw [hmodel] at hh'
    rw [Hh] at hh'
    cases hh'
  | killed ms0 model0 x80 eff model' evs0 sig hh hsvc hspec hk =>
    exfalso
    have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    subst x80
    obtain ⟨-, -, -, -, hmodel, -⟩ :=
      write1_ok_inv segs ms x8 model eff model' _ buf Hfd Hno Hg Hr Hnb hspec
    rw [hmodel] at hk
    rw [m_killed_of_m_halted_none _ Hh] at hk
    cases hk

/-- The full inversion: EXACTLY the `wr_index buf` resolutions
    (NoReserve).  The `SError` arm is excluded because the
    write is modeled and its one access is disjoint. -/
theorem sstep_write_inv_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (evs : List event) (st : step_to)
    (Hh : m_halted model = none)
    (Hout : accesses_outside_lazy [(ms_gpr ms 1, buf.length)] (m_vm_lazy model))
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      evs = List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) ∧
      st = .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩ := by
  cases st with
  | SNext c' =>
    obtain ⟨n, h1, h2, h3, h4⟩ := sstep_write_next_inv_disjoint segs ms model x8 buf evs c'
      Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss
    exact ⟨n, h1, h2, h3, by rw [h4]⟩
  | SError =>
    exfalso
    cases Hss with
    | instr_fault _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | instr_unmodeled _ _ hh hsvc hstep => exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall_materialization_fault ms0 model0 x80 eff model' evs0 hh hsvc hspec hh' hmat =>
      have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      subst x80
      obtain ⟨n, -, Hn2, heff, hmodel, -⟩ :=
        write1_ok_inv segs ms x8 model eff model' _ buf Hfd Hno Hg Hr Hnb hspec
      subst heff
      rw [hmodel] at hmat
      rw [materialize_syscall_effect_copyin_disjoint model (len_word (buf.take n))
        (ms_gpr ms 1) n
        (accesses_outside_lazy_shrink (ms_gpr ms 1) buf.length n (m_vm_lazy model) Hn2 Hout)]
        at hmat
      cases hmat
    | syscall_unmodeled ms0 model0 x80 hh hsvc hspec =>
      have hx : x80 = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      subst x80
      exact write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hbm Hnb hspec

/-- The write(1) node through a disjoint ledger (NoReserve). -/
theorem node_write1_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte)
    (Hh : m_halted model = none)
    (Hout : accesses_outside_lazy [(ms_gpr ms 1, buf.length)] (m_vm_lazy model))
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    node_ok segs (mkCfg ms model) (wr_index buf)
      (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model) := by
  constructor
  · rintro ⟨n, hn1, hn2⟩
    exact sstep.syscall ms model x8
      (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))
      model model ((buf.take n).map (event.WriteEv (BitVec.ofInt 64 1)))
      Hh Hsvc (write1_ok_n segs ms x8 model buf n Hfd Hno Hg Hr Hbm hn1 hn2) Hh
      (materialize_syscall_effect_copyin_disjoint model (len_word (buf.take n))
        (ms_gpr ms 1) n
        (accesses_outside_lazy_shrink (ms_gpr ms 1) buf.length n (m_vm_lazy model) hn2 Hout))
  · intro e st Hss
    obtain ⟨n, hn1, hn2, he, hst⟩ :=
      sstep_write_inv_disjoint segs ms model x8 buf e st Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hss
    exact ⟨⟨n, hn1, hn2⟩, he, hst⟩

/-- The write(1) node as a shape (NoReserve). -/
theorem srz_write1_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (T : TSet)
    (Hh : m_halted model = none)
    (Hout : accesses_outside_lazy [(ms_gpr ms 1, buf.length)] (m_vm_lazy model))
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    srealizes segs (mkCfg ms model) (t_write_ch (BitVec.ofInt 64 1) buf T) := by
  unfold t_write_ch
  exact srz_node segs (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T) (wr_full buf Hnb)
    (node_write1_disjoint segs ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

/- ================================================================= -/
/- RESIDUAL 3 — the chained disjoint straight line                    -/
/- ================================================================= -/

/-- [CatSim.msteps] with the access reports CARRIED: a run of ordinary
    (non-syscall) instruction steps, accumulating every reported
    range.  Chain per-instruction [stepacc_*] facts (below) into one
    [msteps_acc], show the accumulated list disjoint from the ledger
    ONCE, and the whole line walks any obligation through it. -/
inductive msteps_acc (segs : List Segment) :
    machine_state → machine_state → List (word × Nat) → Prop where
  | msta_refl (ms : machine_state) : msteps_acc segs ms ms []
  | msta_step (ms ms1 ms2 : machine_state) (ranges accs : List (word × Nat))
      (hsvc : ms.ms_svc_pending = none)
      (hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms1 ranges))
      (h : msteps_acc segs ms1 ms2 accs) :
      msteps_acc segs ms ms2 (ranges ++ accs)

theorem msteps_acc_one (segs : List Segment) (ms ms' : machine_state)
    (ranges : List (word × Nat))
    (hsvc : ms.ms_svc_pending = none)
    (hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges)) :
    msteps_acc segs ms ms' ranges := by
  rw [← List.append_nil ranges]
  exact .msta_step (ms := ms) (ms1 := ms') (ms2 := ms') (ranges := ranges) (accs := [])
    hsvc hstep (.msta_refl ms')

theorem msteps_acc_trans (segs : List Segment) (ms ms' ms'' : machine_state)
    (accs1 accs2 : List (word × Nat))
    (h1 : msteps_acc segs ms ms' accs1) (h2 : msteps_acc segs ms' ms'' accs2) :
    msteps_acc segs ms ms'' (accs1 ++ accs2) := by
  revert h2
  induction h1 with
  | msta_refl ms => intro h2; exact h2
  | msta_step ms ms1 ms2 ranges accs hsvc hstep _ ih =>
      intro h2
      rw [List.append_assoc]
      exact .msta_step (ms := ms) (ms1 := ms1) (ms2 := ms'') (ranges := ranges)
        (accs := accs ++ accs2) hsvc hstep (ih h2)

/- — the disjoint single-step node lives in `Common/SpinAlg`
    (`node_instr_disjoint` / `rz_step_disjoint` / `srz_step_disjoint`,
    SpinAlg:378-421).  When the three were written, `Common/SpinAlg.lean`
    still listed them as deferred ("need `Common/LazyFrame.lean`
    (`accesses_outside_lazy`, `mi_account_step_disjoint`)").  **That module
    has since stated them at home** — `node_instr_disjoint` at
    `SpinAlg.lean:473`, `rz_step_disjoint` at `:499`, `srz_step_disjoint`
    at `:509` (the same three statements; only `step_accesses` vs the
    qualified
    `RiscvSemantics.step_accesses` differs in spelling) — so the three below
    are exact
    duplicates, kept because this file's `msteps_acc` consumers use the
    local names: `node_instr_disjoint` is cited by the local
    `rz_step_disjoint` / `srz_step_disjoint`, and nothing
    outside this file refers to either copy.  The proofs here are
    independent of `SpinAlg`'s: `LazyFrame.mi_account_step_disjoint` +
    `SpinAlg.sstep_instr`.

    NOTE the difference from `SpinAlg.node_instr`, which needs
    `m_vm_lazy model = []`: the ledger here is ARBITRARY, and only the
    access report has to be disjoint. -/

/-- The disjoint instruction node: an instruction whose access report
    avoids every lazy range is a silent node WHATEVER the ledger holds.
    This is the node the ASan grant path uses once `m_vm_lazy` is
    non-empty and `node_instr` is unavailable.   -/
theorem node_instr_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat))
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model)) :
    node_ok segs (mkCfg ms model) Unit (fun _ => []) (fun _ => mkCfg ms' model) := by
  have Hacc := mi_account_step_disjoint segs ms model ms' ranges Hstep Hout
  constructor
  · intro i
    cases i
    exact sstep.instr ms model ms' model Hh Hsvc Hacc
  · intro e st Hss
    cases Hss with
    | instr ms0 model0 ms0' model0' hh hsvc hstep =>
      rw [Hacc] at hstep
      obtain ⟨rfl, rfl⟩ := machine_result.MachineOk.inj hstep
      exact ⟨(), rfl, rfl⟩
    | instr_fault _ _ hh hsvc hstep =>
      rw [Hacc] at hstep
      cases hstep
    | instr_unmodeled _ _ hh hsvc hstep =>
      rw [Hacc] at hstep
      cases hstep
    | syscall _ _ _ _ _ _ _ hh hsvc hspec hh' hmat =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall_materialization_fault _ _ _ _ _ _ hh hsvc hspec hh' hmat =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | exit _ _ _ _ _ _ _ hh hsvc hspec hh' hk =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | killed _ _ _ _ _ _ _ hh hsvc hspec hk =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall_unmodeled _ _ _ hh hsvc hspec =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)

/-- The disjoint instruction node at `realizes` . -/
theorem rz_step_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model))
    (Hc : realizes segs (mkCfg ms' model) T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T (node_instr_disjoint segs ms model ms' ranges Hh Hsvc Hstep Hout) Hc

/-- The disjoint instruction node at `srealizes` . -/
theorem srz_step_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model))
    (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T (node_instr_disjoint segs ms model ms' ranges Hh Hsvc Hstep Hout) Hc

/-- The chained node: a disjoint straight line is silent and preserves
    the model exactly, whatever the ledger holds (NoReserve). -/
theorem srz_msteps_disjoint (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (accs : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none)
    (Hms : msteps_acc segs ms ms' accs)
    (Hout : accesses_outside_lazy accs (m_vm_lazy model))
    (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T := by
  revert Hc Hout T
  induction Hms with
  | msta_refl ms =>
    intro T hout hc
    exact hc
  | msta_step ms ms1 ms2 ranges accs hsvc hstep hrest ih =>
    intro T hout hc
    exact srz_step_disjoint segs ms model ms1 ranges T Hh hsvc hstep
      (accesses_outside_lazy_app_l ranges accs (m_vm_lazy model) hout)
      (ih T (accesses_outside_lazy_app_r ranges accs (m_vm_lazy model) hout) hc)

/-- The same at `realizes` (NoReserve). -/
theorem rz_msteps_disjoint (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (accs : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none)
    (Hms : msteps_acc segs ms ms' accs)
    (Hout : accesses_outside_lazy accs (m_vm_lazy model))
    (Hc : realizes segs (mkCfg ms' model) T) :
    realizes segs (mkCfg ms model) T := by
  revert Hc Hout T
  induction Hms with
  | msta_refl ms =>
    intro T hout hc
    exact hc
  | msta_step ms ms1 ms2 ranges accs hsvc hstep hrest ih =>
    intro T hout hc
    exact rz_step_disjoint segs ms model ms1 ranges T Hh hsvc hstep
      (accesses_outside_lazy_app_l ranges accs (m_vm_lazy model) hout)
      (ih T (accesses_outside_lazy_app_r ranges accs (m_vm_lazy model) hout) hc)

/-- ...and the straight line INTO a spin (`LazyFrame.ts_step_disjoint`,
    chained — NoReserve:1224-1240). -/
theorem ts_msteps_disjoint (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (accs : List (word × Nat))
    (Hms : msteps_acc segs ms ms' accs)
    (Hout : accesses_outside_lazy accs (m_vm_lazy model))
    (Hspin : to_spin segs ms' model) :
    to_spin segs ms model := by
  revert Hspin Hout
  induction Hms with
  | msta_refl ms =>
    intro hout hspin
    exact hspin
  | msta_step ms ms1 ms2 ranges accs hsvc hstep hrest ih =>
    intro hout hspin
    exact ts_step_disjoint segs ms model ms1 ranges hsvc hstep
      (accesses_outside_lazy_app_l ranges accs (m_vm_lazy model) hout)
      (ih (accesses_outside_lazy_app_r ranges accs (m_vm_lazy model) hout) hspin)

/- ================================================================= -/
/- RESIDUAL 3, per-instruction layer: [PropExec]'s step inventory      -/
/- mirrored at the [step_accesses] level.  Same hypotheses, same      -/
/- successor state, conclusion CARRIES the access report: [] for the  -/
/- ALU / branch / jump / ecall forms, the single read range for the   -/
/- seven load forms.  PropExec has no store lemmas, so none appear    -/
/- here (mirror the coverage, one level down).  These are what an     -/
/- [msteps_acc] chain is built from.                                  -/
/- ================================================================= -/

/- — `stepacc_pipeline`.

     opens this layer with an Ltac:

      Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
        unfold RiscvSemantics.step_accesses;
        cbn [ms_pc ms_pc_val mkst];
        rewrite Hfetch; cbv beta iota;
        unfold RiscvSemantics.decode_exec_accesses;
        rewrite Hecall; cbv beta iota;
        rewrite Hdecode; cbv beta iota zeta delta [ ... ];
        rewrite ?bv_eqb0_is_x0.

    Peran Ltac is rebuilt rather than transliterated, so
    the whole pipeline is the `simp only` below — the SAME one
    `Common/PropExec.lean`'s `step_pipeline` uses, minus `RiscvSemantics.step`
    and `drop_access_report` (this layer keeps the report).
    Each lemma's statement is the corresponding `PropExec.step_*` lemma
    with `.MachineOk <state>` replaced by
    `.MachineOk (mkAccessReport <state> <report>)`; the load forms reuse
    `PropExec`'s `rdn` / `ov_rdn` / `le_word_v` bridges unchanged. -/

open Lean Parser Tactic in
macro "stepacc_pipeline" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step_accesses, mkst, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, exec, interp_eff_accesses, mkAccessReport,
      rset, rget, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet, bvmap_set,
      getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, w0, Bool.false_eq_true, reduceIte,
      ite_true, ite_false])

open Lean Parser Tactic in
macro "stepacc_load_start" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step_accesses, mkst, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, exec, load_val, interp_eff_accesses, mkAccessReport,
      rset, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet, bvmap_set,
      Bool.false_eq_true, reduceIte, ite_true, ite_false, width_bytes])

/- ----------------------------------------------------------------- -/
/- ALU forms: empty report                                            -/
/- ----------------------------------------------------------------- -/

theorem stepacc_opimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg)
    (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.opImm op rd rs imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_shiftimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.shiftImm op rd rs sh, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_op_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.op op rd rs1 rs2, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_opimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.opImm32 rd rs imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm))))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_shiftimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.shiftImm32 op rd rs sh, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_op32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.op32 op rd rs1 rs2, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd
            (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_mul_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : MulOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.mul op rd rs1 rs2, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_mul32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : MulOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.mul32 op rd rs1 rs2, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd
            (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
          (v_addi pc 4) mem rom) []) := by
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/- ----------------------------------------------------------------- -/
/- Branches / jumps / lui / auipc / ecall: empty report               -/
/- ----------------------------------------------------------------- -/

theorem stepacc_branch_tk_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : BranchCond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport (mkst regs (btgt pc imm.toInt) mem rom) []) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  simp only [getr, bv_eqb0_is_x0] at Hc
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, hb, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

theorem stepacc_branch_ft_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : BranchCond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport (mkst regs (v_addi pc 4) mem rom) []) := by
  simp only [getr, bv_eqb0_is_x0] at Hc
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

theorem stepacc_lui (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.lui rd imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_lui (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) []) := by
  have hb : sext 64 (imm ++ (0#12)) = v_lui (zshiftl imm.toInt 12) := b_lui imm
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

theorem stepacc_auipc (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.auipc rd imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_auipc pc (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) []) := by
  have hb : pc + sext 64 (imm ++ (0#12)) = v_auipc pc (zshiftl imm.toInt 12) := b_auipc pc imm
  stepacc_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

theorem stepacc_jal_x0 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (imm : BitVec 21)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.jal 0 imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport (mkst regs (btgt pc imm.toInt) mem rom) []) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  stepacc_pipeline Hfetch, Hecall, Hdecode
  simp only [is_x0_0, ite_true, Bool.false_eq_true, reduceIte, hb]

theorem stepacc_jalr_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.jalr rd rs1 imm, 4)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
          (jalr_tgt (getr regs rs1) imm.toInt) mem rom) []) := by
  have hb : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide : 12 ≤ 64)
  have hj : (getr regs rs1 + sext 64 imm) &&& ~~~(1 : word)
      = jalr_tgt (getr regs rs1) imm.toInt := b_jalr _ imm
  stepacc_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, bv_eqb0_is_x0, w1, reg_get, w0] at hb hj ⊢
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, w0, w1, Bool.false_eq_true,
    reg_get] at hb hj ⊢
  all_goals rw [hj]
  all_goals simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, Nat.zero_add]

theorem stepacc_ecall (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = true) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        { (mkst regs pc mem rom) with ms_svc_pending := some (getr regs 17) } []) := by
  simp only [RiscvSemantics.step_accesses, mkst, ms_pc, Hfetch, decode_exec_accesses, Hecall,
    mkAccessReport, ms_reg, getr, bv_eqb0_is_x0, is_x0_0, ite_true, ite_false, w0]

/- ----------------------------------------------------------------- -/
/- Loads: the report is the single read range                         -/
/- ----------------------------------------------------------------- -/

theorem stepacc_lbu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ1 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = some [b]) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (BitVec.ofInt 64 (b.toNat : Int))) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 1)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = some [b] := by
    rw [hba, ov_rdn]; exact Hread
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]
  simp only [bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, zext8_le_word]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_lb (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ1 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = some [b]) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 1)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = some [b] := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 8 (le_bytes_to_word [b])) = v_lb b := b_lb_val b
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_lh (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ2 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 2 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 2)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 2 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 16 (le_bytes_to_word bs)) = v_lh v := by
    rw [le_word_v bs v Hv, b_lh_val]
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_lhu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ2 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 2 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd v) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 2)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 2 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : zext 64 (bits 0 16 (le_bytes_to_word bs)) = v := by
    rw [le_word_v bs v Hv]
    have hlen : bs.length = 2 := rdn_length segs mem 2 _ bs Hread
    have hbnd : (bytes_le_to_Z bs) < ((2 ^ 16 : Nat) : Int) := by
      have h := bytes_le_to_Z_bound bs
      rw [hlen] at h
      simpa using h
    refine zext_bits v 16 (by decide) ?_
    rw [← Hv]
    exact hbnd
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_lw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ4 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 4 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 4)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 32 (le_bytes_to_word bs)) = v_lw v := by
    rw [le_word_v bs v Hv, b_lw_val]
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_lwu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ4 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 4 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs
          else regupd regs rd v) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 4)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : zext 64 (bits 0 32 (le_bytes_to_word bs)) = v := by
    rw [le_word_v bs v Hv]
    have hlen : bs.length = 4 := rdn_length segs mem 4 _ bs Hread
    have hbnd : (bytes_le_to_Z bs) < ((2 ^ 32 : Nat) : Int) := by
      have h := bytes_le_to_Z_bound bs
      rw [hlen] at h
      simpa using h
    refine zext_bits v 32 (by decide) ?_
    rw [← Hv]
    exact hbnd
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem stepacc_ld (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (.load .SZ8 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 8 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport
        (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom)
        [(getr regs rs + sext 64 imm, 8)]) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 8 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : bits 0 64 (le_bytes_to_word bs) = v := by
    rw [le_word_v bs v Hv]
    apply BitVec.eq_of_toNat_eq
    simp only [bits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (by have := v.isLt; omega)
  stepacc_load_start Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/- ================================================================= -/
/- Worked example: the FULL ASan-init shape in miniature.             -/
/-                                                                    -/
/- A NORESERVE shadow reservation (every refusal spins; a grant       -/
/- leaves a NON-EMPTY lazy ledger), a disjoint straight line to a     -/
/- plain rw mmap (every refusal spins — THROUGH the non-empty ledger; -/
/- every grant continues), a disjoint line to a write(1) of a         -/
/- ledger-disjoint buffer, a disjoint line to an exit.  The           -/
/- conclusion is the standard obs_iff / no_error pair, and the proof  -/
/- is node applications and leaves only: this is the skeleton an      -/
/- proof instantiates on the real binary (the hypotheses below are    -/
/- exactly what its symbolic execution produces — [stepacc_*] chains  -/
/- for the walks, [prove_to_spin]/[ts_*] for the refusal arms,        -/
/- register/decode facts for the ecall shapes).                       -/
/- ================================================================= -/

/- ================================================================= -/
/- The pick/trace bridge the ASan observation set needs                -/
/- ================================================================= -/

/- — this one lemma is `Common/ShapeAlg`'s, not
    NoReserve's: this tree states `t_writes_ch_pick_exit_iff` at
    ShapeAlg:299 (with `t_writes_pick_exit_iff` at :337), and
    NoReserve only CONSUMES it (NoReserve).  When this copy was
    written `Common/ShapeAlg.lean` was not in the tree and
    `Common/SpinAlg.lean`'s SCAFFOLD carried
    only the `t_*` / `wpick` fragments its own proofs needed, so the bridge
    was carried here — at this file's namespace — to close
    `asan_init_obs_iff`.  **`Common/ShapeAlg.lean` has since landed** and
    defines `t_writes_ch_pick_exit_iff` with the same statement,
    so this is now an exact duplicate; its only referrer is
    `asan_init_obs_iff` below, and nothing outside this file refers to
    either copy.  Every ingredient is the stated real thing:
    `CatSim.wpick` / `wpick.wp_cons` / `wpick_wevents` / `wevents_ch`, and
    the prefix lemmas (`is_prefix_app`, `is_prefix_app_split`,
    `is_prefix_app_mono`, `is_prefix_trans`). -/

section AsanInitReal

variable (segs : List Segment)

/-  eight `Let`s are written out below ; this table is
    the translation:
      nZ1        = page_round_up_Z ((ms_gpr ms1 1).toNat : Int)
      n1         = page_round_up (ms_gpr ms1 1)
      model1 a1  = mmap_model_noreserve a1 n1 model
      post1 a1   = advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)]))
      nZ2 a1     = page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)
      n2 a1      = page_round_up (ms_gpr (ms2 a1) 1)
      model2 a1 a2 = mmap_model a2 (n2 a1) (model1 a1)
      post2 a1 a2  = advance_past_svc (apply_effect (ms2 a1)
                       (mkEffect a2 [] [(a2, n2 a1)]))
-/

/- The reservation ecall configuration. -/
variable (ms1 : machine_state) (model : Model) (x8a : word)
variable (Hh : m_halted model = none)
variable (Hfd : fd1chan model)
variable (Hsvc1 : ms1.ms_svc_pending = some x8a)
variable (Hno1 : (x8a.toNat : Int) = 222)
variable (Hargs1 : mmap_args_ok_noreserve ms1)

/- Refusal arm of the reservation: the ledger is still empty here, so a
    per-binary proof feeds this from the no-lazy spellings as-is. -/
variable (Hrefuse1 : ∀ e, e ∈ mmap_errnos →
  to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model)
variable (Hex1 : ∃ a, grant_ok_nr (ms_gpr ms1 0) model a
  (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true)

/- Post-grant straight line to the rw mmap ecall — the ledger is
    non-empty now (`lazy_interior a1 n1 ++ []`), so the walk carries its
    access report and shows it disjoint. -/
variable (ms2 : word → machine_state)
variable (accs1 : word → List (word × Nat))
variable (Hwalk1 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  msteps_acc segs
    (advance_past_svc (apply_effect ms1
      (mkEffect a1 [] [(a1, page_round_up (ms_gpr ms1 1))])))
    (ms2 a1) (accs1 a1))
variable (Hout1 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  accesses_outside_lazy (accs1 a1)
    (m_vm_lazy (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model)))

/- The rw mmap ecall, standing on the non-empty ledger. -/
variable (x8b : word)
variable (Hno2 : (x8b.toNat : Int) = 222)
variable (Hsvc2 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  (ms2 a1).ms_svc_pending = some x8b)
variable (Hargs2 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  mmap_args_ok (ms2 a1))

/- Refusal arm of the rw mmap: spins THROUGH the non-empty ledger (fed
    by `ts_msteps_disjoint`/`ts_spin_no_access` on the real binary). -/
variable (Hrefuse2 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  ∀ e, e ∈ mmap_errnos →
  to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e)))
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))
variable (Hex2 : ∀ a1, grant_ok_nr (ms_gpr ms1 0) model a1
    (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  ∃ a2, grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true)

/- Post-grant straight line to the write ecall. -/
variable (ms3 : word → word → machine_state)
variable (accs2 : word → word → List (word × Nat))
variable (Hwalk2 : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  msteps_acc segs
    (advance_past_svc (apply_effect (ms2 a1)
      (mkEffect a2 [] [(a2, page_round_up (ms_gpr (ms2 a1) 1))])))
    (ms3 a1 a2) (accs2 a1 a2))
variable (Hout2 : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  accesses_outside_lazy (accs2 a1 a2)
    (m_vm_lazy (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))))

/- The write(1) ecall: the buffer is disjoint from the lazy ledger (on
    the real binary: it lives in the image's data/stack, and
    `region_free` keeps the reservation away from the image). -/
variable (buf : List byte)
variable (Hbufnb : 1 ≤ buf.length)
variable (Hbufmod : buf_modeled buf)
variable (x8c : word)
variable (Hno3 : (x8c.toNat : Int) = 64)
variable (Hw_svc : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  (ms3 a1 a2).ms_svc_pending = some x8c)
variable (Hw_fd1 : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  ms_gpr (ms3 a1 a2) 0 = BitVec.ofInt 64 1)
variable (Hw_read : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = some buf)
variable (Hw_out : ∀ a1 a2,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, buf.length)]
    (m_vm_lazy (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))))

/- Post-write straight line (per delivered length) to the exit ecall. -/
variable (msE : word → word → Nat → machine_state)
variable (accs3 : word → word → Nat → List (word × Nat))
variable (Hwalk3 : ∀ a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  1 ≤ n → n ≤ buf.length →
  msteps_acc segs
    (advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (buf.take n))))
    (msE a1 a2 n) (accs3 a1 a2 n))
variable (Hout3 : ∀ a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  1 ≤ n → n ≤ buf.length →
  accesses_outside_lazy (accs3 a1 a2 n)
    (m_vm_lazy (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))))

/- The exit ecall. -/
variable (x8d : word) (cs : word)
variable (HE_no : is_exit_no x8d)
variable (HE_svc : ∀ a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  1 ≤ n → n ≤ buf.length →
  (msE a1 a2 n).ms_svc_pending = some x8d)
variable (HE_code : ∀ a1 a2 n,
  grant_ok_nr (ms_gpr ms1 0) model a1 (page_round_up_Z ((ms_gpr ms1 1).toNat : Int)) = true →
  grant_ok (ms_gpr (ms2 a1) 0)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) a2
    (page_round_up_Z ((ms_gpr (ms2 a1) 1).toNat : Int)) = true →
  1 ≤ n → n ≤ buf.length →
  (ms_gpr (msE a1 a2 n) 0 &&& BitVec.ofInt 64 255) = cs)

/- Every hypothesis above is used only in the PROOFS below, never in a
    theorem's statement, so Lean's variable-inclusion pass would drop it;
    `include` pins the whole section context onto each theorem exactly.'s section does. -/
include segs ms1 model x8a
  Hh Hfd Hsvc1 Hno1 Hargs1 Hrefuse1 Hex1
  ms2 accs1 Hwalk1 Hout1
  x8b Hno2 Hsvc2 Hargs2 Hrefuse2 Hex2
  ms3 accs2 Hwalk2 Hout2
  buf Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out
  msE accs3 Hwalk3 Hout3
  x8d cs HE_no HE_svc HE_code

/-- The derivation: four node applications, three disjoint walks, one
    exit leaf. -/
theorem asan_init_srealizes :
    srealizes segs (mkCfg ms1 model)
      (t_write_ch (BitVec.ofInt 64 1) buf (t_exit cs (m_fs model))) := by
  refine srz_mmap_spin_noreserve segs ms1 model x8a _ Hh Hsvc1 Hno1 Hargs1
    Hrefuse1 ?_ Hex1
  intro a1 Hg1
  refine srz_msteps_disjoint segs
    (advance_past_svc (apply_effect ms1
      (mkEffect a1 [] [(a1, page_round_up (ms_gpr ms1 1))])))
    (ms2 a1) (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model)
    (accs1 a1) _ Hh (Hwalk1 a1 Hg1) (Hout1 a1 Hg1) ?_
  refine srz_mmap_spin_lazy segs (ms2 a1)
    (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model) x8b _
    Hh (Hsvc2 a1 Hg1) Hno2 (Hargs2 a1 Hg1) (Hrefuse2 a1 Hg1) ?_ (Hex2 a1 Hg1)
  intro a2 Hg2
  refine srz_msteps_disjoint segs
    (advance_past_svc (apply_effect (ms2 a1)
      (mkEffect a2 [] [(a2, page_round_up (ms_gpr (ms2 a1) 1))])))
    (ms3 a1 a2)
    (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))
    (accs2 a1 a2) _ Hh (Hwalk2 a1 a2 Hg1 Hg2) (Hout2 a1 a2 Hg1 Hg2) ?_
  refine srz_write1_disjoint segs (ms3 a1 a2)
    (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))
    x8c buf _ Hh (Hw_out a1 a2 Hg1 Hg2) Hfd (Hw_svc a1 a2 Hg1 Hg2) Hno3
    (Hw_fd1 a1 a2 Hg1 Hg2) (Hw_read a1 a2 Hg1 Hg2) Hbufmod Hbufnb ?_
  intro n Hn1 Hn2
  refine srz_msteps_disjoint segs
    (advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (buf.take n))))
    (msE a1 a2 n)
    (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))
    (accs3 a1 a2 n) _ Hh (Hwalk3 a1 a2 n Hg1 Hg2 Hn1 Hn2)
    (Hout3 a1 a2 n Hg1 Hg2 Hn1 Hn2) ?_
  rw [← HE_code a1 a2 n Hg1 Hg2 Hn1 Hn2]
  exact srz_exit segs (msE a1 a2 n)
    (mmap_model a2 (page_round_up (ms_gpr (ms2 a1) 1))
      (mmap_model_noreserve a1 (page_round_up (ms_gpr ms1 1)) model))
    x8d Hh (HE_svc a1 a2 n Hg1 Hg2 Hn1 Hn2) HE_no

/-- The standard pair's `no_error` half. -/
theorem asan_init_no_error : ¬ reaches_error segs (mkCfg ms1 model) :=
  srealizes_no_error segs _ _
    (asan_init_srealizes segs ms1 model x8a
      Hh Hfd Hsvc1 Hno1 Hargs1 Hrefuse1 Hex1
      ms2 accs1 Hwalk1 Hout1
      x8b Hno2 Hsvc2 Hargs2 Hrefuse2 Hex2
      ms3 accs2 Hwalk2 Hout2
      buf Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out
      msE accs3 Hwalk3 Hout3
      x8d cs HE_no HE_svc HE_code)

/-- The standard pair's observation half: the observation set is exactly
    the per-delivery write shape followed by the exit — neither spinning
    refusal arm is visible in it (NoReserve). -/
theorem asan_init_obs_iff (tr : List event) :
    obs_trace segs (mkCfg ms1 model) tr ↔
      (∃ full, wpick (BitVec.ofInt 64 1) [buf] full ∧
        is_prefix tr (full ++ [event.ExitEv cs (m_fs model)])) := by
  rw [srealizes_obs_iff segs (mkCfg ms1 model) _
    (asan_init_srealizes segs ms1 model x8a
      Hh Hfd Hsvc1 Hno1 Hargs1 Hrefuse1 Hex1
      ms2 accs1 Hwalk1 Hout1
      x8b Hno2 Hsvc2 Hargs2 Hrefuse2 Hex2
      ms3 accs2 Hwalk2 Hout2
      buf Hbufnb Hbufmod x8c Hno3 Hw_svc Hw_fd1 Hw_read Hw_out
      msE accs3 Hwalk3 Hout3
      x8d cs HE_no HE_svc HE_code) tr]
  exact t_writes_ch_pick_exit_iff (BitVec.ofInt 64 1) [buf] cs (m_fs model) tr
    (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact Hbufnb)

end AsanInitReal

end LinuxSem.Common.NoReserve

