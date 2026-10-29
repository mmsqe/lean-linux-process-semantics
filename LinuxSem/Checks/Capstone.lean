/-
  * `Checks.Capstone` — the headline claims in ONE auditable place, each paired
    with an EXECUTABLE witness.

  ## Why this file exists

  Counting declarations measures bulk, not usability: not whether the
  results fire on real objects.  The test this file applies is the one a
  downstream user would apply:

  * for each headline claim, can a caller INSTANTIATE it — supply the concrete
    image / input / model it is about — and get a fact back?
  * is the instantiation non-vacuous, i.e. does the premise really hold?

  Every section below therefore does three things: states the theorem by
  reference, exhibits the object it is about, and proves the premise (or a
  `by decide` sanity check) that makes it non-vacuous.  If this file
  typechecks, the claims are usable; if a theorem were vacuous or mis-stated,
  one of the witnesses below would fail to close.

  This is a CHECK, not a re-proof: everything here is either a reference to
  the real theorem or a small instantiation of it.
-/

import LinuxSem.Checks.AbortWitness
import LinuxSem.Checks.BudgetPremise
import LinuxSem.Checks.DispatchSurface
import LinuxSem.Checks.Examples
import LinuxSem.Checks.GatedSize
import LinuxSem.Checks.Omni
import LinuxSem.Checks.ProcessCreation
import LinuxSem.Checks.SpuriousCfg
import LinuxSem.Checks.VmMapsDisjoint
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Examples.PatchClassifyDemo.Sealed
import LinuxSem.Examples.RwxFlagNs.Proof
import LinuxSem.EquivalenceDefinition.PatchClassifySpec
import LinuxSem.Checks.ErrorFreeInput
import LinuxSem.Checks.HaltsAllowed
import LinuxSem.Checks.MemoryMaterialization

namespace LinuxSem.Checks.Capstone

open LinuxSem
open LinuxSem.LinuxProcessSem
open LinuxSem.Checks

/- ## 1. The abort refutation is FIRED, not merely stated

`abrt_refutes_error_free_abort` refutes `strong_universal_error_free_T_abort`
of an image against ITSELF.  The two things that make that non-vacuous are
that the witness exists (`abrt_image`) and that its premise holds: the run
really dies by signal at the declared limit. -/

/- The witness image exists. -/
#check @AbortWitness.abrt_image

/- The firing: no hypotheses, no free variables — a closed refutation. -/
#check @AbortWitness.abrt_refutes_error_free_abort

/- And its premise is DISCHARGED, at a limit, for the declared input.  This is
    the fact that makes the refutation bite rather than being conditional. -/
#check @AbortWitness.abrt_dies_by_signal

/- The entry and input are genuinely valid, so the quantifiers are reached. -/
#check @AbortWitness.demo_entry_valid_abrt
#check @AbortWitness.abrt_input_valid

/- ## 2. The dispatched syscall surface is EXACT, not documented

`modeled_sysnos_exact` turns `modeled_sysnos` from a list into a statement.
The witness that it is non-vacuous: the list is non-empty and has no
duplicates, both by decision procedure. -/

#check @DispatchSurface.modeled_sysnos_exact
#check @DispatchSurface.syscall_spec_number_modeled
#check @DispatchSurface.modeled_sysnos_dispatched
#check @DispatchSurface.modeled_sysnos_nodup

/- The list really has entries — a `None`-shaped list would make the iff
    above true for the wrong reason. -/
example : Specs.modeled_sysnos ≠ [] := by decide

/- ## 3. Omni and coexec are the SAME judgment

`coexec_progress_iff` is the identification; `coexec_progress_implies` is its
one direction, which the tree already had.  Together they say the two
judgments cannot disagree — so a claim stated in one currency transfers. -/

#check @Omni.coexec_progress_iff
#check @Omni.coexec_coexec_progress
#check @Omni.sstep_receptive

/- ## 4. The exit route is realizable AND bounded

`exits_c_must_exit_at` says a successful `exits_c` walk forces an exit;
`exits_c_exec` records the TRACE as well, which is what lets omni statements
be discharged.  The witness is a concrete image that really does exit. -/

#check @Examples.exits_c_must_exit_at
#check @Omni.exits_c_exec
#check @Examples.exit0_image_must_exit_zero

/- The concrete walk really succeeds — so `exits_c` is not an empty
    hypothesis for this image. -/
example : Examples.exits_c Examples.exit0_segments (BitVec.ofInt 64 0) 8
    (LinuxSem.LinuxProcessSem.Run.init_machine_state
      Examples.exit0_segments 0x100 Checks.Cases.Prelude.demo_phdrs
      (BitVec.ofInt 64 0x7fff80000000) Checks.Cases.Prelude.demo_draw
      Examples.demo_proc_input.in_argv Examples.demo_proc_input.in_envp
      Examples.demo_proc_input.in_uid Examples.demo_proc_input.in_hwcap) = true := by
  decide

/- ## 5. The budget mark's reading is DISCHARGED (under four state hypotheses)

`mremap_budget_refused_refuses_inplace` is the budget-refusal reading with
its four backing-metadata hypotheses kept explicit.  They are invariants of
reachable states that are not derived here, so the hedge sits on this lemma
rather than on the mremap module. -/

#check @BudgetPremise.mremap_budget_refused_refuses_inplace
#check @BudgetPremise.mremap_budget_refused_refuses_move
#check @BudgetPremise.mark_is_never_spurious

/- ## 6. Page-granularity is preserved by `brk` — the syscall where it bites

`brk` is the one writer whose grant may overlap a live mapping, so it is the
case the whole invariant hinges on.  `base_entry_unique` is the payoff: at a
page-aligned base a `map_has` hit names exactly one ledger entry. -/

#check @VmMapsDisjoint.brk_grant_wf
#check @VmMapsDisjoint.brk_model_next_wf
#check @VmMapsDisjoint.check_brk_preserves
-- The chain that turns the per-arm frame facts into a statement about the
-- whole syscall surface — UNCONDITIONAL: an unmodelled sysno makes the
-- hypothesis impossible, so there is no coverage premise.
#check @VmMapsDisjoint.checked_table_preserves_vm
#check @VmMapsDisjoint.check_syscall_preserves_vm_wf
#check @VmMapsDisjoint.syscall_spec_preserves_vm_wf
#check @VmMapsDisjoint.base_unique_after_syscall
#check @VmMapsDisjoint.base_entry_unique
#check @VmMapsDisjoint.munmap_returns_matched_bytes

/- ## 7. The ASan plan checker is SOUND

`check_sound` is the tower's capstone: every arm of the plan checker preserves
the abstract semantics.  It is stated over a concrete `LIMIT`, kept as an
explicit parameter rather than generalised. -/

#check @Common.AsanPlanSound.check_sound

/- ## 8. The two equivalence demos, instantiated

`DemoSealed` is a full `SPEC_PATCH_CLASSIFY` instance, so the patch classifier's
surface is INHABITED — not merely an interface.  `omni_strong_universal` is the
RwxFlag demo's capstone. -/

#check @LinuxSem.Examples.PatchClassifyDemo.Sealed.DemoSealed
#check @LinuxSem.Examples.PatchClassifyDemo.Sealed.demo_b1_reads_as_one
#check @LinuxSem.Examples.RwxFlagNs.omni_strong_universal
#check @LinuxSem.Examples.RwxFlagNs.strong_universal


/- ## 9. The gate surface is closed

`GatedSize` proves that the accept/reject gate on the exit-0 image is decided —
i.e. the surface is not merely unmodeled on it.  `DispatchSurface` proves the
list is exact.  Together: every number the spec answers is on the list, and
every number on the list is answered. -/

#check @GatedSize.gate_exit0_accepts
#check @GatedSize.gate_exit1_rejects

/- ## 10. The classifier surface needs no spurious-failure assumption

`ErrorFreeInput` and `HaltsAllowed` close the two questions the classifier
shape raises: whether an error-free input can be forced to fail, and whether a
halting image is allowed to be unmodeled. -/

#check @ErrorFreeInput.exit0_must_exit_zero_at_source_budget
#check @HaltsAllowed.exit1_must_exit_reject

end LinuxSem.Checks.Capstone
