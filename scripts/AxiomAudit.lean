/-
A soundness audit: the theorems below must depend only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

A tactic that silently *drops* a goal (e.g. an `elab` that clears the goal
list on failure — see PORTING.md §5.3) would leave a `sorryAx` in the proof
term while `scripts/check.sh`'s token grep would stay clean.  Checking the
axioms catches that class of hole.
-/
import LinuxSem

open LinuxSem

#print axioms Common.ShapeAlg.alloc_mmap_strong_equiv_alg
#print axioms Common.SymExec.sym_exec_sound
#print axioms Common.FileSim.fout_strong_equiv
#print axioms Common.DrainSim.drain_strong_equiv
#print axioms Common.StreamSim.stream_strong_equiv
#print axioms Common.AllocSim.alloc_strong_equiv
#print axioms Common.WallSim.wall_strong_equiv
#print axioms Common.MmapSim.mmap_strong_equiv_te
#print axioms Common.MuslCall.musl_write_frame
#print axioms Common.MuslStrlen.mstr_argv_ptr_bounds
#print axioms Common.AxSymExec3Sound.erange_f_sound
#print axioms Common.AxSymExec3Sound.evalS_eq
#print axioms Common.AxSymExec3Sound.mkOr_denot
#print axioms Common.AxSymExec3Sound.sym_exec_ex
#print axioms Common.AxSymExec3Sound.sym_execT_ex
#print axioms Common.AxSymRun3.run_sound
#print axioms Common.AxSymRun3.runTX_sound
#print axioms Common.AxSymRun3.carry_after
#print axioms Common.AxSymExec3Sound.carry_sound
#print axioms EquivalenceDefinition.MeasureLib.full_support_base_mass_lower_certificate
#print axioms EquivalenceDefinition.MeasureLib.calibrated_mixture_mass_lower_certificate
#print axioms Common.AsanPlanSound.check_sound
#print axioms Common.AxSymExec3B.carryK0_eq
#print axioms Common.AsanPlanCore.run_block_eq
#print axioms Common.AsanPopFree.popfree_spec_of_code
#print axioms Checks.ExecutableSpecs.check_syscall_for_run
