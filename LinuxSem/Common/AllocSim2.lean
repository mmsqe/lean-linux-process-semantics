/-
  * Common.AllocSim2 — mixed-allocator equivalence glue.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Glue for the allocator-divergence examples: a SOURCE binary whose
    behavior is characterized as an [AllocSim.to_outcomes] set (brk
    branching) and a TARGET binary characterized as a [MmapSim.tmw]
    derivation (one mmap with a failure tail and a success tail).  When
    the source's outcome set is exactly the two-element set
    { (bf, cf); (bs, cs) } matching the target's two tails, the two
    binaries are observably equivalent: allocation emits no trace
    events, so each side's trace set is the prefixes of the same two
    candidate traces even though the failing/succeeding resolutions
    come from different syscalls.

    NOTES.  This is the smallest [Common] file: the definition
    [two_outcomes] plus the two glue lemmas.  Its proofs go through the
    two run-level trace characterizations ([AllocSim.alloc_obs_iff],
    [MmapSim.mmap_obs_iff_te]) and the two no-error lemmas; nothing here
    mentions the shape algebra, so [ShapeAlg] can import this file (and
    does, for [t_outcomes_two_alt2] / the two [alloc_mmap_*_alg]
    re-derivations).
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.AllocSim
import LinuxSem.Common.MmapSim

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LinuxSem.Common.AllocSim2

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Common.CatSim
open LinuxSem.Common.SimInv
open LinuxSem.Common.AllocSim
open LinuxSem.Common.MmapSim
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

/-- The FP state at process entry, so that the [AllocSim]/[MmapSim]
    lemmas (whose proofs go through [PropExec.mkst]) elaborate.  Same
    local instance `ShapeAlg.lean` declares. -/
local instance allocsim2_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/-- The two-element outcome set of a fail/succeed allocator run. -/
def two_outcomes (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    : (List (List byte) × word) → Prop :=
  fun o => o = (bf, cf) ∨ o = (bs, cs)

/-- [Equivalence.equiv] for a brk-allocating source whose outcome set is
    [two_outcomes bf cf bs cs] and an mmap-allocating target with the
    same failure tail [(bf, cf)] and success tail [(bs, cs)]. -/
theorem alloc_mmap_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      (two_outcomes bf cf bs cs))
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp
        (two_outcomes bf cf bs cs) Hsource)
  · intro tr
    show obs_trace source_segs
        (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) tr
      ↔ obs_trace target_segs
        (init_config target_segs apc aph asp abrk amb arnd alim inp) tr
    rw [alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp
          (two_outcomes bf cf bs cs) Hsource tr,
        mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp
          bf cf bs cs Htarget Hbf Hbs tr]
    unfold two_traces two_outcomes outcome_trace
    constructor
    · rintro ⟨o, (ho | ho), Hp⟩
      · subst ho; exact Or.inl (by simpa using Hp)
      · subst ho; exact Or.inr (by simpa using Hp)
    · rintro (Hp | Hp)
      · exact ⟨(bf, cf), Or.inl rfl, by simpa using Hp⟩
      · exact ⟨(bs, cs), Or.inr rfl, by simpa using Hp⟩
  · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp
      bf cf bs cs Htarget Hbf Hbs

/-- The omni equivalence of a brk-branching source against a mmap-branching
    target with the same two outcomes, at the two role budgets. -/
theorem alloc_mmap_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (two_outcomes bf cf bs cs))
    (Htarget : tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp :=
  (strong_equiv_iff (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp).mp
    (alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
      target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp
      Hsource Htarget Hbf Hbs)

end LinuxSem.Common.AllocSim2
