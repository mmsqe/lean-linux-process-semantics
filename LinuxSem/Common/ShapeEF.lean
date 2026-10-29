/-
  * Common.ShapeEF — the ERROR-FREE master theorem over [ShapeAlg.realizes].

    Image-INDEPENDENT.  ([init_config] / [mkEntry] take the mmap base and
    the AT_RANDOM draw [en_random] as extra arguments, so every statement
    carries one more binder of each per side.)

    [ShapeAlg.shape_strong_equiv] concludes [modeled /\ equiv]; the checked
    statements are [strong_universal_error_free_T], whose per-triple
    obligation is [strong_equiv_error_free] =
      error_free (run src) /\ error_free (run tgt) /\ trace_equiv ....
    Both sides being [realizes] of ONE shape gives exactly that
    conjunction (stated with the images/limits/entries spelled out, so it
    unifies with [strong_equiv_error_free src tgt (mkEntry ..) (mkEntry ..) inp]
    after [unfold strong_equiv_error_free]): [realizes_no_error] on each
    side and [realizes_obs_iff] twice.

    The configuration surface ([Equivalence.strong_universal_error_free_T_cfg
    alloc_may_fail]) is reached only in its [true] reading, which is this
    statement by [Equivalence.strong_universal_error_free_T_cfg_true];
    [ShapeAlg.realizes] is stated over the default configuration, so the
    forced-only ([alloc_may_fail = false]) sibling is not derivable here.

  NOTES.

  - values are `Int`, lists are `List`, and the section-free statement is
    carried as explicit binders: every lemma below names [segs] (and the
    image/entry/limit/input it is about) as arguments, exactly as
    `Common/ShapeAlg.lean` does for `realizes`.
  - `rrnd` / `arnd` are `StackLayout.EntryDraw` (the two byte-level entry
    draws: AT_RANDOM and the slack above the block), as in
    `Run.init_config`.
 The statements themselves are unchanged.
-/

import LinuxSem.Common.ShapeAlg

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.Common.ShapeAlg

namespace LinuxSem.Common.ShapeEF

/-- THE ERROR-FREE MASTER THEOREM: a source and a target that both realize
    the SAME shape are error-free, and their trace-prefix sets agree. -/
theorem shape_strong_equiv_ef (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    error_free (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ error_free (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)
    ∧ trace_equiv (bh_traces (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp))
        (bh_traces (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  refine ⟨?_, ?_, ?_⟩
  · show ¬ reaches_error source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
    exact realizes_no_error source_segs _ T Hsource
  · show ¬ reaches_error target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
    exact realizes_no_error target_segs _ T Htarget
  · intro tr
    exact (realizes_obs_iff source_segs _ T Hsource tr).trans
      (realizes_obs_iff target_segs _ T Htarget tr).symm

/-- Same, when the two sides were proved against extensionally equal but
    syntactically different shapes. -/
theorem shape_strong_equiv_ef_eq (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T T' : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T')
    (Heq : t_eq T T') :
    error_free (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ error_free (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)
    ∧ trace_equiv (bh_traces (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp))
        (bh_traces (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  exact shape_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim T' inp
    (.rz_conseq _ T T' Hsource Heq) Htarget

/-- The single-side facts, for callers that assemble the conjunction
    themselves. -/
theorem realizes_error_free (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (T : TSet)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    error_free (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) := by
  show ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)
  exact realizes_no_error segs _ T H

/-- ... and the trace half, as an `iff` at an arbitrary prefix [tr]. -/
theorem realizes_traces_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (T : TSet)
    (tr : List event)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    bh_traces (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) tr ↔ T tr := by
  show obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔ T tr
  exact realizes_obs_iff segs _ T H tr

end LinuxSem.Common.ShapeEF
