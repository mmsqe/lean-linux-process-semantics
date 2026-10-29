/-
  * Common.ShapeEFS — the ERROR-FREE master theorem, MIXED form:
    source side [ShapeAlg.realizes], target side [SpinAlg.srealizes]
    (spin leaves allowed).

  ** Common.ShapeEFS — [ShapeEF.shape_strong_equiv_ef] with an
     [srealizes] target.

     Image-INDEPENDENT.  The plain build realizes its shape in the
     inductive, always-halting sense; a sanitizer build answers every
     refused memory request of its runtime with a silent self-jump, so its
     derivation needs [SpinAlg.srealizes] (the extra [srz_spin] leaf
     contributes only the empty trace, which every realized shape already
     contains).  The conclusion is spelled exactly as in
     [ShapeEF.shape_strong_equiv_ef] (so it unifies with
     [strong_equiv_error_free src tgt (mkEntry ..) (mkEntry ..) inp] after
     [unfold strong_equiv_error_free]).

  NOTES.

  - Every [Z] of  — the two allocation limits [rlim]/[alim] — is
    [Int], as everywhere in this tree.
  - [ShapeEF.lean] (the [realizes]/[realizes] sibling of this file) is a
    separate module and is deliberately NOT imported here: this file
    consumes only [ShapeAlg] and [SpinAlg] — the mixed form differs from
    [ShapeEF] in its TARGET hypothesis alone — so it stands alone (and
    does not drag in [SpinAlg]'s consumers either).
-/

import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.SpinAlg
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Common.ShapeEFS

/- =========================================================================
   The master theorem, mixed form
   ========================================================================= -/

/-- The error-free master theorem with a [srealizes] target: a source that
    realizes [T] in the always-halting sense and a TARGET that realizes [T]
    with spin leaves allowed are both error-free and trace-equivalent.
-/
theorem shape_strong_equiv_efs (source_segs : List Segment)
    (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : srealizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    error_free (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ error_free (run (mkImage target_segs apc aph) alim
        ⟨asp, abrk, amb, arnd⟩ inp)
    ∧ trace_equiv
        (bh_traces (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp))
        (bh_traces (run (mkImage target_segs apc aph) alim
          ⟨asp, abrk, amb, arnd⟩ inp)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- [error_free] of the source run: [realizes] reaches no error.
    show ¬ reaches_error source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
    exact realizes_no_error source_segs _ T Hsource
  · -- [error_free] of the target run: [srealizes] reaches no error either.
    show ¬ reaches_error target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
    exact srealizes_no_error target_segs _ T Htarget
  · -- Trace equality: both observation sets are exactly [T].
    intro tr
    show obs_trace source_segs
        (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) tr
      ↔ obs_trace target_segs
        (init_config target_segs apc aph asp abrk amb arnd alim inp) tr
    -- Both observation sets are [T], so the goal closes by [rfl].
    rw [realizes_obs_iff source_segs _ T Hsource tr,
      srealizes_obs_iff target_segs _ T Htarget tr]

/-- Same, when the two sides were proved against extensionally equal but
    syntactically different shapes. -/
theorem shape_strong_equiv_efs_eq (source_segs : List Segment)
    (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T T' : TSet) (inp : ProcInput)
    (Hs : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Ht : srealizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T')
    (Heq : t_eq T T') :
    error_free (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ error_free (run (mkImage target_segs apc aph) alim
        ⟨asp, abrk, amb, arnd⟩ inp)
    ∧ trace_equiv
        (bh_traces (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp))
        (bh_traces (run (mkImage target_segs apc aph) alim
          ⟨asp, abrk, amb, arnd⟩ inp)) := by
  -- [srz_conseq] turns the target's [T'] derivation into one at [T]
  -- ( derives [t_eq T' T] from [Heq] in the same place).
  exact shape_strong_equiv_efs source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim T inp Hs
    (srz_conseq target_segs _ T' T Ht (t_eq_sym Heq))

/-- Both sides with spin leaves (for a twin where the source also spins). -/
theorem shape_strong_equiv_ss (source_segs : List Segment)
    (rpc : Nat) (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : srealizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : srealizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    error_free (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ error_free (run (mkImage target_segs apc aph) alim
        ⟨asp, abrk, amb, arnd⟩ inp)
    ∧ trace_equiv
        (bh_traces (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp))
        (bh_traces (run (mkImage target_segs apc aph) alim
          ⟨asp, abrk, amb, arnd⟩ inp)) := by
  refine ⟨?_, ?_, ?_⟩
  · show ¬ reaches_error source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
    exact srealizes_no_error source_segs _ T Hsource
  · show ¬ reaches_error target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
    exact srealizes_no_error target_segs _ T Htarget
  · intro tr
    show obs_trace source_segs
        (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) tr
      ↔ obs_trace target_segs
        (init_config target_segs apc aph asp abrk amb arnd alim inp) tr
    -- Both observation sets are [T], so the goal closes by [rfl].
    rw [srealizes_obs_iff source_segs _ T Hsource tr,
      srealizes_obs_iff target_segs _ T Htarget tr]

end LinuxSem.Common.ShapeEFS
