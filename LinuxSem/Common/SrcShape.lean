/-
  * Common.SrcShape — shape realization for a SOURCE that may FAULT

  TRUST BOUNDARY: image-INDEPENDENT proof library, like every other file
  in [Common/].  Nothing here is part of the trusted specification, and
  [EquivalenceDefinition/Equivalence.lean] is NOT touched.

  ** The problem

  [ShapeAlg.realizes segs c T] proves TWO things about [c]: its trace
  set is exactly [T] ([realizes_obs_iff]) AND it never takes the error
  transition ([realizes_no_error]).  That is what the TARGET side of
  [Equivalence.strong_equiv] needs ([~ bh_errors target]).  The SOURCE
  side needs strictly less: [Equivalence.modeled] — the run never
  reaches a configuration the MODEL declines to interpret
  ([Run.unmodeled_at]: a [MachineUnmodeled] instruction or an
  [Unmodeled] syscall) — plus trace-set equality with the target.

  A reference binary is entitled to CRASH on some nondeterministic
  branch (the canonical case: [malloc] returns NULL after a failed
  [mmap]/[brk], and the following store to address 0 is a
  [RiscvSemantics.MachineFault]).  [Run.lean] is explicit that a fault is
  a faithfully modeled event (the process really dies, SIGSEGV) and is
  NOT [unmodeled_at]: [unmodeled_at] asks for [MachineUnmodeled], never
  for [MachineFault].  The faulting branch contributes exactly the empty
  trace to [obs_trace] (its only transition is [sstep_instr_fault],
  which goes to [SError] and emits nothing), so as far as trace-set
  equality is concerned it is a [t_nil] leaf.

  ** The design

  [srealizes] is [realizes] plus ONE constructor, [srz_fault]: a
  non-halted, non-syscall configuration whose instruction step is
  [MachineFault] realizes [t_nil].  Everything [ShapeAlg] proves by
  induction on [realizes] is re-proved here by the same induction with
  one extra (trivial) case — EXCEPT [realizes_no_error], which is false
  for [srealizes] and is replaced by

    [srealizes_modeled] : srealizes c T -> ¬ reaches_unmodeled segs c.

  WHY THIS IS LEGITIMATE FOR THE SOURCE ONLY.  The master theorem
  [src_shape_strong_equiv] takes [srealizes] for the SOURCE and the
  ordinary [realizes] for the TARGET.  The target's obligation in
  [Equivalence.equiv] is [¬ bh_errors], which a fault would violate, so
  a target derivation must still rule faults out; the source's
  obligation is [modeled = ¬ bh_unmodeled], which a fault does not
  violate.  Nothing about the trusted definitions is weakened: the
  conclusion is literally [Equivalence.modeled ∧ Equivalence.equiv]
  (right disjunct: trace equality + target never errors).

  [srz_realizes] embeds every [realizes] derivation, so all the
  [ShapeAlg] node combinators remain usable on the source side.

  ** Inventory

  - relation: [srealizes] with [srz_node] / [srz_halt] / [srz_fault] /
    [srz_conseq]; embedding [srz_realizes]; [srz_fault_any].
  - theorems: [srealizes_nonempty], [srealizes_pclosed],
    [srealizes_star_only], [srealizes_admits], [srealizes_obs_iff],
    [srealizes_star_not_unmodeled], [srealizes_modeled],
    [srealizes_unique].
  - generic combinators over a [ShapeAlg.node_ok] interface:
    [srz_of_node], [srz_silent1], [srz_emit1], [srz_alt2],
    [srz_node_same] (all resolutions continue as the same shape),
    [srz_node_same_or_nil] / [srz_alt2_absorb_l] / [srz_alt2_absorb_r]
    (FAULT ABSORPTION: resolutions that die silently contribute only
    the empty trace, so they vanish next to a branch realizing [T]).
  - concrete nodes: [srz_step], [srz_msteps], [srz_msteps_fault],
    [srz_write1], [srz_write_ch], [srz_exit], [srz_munmap], [srz_mmap].
  - master theorem: [src_shape_strong_equiv] (source [srealizes T],
    target [realizes T'], [t_eq T T']) and [src_shape_strong_equiv_same].
 Nothing
    is added to the relation and no shape is weakened.
  - All 38  declarations are present (the inductive [srealizes]
    with its four constructors, and 37 lemmas/theorems); none is deferred.
-/

import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.ShapeAlg
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.MmapSim
open LinuxSem.Common.ShapeAlg
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Common.SrcShape

/-- The FP state at process entry, so that the [MmapSim]/[CatSim] lemmas
    (whose proofs go through [PropExec.mkst]) elaborate.  Same local
    instance `ShapeAlg.lean` / `SpinAlg.lean` declare. -/
local instance srcshape_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   The relation: [realizes] + a fault leaf
   ========================================================================= -/

/-- [`realizes`] plus ONE constructor, [`srz_fault`]: a config that is not
    halted, has no pending syscall, has no lazy mapping left to charge, and
    whose instruction step is a genuine [`MachineFault`] realizes [`t_nil`]
    (the fault emits nothing — its only transition is
    [`sstep.instr_fault`], which lands in [`SError`]). -/
inductive srealizes (segs : List Segment) : config → TSet → Prop where
  | srz_node (c : config) (I : Type) (evs : I → List event) (nx : I → config)
      (T : I → TSet) (i0 : I)
      (hnode : node_ok segs c I evs nx)
      (hcont : ∀ i, srealizes segs (nx i) (T i)) :
      srealizes segs c (t_alt (fun i => t_emit (evs i) (T i)))
  | srz_halt (c : config) (hh : m_halted c.cfg_model ≠ none) :
      srealizes segs c t_nil
  | srz_fault (c : config) (hh : m_halted c.cfg_model = none)
      (hsvc : c.cfg_ms.ms_svc_pending = none)
      (hlazy : m_vm_lazy c.cfg_model = [])
      (hf : RiscvSemantics.step segs c.cfg_ms = .MachineFault) :
      srealizes segs c t_nil
  | srz_conseq (c : config) (T T' : TSet)
      (h : srealizes segs c T) (heq : t_eq T T') :
      srealizes segs c T'

/-- The embedding: an error-free realization is a source realization. -/
theorem srz_realizes (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : srealizes segs c T := by
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    exact .srz_node c I evs nx T i0 hnode ih
  | rz_halt c hh => exact .srz_halt c hh
  | rz_conseq c T T' h heq ih => exact .srz_conseq c T T' ih heq

/- -------------------------------------------------------------------------
   The fault leaf: no [SNext] successor, not unmodeled.
   ------------------------------------------------------------------------- -/

theorem fault_no_snext (segs : List Segment) (c : config) (evs : List event)
    (c' : config) :
    c.cfg_ms.ms_svc_pending = none →
    m_vm_lazy c.cfg_model = [] →
    RiscvSemantics.step segs c.cfg_ms = .MachineFault →
    ¬ sstep segs c evs (.SNext c') := by
  obtain ⟨ms, model⟩ := c
  intro Hsvc Hlazy Hf Hss
  have Hacc : mi_account_step segs ms model = .MachineFault := by
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hf]
  -- The target index is a CONSTRUCTOR here, so the case split is taken over
  -- a variable-indexed restatement first (the `FileMixSim` house device).
  have Honly : ∀ (evs' : List event) (st : step_to),
      sstep segs ⟨ms, model⟩ evs' st → st ≠ .SNext c' := by
    intro evs' st hss
    cases hss with
    | instr ms0 model0 ms0' model0' hh hsvc hacc =>
      rw [Hacc] at hacc
      exact nomatch hacc
    | instr_fault ms0 model0 hh hsvc hacc => exact fun h => nomatch h
    | instr_unmodeled ms0 model0 hh hsvc hacc =>
      rw [Hacc] at hacc
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
  exact Honly evs (.SNext c') Hss rfl

/-- Every transition out of a fault leaf is the silent error transition. -/
theorem fault_sstep_inv (segs : List Segment) (c : config) (evs : List event)
    (st : step_to) :
    c.cfg_ms.ms_svc_pending = none →
    m_vm_lazy c.cfg_model = [] →
    RiscvSemantics.step segs c.cfg_ms = .MachineFault →
    sstep segs c evs st → evs = [] ∧ st = .SError := by
  obtain ⟨ms, model⟩ := c
  intro Hsvc Hlazy Hf Hss
  have Hacc : mi_account_step segs ms model = .MachineFault := by
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hf]
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    rw [Hacc] at hacc
    exact nomatch hacc
  | instr_fault ms0 model0 hh hsvc hacc => exact ⟨rfl, rfl⟩
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
    rw [Hacc] at hacc
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

theorem fault_star_refl (segs : List Segment) (c : config) (tr : List event)
    (c' : config) :
    c.cfg_ms.ms_svc_pending = none →
    m_vm_lazy c.cfg_model = [] →
    RiscvSemantics.step segs c.cfg_ms = .MachineFault →
    star segs c tr c' → tr = [] ∧ c' = c := by
  intro Hsvc Hlazy Hf Hstar
  cases Hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step c1 evs c2 tr2 c3 hss htail =>
    exact absurd hss (fault_no_snext segs c evs c2 Hsvc Hlazy Hf)

theorem fault_not_unmodeled (segs : List Segment) (c : config) :
    c.cfg_ms.ms_svc_pending = none →
    m_vm_lazy c.cfg_model = [] →
    RiscvSemantics.step segs c.cfg_ms = .MachineFault →
    ¬ unmodeled_at segs c := by
  obtain ⟨ms, model⟩ := c
  intro Hsvc Hlazy Hf Hun
  obtain ⟨-, hun | hun⟩ := Hun
  · obtain ⟨-, hacc⟩ := hun
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hf] at hacc
    exact nomatch hacc
  · obtain ⟨x8, hsvcx, -⟩ := hun
    exact absurd hsvcx (by rw [Hsvc]; simp)

theorem halted_not_unmodeled (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model ≠ none) : ¬ unmodeled_at segs c := by
  intro Hun
  exact Hh Hun.1

/-- At a node every transition is an [`SNext`] of the family, so the node is
    covered by the model. -/
theorem node_not_unmodeled (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config)
    (Hnode : node_ok segs c I evs nx) : ¬ unmodeled_at segs c := by
  intro Hun
  obtain ⟨e, hss⟩ := unmodeled_at_sstep_error segs c Hun
  obtain ⟨i, -, hbad⟩ := Hnode.2 e .SError hss
  exact nomatch hbad

/- -------------------------------------------------------------------------
   Structural facts: nonempty, prefix-closed.
   ------------------------------------------------------------------------- -/

theorem srealizes_nonempty (segs : List Segment) (c : config) (T : TSet)
    (H : srealizes segs c T) : T [] := by
  induction H with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
  | srz_halt c hh => rfl
  | srz_fault c hh hsvc hlazy hf => rfl
  | srz_conseq c T T' h heq ih => exact (heq []).1 ih

theorem srealizes_pclosed (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T →
      ∀ (tr tr' : List event), T tr → is_prefix tr' tr → T tr' := by
  intro H
  induction H with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr tr' HT Hp
    rcases HT with ⟨i, Hpre | ⟨tr0, htr, HT0⟩⟩
    · exact ⟨i, Or.inl (is_prefix_trans Hp Hpre)⟩
    · subst htr
      rcases is_prefix_app_split (evs i) tr0 tr' Hp with Hp' | ⟨tr0', htr', Hp'⟩
      · exact ⟨i, Or.inl Hp'⟩
      · subst htr'
        exact ⟨i, Or.inr ⟨tr0', rfl, ih i tr0 tr0' HT0 Hp'⟩⟩
  | srz_halt c hh =>
    intro tr tr' HT Hp
    simp only [t_nil] at HT
    subst HT
    exact is_prefix_nil_r tr' Hp
  | srz_fault c hh hsvc hlazy hf =>
    intro tr tr' HT Hp
    simp only [t_nil] at HT
    subst HT
    exact is_prefix_nil_r tr' Hp
  | srz_conseq c T T' h heq ih =>
    intro tr tr' HT Hp
    exact (heq tr').1 (ih tr tr' ((heq tr).2 HT) Hp)

/- -------------------------------------------------------------------------
   Soundness / completeness of the trace set.
   ------------------------------------------------------------------------- -/

theorem srealizes_star_only (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T →
      ∀ (tr : List event) (c' : config), star segs c tr c' → T tr := by
  intro H
  induction H with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr c' hstar
    cases hstar with
    | refl => exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
    | step c1 e c2 tr2 c3 hss htail =>
      obtain ⟨i, he, hst⟩ := hnode.2 e (.SNext c2) hss
      subst he
      cases hst
      exact ⟨i, Or.inr ⟨tr2, rfl, ih i tr2 _ htail⟩⟩
  | srz_halt c hh =>
    intro tr c' hstar
    obtain ⟨rfl, -⟩ := star_halted_nil segs c tr c' hh hstar
    rfl
  | srz_fault c hh hsvc hlazy hf =>
    intro tr c' hstar
    obtain ⟨rfl, -⟩ := fault_star_refl segs c tr c' hsvc hlazy hf hstar
    rfl
  | srz_conseq c T T' h heq ih =>
    intro tr c' hstar
    exact (heq tr).1 (ih tr c' hstar)

theorem srealizes_admits (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ tr, T tr → obs_trace segs c tr := by
  intro H
  induction H with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr HT
    rcases HT with ⟨i, Hpre | ⟨tr0, htr, HT0⟩⟩
    · exact ⟨evs i, nx i, star_one segs c (evs i) (nx i) (hnode.1 i), Hpre⟩
    · subst htr
      obtain ⟨tr'', c'', hstar, hp⟩ := ih i tr0 HT0
      exact ⟨evs i ++ tr'', c'',
        star.step c (evs i) (nx i) tr'' c'' (hnode.1 i) hstar,
        is_prefix_app_mono (evs i) tr0 tr'' hp⟩
  | srz_halt c hh =>
    intro tr HT
    simp only [t_nil] at HT
    subst HT
    exact obs_trace_nil segs c
  | srz_fault c hh hsvc hlazy hf =>
    intro tr HT
    simp only [t_nil] at HT
    subst HT
    exact obs_trace_nil segs c
  | srz_conseq c T T' h heq ih =>
    intro tr HT
    exact ih tr ((heq tr).2 HT)

/-- The master observation theorem, fault leaves included: shape membership
    IS trace-prefix-set membership.  A fault leaf contributes exactly the
    empty trace, which is all its single (silent, error) transition emits. -/
theorem srealizes_obs_iff (segs : List Segment) (c : config) (T : TSet)
    (H : srealizes segs c T) (tr : List event) :
    obs_trace segs c tr ↔ T tr := by
  constructor
  · rintro ⟨tr', c', hstar, hp⟩
    exact srealizes_pclosed segs c T H tr' tr
      (srealizes_star_only segs c T H tr' c' hstar) hp
  · exact srealizes_admits segs c T H tr

/- -------------------------------------------------------------------------
   Coverage: a source realization never reaches an unmodeled configuration.
   ------------------------------------------------------------------------- -/

theorem srealizes_star_not_unmodeled (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T →
      ∀ (tr : List event) (c' : config), star segs c tr c' → ¬ unmodeled_at segs c' := by
  intro H
  induction H with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr c' hstar
    cases hstar with
    | refl => exact node_not_unmodeled segs c I evs nx hnode
    | step c1 e c2 tr2 c3 hss htail =>
      obtain ⟨i, -, hst⟩ := hnode.2 e (.SNext c2) hss
      have hc2 : c2 = nx i := by injection hst
      subst hc2
      exact ih i tr2 c' htail
  | srz_halt c hh =>
    intro tr c' hstar
    cases hstar with
    | refl => exact halted_not_unmodeled segs c hh
    | step c1 evs c2 tr2 c3 hss htail =>
      exact absurd (sstep_halted_none segs c evs (.SNext c2) hss) hh
  | srz_fault c hh hsvc hlazy hf =>
    intro tr c' hstar
    cases hstar with
    | refl => exact fault_not_unmodeled segs c hsvc hlazy hf
    | step c1 evs c2 tr2 c3 hss htail =>
      exact absurd hss (fault_no_snext segs c evs c2 hsvc hlazy hf)
  | srz_conseq c T T' h heq ih =>
    intro tr c' hstar
    exact ih tr c' hstar

/-- THE SOURCE OBLIGATION.  A source realization never reaches a
    configuration the model declines to interpret.  (It may FAULT — that is
    the whole point of the extra leaf; a fault is modeled.) -/
theorem srealizes_modeled (segs : List Segment) (c : config) (T : TSet)
    (H : srealizes segs c T) : ¬ reaches_unmodeled segs c := by
  rintro ⟨tr, c', Hstar, Hun⟩
  exact srealizes_star_not_unmodeled segs c T H tr c' Hstar Hun

/-- The shape a configuration realizes is unique up to [`t_eq`] (both are
    its [`obs_trace`]). -/
theorem srealizes_unique (segs : List Segment) (c : config) (T T' : TSet)
    (H : srealizes segs c T) (H' : srealizes segs c T') : t_eq T T' := by
  intro tr
  exact (srealizes_obs_iff segs c T H tr).symm.trans
    (srealizes_obs_iff segs c T' H' tr)

/- -------------------------------------------------------------------------
   Shape algebra facts used by the fault-absorbing combinators.
   ------------------------------------------------------------------------- -/

theorem t_alt2_nil_l (T : TSet) (H0 : T []) : t_eq (t_alt2 t_nil T) T := by
  intro tr
  constructor
  · rintro (h | h)
    · simp only [t_nil] at h
      subst h
      exact H0
    · exact h
  · intro HT
    exact Or.inr HT

theorem t_alt2_nil_r (T : TSet) (H0 : T []) : t_eq (t_alt2 T t_nil) T := by
  intro tr
  constructor
  · rintro (h | h)
    · exact h
    · simp only [t_nil] at h
      subst h
      exact H0
  · intro HT
    exact Or.inl HT

theorem t_alt2_comm (A B : TSet) : t_eq (t_alt2 A B) (t_alt2 B A) := by
  intro tr
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/- =========================================================================
   Combinators (continuation-polymorphic), mirroring [ShapeAlg]
   ========================================================================= -/

/-- Generic node introduction (the constructor, with the shape left to
    unification). -/
theorem srz_of_node (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) (T : I → TSet)
    (hnode : node_ok segs c I evs nx) (i0 : I)
    (hcont : ∀ i, srealizes segs (nx i) (T i)) :
    srealizes segs c (t_alt (fun i => t_emit (evs i) (T i))) :=
  .srz_node c I evs nx T i0 hnode hcont

/-- The fault leaf regardless of the halted flag. -/
theorem srz_fault_any (segs : List Segment) (c : config) :
    c.cfg_ms.ms_svc_pending = none →
    m_vm_lazy c.cfg_model = [] →
    RiscvSemantics.step segs c.cfg_ms = .MachineFault →
    srealizes segs c t_nil := by
  intro Hsvc Hlz Hf
  cases hh : m_halted c.cfg_model with
  | some code => exact .srz_halt c (by rw [hh]; simp)
  | none => exact .srz_fault c hh Hsvc Hlz Hf

theorem srz_silent1 (segs : List Segment) (c c' : config) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => []) (fun _ => c'))
    (Hc : srealizes segs c' T) : srealizes segs c T := by
  refine .srz_conseq c (t_alt (fun _ : Unit => t_emit [] T)) T ?_ ?_
  · exact .srz_node c Unit (fun _ => []) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_eq_trans (t_alt_unit (fun _ : Unit => t_emit [] T))
      (t_emit_nil_eq T (srealizes_nonempty segs c' T Hc))

theorem srz_emit1 (segs : List Segment) (c c' : config) (e : List event) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => e) (fun _ => c'))
    (Hc : srealizes segs c' T) : srealizes segs c (t_emit e T) := by
  refine .srz_conseq c (t_alt (fun _ : Unit => t_emit e T)) (t_emit e T) ?_ ?_
  · exact .srz_node c Unit (fun _ => e) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_alt_unit (fun _ : Unit => t_emit e T)

theorem srz_alt2 (segs : List Segment) (c : config) (IA IB : Type)
    (nx : IA ⊕ IB → config) (A B : TSet) (a0 : IA) (b0 : IB)
    (Hnode : node_ok segs c (IA ⊕ IB) (fun _ => []) nx)
    (HA : ∀ i, srealizes segs (nx (.inl i)) A)
    (HB : ∀ i, srealizes segs (nx (.inr i)) B) :
    srealizes segs c (t_alt2 A B) := by
  have HA0 : A [] := srealizes_nonempty segs (nx (.inl a0)) A (HA a0)
  have HB0 : B [] := srealizes_nonempty segs (nx (.inr b0)) B (HB b0)
  refine .srz_conseq c
    (t_alt (fun i : IA ⊕ IB => t_emit [] (match i with | .inl _ => A | .inr _ => B)))
    (t_alt2 A B) ?_ ?_
  · exact .srz_node c (IA ⊕ IB) (fun _ => []) nx
      (fun i => match i with | .inl _ => A | .inr _ => B) (.inl a0) Hnode
      (fun i => by cases i with | inl i => exact HA i | inr i => exact HB i)
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl i => exact Or.inl ((t_emit_nil_eq A HA0 tr).1 Hi)
      | inr i => exact Or.inr ((t_emit_nil_eq B HB0 tr).1 Hi)
    · rintro (H | H)
      · exact ⟨.inl a0, (t_emit_nil_eq A HA0 tr).2 H⟩
      · exact ⟨.inr b0, (t_emit_nil_eq B HB0 tr).2 H⟩

/-- A SILENT nondeterministic node all of whose resolutions continue as the
    SAME shape collapses to that shape (no inhabitation premise beyond one
    index, which the always-admissible failure arm supplies for
    brk/mmap/mprotect). -/
theorem srz_node_same (segs : List Segment) (c : config) (I : Type)
    (nx : I → config) (T : TSet)
    (Hnode : node_ok segs c I (fun _ => []) nx) (i0 : I)
    (Hcont : ∀ i, srealizes segs (nx i) T) : srealizes segs c T := by
  have H0 : T [] := srealizes_nonempty segs (nx i0) T (Hcont i0)
  refine .srz_conseq c (t_alt (fun _ : I => t_emit [] T)) T ?_ ?_
  · exact .srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hcont
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      exact (t_emit_nil_eq T H0 tr).1 Hi
    · intro HT
      exact ⟨i0, (t_emit_nil_eq T H0 tr).2 HT⟩

/-- FAULT ABSORPTION.  A silent nondeterministic node where every resolution
    either continues as [T] or dies silently ([t_nil] — e.g. a failed
    allocation followed by a store through NULL), and at least one
    resolution continues as [T], realizes [T]: the dying branches add only
    the empty trace, which [T] already contains. -/
theorem srz_node_same_or_nil (segs : List Segment) (c : config) (I : Type)
    (nx : I → config) (T : TSet)
    (Hnode : node_ok segs c I (fun _ => []) nx)
    (Hex : ∃ i, srealizes segs (nx i) T)
    (Hcont : ∀ i, srealizes segs (nx i) T ∨ srealizes segs (nx i) t_nil) :
    srealizes segs c T := by
  obtain ⟨i1, Hi1⟩ := Hex
  have H0 : T [] := srealizes_nonempty segs (nx i1) T Hi1
  have Hcont' : ∀ i, srealizes segs (nx i)
      (fun tr => (srealizes segs (nx i) T ∧ T tr)
        ∨ (srealizes segs (nx i) t_nil ∧ tr = [])) := by
    intro i
    rcases Hcont i with Hi | Hi
    · refine .srz_conseq (nx i) T
        (fun tr => (srealizes segs (nx i) T ∧ T tr)
          ∨ (srealizes segs (nx i) t_nil ∧ tr = [])) Hi ?_
      intro tr
      constructor
      · intro HT
        exact Or.inl ⟨Hi, HT⟩
      · rintro (⟨-, HT⟩ | ⟨-, hnil⟩)
        · exact HT
        · rw [hnil]; exact H0
    · refine .srz_conseq (nx i) t_nil
        (fun tr => (srealizes segs (nx i) T ∧ T tr)
          ∨ (srealizes segs (nx i) t_nil ∧ tr = [])) Hi ?_
      intro tr
      constructor
      · intro Htr
        simp only [t_nil] at Htr
        subst Htr
        exact Or.inr ⟨Hi, rfl⟩
      · rintro (⟨HiT, HT⟩ | ⟨-, hnil⟩)
        · exact (srealizes_unique segs (nx i) T t_nil HiT Hi tr).1 HT
        · exact hnil
  refine .srz_conseq c (t_alt (fun i : I => t_emit [] (fun tr =>
      (srealizes segs (nx i) T ∧ T tr)
        ∨ (srealizes segs (nx i) t_nil ∧ tr = [])))) T ?_ ?_
  · exact .srz_node c I (fun _ => []) nx
      (fun i tr => (srealizes segs (nx i) T ∧ T tr)
        ∨ (srealizes segs (nx i) t_nil ∧ tr = [])) i1 Hnode Hcont'
  · intro tr
    constructor
    · rintro ⟨i, hpre | ⟨tr', htr, hT'⟩⟩
      · have h' : tr = [] := is_prefix_nil_r tr hpre
        rw [h']
        exact H0
      · have htr' : tr = tr' := htr
        rw [htr']
        rcases hT' with ⟨-, hT⟩ | ⟨-, hnil⟩
        · exact hT
        · rw [hnil]; exact H0
    · intro HT
      exact ⟨i1, Or.inr ⟨tr, rfl, Or.inl ⟨Hi1, HT⟩⟩⟩

/-- The two-group instance: one group of resolutions dies silently, the
    other continues as [B]. -/
theorem srz_alt2_absorb_l (segs : List Segment) (c : config) (IA IB : Type)
    (nx : IA ⊕ IB → config) (B : TSet) (b0 : IB)
    (Hnode : node_ok segs c (IA ⊕ IB) (fun _ => []) nx)
    (HA : ∀ i, srealizes segs (nx (.inl i)) t_nil)
    (HB : ∀ i, srealizes segs (nx (.inr i)) B) : srealizes segs c B := by
  refine srz_node_same_or_nil segs c (IA ⊕ IB) nx B Hnode ⟨.inr b0, HB b0⟩ ?_
  rintro (i | i)
  · exact Or.inr (HA i)
  · exact Or.inl (HB i)

/-- The mirror instance: the FIRST group continues as [A], the second dies
    silently. -/
theorem srz_alt2_absorb_r (segs : List Segment) (c : config) (IA IB : Type)
    (nx : IA ⊕ IB → config) (A : TSet) (a0 : IA)
    (Hnode : node_ok segs c (IA ⊕ IB) (fun _ => []) nx)
    (HA : ∀ i, srealizes segs (nx (.inl i)) A)
    (HB : ∀ i, srealizes segs (nx (.inr i)) t_nil) : srealizes segs c A := by
  refine srz_node_same_or_nil segs c (IA ⊕ IB) nx A Hnode ⟨.inl a0, HA a0⟩ ?_
  rintro (i | i)
  · exact Or.inl (HA i)
  · exact Or.inr (HB i)

/- -------------------------------------------------------------------------
   Concrete nodes: instruction step(s), write, exit, munmap, mmap.
   ------------------------------------------------------------------------- -/

theorem srz_step (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (T : TSet)
    (Hh : m_halted model = none) (Hlz : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T (node_instr segs ms model ms' Hh Hlz Hsvc Hstep) Hc

theorem srz_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (T : TSet) (Hh : m_halted model = none) (Hlz : m_vm_lazy model = [])
    (Hms : msteps segs ms ms') (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T := by
  revert Hc
  induction Hms with
  | mst_refl ms => intro Hc; exact Hc
  | mst_step ms ms1 ms2 hsvc hstep hrest ih =>
    intro Hc
    exact srz_step segs ms model ms1 T Hh Hlz hsvc hstep (ih Hc)

/-- A deterministic instruction line that ends in a genuine fault: the
    [ErrEscape] path, as a [t_nil] leaf. -/
theorem srz_msteps_fault (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (Hh : m_halted model = none) (Hlz : m_vm_lazy model = [])
    (Hms : msteps segs ms ms') (Hsvc : ms'.ms_svc_pending = none)
    (Hf : RiscvSemantics.step segs ms' = .MachineFault) :
    srealizes segs (mkCfg ms model) t_nil :=
  srz_msteps segs ms ms' model t_nil Hh Hlz Hms (.srz_fault (mkCfg ms' model) Hh Hsvc Hlz Hf)

theorem srz_write1 (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    srealizes segs (mkCfg ms model) (t_write_ch (BitVec.ofInt 64 1) buf T) := by
  unfold t_write_ch
  exact srz_of_node segs (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T)
    (node_write1 segs ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb)
    (wr_full buf Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

theorem srz_write_ch (segs : List Segment) (ms : machine_state) (model : Model)
    (fd ch x8 : word) (buf : List byte) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : fd32 fd = fd)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = fd)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    srealizes segs (mkCfg ms model) (t_write_ch ch buf T) := by
  unfold t_write_ch
  exact srz_of_node segs (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv ch))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T)
    (node_write_ch segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb)
    (wr_full buf Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

/-- The [exit] leaf (error-free, so simply embedded). -/
theorem srz_exit (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hx8 : is_exit_no x8) :
    srealizes segs (mkCfg ms model)
      (t_exit (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)) :=
  srz_realizes segs _ _ (rz_exit segs ms model x8 Hh Hsvc Hx8)

theorem srz_munmap (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 215)
    (Hargs : munmap_args_ok ms model)
    (Hc : srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T) :
    srealizes segs (mkCfg ms model) T := by
  refine srz_silent1 segs _ _ T ?_ Hc
  constructor
  · intro i
    cases i
    exact sstep.syscall ms model x8 (munmap_eff ms)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
      Hh Hsvc (munmap_ok segs ms x8 model Hno Hargs)
      (by rw [munmap_model_halted]; exact Hh)
      (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))
  · intro e st Hss
    obtain ⟨he, hst⟩ :=
      sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
    exact ⟨(), he, hst⟩

/-- The [mmap] node: failure resolutions continue as [A] (typically the
    branch that later FAULTS), success resolutions as [B]. -/
theorem srz_mmap (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (A B : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
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
  let IA := { e : Int // e ∈ mmap_errnos }
  let IB := { a : word // grant_ok (ms_gpr ms 0) model a
                (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }
  let nx : IA ⊕ IB → config := fun i =>
    match i with
    | .inl e => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e.1))) model
    | .inr a => mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a.1 [] [(a.1, page_round_up (ms_gpr ms 1))])))
        (mmap_model a.1 (page_round_up (ms_gpr ms 1)) model)
  have Hnode : node_ok segs (mkCfg ms model) (IA ⊕ IB) (fun _ => []) nx := by
    constructor
    · rintro (⟨e, He⟩ | ⟨a, Ha⟩)
      · exact sstep.syscall ms model x8 (mkEffect (errno_ret e) [] []) model model []
          Hh Hsvc (mmap_fail_ok segs ms x8 model e Hno Hargs He) Hh
          (materialize_model_accesses_no_lazy _ _ Hlazy)
      · exact sstep.syscall ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
          (mmap_model a (page_round_up (ms_gpr ms 1)) model)
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) []
          Hh Hsvc (mmap_succ_ok segs ms x8 model a Hno Hargs Ha)
          (by rw [mmap_model_halted]; exact Hh)
          (materialize_model_accesses_no_lazy _ _ (by rw [mmap_model_lazy]; exact Hlazy))
    · intro e st Hss
      obtain ⟨he, hst⟩ := sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
      rcases hst with ⟨er, Her, hst⟩ | ⟨a, Ha, hst⟩
      · exact ⟨.inl ⟨er, Her⟩, he, hst⟩
      · exact ⟨.inr ⟨a, Ha⟩, he, hst⟩
  exact srz_alt2 segs (mkCfg ms model) IA IB nx A B
    ⟨ENOMEM, ENOMEM_in_mmap_errnos⟩ ⟨a0, Ha0⟩ Hnode
    (fun i => HA i.1 i.2)
    (fun i => HB i.1 i.2)

/- =========================================================================
   The master equivalence theorem: may-faulting SOURCE vs error-free TARGET
   ========================================================================= -/

/-- A source that may FAULT (its shape is [srealizes T]) and an error-free
    target (its shape is [realizes T']) with [t_eq T T'] are equivalent, and
    the source is covered by the model.

    The two conclusions are the trusted ones, unchanged: [modeled] for the
    source (a fault is not unmodeled, so [srealizes_modeled] discharges it),
    and [equiv] — here the RIGHT disjunct, trace equality plus a target that
    never errors ([realizes_no_error], which a fault would break and which
    is therefore required of the target only). -/
theorem src_shape_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T T' : TSet) (inp : ProcInput)
    (Hsource : srealizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T')
    (Heq : t_eq T T') :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · -- source coverage: a fault is a modeled event, so [srealizes_modeled]
    -- is exactly [modeled].
    exact srealizes_modeled source_segs _ T Hsource
  · refine Or.inr ⟨?_, ?_⟩
    · intro tr
      have hs : (run (mkImage source_segs rpc rph) rlim
          ⟨rsp, rbrk, rmb, rrnd⟩ inp).bh_traces
          = obs_trace source_segs
              (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) := rfl
      have ht : (run (mkImage target_segs apc aph) alim
          ⟨asp, abrk, amb, arnd⟩ inp).bh_traces
          = obs_trace target_segs
              (init_config target_segs apc aph asp abrk amb arnd alim inp) := rfl
      rw [hs, ht]
      exact (srealizes_obs_iff source_segs _ T Hsource tr).trans
        ((Heq tr).trans (realizes_obs_iff target_segs _ T' Htarget tr).symm)
    · exact realizes_no_error target_segs _ T' Htarget

/-- Same-shape instance. -/
theorem src_shape_strong_equiv_same
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : srealizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) :=
  src_shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim T T inp Hsource Htarget
    (t_eq_refl T)

/- =========================================================================
   The formers at their  (FLAT) names
   =========================================================================

    declares these INSIDE `Inductive srealizes` but in a
   `Section WithSegs`, so they are flat names with [segs] as an
   explicit first argument:

     | srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                         (T : I -> TSet) (i0 : I),
         node_ok segs c I evs nx ->
         (forall i, srealizes (nx i) (T i)) ->
         srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
     | srz_fault : forall c,
         m_halted (cfg_model c) = None ->
         ms_svc_pending (cfg_ms c) = None ->
         m_vm_lazy (cfg_model c) = [] ->
         RiscvSemantics.step segs (cfg_ms c) = MachineFault ->
         srealizes c t_nil
     | srz_conseq : forall c T T',
         srealizes c T -> t_eq T T' -> srealizes c T'

   and that is how every consumer applies them.  In Lean a constructor
   lives in its inductive's namespace, so such a call site would fail on
   the NAME and not on the mathematics.

   The three theorems below are those constructors RESTATED AT THE FLAT
   NAME, [segs] explicit exactly as the section makes it: the
   statements are the constructors' verbatim and the proofs are the
   constructors themselves.    This file's own proofs keep using the dotted [.srz_*] form.
   ([srz_halt] is left as the constructor only, matching
   `Common/SpinAlg.lean`.) -/

/-- `srz_node`: every resolution [i] of the node emits [evs i] and
    continues as [nx i], realizing [T i]. -/
theorem srz_node (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) (T : I → TSet) (i0 : I)
    (hnode : node_ok segs c I evs nx)
    (hcont : ∀ i, srealizes segs (nx i) (T i)) :
    srealizes segs c (t_alt (fun i => t_emit (evs i) (T i))) :=
  .srz_node c I evs nx T i0 hnode hcont

/-- `srz_fault`: a non-halted, non-syscall, faulting configuration
    emits nothing, so it realizes [t_nil]. -/
theorem srz_fault (segs : List Segment) (c : config)
    (hh : m_halted c.cfg_model = none)
    (hsvc : c.cfg_ms.ms_svc_pending = none)
    (hlazy : m_vm_lazy c.cfg_model = [])
    (hf : RiscvSemantics.step segs c.cfg_ms = .MachineFault) :
    srealizes segs c t_nil :=
  .srz_fault c hh hsvc hlazy hf

/-- `srz_conseq`: consequence under trace-set equality. -/
theorem srz_conseq (segs : List Segment) (c : config) (T T' : TSet)
    (h : srealizes segs c T) (heq : t_eq T T') : srealizes segs c T' :=
  .srz_conseq c T T' h heq

end LinuxSem.Common.SrcShape
