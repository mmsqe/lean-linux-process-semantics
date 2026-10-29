/-
  * Common.SpinAlg — the shape algebra with a SPIN leaf, and the
    spin-armed mmap node

  TRUST BOUNDARY: image-INDEPENDENT proof library, like [ShapeAlg]
  (which this file extends) and [DivergeSim] (which supplies the spin
  machinery).  Nothing here is part of the trusted specification.

  ** The problem

  [ShapeAlg.realizes] is an INDUCTIVE relation whose only leaf is
  [rz_halt]: every derivation witnesses a run that reaches a halted
  configuration in finitely many nodes.  A binary whose mmap-refusal
  arm answers with a tight syscall-free infinite loop (the sealed
  ASan runtime's allocation-failure behavior — see [DivergeSim]) has
  NO such derivation for the refusal branch, so [rz_mmap] — which
  demands a [realizes] continuation for BOTH resolutions — cannot be
  applied; without this file, the [DivergeSim] lemmas must be composed
  against raw [star] derivations by hand ([spin_branch_toy_*]).

  ** The design

  A sibling relation, [srealizes], with the same three constructors
  as [realizes] plus ONE new leaf:

    [srz_spin] — the configuration spins ([DivergeSim.to_spin], an
                 un-halted model): nothing more is ever emitted, so
                 the configuration realizes [t_nil].

  [realizes] embeds ([srealizes_of_realizes]), so every existing
  combinator and bridge ([rz_write1], [twm_realizes], [rz_drain],
  a [sym_block] chain, ...) is usable for any spin-free subtree; the
  [srz_*] mirrors below are needed only ABOVE a spin leaf.  The
  master theorems ([srealizes_obs_iff], [srealizes_no_error],
  [spin_shape_strong_equiv]) are re-proved by the same inductions
  with one extra leaf case each, discharged by [DivergeSim]'s
  [spin_star_nil] / [spin_no_sstep_error] / [spinning_silent_loop].

  A NEW RELATION RATHER THAN A NEW CONSTRUCTOR on purpose: adding a
  constructor to [ShapeAlg.realizes] would change its induction
  scheme and re-open every proof in the 58 files that consume the
  algebra; the mirror is additive and the embedding is total, so
  nothing existing moves.
 The last section of this file
  restates those three AT THE FLAT NAME with [segs] explicit, so a call site
  reads the same in both spellings.
  ** The spin-armed mmap node
  [srz_mmap_spin] is the sibling of [ShapeAlg.rz_mmap] this file
  exists for.  Same node interface (same [node_ok], extracted here as
  [node_mmap]), but the refusal resolutions discharge by
  [DivergeSim.to_spin] instead of a [realizes] continuation, and the
  conclusion is the GRANT shape [B] alone: the spinning refusal arm
  contributes only [[]], which [B] already contains (every realized
  shape is nonempty), so the refusal arm is invisible in the shape.
  Two binaries of which only one spins on refusal can therefore still
  realize the SAME [TSet], which is exactly what
  [spin_shape_strong_equiv] compares.
  ** Wiring (the [SymTac]/[DrainAlg] house pattern)
  [chain_mst_sp] extends [SymTac.chain_mst] with the [srz_msteps]
  alternative (same pre-discharged model side conditions, same two
  remaining goals), pinned by [chain_mst_srealizes] /
  [chain_mst_srealizes_mmap] exactly as [SymTac] pins its own.
  [srz_spin_alloc_writes] is the [rz_alloc_writes]/[rz_mmap_drain]
  -style bundling corollary: silent prologue, spin-armed mmap,
  [MmapSim.twm] grant tail.
  ** What this file deliberately does NOT do
  - It does not model the NORESERVE-flagged mmap itself:
    [mmap_args_ok] (hence [node_mmap], hence both mmap nodes here)
    pins flags = MAP_PRIVATE|MAP_ANONYMOUS, whose grant leaves the
    lazy ledger empty.  A noreserve node (flags carrying 0x4000,
    grant successor [vm_add_lazy]-wrapped) is the next missing piece
    for a full ASan skeleton, and every node's [m_vm_lazy model = []]
    premise after such a grant must be replaced by the
    [Common.LazyFrame] disjointness discipline.
  - The single-instruction [srz_step_disjoint] is provided (through
    [LazyFrame]); a CHAINED disjoint straight line (an [msteps]
    analog carrying per-step access reports) is left for the same
    follow-up.
  **

  `Common/{CatSim,ExitSim,MmapSim,DivergeSim,SimInv,LazyFrame,ShapeAlg}.lean`
  are stated and imported; every fact this file needs from them is the
  real thing.  This file used to carry a `SCAFFOLD` section with a
  verbatim copy of the LAYER-1/2 algebra ([TSet], [t_*], [node_ok],
  [realizes]) and of the shape combinators it consumes ([node_instr],
  [sstep_instr_inv], [rz_silent1], [rz_emit1], [rz_alt2], [rz_step],
  [rz_exit], [node_write1]); `Common/ShapeAlg.lean` now exists with the
  same spellings (`.rz_node`, `node_ok segs …`, `.rz_conseq`), so the
  scaffold is gone and this file does `import`/`open`
  `LinuxSem.Common.ShapeAlg`.  Nothing of the algebra is
  restated here; only the [srealizes] mirror, the mmap/munmap nodes and
  the [MmapSim.twm] tail bundling are this file's own.
  All 35  declarations are present; none is deferred.
  DEVIATION (one, spelling only). -/

import LinuxSem.Common.CatSim
import LinuxSem.Common.ExitSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.DivergeSim
import LinuxSem.Common.SimInv
import LinuxSem.Common.LazyFrame
import LinuxSem.Common.ShapeAlg
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Common.SharedFacts

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Common.CatSim
open LinuxSem.Common.ExitSim
open LinuxSem.Common.MmapSim
open LinuxSem.Common.DivergeSim
open LinuxSem.Common.SimInv
open LinuxSem.Common.LazyFrame
open LinuxSem.Common.ShapeAlg
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence

/-- The FP state at process entry, so that the [MmapSim] lemmas (whose
    proofs go through [PropExec.mkst]) elaborate.  Same local instance
    `AsanAcct.lean` declares. -/
local instance spin_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

namespace LinuxSem.Common.SpinAlg
open LinuxSem.Common.SharedFacts (is_prefix_app_mono is_prefix_app_r)

/- =========================================================================
   The relation: [ShapeAlg.realizes] plus the spin leaf
   ========================================================================= -/

/-- A sibling relation to [ShapeAlg.realizes], with the same three
    constructors plus ONE new leaf: [srz_spin]. -/
inductive srealizes (segs : List Segment) : config → TSet → Prop where
  | srz_node (c : config) (I : Type) (evs : I → List event) (nx : I → config)
      (T : I → TSet) (i0 : I)
      (hnode : node_ok segs c I evs nx)
      (hcont : ∀ i, srealizes segs (nx i) (T i)) :
      srealizes segs c (t_alt (fun i => t_emit (evs i) (T i)))
  | srz_halt (c : config) (hh : m_halted c.cfg_model ≠ none) :
      srealizes segs c t_nil
  | srz_spin (c : config) (hspin : to_spin segs c.cfg_ms c.cfg_model)
      (hh : m_halted c.cfg_model = none) :
      srealizes segs c t_nil
  | srz_conseq (c : config) (T T' : TSet)
      (h : srealizes segs c T) (heq : t_eq T T') :
      srealizes segs c T'

/-- Every [realizes] derivation is an [srealizes] derivation: the
    existing combinators and bridges plug into any spin-free subtree. -/
theorem srealizes_of_realizes (segs : List Segment) (c : config) (T : TSet)
    (h : realizes segs c T) : srealizes segs c T := by
  induction h with
  | rz_node c I evs nx T i0 hnode hcont ih => exact .srz_node c I evs nx T i0 hnode ih
  | rz_halt c hh => exact .srz_halt c hh
  | rz_conseq c T T' h heq ih => exact .srz_conseq c T T' ih heq

/-- The [DivergeSim.spinning] spelling of the spin leaf. -/
theorem srz_spinning (segs : List Segment) (c : config) (h : spinning segs c) :
    srealizes segs c t_nil :=
  .srz_spin c h.1 h.2

/- -------------------------------------------------------------------------
   Structural facts (mirroring [ShapeAlg], one extra leaf case each)
   ------------------------------------------------------------------------- -/

theorem srealizes_nonempty (segs : List Segment) (c : config) (T : TSet)
    (h : srealizes segs c T) : T [] := by
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih => exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
  | srz_halt c hh => rfl
  | srz_spin c hspin hh => rfl
  | srz_conseq c T T' h heq ih => exact (heq []).1 ih

theorem srealizes_pclosed (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ (tr tr' : List event), T tr → is_prefix tr' tr → T tr' := by
  intro h
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr tr' hT hp
    rcases hT with ⟨i, hpre | ⟨tr0, htr, hT0⟩⟩
    · exact ⟨i, Or.inl (is_prefix_trans hp hpre)⟩
    · subst htr
      rcases is_prefix_app_split (evs i) tr0 tr' hp with hp' | ⟨tr0', htr', hp'⟩
      · exact ⟨i, Or.inl hp'⟩
      · subst htr'
        exact ⟨i, Or.inr ⟨tr0', rfl, ih i tr0 tr0' hT0 hp'⟩⟩
  | srz_halt c hh =>
    intro tr tr' hT hp
    simp only [t_nil] at hT
    subst hT
    exact is_prefix_nil_r tr' hp
  | srz_spin c hspin hh =>
    intro tr tr' hT hp
    simp only [t_nil] at hT
    subst hT
    exact is_prefix_nil_r tr' hp
  | srz_conseq c T T' h heq ih =>
    intro tr tr' hT hp
    exact (heq tr').1 (ih tr tr' ((heq tr).2 hT) hp)

/- -------------------------------------------------------------------------
   Soundness: every reachable trace is in the shape
   ------------------------------------------------------------------------- -/

theorem srealizes_star_only (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ (tr : List event) (c' : config), star segs c tr c' → T tr := by
  intro h
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr c' hstar
    rcases star_case segs c tr c' hstar with ⟨rfl, rfl⟩ | ⟨e, c2, tr2, hs, htail, htr⟩
    · exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
    · obtain ⟨i, he, hst⟩ := hnode.2 e (.SNext c2) hs
      subst he
      have hc2 : c2 = nx i := by injection hst
      subst hc2
      subst htr
      exact ⟨i, Or.inr ⟨tr2, rfl, ih i tr2 _ htail⟩⟩
  | srz_halt c hh =>
    intro tr c' hstar
    obtain ⟨rfl, -⟩ := star_halted_nil segs c tr c' hh hstar
    rfl
  | srz_spin c hspin hh =>
    intro tr c' hstar
    exact spin_star_nil segs c.cfg_ms c.cfg_model tr c' hspin hh hstar
  | srz_conseq c T T' h heq ih =>
    intro tr c' hstar
    exact (heq tr).1 (ih tr c' hstar)

/- -------------------------------------------------------------------------
   Completeness: every trace in the shape is admitted
   ------------------------------------------------------------------------- -/

theorem srealizes_admits (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ tr, T tr → obs_trace segs c tr := by
  intro h
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro tr hT
    rcases hT with ⟨i, hpre | ⟨tr0, htr, hT0⟩⟩
    · exact ⟨evs i, nx i, star_one segs c (evs i) (nx i) (hnode.1 i), hpre⟩
    · subst htr
      obtain ⟨tr'', c'', hstar, hp⟩ := ih i tr0 hT0
      exact ⟨evs i ++ tr'', c'', star.step c (evs i) (nx i) tr'' c'' (hnode.1 i) hstar,
        is_prefix_app_mono (evs i) tr0 tr'' hp⟩
  | srz_halt c hh =>
    intro tr hT
    simp only [t_nil] at hT
    subst hT
    exact obs_trace_nil segs c
  | srz_spin c hspin hh =>
    intro tr hT
    simp only [t_nil] at hT
    subst hT
    exact obs_trace_nil segs c
  | srz_conseq c T T' h heq ih =>
    intro tr hT
    exact ih tr ((heq tr).2 hT)

/-- The master observation theorem, spin leaves included. -/
theorem srealizes_obs_iff (segs : List Segment) (c : config) (T : TSet)
    (h : srealizes segs c T) (tr : List event) :
    obs_trace segs c tr ↔ T tr := by
  constructor
  · rintro ⟨tr', c', hstar, hp⟩
    exact srealizes_pclosed segs c T h tr' tr (srealizes_star_only segs c T h tr' c' hstar) hp
  · exact srealizes_admits segs c T h tr

/- -------------------------------------------------------------------------
   No error
   ------------------------------------------------------------------------- -/

theorem srealizes_step (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ (e : List event) (c' : config),
      sstep segs c e (.SNext c') → ∃ T', srealizes segs c' T' := by
  intro h
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro e c' hss
    obtain ⟨i, -, hst⟩ := hnode.2 e (.SNext c') hss
    have hc' : c' = nx i := by injection hst
    subst hc'
    exact ⟨T i, hcont i⟩
  | srz_halt c hh =>
    intro e c' hss
    exact absurd (sstep_halted_none segs c e (.SNext c') hss) hh
  | srz_spin c hspin hh =>
    intro e c' hss
    obtain ⟨-, c'', heq, hsp⟩ := silent_loop_sstep segs (spinning segs) c e (.SNext c')
      (spinning_silent_loop segs) ⟨hspin, hh⟩ hss
    injection heq with hc''
    subst hc''
    exact ⟨t_nil, srz_spinning segs _ hsp⟩
  | srz_conseq c T T' h heq ih =>
    intro e c' hss
    exact ih e c' hss

theorem srealizes_no_sserror (segs : List Segment) (c : config) (T : TSet) :
    srealizes segs c T → ∀ e, ¬ sstep segs c e .SError := by
  intro h
  induction h with
  | srz_node c I evs nx T i0 hnode hcont ih =>
    intro e hss
    obtain ⟨i, -, hbad⟩ := hnode.2 e .SError hss
    exact nomatch hbad
  | srz_halt c hh =>
    intro e hss
    exact hh (sstep_halted_none segs c e .SError hss)
  | srz_spin c hspin hh =>
    intro e hss
    exact spin_no_sstep_error segs c.cfg_ms c.cfg_model hspin hh e hss
  | srz_conseq c T T' h heq ih =>
    intro e hss
    exact ih e hss

/-- "Configuration [c] realizes some shape". -/
def srz_path (segs : List Segment) (c : config) : Prop := ∃ T, srealizes segs c T

theorem srealizes_no_error (segs : List Segment) (c : config) (T : TSet)
    (h : srealizes segs c T) : ¬ reaches_error segs c := by
  refine inv_no_reaches_error segs (srz_path segs) ?_ ?_ c ⟨T, h⟩
  · rintro c1 e c2 ⟨T1, h1⟩ hss
    exact srealizes_step segs c1 T1 h1 e c2 hss
  · rintro c1 e ⟨T1, h1⟩ hss
    exact srealizes_no_sserror segs c1 T1 h1 e hss

/- =========================================================================
   Combinator mirrors (needed only ABOVE a spin leaf; spin-free subtrees
   lift through [srealizes_of_realizes])
   ========================================================================= -/

/-- A silent [Unit]-indexed node collapses to its continuation. -/
theorem srz_silent1 (segs : List Segment) (c c' : config) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => []) (fun _ => c'))
    (Hc : srealizes segs c' T) : srealizes segs c T := by
  refine .srz_conseq c (t_alt (fun _ : Unit => t_emit [] T)) T ?_ ?_
  · exact .srz_node c Unit (fun _ => []) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_eq_trans (t_alt_unit (fun _ => t_emit [] T))
      (t_emit_nil_eq T (srealizes_nonempty segs c' T Hc))

/-- A [Unit]-indexed node emitting a block. -/
theorem srz_emit1 (segs : List Segment) (c c' : config) (e : List event) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => e) (fun _ => c'))
    (Hc : srealizes segs c' T) : srealizes segs c (t_emit e T) := by
  refine .srz_conseq c (t_alt (fun _ : Unit => t_emit e T)) (t_emit e T) ?_ ?_
  · exact .srz_node c Unit (fun _ => e) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_alt_unit (fun _ : Unit => t_emit e T)

/-- A silent two-way nondeterministic node (the mmap/brk pattern). -/
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

/-- Instruction steps. -/
theorem srz_step (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hc : srealizes segs (mkCfg ms' model) T) : srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep) Hc

/-- A run of straight-line instruction steps, lifted. -/
theorem srz_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hms : msteps segs ms ms') (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T := by
  revert Hc
  induction Hms with
  | mst_refl ms => intro Hc; exact Hc
  | mst_step ms ms1 ms2 hsvc hstep hrest ih =>
    intro Hc
    exact srz_step segs ms model ms1 T Hh Hlazy hsvc hstep (ih Hc)

/-- The [write(1, ...)] node. -/
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
  exact .srz_node (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T) (wr_full buf Hnb)
    (node_write1 segs ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

/-- The [exit] leaf, lifted (an exit subtree is spin-free). -/
theorem srz_exit (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hx8 : is_exit_no x8) :
    srealizes segs (mkCfg ms model)
      (t_exit (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)) :=
  srealizes_of_realizes segs _ _ (rz_exit segs ms model x8 Hh Hsvc Hx8)

/-- The disjoint instruction node: a load/store whose access report
    avoids every lazy range is a silent node WHATEVER the ledger holds
    ([LazyFrame]).  This is the node the ASan grant path uses once
    [m_vm_lazy] is non-empty and [node_instr] is unavailable. -/
theorem node_instr_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat))
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model)) :
    node_ok segs (mkCfg ms model) Unit (fun _ => []) (fun _ => mkCfg ms' model) := by
  have Hacc := mi_account_step_disjoint segs ms model ms' ranges Hstep Hout
  constructor
  · intro i
    cases i
    exact sstep.instr ms model ms' model Hh Hsvc Hacc
  · intro e st Hss
    cases Hss with
    | instr =>
      rename_i ms2 model2 hsvc2 hh2 hacc
      rw [Hacc] at hacc
      obtain ⟨rfl, rfl⟩ := machine_result.MachineOk.inj hacc
      exact ⟨(), rfl, rfl⟩
    | instr_fault => simp_all
    | instr_unmodeled => simp_all
    | syscall => simp_all
    | syscall_materialization_fault => simp_all
    | exit => simp_all
    | killed => simp_all
    | syscall_unmodeled => simp_all

theorem rz_step_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model))
    (Hc : realizes segs (mkCfg ms' model) T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T
    (node_instr_disjoint segs ms model ms' ranges Hh Hsvc Hstep Hout) Hc

theorem srz_step_disjoint (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (ranges : List (word × Nat)) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model))
    (Hc : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T
    (node_instr_disjoint segs ms model ms' ranges Hh Hsvc Hstep Hout) Hc

/- =========================================================================
   The munmap node
   ========================================================================= -/

/-- The [munmap] node's interface, extracted from [ShapeAlg.rz_munmap]
    (which keeps it inline). -/
theorem node_munmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 215)
    (Hargs : munmap_args_ok ms model) :
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
      (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))
  · intro e st Hss
    obtain ⟨he, hst⟩ :=
      sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
    exact ⟨(), he, hst⟩

theorem srz_munmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 215)
    (Hargs : munmap_args_ok ms model)
    (Hc : srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T (node_munmap segs ms model x8 Hh Hlazy Hsvc Hno Hargs) Hc

/- =========================================================================
   The mmap nodes
   ========================================================================= -/

/-- The index type of an mmap node's resolutions: an errno refusal, or a
    grantable address. -/
abbrev MmapIdx (ms : machine_state) (model : Model) : Type :=
  { e : Int // e ∈ mmap_errnos } ⊕
  { a : word // grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }

/-- The successor configuration of an mmap resolution. -/
def mmap_next (ms : machine_state) (model : Model) : MmapIdx ms model → config
  | .inl e => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e.1))) model
  | .inr a => mkCfg (advance_past_svc
      (apply_effect ms (mkEffect a.1 [] [(a.1, page_round_up (ms_gpr ms 1))])))
      (mmap_model a.1 (page_round_up (ms_gpr ms 1)) model)

/-- The [mmap] node's interface, extracted from [ShapeAlg.rz_mmap]
    (which keeps it inline): the admissible transitions out of the
    modeled-shape mmap ecall are EXACTLY the errno resolutions plus the
    grantable-address resolutions, all silent. -/
theorem node_mmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms) :
    node_ok segs (mkCfg ms model) (MmapIdx ms model) (fun _ => []) (mmap_next ms model) := by
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

/-- The plain two-branch node, mirrored (for an mmap whose BOTH
    resolutions continue, sitting above a spin leaf elsewhere). -/
theorem srz_mmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (A B : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (HA : ∀ e, e ∈ mmap_errnos →
      srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
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
    (node_mmap segs ms model x8 Hh Hlazy Hsvc Hno Hargs) ?_ ?_
  · rintro ⟨e, He⟩
    exact HA e He
  · rintro ⟨a, Ha⟩
    exact HB a Ha

/-- THE SPIN-ARMED MMAP NODE.  Grant resolutions continue as [B]
    exactly as in [rz_mmap]/[srz_mmap]; every refusal resolution SPINS
    ([DivergeSim.to_spin] at the post-refusal machine state, model
    unchanged).  The refusal arm contributes only the empty trace —
    which [B] contains anyway — and can never error, so the whole node
    realizes [B]: the spinning arm is invisible in the shape. -/
theorem srz_mmap_spin (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (B : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      srealizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    srealizes segs (mkCfg ms model) B := by
  obtain ⟨a0, Ha0⟩ := Hex
  have HB0 : B [] :=
    srealizes_nonempty segs _ B (HB a0 Ha0)
  have Hnode : node_ok segs (mkCfg ms model) (MmapIdx ms model) (fun _ => [])
      (mmap_next ms model) :=
    node_mmap segs ms model x8 Hh Hlazy Hsvc Hno Hargs
  refine .srz_conseq (mkCfg ms model)
    (t_alt (fun i : MmapIdx ms model =>
      t_emit [] (match i with | .inl _ => t_nil | .inr _ => B))) B ?_ ?_
  · refine .srz_node (mkCfg ms model) (MmapIdx ms model) (fun _ => []) (mmap_next ms model)
      (fun i => match i with | .inl _ => t_nil | .inr _ => B) (.inr ⟨a0, Ha0⟩)
      Hnode ?_
    rintro (⟨e, He⟩ | ⟨a, Ha⟩)
    · exact .srz_spin _ (Hrefuse e He) Hh
    · exact HB a Ha
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl e => exact (t_emit_nil_eq t_nil rfl tr).1 Hi ▸ HB0
      | inr a => exact (t_emit_nil_eq B HB0 tr).1 Hi
    · intro HBtr
      exact ⟨.inr ⟨a0, Ha0⟩, (t_emit_nil_eq B HB0 tr).2 HBtr⟩

/- =========================================================================
   The master equivalence theorem, spin leaves included
   ========================================================================= -/

/-- [ShapeAlg.shape_strong_equiv], verbatim, over [srealizes]: a source
    and a target realizing the SAME shape — either or both through
    spinning refusal arms — are equivalent, and the source is covered
    by the model.  ([srealizes_no_error] covers the source conjunct: a
    spinning branch is an infinite MODELED execution, not an error.) -/
theorem spin_shape_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : srealizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : srealizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (srealizes_no_error source_segs _ T Hsource)
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
        (srealizes_obs_iff target_segs _ T Htarget tr).symm
    · exact srealizes_no_error target_segs _ T Htarget

/- =========================================================================
   The three formers at their  (FLAT) names
   =========================================================================

    declares these three INSIDE [Inductive srealizes] but in a
   [Section WithSegs], so they are flat names with [segs] as an
   explicit first argument:

     | srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                         (T : I -> TSet) (i0 : I),
         node_ok segs c I evs nx ->
         (forall i, srealizes (nx i) (T i)) ->
         srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
     | srz_spin : forall c,
         to_spin segs (cfg_ms c) (cfg_model c) ->
         m_halted (cfg_model c) = None ->
         srealizes c t_nil
     | srz_conseq : forall c T T',
         srealizes c T -> t_eq T T' -> srealizes c T'

   and that is how every consumer applies them ([NoReserve]:
   `apply (srz_node segs (mkCfg ms model) ...)`, `apply srz_spin`,
   `eapply srz_conseq`; likewise `SrcShape`, `AsanPlanSound`,
   `ShapeEFS`).  In Lean a constructor lives in its inductive's
   namespace, so those call sites would fail on the NAME and not on the
   mathematics.

   The three theorems below are those constructors RESTATED AT THE FLAT
   NAME, [segs] explicit exactly as the section makes it: the
   statements are the constructors' verbatim and the proofs are the
   constructors themselves.  This file's own proofs keep using the dotted [.srz_*] form.
    -/

/-- `srz_node`: every resolution [i] of the node emits [evs i]
    and continues as [nx i], realizing [T i]. -/
theorem srz_node (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) (T : I → TSet) (i0 : I)
    (hnode : node_ok segs c I evs nx)
    (hcont : ∀ i, srealizes segs (nx i) (T i)) :
    srealizes segs c (t_alt (fun i => t_emit (evs i) (T i))) :=
  .srz_node c I evs nx T i0 hnode hcont

/-- `srz_spin`: a spinning (un-halted) configuration emits
    nothing more, so it realizes [t_nil]. -/
theorem srz_spin (segs : List Segment) (c : config)
    (hspin : to_spin segs c.cfg_ms c.cfg_model)
    (hh : m_halted c.cfg_model = none) :
    srealizes segs c t_nil :=
  .srz_spin c hspin hh

/-- `srz_conseq`: consequence under trace-set equality. -/
theorem srz_conseq (segs : List Segment) (c : config) (T T' : TSet)
    (h : srealizes segs c T) (heq : t_eq T T') :
    srealizes segs c T' :=
  .srz_conseq c T T' h heq

/- =========================================================================
   SymTac wiring: [chain_mst] with the [srealizes] alternative
   ========================================================================= -/

/-- [SymTac.chain_mst], extended with the [srz_msteps] alternative (its
    model side conditions pre-discharged the same way, leaving the same
    two goals in the same order, so `chain_mst_sp; [exact Hms | exact Hr]`
    works verbatim inside an [srealizes] derivation).
| chain_mst ]`, with
    the fallback in `Common/SymTac.lean` (that module has since been
    stated, and its `chain_mst` macro is available). -/
macro "chain_mst_sp" : tactic =>
  `(tactic| (apply srz_msteps <;> try assumption))

/-- Regression pin, mirroring [SymTac.chain_mst_realizes]. -/
theorem chain_mst_srealizes (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hms : msteps segs ms ms') (Hr : srealizes segs (mkCfg ms' model) T) :
    srealizes segs (mkCfg ms model) T := by
  chain_mst_sp

/-- Regression pin with the grant model threaded through. -/
theorem chain_mst_srealizes_mmap (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (a n : word) (T : TSet)
    (Hh : m_halted (mmap_model a n model) = none)
    (Hlazy : m_vm_lazy (mmap_model a n model) = [])
    (Hms : msteps segs ms ms')
    (Hr : srealizes segs (mkCfg ms' (mmap_model a n model)) T) :
    srealizes segs (mkCfg ms (mmap_model a n model)) T := by
  chain_mst_sp

/- =========================================================================
   The bundling corollary ([rz_alloc_writes]/[rz_mmap_drain] house style)
   ========================================================================= -/

/-- Silent prologue, then the spin-armed mmap: refusal spins, grant runs a
    [MmapSim.twm] (retry-loop writes / munmap / exit) tail.  The shape is
    the grant tail's shape ALONE. -/
theorem srz_spin_alloc_writes (segs : List Segment) (ms0 ms : machine_state) (model : Model)
    (x8 : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (Hgrant : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      MmapSim.twm segs
        (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbs : bufs_modeled bs) :
    srealizes segs (mkCfg ms0 model) (t_writes bs (t_exit cs (m_fs model))) := by
  refine srz_msteps segs ms0 ms model _ Hh Hlazy Hms ?_
  refine srz_mmap_spin segs ms model x8 _ Hh Hlazy Hsvc Hno Hargs Hrefuse ?_ Hex
  intro a Ha
  refine srealizes_of_realizes segs _ _ ?_
  rw [← mmap_model_fs]
  exact twm_realizes segs _ (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs
    (by rw [mmap_model_halted]; exact Hh)
    (by rw [mmap_model_lazy]; exact Hlazy)
    (mmap_model_fd1chan _ _ _ Hfd) (Hgrant a Ha) Hbs

/- =========================================================================
   Worked example: [DivergeSim]'s [spin_branch_toy_*], redone through the
   node in the real [MmapSim] idiom
   ========================================================================= -/

/- The configuration is a genuine modeled-shape mmap ecall.  The grant
    resolutions run a real [MmapSim.twm] tail (retry-loop writes, a
    munmap, an exit); the refusal resolutions spin.  Where
    [DivergeSim.spin_branch_toy_obs_iff] needed ~25 lines of by-hand
    [star]/[sstep] case surgery against abstract split hypotheses, here
    each conclusion is the node application plus its leaf obligations.
 The hypotheses'  prose:
    * [Hrefuse] — the refusal arm: whatever errno the environment
      answers, the binary spins (established per-binary by
      [prove_to_spin] or the [ts_*] constructors, including
      [LazyFrame.ts_step_disjoint]).
    * [Hgrant] — the grant arm: the binary's write/munmap/exit tail. -/

/-- The derivation: one node application, one lift of the grant tail. -/
theorem spin_branch_node_srealizes (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (Hgrant : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      MmapSim.twm segs
        (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbs : bufs_modeled bs) :
    srealizes segs (mkCfg ms model) (t_writes bs (t_exit cs (m_fs model))) := by
  refine srz_mmap_spin segs ms model x8 _ Hh Hlazy Hsvc Hno Hargs Hrefuse ?_ Hex
  intro a Ha
  refine srealizes_of_realizes segs _ _ ?_
  rw [← mmap_model_fs]
  exact twm_realizes segs _ (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs
    (by rw [mmap_model_halted]; exact Hh)
    (by rw [mmap_model_lazy]; exact Hlazy)
    (mmap_model_fd1chan _ _ _ Hfd) (Hgrant a Ha) Hbs

/-- [DivergeSim.spin_branch_toy_obs_iff], in the real idiom: the refusal
    branch changes nothing — the observation set is exactly the grant
    tail's prefixes. -/
theorem spin_branch_node_obs_iff (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (Hgrant : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      MmapSim.twm segs
        (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbs : bufs_modeled bs) (tr : List event) :
    obs_trace segs (mkCfg ms model) tr
      ↔ is_prefix tr (wevents bs ++ [event.ExitEv cs (m_fs model)]) := by
  rw [srealizes_obs_iff segs (mkCfg ms model)
    (t_writes bs (t_exit cs (m_fs model)))
    (spin_branch_node_srealizes segs ms model x8 bs cs Hh Hlazy Hfd Hsvc Hno Hargs
      Hrefuse Hgrant Hex Hbs) tr]
  exact t_writes_exit_iff bs cs (m_fs model) tr

/-- [DivergeSim.spin_branch_toy_no_error], in the real idiom. -/
theorem spin_branch_node_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222) (Hargs : mmap_args_ok ms)
    (Hrefuse : ∀ e, e ∈ mmap_errnos →
      to_spin segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model)
    (Hgrant : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      MmapSim.twm segs
        (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
      (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbs : bufs_modeled bs) :
    ¬ reaches_error segs (mkCfg ms model) :=
  srealizes_no_error segs _ _
    (spin_branch_node_srealizes segs ms model x8 bs cs Hh Hlazy Hfd Hsvc Hno Hargs
      Hrefuse Hgrant Hex Hbs)

end LinuxSem.Common.SpinAlg
