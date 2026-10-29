/-
  * Common.AsanAcctShape — [Acct.AsanAcct] instantiated for
    [ShapeAlg.realizes].

    Exported:
     - [node_ok_same]           : AsanAcct.node_ok segs = ShapeAlg.node_ok segs
                                  (convertible; proof is [reflexivity]).
     - [rz_step_restricted_T]   : one restricted step under [realizes].
     - [rz_msteps_restricted_T] : a restricted [msteps] chain under
                                  [realizes].

  NOTES (spelling only; nothing is weakened or dropped).

  - SECTION VARIABLES.  The whole file is parameterized by `segs`, `H`,
    `HH` and `Hwx`.  Lean's [variable] command only generalizes over the
    variables a STATEMENT mentions — and [Hwx] / part of [HH] are needed by
    the PROOFS, not by the statements — so all four are written out as
    explicit parameters, in that order, exactly as `Common/SpinAlg.lean`
    does for its own sections.
  - The accounting ranges [A] are `List (Int × Int)`, as in
    `AsanAcct.lean`.
  - The shape predicates `P_of` / `P_of_silent1` (resp. [SP_of] /
    [SP_of_silent1] for the spin side) are `private`, so they stay out of
    the module interface.
  - The [mkCfg] of [ShapeAlg]/[AsanAcct] is the same function in both
    modules (both are the anonymous [config] constructor), but both
    namespaces are open here, so it is spelled `AsanAcct.mkCfg` — the
    namespace whose chain lemmas build those configurations.  The two
    candidates are definitionally equal, for the same reason [node_ok_same]
    is [rfl].
  - [rz_step_restricted] / [rz_msteps_restricted'] are the GENERIC chain
    lemmas of `AsanAcct.lean`, parameterized by the shape predicate [P];
    this file is the instantiation `P := realizes segs · T`
    (`P_silent1 := rz_silent1 segs _ _ T`) and its [srealizes] mirror
    (`P := srealizes segs · T`, `P_silent1 := srz_silent1 segs _ _ T`),
    which is what makes the shape algebra's nodes usable inside a
    restricted-accounting chain.
-/

import LinuxSem.Common.CatSim
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.AsanAcct
import LinuxSem.Common.SpinAlg
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Common.CatSim
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.SpinAlg
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Common.AsanAcctShape

/- =========================================================================
   The node interface is the same in both modules
   ========================================================================= -/

/-- [AsanAcct.node_ok] is [ShapeAlg.node_ok] (the two definitions are
    verbatim copies, so the proof is [reflexivity]); this is what lets a
    [node_ok] produced by the restricted-accounting chain feed
    [rz_silent1] / [srz_silent1]. -/
theorem node_ok_same (segs : List Segment) :
    AsanAcct.node_ok segs = ShapeAlg.node_ok segs := rfl

/- =========================================================================
   [realizes]: the restricted-accounting chain, shape-instantiated
   ========================================================================= -/

/-- The shape predicate the chain lemma is instantiated at. -/
private def P_of (segs : List Segment) (T : TSet) : config → Prop :=
  fun c => realizes segs c T

/-- `P_of` is closed under silent [Unit]-indexed nodes, by
    [ShapeAlg.rz_silent1]. -/
private theorem P_of_silent1 (segs : List Segment) (T : TSet) :
    ∀ c c', AsanAcct.node_ok segs c Unit (fun _ => []) (fun _ => c') →
      P_of segs T c' → P_of segs T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr

/-- One restricted instruction step discharges [realizes] at the full
    configuration.  [Hk] is the continuation, stated at every admissible
    successor (full memory put back; model changed only in its materialized
    ledger, still [MInv]). -/
theorem rz_step_restricted_T (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms msr' : machine_state) (model : Model)
    (T : TSet)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A)
    (Hinv : MInv A model) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = none)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        realizes segs (AsanAcct.mkCfg (unrestrict H ms.ms_mem msr') model') T) :
    realizes segs (AsanAcct.mkCfg ms model) T :=
  rz_step_restricted segs H HH Hwx (P_of segs T) (P_of_silent1 segs T)
    A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk

/-- A restricted [msteps] chain discharges [realizes] at the full
    configuration; the continuation also learns that the chain's final
    restricted state is H-clean. -/
theorem rz_msteps_restricted_T (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms msr' : machine_state) (model : Model)
    (T : TSet)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A)
    (Hinv : MInv A model) (Hh : m_halted model = none)
    (Hms : msteps segs (restrict H ms) msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        hclean H msr' →
        realizes segs (AsanAcct.mkCfg (unrestrict H ms.ms_mem msr') model') T) :
    realizes segs (AsanAcct.mkCfg ms model) T :=
  rz_msteps_restricted' segs H HH Hwx (P_of segs T) (P_of_silent1 segs T)
    A ms msr' model Hcov Hwf Hinv Hh Hms Hk

/- =========================================================================
   The same two chain lemmas for [SpinAlg.srealizes]
   (shapes with spin leaves; the spec's refused-then-spinning arms).
   ========================================================================= -/

/-- The spin-side shape predicate. -/
private def SP_of (segs : List Segment) (T : TSet) : config → Prop :=
  fun c => srealizes segs c T

/-- `SP_of` is closed under silent [Unit]-indexed nodes, by
    [SpinAlg.srz_silent1]. -/
private theorem SP_of_silent1 (segs : List Segment) (T : TSet) :
    ∀ c c', AsanAcct.node_ok segs c Unit (fun _ => []) (fun _ => c') →
      SP_of segs T c' → SP_of segs T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr

/-- One restricted instruction step discharges [srealizes] (spin leaves
    allowed above the node) at the full configuration. -/
theorem srz_step_restricted_T (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms msr' : machine_state) (model : Model)
    (T : TSet)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A)
    (Hinv : MInv A model) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = none)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        srealizes segs (AsanAcct.mkCfg (unrestrict H ms.ms_mem msr') model') T) :
    srealizes segs (AsanAcct.mkCfg ms model) T :=
  rz_step_restricted segs H HH Hwx (SP_of segs T) (SP_of_silent1 segs T)
    A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk

/-- A restricted [msteps] chain discharges [srealizes] at the full
    configuration. -/
theorem srz_msteps_restricted_T (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms msr' : machine_state) (model : Model)
    (T : TSet)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A)
    (Hinv : MInv A model) (Hh : m_halted model = none)
    (Hms : msteps segs (restrict H ms) msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        hclean H msr' →
        srealizes segs (AsanAcct.mkCfg (unrestrict H ms.ms_mem msr') model') T) :
    srealizes segs (AsanAcct.mkCfg ms model) T :=
  rz_msteps_restricted' segs H HH Hwx (SP_of segs T) (SP_of_silent1 segs T)
    A ms msr' model Hcov Hwf Hinv Hh Hms Hk

end LinuxSem.Common.AsanAcctShape
