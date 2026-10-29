/-
  * Common.ErrEscape2 — SOURCE-ERROR ESCAPE glue through syscall steps.

  TRUST BOUNDARY: image-INDEPENDENT proof library (like
  `Common.ErrEscape`), NOT part of the trusted specification.

  The statements are model-generic glue: `x8 : word` is a `BitVec 64`
  syscall number, and the `Equivalence`-level conclusion is spelled
  `Equivalence.equiv` (`equiv` is unambiguous inside this namespace).

  `Common.ErrEscape` covers the universal escape for a straight line of
  ordinary instructions ending in an illegal one.  This file retains
  compositional MAY-error reachability helpers for diagnostics and
  target-safety proofs.  In particular, choosing one successful brk
  resolution and faulting afterward does NOT establish the source
  escape when a different brk resolution avoids error:

  - `reaches_error_star`: prepend any `star` run to a
    `reaches_error` witness;
  - `reaches_error_msteps`: prepend a deterministic instruction run;
  - `reaches_error_syscall`: step through an ecall with a CHOSEN
    admissible effect (the erroring resolution the prover picks);
  - `reaches_error_illegal`: the terminal witness — the current
    instruction is illegal;
  - `err_escape_run`: at the `Equivalence` level, an
    `all_traces_error` proof (not a `reaches_error` witness) discharges
    `equiv` against any target.

  NOTES (this file).

  - `segs : List Segment` is an EXPLICIT LEADING PARAMETER of every
    declaration that mentions it, as `Common.FileSim`/`Common.ErrEscape` do
    for their sections.  There is no section to close, so `err_escape_run`
    carries `segs` explicitly as well.
  - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` record constructor
    `⟨sp, brk0, mb, rnd⟩`.
  - `sstep_syscall`/`sstep_instr_fault` are the `Run.sstep` constructors
    `.syscall`/`.instr_fault`; the trailing
    `rewrite (materialize_model_accesses_no_lazy model' _ Hlazy);
    reflexivity` closes the constructor's `hmat` field (`model'' = model'`).
  - The limits are `Int` (`lim : Int`).
  - Whatever `run`'s own reduction would need, `err_escape_run` needs no
    `cbn` step: `run` reads the image fields off the `mkImage` record and
    the entry fields off the `ExecEntry` literal, so the `bh_all_errors`
    projection of the resulting `behavior` structure is already
    `all_traces_error segs (init_config …)` up to `rfl`.  `Or.inl Hall`
    therefore typechecks as-is — the same `rfl`-level step
    `FileSim.spec_err_escape_equiv` takes.
-/
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.ErrEscape
import LinuxSem.Common.FileSim

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace LinuxSem.Common.ErrEscape2

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.ErrEscape
open LinuxSem.Common.FileSim

/-- Nothing here builds a `mkst`, so no FP state is semantically involved.
    `Common.FileSim.reaches_error_star` nevertheless carries the ambient
    `variable [fx : FPState]` its own file declares, purely because
    `FileSim`'s proof term is abstracted over it.  Supplying the
    process-entry FP state with a local instance keeps THIS file's
    statements instance-free.  (Same device as `Common.ShapeAlg`,
    `Common.SpinAlg` and `Common/AsanAcct.lean`.) -/
local instance erre2_fx : PropExec.FPState := PropExec.fx0

/- The segment list `segs` is an explicit leading parameter on each
   declaration below. -/

/- `reaches_error_star` lives in `Common.FileSim`. -/

/-- Prepend a deterministic instruction run (the model is untouched). -/
theorem reaches_error_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hm : msteps segs ms ms')
    (Herr : reaches_error segs ⟨ms', model⟩) :
    reaches_error segs ⟨ms, model⟩ :=
  reaches_error_star segs ⟨ms, model⟩ [] ⟨ms', model⟩
    (msteps_star_nil segs ms ms' model Hh Hlazy Hm) Herr

/-- Step through an ecall with a CHOSEN admissible effect. -/
theorem reaches_error_syscall (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
    (Hh' : m_halted model' = none)
    (Hlazy : m_vm_lazy model' = [])
    (Herr : reaches_error segs
      ⟨advance_past_svc (apply_effect ms eff), model'⟩) :
    reaches_error segs ⟨ms, model⟩ := by
  refine reaches_error_star segs ⟨ms, model⟩ evs
    ⟨advance_past_svc (apply_effect ms eff), model'⟩ ?_ Herr
  exact star_one segs ⟨ms, model⟩ evs _
    (sstep.syscall ms model x8 eff model' model' evs Hh Hsvc Hspec Hh'
      (materialize_model_accesses_no_lazy model' _ Hlazy))

/-- Terminal witness: the current instruction faults. -/
theorem reaches_error_illegal (segs : List Segment) (ms : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hill : RiscvSemantics.step segs ms = .MachineFault) :
    reaches_error segs ⟨ms, model⟩ := by
  refine ⟨[], ⟨ms, model⟩, [], star.refl _, ?_⟩
  exact sstep.instr_fault ms model Hh Hsvc
    (by rw [mi_account_step_no_lazy segs ms model Hlazy, Hill])

/-- Equivalence-level escape: every source execution must error. -/
theorem err_escape_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (target : behavior)
    (Hall : all_traces_error segs (init_config segs pc ph sp brk0 mb rnd lim inp)) :
    equiv (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) target :=
  Or.inl Hall

end LinuxSem.Common.ErrEscape2
