/-
  * LinuxProcessSem.Run — Kleene-star trace semantics and trace equivalence


  TRUST BOUNDARY: this file is part of the trusted specification.

  Machine words are `BitVec 64`, bytes are `BitVec 8`, and the
  segment/stack range arithmetic is in `Int` over unsigned values.  `machine_state` carries an LR/SC reservation field
  `ms_resv` (initialized `none`; preserved across syscalls).

  A binary's observable behavior is its set of finite trace prefixes plus
  TWO error facts: whether SOME execution can reach the explicit error
  transition (`reaches_error`), and whether ALL executions must reach it
  (`all_traces_error`).  Equivalence is equality of prefix sets (with an
  escape only when all source executions error — see
  `Equivalence.equiv`).  For the TARGET an error is fatal
  (`Equivalence.equiv` requires the target error-free).  For the SOURCE,
  the vacuity escape applies only when `all_traces_error` proves that
  EVERY nondeterministic execution reaches error; one erroring resolution
  is not enough when another resolution exits or runs forever without
  error.

  A behavior additionally records `reaches_unmodeled`: whether the run can
  reach a configuration where THIS MODEL gave up, as opposed to one where
  the PROGRAM died.  The two are distinct — `MachineFault` and
  `MachineUnmodeled` on the machine side, and on the syscall side an
  errno-returning `Ok` versus the fail-closed `Unmodeled` — and the source
  side of `Equivalence.strong_equiv` requires the model to cover the
  source everywhere, so that its equivalence claim cannot be satisfied by
  a semantics too weak to follow the binary.

  SECTIONS.  The image-facing fields — `mi_loaded_segments`, `mi_init_pc`,
  `mi_phdrs`, `mi_init_sp`, `mi_init_brk`, `mi_mmap_base`, `mi_draw` and
  `mi_alloc_limit` — are passed explicitly.  As in `RiscvSemantics.lean`,
  every definition that mentions one takes it as an EXPLICIT leading
  parameter, in a fixed order.  `sstep_cfg` and the budget section re-bind
  `segs`; the same convention applies.

  RECORDS.  `machine_state` has function-valued fields, so no
  `DecidableEq`/`Repr`; state equalities are proved field-wise.  `x <- c ;; k`
  is `bind c (fun x => k)` and does not appear here.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateInit
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateStreams
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei
import LinuxSem.LinuxProcessSem.Sys.Fs.Open
import LinuxSem.LinuxProcessSem.Sys.Fs.DPath
import LinuxSem.LinuxProcessSem.Sys.Fs.File
import LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.LinuxProcessSem.Sys.Net.Socket
import LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Run

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout

/- =========================================================================
   Trace prefixes and observable behaviors
   ========================================================================= -/

/-- `l1` is a prefix of `l2`. -/
def is_prefix {A : Type} : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ is_prefix xs ys

theorem is_prefix_refl {A : Type} (l : List A) : is_prefix l l := by
  induction l with
  | nil => exact True.intro
  | cons x xs ih => exact ⟨rfl, ih⟩

theorem is_prefix_nil {A : Type} (l : List A) : is_prefix [] l := by
  cases l <;> exact True.intro

theorem is_prefix_trans {A : Type} {l1 l2 l3 : List A}
    (h12 : is_prefix l1 l2) (h23 : is_prefix l2 l3) : is_prefix l1 l3 := by
  induction l1 generalizing l2 l3 with
  | nil => exact True.intro
  | cons x xs ih =>
    cases l2 with
    | nil => exact False.elim h12
    | cons y ys =>
      cases l3 with
      | nil => exact False.elim h23
      | cons z zs =>
        obtain ⟨rfl, h12'⟩ := h12
        obtain ⟨rfl, h23'⟩ := h23
        exact ⟨rfl, ih h12' h23'⟩

theorem is_prefix_app {A : Type} (l1 l2 : List A) : is_prefix l1 (l1 ++ l2) := by
  induction l1 with
  | nil => exact True.intro
  | cons x xs ih => exact ⟨rfl, ih⟩

/-- Everything observable about one binary on one input: its finite trace
    prefixes, whether it CAN reach the error transition, whether EVERY
    execution MUST reach the error transition, and whether it can reach a
    place where THIS MODEL — rather than the program — gave up.  The two
    error propositions deliberately have different quantifiers: the source
    escape consumes `bh_all_errors`, while target safety consumes
    `¬ bh_errors`.

    `bh_unmodeled` is not an observation about the program at all; it is an
    observation about the semantics' COVERAGE of the program, and it is what
    the `modeled` clause of `Equivalence.strong_equiv` rules out for the
    source.  It is a strict sub-case of `bh_errors`: everything unmodeled
    errors, but not everything that errors is unmodeled (see
    `reaches_unmodeled_reaches_error`). -/
structure behavior where
  /-- The finite trace prefixes. -/
  bh_traces : List event → Prop
  /-- SOME execution reaches the explicit error transition. -/
  bh_errors : Prop
  /-- EVERY execution must reach the explicit error transition. -/
  bh_all_errors : Prop
  /-- The run can reach a configuration the model does not cover. -/
  bh_unmodeled : Prop

/- The four observations are read as functions (`bh_traces b tr`), so
   the projections are opened here. -/
open behavior

/- =========================================================================
   Applying a chosen syscall effect to the machine
   ========================================================================= -/

/-- The decoded syscall argument registers a0..a5 at the `ecall`. -/
def syscall_args (ms : machine_state) : List word :=
  [ms_gpr ms 0, ms_gpr ms 1, ms_gpr ms 2, ms_gpr ms 3, ms_gpr ms 4, ms_gpr ms 5]

/-- Apply a list of byte writes, in order, to a memory overlay. -/
def apply_writes (mem : word → Option byte) (ws : List (word × List byte)) :
    word → Option byte :=
  match ws with
  | [] => mem
  | (a, bs) :: r => apply_writes (write_to_mem mem a bs) r

/-- Is `a` inside one of the (base, size) ranges?  Computed in `Int` over
    unsigned values (grant ranges never wrap; see Specs.v). -/
def zeros_cover (zs : List (word × word)) (a : word) : Bool :=
  zs.any (fun z =>
    decide ((z.1.toNat : Int) ≤ (a.toNat : Int)) &&
    decide ((a.toNat : Int) < (z.1.toNat : Int) + (z.2.toNat : Int)))

/-- Zero-fill the effect's granted ranges (anonymous mmap/brk memory):
    every covered address reads as byte 0, REPLACING whatever was there.
    Kept as a functional overlay so multi-megabyte grants never materialize
    byte lists. -/
def apply_zeros (mem : word → Option byte) (zs : List (word × word)) :
    word → Option byte :=
  match zs with
  | [] => mem
  | _ => fun a => if zeros_cover zs a then some (BitVec.ofInt 8 0) else mem a

/-- Erase the effect's inaccessible ranges (munmap, a PROT_NONE mapping,
    mremap, or the tail a brk shrink frees — see `State.eff_unmaps`): every
    covered address becomes UNMAPPED in the writable overlay, so a later
    load faults instead of reading stale bytes, as on Linux.  The SPECS only
    unmap recorded anonymous mappings, their subranges, or ranges of them and
    free pages, disjoint from every loaded segment and from the stack, so
    erasing the overlay really makes the range inaccessible (there is no
    segment underneath for reads to fall back to). -/
def apply_unmaps (mem : word → Option byte) (us : List (word × word)) :
    word → Option byte :=
  match us with
  | [] => mem
  | _ => fun a => if zeros_cover us a then none else mem a

/-- Apply symbolic copies against an immutable snapshot of the memory from
    BEFORE this syscall effect.  Destination ranges use list order (later
    copies override earlier ones); every source read uses `before`, never a
    range already zeroed, copied, or unmapped by the effect. -/
def apply_copy (before mem : word → Option byte) (c : MemCopy) :
    word → Option byte :=
  fun a =>
    if decide ((c.copy_dst.toNat : Int) ≤ (a.toNat : Int)) &&
       decide ((a.toNat : Int) <
               (c.copy_dst.toNat : Int) + (c.copy_len.toNat : Int))
    then before (BitVec.ofInt 64
           ((c.copy_src.toNat : Int) + ((a.toNat : Int) - (c.copy_dst.toNat : Int))))
    else mem a

/-- Apply the effect's symbolic copies in list order. -/
def apply_copies (before mem : word → Option byte) (cs : List MemCopy) :
    word → Option byte :=
  match cs with
  | [] => mem
  | c :: r => apply_copies before (apply_copy before mem c) r

/-- Apply a chosen effect: set a0 (= x10) to the return value, snapshot the
    pre-effect memory, erase the unmapped ranges, zero-fill the granted
    ranges, copy preserved bytes from the snapshot, and write exactly the
    declared byte ranges.  SP, every other GPR, the LR/SC reservation, ROM,
    and all memory outside the declared ranges are preserved BY
    CONSTRUCTION — the generative spec cannot silently rewrite anything it
    did not declare, so no frame side-conditions are needed.

    (Mechanically, writes land in the writable overlay `ms_mem` at whatever
    addresses the effect declares; the SPECS guarantee those addresses are
    writable-mapped — output buffers are checked against `in_wmem`, the
    copy_to_user/EFAULT analogue, zero ranges are fresh anonymous grants,
    mremap growth tails, noaccess pages made rw, or a live rw range replaced
    by MAP_FIXED or zapped by madvise(MADV_DONTNEED), and unmap ranges are
    tracked anonymous subranges.  A moved-growing mremap deliberately
    combines all three symbolic ledgers; the ordering above preserves its
    old prefix.  A brk transition either grows (zeros, no unmaps) or shrinks
    (unmaps, no zeros).) -/
def apply_effect (ms : machine_state) (eff : SyscallEffect) : machine_state :=
  let ms' := set_reg ms 10 (eff.eff_ret)
  { ms' with
    ms_mem :=
      apply_writes
        (apply_copies ms'.ms_mem
          (apply_zeros (apply_unmaps ms'.ms_mem eff.eff_unmaps) eff.eff_zeros)
          eff.eff_copies)
        (eff.eff_writes) }

/-- Advance PC past the ecall instruction (+4) and clear svc_pending. -/
def advance_past_svc (ms : machine_state) : machine_state :=
  { ms with ms_pc_val := ms_pc ms + BitVec.ofInt 64 4, ms_svc_pending := none }

/- =========================================================================
   Configurations and the one-step relation
   ========================================================================= -/

/-- A configuration: the machine plus the model. -/
structure config where
  cfg_ms    : machine_state
  cfg_model : Model

/-- The address space the kernel already used at `execve`: each LOAD
    segment, PAGE-ROUNDED.  Segments are `Nat`-based snapshot data far below
    2^64, so the rounding in `Int` re-enters `word` losslessly. -/
def segment_reservation (s : Segment) : word × word :=
  let lo := page_round_down_Z (Int.ofNat s.seg_base)
  let hi := page_round_up_Z (Int.ofNat s.seg_base + Int.ofNat s.seg_size)
  (BitVec.ofInt 64 lo, BitVec.ofInt 64 (hi - lo))

/-- The page-rounded reservations of every loaded segment. -/
def segments_reserved (segs : List Segment) : List (word × word) :=
  segs.map segment_reservation

/-- Where a step can go: on to another configuration, or the explicit error
    transition. -/
inductive step_to where
  | SNext (c : config)
  | SError

/- =========================================================================
   The `WithMemImage` section, spelled as explicit leading parameters
   =========================================================================

   The section abstracts `mi_loaded_segments : List Segment`,
   `mi_init_pc : N`, `mi_phdrs : PhdrInfo`, `mi_init_sp`, `mi_init_brk`,
   `mi_mmap_base : word`, `mi_draw : EntryDraw` and `mi_alloc_limit : Z`.
   Every definition below that reads one takes it explicitly, in that
   order (only the variables a definition actually mentions appear — the
   same set the section discharge produces). -/

/-- Execute one instruction and atomically charge every newly touched page
    in a lazy anonymous reservation.  The interpreter returns the complete
    access report before this function changes the model, so an instruction
    spanning two new pages either charges both or takes the fault
    transition. -/
def mi_account_step (mi_loaded_segments : List Segment) (ms : machine_state)
    (model : Model) : machine_result (machine_state × Model) :=
  match step_accesses mi_loaded_segments ms with
  | .MachineOk report =>
      match materialize_model_accesses model report.accessed_ranges with
      | some model' => .MachineOk (report.access_value, model')
      | none => .MachineFault
  | .MachineFault => .MachineFault
  | .MachineUnmodeled => .MachineUnmodeled

/-- Accounting is an overlay on the authoritative instruction semantics: a
    successful accounted step has exactly the machine state produced by
    `RiscvSemantics.step`. -/
theorem mi_account_step_projects (mi_loaded_segments : List Segment)
    (ms : machine_state) (model : Model) (ms' : machine_state) (model' : Model)
    (Haccount : mi_account_step mi_loaded_segments ms model = .MachineOk (ms', model')) :
    RiscvSemantics.step mi_loaded_segments ms = .MachineOk ms' := by
  unfold mi_account_step at Haccount
  cases hstep : step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    cases hmat : materialize_model_accesses model report.accessed_ranges with
    | none => simp [hstep, hmat] at Haccount
    | some macc =>
      simp only [hstep, hmat, machine_result.MachineOk.injEq, Prod.mk.injEq] at Haccount
      obtain ⟨rfl, rfl⟩ := Haccount
      show drop_access_report (step_accesses mi_loaded_segments ms) = .MachineOk _
      simp only [drop_access_report, hstep]
  | MachineFault => simp [hstep] at Haccount
  | MachineUnmodeled => simp [hstep] at Haccount

/-- Accounting never touches the descriptor table, the VMMaps, the lazy
    backing ledger, the I/O state, the file system, the process state or the
    resource limits: it is a model OVERLAY on the instruction step. -/
theorem mi_account_step_model_frame (mi_loaded_segments : List Segment)
    (ms : machine_state) (model : Model) (ms' : machine_state) (model' : Model)
    (Haccount : mi_account_step mi_loaded_segments ms model = .MachineOk (ms', model')) :
    model'.m_fd = model.m_fd ∧
    m_vmmaps model' = m_vmmaps model ∧
    m_vm_lazy model' = m_vm_lazy model ∧
    model'.m_io = model.m_io ∧
    model'.m_fsys = model.m_fsys ∧
    model'.m_proc = model.m_proc ∧
    model'.m_lim = model.m_lim := by
  unfold mi_account_step at Haccount
  cases hstep : step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    cases hmat : materialize_model_accesses model report.accessed_ranges with
    | none => simp [hstep, hmat] at Haccount
    | some macc =>
      simp only [hstep, hmat, machine_result.MachineOk.injEq, Prod.mk.injEq] at Haccount
      obtain ⟨rfl, rfl⟩ := Haccount
      exact materialize_model_accesses_frame model _ macc hmat
  | MachineFault => simp [hstep] at Haccount
  | MachineUnmodeled => simp [hstep] at Haccount

/-- With no lazy mappings there is nothing to charge, so accounting erases
    completely and preserves the model as well as the machine step. -/
theorem mi_account_step_no_lazy (mi_loaded_segments : List Segment)
    (ms : machine_state) (model : Model) (Hlazy : m_vm_lazy model = []) :
    mi_account_step mi_loaded_segments ms model =
      match RiscvSemantics.step mi_loaded_segments ms with
      | .MachineOk ms' => .MachineOk (ms', model)
      | .MachineFault => .MachineFault
      | .MachineUnmodeled => .MachineUnmodeled := by
  unfold mi_account_step RiscvSemantics.step
  cases hstep : step_accesses mi_loaded_segments ms with
  | MachineOk report =>
    simp only [drop_access_report,
      materialize_model_accesses_no_lazy model report.accessed_ranges Hlazy]
  | MachineFault => rfl
  | MachineUnmodeled => rfl

/-- The input handed to the syscall spec: the syscall number, the argument
    registers, the COMPLETE pre-syscall memory (`ms_read_byte`) and the
    WRITABLE view (`ms_writable_byte`). -/
def sys_input (mi_loaded_segments : List Segment) (ms : machine_state) (x8 : word) :
    SyscallInput :=
  ⟨x8, syscall_args ms, ms_read_byte ms,
   ms_writable_byte mi_loaded_segments ms⟩

/-- One transition. -/
inductive sstep (mi_loaded_segments : List Segment) : config → List event → step_to → Prop where
  | instr (ms : machine_state) (model : Model) (ms' : machine_state) (model' : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step mi_loaded_segments ms model = .MachineOk (ms', model')) :
      sstep mi_loaded_segments ⟨ms, model⟩ [] (.SNext ⟨ms', model'⟩)
  | instr_fault (ms : machine_state) (model : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step mi_loaded_segments ms model = .MachineFault) :
      sstep mi_loaded_segments ⟨ms, model⟩ [] .SError
  | instr_unmodeled (ms : machine_state) (model : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step mi_loaded_segments ms model = .MachineUnmodeled) :
      sstep mi_loaded_segments ⟨ms, model⟩ [] .SError
  | syscall (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' model'' : Model) (evs : List event)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input mi_loaded_segments ms x8) model (.ok eff model' evs))
      (hh' : m_halted model' = none)
      (hmat : materialize_model_accesses model' (syscall_effect_accesses eff) = some model'') :
      sstep mi_loaded_segments ⟨ms, model⟩ evs
        (.SNext ⟨advance_past_svc (apply_effect ms eff), model''⟩)
  | syscall_materialization_fault (ms : machine_state) (model : Model) (x8 : word)
      (eff : SyscallEffect) (model' : Model) (evs : List event)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input mi_loaded_segments ms x8) model (.ok eff model' evs))
      (hh' : m_halted model' = none)
      (hmat : materialize_model_accesses model' (syscall_effect_accesses eff) = none) :
      sstep mi_loaded_segments ⟨ms, model⟩ [] .SError
  | exit (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' : Model) (evs : List event) (code : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input mi_loaded_segments ms x8) model (.ok eff model' evs))
      (hh' : m_halted model' = some code)
      (hk : m_killed model' = none) :
      sstep mi_loaded_segments ⟨ms, model⟩ (evs ++ [event.ExitEv code (m_fs model')])
        (.SNext ⟨ms, model'⟩)
  /-- The other way a process ends: a fatal signal it sent itself.  Same
      shape as `exit` and the same discarded effect — the syscall completes
      in the kernel and the process is killed on the way back to user space,
      so what it wrote to its own memory is never read — and the two arms
      are disjoint by `m_killed`, which `exit` requires to be `none`.

      THE DECLARATION IS NOT A PREMISE HERE.  It is one inside
      `Kernel.Signal.tkill_spec`, which is the only arm that can write
      `State.m_killed` at all, and putting it here as well would make this
      rule unable to fire on an outcome the spec layer produced — which is a
      STUCK configuration, not a decline, and `sstep_cfg_progress` below
      would be false.  What carries the compatibility claim instead is
      `decl_off_frame` below, stated once and consumed by
      `sstep_off_no_kill`. -/
  | killed (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' : Model) (evs : List event) (sig : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input mi_loaded_segments ms x8) model (.ok eff model' evs))
      (hk : m_killed model' = some sig) :
      sstep mi_loaded_segments ⟨ms, model⟩ (evs ++ [event.KillEv sig (m_fs model')])
        (.SNext ⟨ms, model'⟩)
  | syscall_unmodeled (ms : machine_state) (model : Model) (x8 : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input mi_loaded_segments ms x8) model .unmodeled) :
      sstep mi_loaded_segments ⟨ms, model⟩ [] .SError

/-- Kleene star of `sstep`, accumulating events. -/
inductive star (mi_loaded_segments : List Segment) : config → List event → config → Prop where
  | refl (c : config) : star mi_loaded_segments c [] c
  | step (c1 : config) (evs : List event) (c2 : config) (tr : List event) (c3 : config)
      (h1 : sstep mi_loaded_segments c1 evs (.SNext c2))
      (h2 : star mi_loaded_segments c2 tr c3) :
      star mi_loaded_segments c1 (evs ++ tr) c3

theorem star_one (mi_loaded_segments : List Segment) (c : config) (evs : List event)
    (c' : config) (h : sstep mi_loaded_segments c evs (.SNext c')) :
    star mi_loaded_segments c evs c' := by
  have := star.step c evs c' [] c' h (star.refl c')
  rwa [List.append_nil] at this

theorem star_trans (mi_loaded_segments : List Segment) :
    ∀ (c1 : config) (t1 : List event) (c2 : config),
      star mi_loaded_segments c1 t1 c2 →
      ∀ (t2 : List event) (c3 : config),
        star mi_loaded_segments c2 t2 c3 →
        star mi_loaded_segments c1 (t1 ++ t2) c3 := by
  intro c1 t1 c2 h1
  induction h1 with
  | refl c => intro t2 c3 h2; simpa using h2
  | step c1 evs c2 tr c3 hs _ ih =>
    intro t2 c4 h2
    rw [List.append_assoc]
    exact star.step c1 evs c2 (tr ++ t2) c4 hs (ih t2 c4 h2)

/- =========================================================================
   Observable behavior: finite trace prefixes + reachability of error
   ========================================================================= -/

/-- `tr` is an event-level prefix of an admissible run (prefix-closed at
    BYTE granularity). -/
def obs_trace (mi_loaded_segments : List Segment) (c0 : config)
    (tr : List event) : Prop :=
  ∃ tr' c, star mi_loaded_segments c0 tr' c ∧ is_prefix tr tr'

theorem obs_trace_nil (mi_loaded_segments : List Segment) (c0 : config) :
    obs_trace mi_loaded_segments c0 [] :=
  ⟨[], c0, star.refl c0, is_prefix_nil []⟩

theorem obs_trace_prefix_closed (mi_loaded_segments : List Segment) (c0 : config)
    (tr tr' : List event) (h : obs_trace mi_loaded_segments c0 tr)
    (hp : is_prefix tr' tr) : obs_trace mi_loaded_segments c0 tr' := by
  obtain ⟨tr'', c, hstar, hp'⟩ := h
  exact ⟨tr'', c, hstar, is_prefix_trans hp hp'⟩

/- =========================================================================
   The declaration off adds no behavior: what that rests on
   ========================================================================= -/

/-- THE FRAME THE COMPATIBILITY CLAIM RESTS ON, NAMED RATHER THAN ASSUMED
    SILENTLY.

    `State.in_abort_terminal` is meant to be inert when it is `false`: a run
    whose task did not declare the abort path should produce exactly the
    traces, errors and uncovered points it would produce if 130 and 131 had
    no arms.  Two of the three things that has to mean are facts about the
    SPEC LAYER rather than about this file — that no syscall arm turns the
    declaration on, that none records a kill under it, and that none emits a
    `State.KillEv` of its own — and this development has no lemma quantified
    over the arms of `Sys.SyscallTable.spec_table` to prove them with.

    So they are a hypothesis with a name.  `decl_off_frame` states exactly
    what the abort path's code establishes BY INSPECTION:
    `State.with_abort_terminal` has one caller (`State.init_model`);
    `State.with_killed` has two, `Kernel.Signal.send_sigabrt` and
    `Kernel.Signal.sigmask_deliver_model`; and no spec emits any event but
    `State.ReadEv` and `State.WriteEv`.  Every other setter carries the
    three fields across, which is what the `m_killed_with_*`,
    `m_sigabrt_pending_with_*` and `m_abort_terminal_with_*` blocks in
    `State.lean` say, one `rfl` each.

    IT IS AN INVARIANT AND NOT A ONE-SIDED FRAME, and the second hypothesis
    is the whole reason.  Of `State.with_killed`'s two callers only the
    first is behind `State.m_abort_terminal`:
    `Kernel.Signal.sigmask_deliver_model` branches on
    `State.m_sigabrt_pending` instead, because a signal already pending has
    to be delivered by the mask install that uncovers it whatever the task
    declared.  So the declaration ALONE does not keep a kill out — a model
    with the declaration clear and the pending bit set is directly
    constructible, and an ordinary `rt_sigprocmask(SIG_UNBLOCK, {SIGABRT})`
    kills it.  `Checks/Cases/Kernel/Signal.lean` builds that model as
    `one_sided_model` and proves
    `decl_off_frame_one_sided_refuted : ¬ decl_off_frame_one_sided`, so
    the one-sided form below is refuted rather than merely described.

    What IS true is the pair moving together: with both bits clear no arm can
    set either, because the only writer of the pending bit is
    `Kernel.Signal.send_sigabrt`, which IS behind the declaration.  That is
    why the hypothesis carries `m_sigabrt_pending` and the conclusion
    re-establishes it, and why `State.init_model` — which clears both — is
    the base case the run-level consequence starts from.

    This is the same standing `State.with_children`'s note describes for
    `procst_children`: a property maintained by every construction site and
    documented at the setter, which a new setter can break without breaking
    any proof.  Writing it as a hypothesis is one step better than that note
    — the consequences below are mechanized, and the day a table-wide frame
    lemma exists it is discharged rather than assumed. -/
def decl_off_frame : Prop :=
  ∀ (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event),
    Specs.syscall_spec i m (.ok eff m' evs) →
    m_abort_terminal m = false →
    m_sigabrt_pending m = false →
    m_abort_terminal m' = false ∧
    m_sigabrt_pending m' = false ∧
    m_killed m' = none ∧
    (∀ (sig : word) (fs : Fs.Fs), event.KillEv sig fs ∉ evs)

/-- The form this had before, kept ONLY so that
    `Checks.Cases.Kernel.Signal.decl_off_frame_one_sided_refuted` has
    something to refute, and so the shape a reader reaches for stays
    visible.  That result is about THIS definition — `¬
    decl_off_frame_one_sided`, proved in `Checks/Cases/Kernel/Signal.lean`
    — so its falsity is checked there, beside the argument in the
    paragraph above.
    Nothing may consume it: it is FALSE, and a theorem
    stated with it as a hypothesis is vacuous.
    It is the shape a reader reaches for first — the declaration is the
    switch, so surely the
    declaration is the guard — and the refutation is what says why that
    reading is wrong. -/
def decl_off_frame_one_sided : Prop :=
  ∀ (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event),
    Specs.syscall_spec i m (.ok eff m' evs) →
    m_abort_terminal m = false →
    m_abort_terminal m' = false ∧
    m_killed m' = none ∧
    (∀ (sig : word) (fs : Fs.Fs), event.KillEv sig fs ∉ evs)

theorem m_abort_terminal_proc (m1 m2 : Model) (h : m1.m_proc = m2.m_proc) :
    m_abort_terminal m1 = m_abort_terminal m2 := by
  unfold m_abort_terminal
  rw [h]

theorem m_sigabrt_pending_proc (m1 m2 : Model) (h : m1.m_proc = m2.m_proc) :
    m_sigabrt_pending m1 = m_sigabrt_pending m2 := by
  unfold m_sigabrt_pending
  rw [h]

/-- One step, with the declaration off and nothing pending: BOTH bits stay
    clear, and the events the step contributes carry no kill.  The pending
    bit is carried for the reason the frame carries it — see
    `decl_off_frame` — and dropping it from either side makes this lemma's
    hypothesis the false one. -/
theorem sstep_off_no_kill (mi_loaded_segments : List Segment) (Hframe : decl_off_frame)
    (ms : machine_state) (model : Model) (evs : List event) (c' : config)
    (Hoff : m_abort_terminal model = false)
    (Hpend : m_sigabrt_pending model = false)
    (Hstep : sstep mi_loaded_segments ⟨ms, model⟩ evs (.SNext c')) :
    m_abort_terminal c'.cfg_model = false ∧
    m_sigabrt_pending c'.cfg_model = false ∧
    (∀ (sig : word) (fs : Fs.Fs), event.KillEv sig fs ∉ evs) := by
  obtain ⟨cms, cmodel⟩ := c'
  cases Hstep with
  | instr ms1 model1 ms' model' hh hsvc hstep =>
    obtain ⟨_h1, _h2, _h3, _h4, _h5, hp, _h7⟩ :=
      mi_account_step_model_frame mi_loaded_segments ms model cms cmodel hstep
    refine ⟨?_, ?_, ?_⟩
    · rw [m_abort_terminal_proc _ _ hp, Hoff]
    · rw [m_sigabrt_pending_proc _ _ hp, Hpend]
    · intro sig fs hin
      exact absurd hin (by simp)
  | syscall ms1 model1 x8 eff model' model'' evs1 hh hsvc hspec hh' hmat =>
    obtain ⟨Hoff', Hpend', _hk, Hev⟩ := Hframe _ _ _ _ _ hspec Hoff Hpend
    obtain ⟨_h1, _h2, _h3, _h4, _h5, hp, _h7⟩ :=
      materialize_model_accesses_frame model' _ cmodel hmat
    refine ⟨?_, ?_, ?_⟩
    · rw [m_abort_terminal_proc _ _ hp, Hoff']
    · rw [m_sigabrt_pending_proc _ _ hp, Hpend']
    · exact Hev
  | exit ms1 model1 x8 eff model' evs1 code hh hsvc hspec hh' hk =>
    obtain ⟨Hoff', Hpend', _hk, Hev⟩ := Hframe _ _ _ _ _ hspec Hoff Hpend
    refine ⟨Hoff', Hpend', ?_⟩
    intro sig fs hin
    rcases List.mem_append.mp hin with hin | hin
    · exact Hev sig fs hin
    · exact absurd hin (by simp)
  | killed ms1 model1 x8 eff model' evs1 sig hh hsvc hspec hk =>
    obtain ⟨_Hoff', _Hpend', Hk, _Hev⟩ := Hframe _ _ _ _ _ hspec Hoff Hpend
    rw [Hk] at hk
    exact absurd hk (by simp)

/-- In a whole execution, the same.  `State.init_model` clears both bits
    (`State.m_sigabrt_pending_init_model`, and
    `State.m_abort_terminal_init_model` reads the declaration off the
    input), so a run whose task did not declare the abort path meets this
    lemma's hypotheses at its first configuration. -/
theorem star_off_no_kill (mi_loaded_segments : List Segment) (Hframe : decl_off_frame) :
    ∀ (c : config) (tr : List event) (c' : config),
      m_abort_terminal c.cfg_model = false →
      m_sigabrt_pending c.cfg_model = false →
      star mi_loaded_segments c tr c' →
      ∀ (sig : word) (fs : Fs.Fs), event.KillEv sig fs ∉ tr := by
  intro c tr c' Hoff Hpend Hstar
  revert Hoff Hpend
  induction Hstar with
  | refl c =>
    intro Hoff Hpend sig fs hin
    exact absurd hin (by simp)
  | step c1 evs c2 tr c3 hstep hstar ih =>
    intro Hoff Hpend sig fs hin
    obtain ⟨ms, model⟩ := c1
    obtain ⟨Hoff', Hpend', Hev⟩ :=
      sstep_off_no_kill mi_loaded_segments Hframe ms model evs c2 Hoff Hpend hstep
    rcases List.mem_append.mp hin with hin | hin
    · exact Hev sig fs hin
    · exact ih Hoff' Hpend' sig fs hin

theorem in_is_prefix {A : Type} (x : A) : ∀ (l1 l2 : List A),
    is_prefix l1 l2 → x ∈ l1 → x ∈ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 hp hin; exact absurd hin (by simp)
  | cons a l1 ih =>
    intro l2 hp hin
    cases l2 with
    | nil => exact absurd hp (by simp [is_prefix])
    | cons b l2 =>
      obtain ⟨rfl, hp'⟩ := hp
      rcases List.mem_cons.mp hin with rfl | hin
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih l2 hp' hin)

/-- The run can take the explicit error transition. -/
def reaches_error (mi_loaded_segments : List Segment) (c0 : config) : Prop :=
  ∃ tr c evs, star mi_loaded_segments c0 tr c ∧ sstep mi_loaded_segments c evs .SError

/- =========================================================================
   Coverage: where the MODEL gives up, as opposed to where the PROGRAM dies
   ========================================================================= -/

/-- `c` is a configuration this model does not cover.  There are exactly two
    ways to be uncovered, matching the two places the semantics can decline
    to say what happens:

    - the pending instruction is `MachineUnmodeled` — a word the decoder does
      not decode, an instruction outside the modeled subset, or an unmodeled
      ISA boundary node (see `RiscvSemantics.machine_result`);
    - the pending syscall's spec yields `Unmodeled` — the fail-closed arm of
      `Specs.syscall_spec`, reached by a syscall number outside
      `Specs.modeled_sysnos`, by unmodeled flags, or by a buffer the spec
      declines to interpret (`Monad.unmodeled` means "the model does not
      cover this", never "Linux would fail here": real Linux failures are
      modeled as `Ok` with a negative errno).

    Deliberately NOT included: `MachineFault` (a wild jump, an unmapped load,
    a store into a read-only segment, an `ebreak`).  Those are faithful
    models of a process that really does die, and a source binary is entitled
    to reach them.  This is the whole point of the distinction — an
    equivalence task is allowed to be about a program that crashes, but it
    must not be about a program the semantics failed to follow.

    THAT EXCLUSION IS A CLAIM ABOUT SIGNAL DISPOSITIONS, and it is not
    self-evident: a process that has installed a SIGSEGV handler does NOT
    die here, it runs the handler and carries on.  So the exclusion holds
    only while no fault signal can have a handler, which is why
    `Signal.sigaction_accepted` refuses an `rt_sigaction` install for SIGSEGV,
    SIGBUS, SIGILL and SIGTRAP, and why no modeled syscall can SEND one of
    the four.  `Specs.modeled_sysnos` contains no `kill` (129) and no
    `rt_sigreturn` (139); it does contain `tkill` (130) and `tgkill` (131),
    and what stands in for their absence is `Kernel.Signal.tkill_self`'s
    envelope, which sends SIGABRT and declines every other signal — so no
    fault signal is reachable through them either, and a widening there is a
    widening HERE.  Widening any of those without also routing
    `MachineFault` to `unmodeled_at` makes this premise false, and the cost
    is not a wrong answer but a silent one: every execution reaches `SError`,
    `Equivalence.bh_all_errors` holds, `Equivalence.equiv`'s escape admits an
    ARBITRARY target, and `Equivalence.modeled` is still satisfied because a
    fault is not unmodeled.  The theorem stays true and says nothing.

    BLOCKING A FAULT SIGNAL DOES NOT WEAKEN THAT EXCLUSION, which is worth
    saying because a mask can be set: `force_sig_info_to_task`
    (kernel/signal.c) resets the disposition to SIG_DFL and removes the
    signal from the mask before delivering a synchronous fault, so a process
    that blocks SIGSEGV and then faults dies exactly as one that never
    blocked it.

    THE SIGNALS THE ACCEPTED SET LETS THROUGH REST ON A SECOND PREMISE,
    WHICH IS THIS DEVELOPMENT'S AND NOT LINUX'S: THE ENVIRONMENT THIS
    THEOREM QUANTIFIES OVER DELIVERS NO SIGNALS AT ALL.  `State.ProcInput`
    quantifies argv, envp, the file system and stdin and quantifies no
    signal source; `sstep` has no transition a signal could arrive on;
    `State.Model` holds no disposition, mask or pending queue.  So an
    `rt_sigaction` install that `Signal.sigaction_accepted` admits is a pure
    no-op, and the SIGINT and SIGTERM it admits are exactly the signals that
    an OUTSIDE sender — not any modeled operation — could raise.  Two
    binaries that differ only in whether they installed such a handler have
    identical traces here and differ under a real signal, so the premise is
    what makes their equivalence true rather than merely provable.  It is a
    premise, stated nowhere as a hypothesis because there is no state for it
    to constrain.  Applying this theorem to a program whose environment does
    send signals is outside what it was proved about.

    THAT PREMISE HAS A SECOND HALF, AND IT IS THE ONE WITH TEETH: THE
    PROCESS STARTS WITH SIGABRT AT ITS DEFAULT DISPOSITION.
    `Kernel.Signal.tkill_self` is a modeled operation that DELIVERS a signal
    rather than merely admitting an install, so "the model holds no
    disposition" is not harmless.  The disposition a modeled operation could
    install is covered — `Signal.sigaction_accepted` declines every install
    for signal 6, which `Checks/Cases/Kernel/Signal.lean` pins as
    `rt_sigaction_sigabrt_unmodeled` — but the disposition the process
    INHERITS is not: `begin_new_exec`
    calls `flush_signal_handlers(me, 0)`, and that function resets a slot
    only `if (force_default || ka->sa.sa_handler != SIG_IGN)`, so SIG_IGN
    survives execve where a handler does not (kernel/signal.c and fs/exec.c,
    Linux v6.18.46, commit 1f99e9ab748f; execve(2) says the same).  A
    launcher that ignores SIGABRT and then execs the binary hands this model
    a process it kills and Linux does not — `get_signal`'s `if
    (ka->sa.sa_handler == SIG_IGN) continue` — which is an ACCEPTANCE of a
    trace Linux cannot produce rather than a refusal of one it can, the
    direction the design priorities (README.md) call a bug.

    IT IS A PREMISE ABOUT THE LAUNCH, in the same position as
    `Kernel.Exit.wait4_spec`'s empty child and tracee lists, and nothing here
    checks it: a launcher that does not leave SIGABRT at SIG_DFL is outside
    the model.  The premise is only reachable at all under
    `valid_input_abort`: with the declaration clear, `tkill_self` declines
    and no disposition can matter.

    `Kernel.Signal.rt_sigprocmask_spec` (135) rests on the same premise and
    leans on it hardest, being the only modeled syscall that both changes how
    a signal would be handled and REPORTS the answer back to the program.  It
    keeps the mask in `State.ProcState` and copies the entry value out
    through `oset`, so what the premise costs here is not coverage but a
    VALUE: Linux has two writers of `->blocked` that no program calls —
    `signal_delivered` (kernel/signal.c), which unions in `sa_mask` on
    handler entry, and riscv's `SYSCALL_DEFINE0(rt_sigreturn)`
    (arch/riscv/kernel/signal.c), which restores it from the sigframe — and
    neither has an arm here.  Under a delivered signal the eight bytes this
    spec hands back would be the wrong number, where a spec that merely
    declined would have been incomplete instead.  Two binaries differing only
    in what they block are not equivalent under this theorem, but the answer
    is right only while nothing is delivered.  The reasoning is in
    `Sys/Kernel/Signal.lean`'s header. -/
def unmodeled_at (mi_loaded_segments : List Segment) (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
  ( (c.cfg_ms.ms_svc_pending = none ∧
      mi_account_step mi_loaded_segments c.cfg_ms c.cfg_model = .MachineUnmodeled)
    ∨ (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
        Specs.syscall_spec (sys_input mi_loaded_segments c.cfg_ms x8) c.cfg_model .unmodeled))

/-- The run can reach a configuration the model does not cover. -/
def reaches_unmodeled (mi_loaded_segments : List Segment) (c0 : config) : Prop :=
  ∃ tr c, star mi_loaded_segments c0 tr c ∧ unmodeled_at mi_loaded_segments c

/-- Being uncovered is a special case of erroring: both uncovered shapes are
    premises of an `SError` transition.  Consequently every proof of
    `¬ reaches_error` — which the simulation library already produces for the
    well-behaved paths — discharges `¬ reaches_unmodeled` for free, and only
    the paths that genuinely fault need new reasoning. -/
theorem unmodeled_at_sstep_error (mi_loaded_segments : List Segment) (c : config)
    (h : unmodeled_at mi_loaded_segments c) :
    ∃ evs, sstep mi_loaded_segments c evs .SError := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨hh, h | h⟩ := h
  · obtain ⟨hsvc, hstep⟩ := h
    exact ⟨[], sstep.instr_unmodeled ms model hh hsvc hstep⟩
  · obtain ⟨x8, hsvc, hspec⟩ := h
    exact ⟨[], sstep.syscall_unmodeled ms model x8 hh hsvc hspec⟩

theorem reaches_unmodeled_reaches_error (mi_loaded_segments : List Segment) (c0 : config)
    (h : reaches_unmodeled mi_loaded_segments c0) :
    reaches_error mi_loaded_segments c0 := by
  obtain ⟨tr, c, hstar, hun⟩ := h
  obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error mi_loaded_segments c hun
  exact ⟨tr, c, evs, hstar, hss⟩

theorem no_error_no_unmodeled (mi_loaded_segments : List Segment) (c0 : config)
    (h : ¬ reaches_error mi_loaded_segments c0) :
    ¬ reaches_unmodeled mi_loaded_segments c0 :=
  fun hun => h (reaches_unmodeled_reaches_error mi_loaded_segments c0 hun)

/-- NON-VACUITY.  Everything above is a way of RULING OUT
    `reaches_unmodeled`, so it is worth pinning that the predicate is
    inhabited — otherwise `Equivalence.modeled` would be a clause no binary
    could ever violate, and adding it to the obligation would buy nothing.
    Every machine state the step function declines is a witness, reached in
    zero steps.  (For a CONCRETE inhabitant, closed under no hypotheses at
    all, `Checks.Examples.run_of_undecodable_image_is_unmodeled`
    and `Checks.Examples.run_of_undecodable_image_refutes_modeled` do it,
    and the fetch-side shape
    `Checks.RiscvCompressedFetch.badhex_step_unmodeled` does it from inside
    this module's own dependency closure.
    Compare `all_traces_error_reaches_error`, which guards the other
    quantifier the same way: a guard nobody can trip is a guard that guards
    nothing.) -/
theorem reaches_unmodeled_intro (mi_loaded_segments : List Segment) (ms : machine_state)
    (model : Model) (hh : m_halted model = none) (hsvc : ms.ms_svc_pending = none)
    (hstep : mi_account_step mi_loaded_segments ms model = .MachineUnmodeled) :
    reaches_unmodeled mi_loaded_segments ⟨ms, model⟩ :=
  ⟨[], ⟨ms, model⟩, star.refl _, ⟨hh, Or.inl ⟨hsvc, hstep⟩⟩⟩

/-- Every maximal execution from `c0` reaches the explicit error transition
    after finitely many steps.

    This is the accessibility predicate for the relation formed by `SNext`
    transitions, with an additional progress premise.  The progress premise
    prevents halted or stuck configurations from satisfying the predicate
    vacuously.  The recursive premise covers EVERY `SNext` successor, so one
    chosen erroring resolution cannot hide a different successor that exits
    or diverges without error.

    Being inductive is important: a configuration with an infinite `SNext`
    execution cannot construct this proof merely because an error
    alternative remains available at every finite prefix. -/
inductive all_traces_error (mi_loaded_segments : List Segment) : config → Prop where
  | intro (c : config)
      (hprog : ∃ evs to, sstep mi_loaded_segments c evs to)
      (hnext : ∀ evs c', sstep mi_loaded_segments c evs (.SNext c') →
        all_traces_error mi_loaded_segments c') :
      all_traces_error mi_loaded_segments c

/-- Universal error implies existential error.  Keeping this lemma next to
    the definitions makes the intended relationship between the two behavior
    fields explicit and guards against an accidentally vacuous universal
    predicate. -/
theorem all_traces_error_reaches_error (mi_loaded_segments : List Segment) :
    ∀ c, all_traces_error mi_loaded_segments c → reaches_error mi_loaded_segments c := by
  intro c Hall
  induction Hall with
  | intro c hprog hnext ih =>
    obtain ⟨evs, to, hstep⟩ := hprog
    cases to with
    | SNext c' =>
      obtain ⟨tr, c2, err_evs, hstar, herr⟩ := ih evs c' hstep
      exact ⟨evs ++ tr, c2, err_evs,
        star.step c evs c' tr c2 hstep hstar, herr⟩
    | SError =>
      exact ⟨[], c, evs, star.refl c, hstep⟩

/- =========================================================================
   The entry stack image: the block, then the rest of its page
   =========================================================================

   `StackLayout.build_stack_bytes` is what the kernel WRITES on the new
   stack.  What it MAPS is whole pages: the stack is a VMA, and
   `setup_arg_pages` (fs/exec.c, Linux v6.18.46, commit 1f99e9ab748f) fixes
   its top with

     `stack_top = arch_align_stack(stack_top); stack_top = PAGE_ALIGN(stack_top);`

   so `vma->vm_end` is page-aligned and every address below it inside the
   VMA is ordinary readable, writable stack.  Mapping exactly the block
   would leave the rest of the page it ends in unmapped, which is a FAULT no
   kernel produces — a sanitizer's fast unwinder, for one, bounds its frame
   walk by the page above the frame it starts from and reads up to it on
   every allocation.

   So the image is the block followed by `entry_slack`, the rest of that
   page, whose bytes are the entry's own `StackLayout.ed_slack` draw (see
   there for what Linux puts up there and why the model cannot say which
   address holds which).  Three consequences:

   - the model still stops at the page ABOVE the block, while a real stack
     VMA runs up to `PAGE_ALIGN(randomize_stack_top(STACK_TOP))`, above the
     strings and the filename.  That page is the MINIMUM every kernel maps,
     so nothing the model admits inside it is unreal; a fault the model
     reports above it may still not be a real one.
   - the top of the image never rises above the top of the user address
     space: `State.sp_window_hi` is page-aligned, so the page boundary above
     a block that `entry_stack_fits` admits is still at or below it.  That is
     `PropExec.entry_page_top_within_window`, proved where the length bound
     it needs lives; this file cannot import it.
   - no ADDRESS in the layout moves.  The slack sits above the block, so
     `StackLayout.at_random_ptr`, the string addresses and the auxv are
     exactly where the block alone puts them
     (`entry_stack_image_block_prefix`). -/

/-- The address just past the last byte the kernel WROTE. -/
def entry_block_top (sp : word) (bytes : List byte) : Int :=
  (sp.toNat : Int) + (bytes.length : Int)

/-- The address of the page boundary above the block. -/
def entry_page_top (sp : word) (bytes : List byte) : Int :=
  page_round_up_Z (entry_block_top sp bytes)

/-- The number of bytes between the block's top and that page boundary. -/
def entry_slack_len (sp : word) (bytes : List byte) : Nat :=
  (entry_page_top sp bytes - entry_block_top sp bytes).toNat

/-- The rest of the block's last page, read out of the entry's draw. -/
def entry_slack (sp : word) (bytes : List byte) (slack : word → byte) : List byte :=
  (List.range (entry_slack_len sp bytes)).map
    (fun k => slack (BitVec.ofInt 64 (entry_block_top sp bytes + Int.ofNat k)))

/-- The whole entry stack image: the block the kernel writes, then the rest
    of its last page. -/
def entry_stack_image (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    List byte :=
  let bytes := build_stack_bytes ph sp argv envp uid hwcap draw
  bytes ++ entry_slack sp bytes draw.ed_slack

/-- The page boundary is at or above the block's top: rounding up never moves
    an address down.  Everything below rests on this, so it is proved here
    rather than assumed by an `omega` at each use. -/
theorem entry_page_top_ge (sp : word) (bytes : List byte) :
    entry_block_top sp bytes ≤ entry_page_top sp bytes := by
  unfold entry_page_top page_round_up_Z page_size
  omega

theorem length_entry_slack (sp : word) (bytes : List byte) (slack : word → byte) :
    (entry_slack sp bytes slack).length = entry_slack_len sp bytes := by
  simp [entry_slack]

/-- NO ADDRESS IN THE LAYOUT MOVES: the slack is a SUFFIX, so every byte the
    kernel writes is still at the offset `build_stack_bytes` put it at.  This
    is what keeps every concrete-layout proof in the tree — the argc word,
    the argv and envp pointers, the auxv, the strings, the AT_RANDOM block —
    reading exactly what it read before the page was mapped whole. -/
theorem entry_stack_image_block_prefix (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) (i : Nat)
    (Hi : i < (build_stack_bytes ph sp argv envp uid hwcap draw).length) :
    (entry_stack_image ph sp argv envp uid hwcap draw)[i]?
      = (build_stack_bytes ph sp argv envp uid hwcap draw)[i]? := by
  show (build_stack_bytes ph sp argv envp uid hwcap draw
        ++ entry_slack sp (build_stack_bytes ph sp argv envp uid hwcap draw)
             draw.ed_slack)[i]?
      = (build_stack_bytes ph sp argv envp uid hwcap draw)[i]?
  exact List.getElem?_append_left Hi

/-- INSIDE THE BLOCK, the image answers exactly as the block does.  Every
    read-back lemma in the tree — the argc word, the argv and envp pointers,
    the auxv slots, the strings — is about an address below `entry_block_top`,
    so this is the one step each of them takes to see past the page the model
    maps whole. -/
theorem stack_to_mem_image_in_block (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) (addr : word)
    (Hlt : (addr.toNat : Int) <
      entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)) :
    stack_to_mem sp (entry_stack_image ph sp argv envp uid hwcap draw) addr
      = stack_to_mem sp (build_stack_bytes ph sp argv envp uid hwcap draw) addr := by
  have htop : entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
      = (sp.toNat : Int)
        + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) := rfl
  have himglen : (entry_stack_image ph sp argv envp uid hwcap draw).length
      = (build_stack_bytes ph sp argv envp uid hwcap draw).length
        + (entry_slack sp (build_stack_bytes ph sp argv envp uid hwcap draw)
             draw.ed_slack).length := by
    simp [entry_stack_image]
  unfold stack_to_mem
  by_cases hle : sp.toNat ≤ addr.toNat
  · rw [ite_eq_left hle, ite_eq_left hle]
    have hoffZ : (addr.toNat : Int) - (sp.toNat : Int)
        < ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) := by omega
    have hoffn : ((addr.toNat : Int) - (sp.toNat : Int)).toNat
        < (build_stack_bytes ph sp argv envp uid hwcap draw).length := by omega
    have himg : (addr.toNat : Int) - (sp.toNat : Int)
        < ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int) := by omega
    rw [ite_eq_left himg, ite_eq_left hoffZ]
    exact List.getElem?_append_left hoffn
  · rw [ite_eq_right hle, ite_eq_right hle]

/-- The image ends exactly at the page boundary above the block. -/
theorem entry_stack_image_top (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    (sp.toNat : Int)
      + ((entry_stack_image ph sp argv envp uid hwcap draw).length : Int)
      = entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) := by
  have hge : entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
      ≤ entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) :=
    entry_page_top_ge sp _
  have hlen : ((entry_slack_len sp (build_stack_bytes ph sp argv envp uid hwcap draw) : Nat) : Int)
      = entry_page_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
        - entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw) := by
    unfold entry_slack_len
    exact Int.toNat_of_nonneg (by omega)
  have hlen2 : (entry_stack_image ph sp argv envp uid hwcap draw).length
      = (build_stack_bytes ph sp argv envp uid hwcap draw).length
        + entry_slack_len sp (build_stack_bytes ph sp argv envp uid hwcap draw) := by
    simp [entry_stack_image, entry_slack]
  rw [hlen2]
  have htop : entry_block_top sp (build_stack_bytes ph sp argv envp uid hwcap draw)
      = (sp.toNat : Int)
        + ((build_stack_bytes ph sp argv envp uid hwcap draw).length : Int) := rfl
  omega

/-- ** Initial machine state at `execve`

    Sets PC (from the `Nat`-based snapshot); SP (x2) is the quantified
    `mi_init_sp`.  Populates stack memory from the argv/envp/auxv layout
    (StackLayout.lean — the auxv carries this image's `mi_phdrs`, and
    AT_UID/AT_EUID the `uid` this run is launched as); the dynamic stack
    region below SP is zero-mapped.  All other registers start at 0; no LR/SC
    reservation is held.

    `uid` is the run's `State.in_uid`, the same field `State.init_model`
    copies into the credentials the id syscalls read, so the auxv on the
    stack and `getuid`'s answer come from ONE source and cannot disagree — as
    they cannot on Linux, where `create_elf_tables` and
    `SYSCALL_DEFINE0(getuid)` both munge `current_cred()->uid` (Linux
    v6.18.46, commit 1f99e9ab748f, fs/binfmt_elf.c and kernel/sys.c; the
    `NEW_AUX_ENT(AT_UID ...)` line and the `SYSCALL_DEFINE0(getuid)` body are
    byte-identical there and at every mainline release tag from v4.4 through
    v6.18). -/
def init_machine_state (mi_loaded_segments : List Segment) (mi_init_pc : Nat)
    (mi_phdrs : PhdrInfo) (mi_init_sp : word) (mi_draw : EntryDraw)
    (argv : List (List byte)) (envp : List (List byte)) (uid : word) (hwcap : word) :
    machine_state :=
  let regs :=
    bvmapSet (2 : reg) mi_init_sp          -- sp
      (bvmapSet (10 : reg) (BitVec.ofInt 64 0)    -- a0 — 0 on Linux entry; the entry
         (bvmap_empty : BvMap word))       -- is redundant (missing keys read as
                                           -- 0) but register-file proofs match
                                           -- on the map shape, so keep it
  -- execve zeroes the FP state: an empty FP register file (missing keys read
  -- as 0) and fcsr = 0, i.e. no accrued exceptions and round-to-nearest-even
  -- as the dynamic mode.
  { ms_regs := regs
    ms_fregs := (bvmap_empty : BvMap word)
    ms_pc_val := BitVec.ofInt 64 (Int.ofNat mi_init_pc)
    ms_svc_pending := none
    ms_resv := none
    ms_fcsr := BitVec.ofInt 32 0
    ms_mem :=
      let stk := stack_to_mem mi_init_sp
        (entry_stack_image mi_phdrs mi_init_sp argv envp uid hwcap mi_draw)
      fun addr =>
        match stk addr with
        | some b => some b
        | none =>
          if decide ((mi_init_sp.toNat : Int) - stack_max_size ≤ (addr.toNat : Int)) &&
             decide ((addr.toNat : Int) < (mi_init_sp.toNat : Int))
          then some (BitVec.ofInt 8 0)
          else none
    ms_rom := fun addr =>
      match memory_read mi_loaded_segments addr 1 with
      | some (b :: _) => some b
      | _ => none }

/-- The initial configuration for one run of THIS image on the
    caller-supplied inputs `inp`. -/
def init_config (mi_loaded_segments : List Segment) (mi_init_pc : Nat)
    (mi_phdrs : PhdrInfo) (mi_init_sp mi_init_brk mi_mmap_base : word)
    (mi_draw : EntryDraw) (mi_alloc_limit : Int) (inp : ProcInput) : config :=
  ⟨init_machine_state mi_loaded_segments mi_init_pc mi_phdrs mi_init_sp mi_draw
     inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap,
   init_model (segments_reserved mi_loaded_segments) mi_init_brk mi_mmap_base
     mi_init_sp mi_alloc_limit inp⟩

/- =========================================================================
   Running a binary: the three groups of arguments
   =========================================================================

   What `execve` chooses for THIS run, as opposed to what the binary or the
   caller supplies: the initial stack pointer, the program break and the mmap
   base — all placed non-deterministically (ASLR and the layout draw:
   `valid_sp`, `valid_brk`, `valid_mmap_base`) — and
   `StackLayout.EntryDraw`, the two byte-level choices in the entry stack
   image the model does not determine: the 16 bytes of startup entropy
   AT_RANDOM points at (`get_random_bytes` in `create_elf_tables`,
   fs/binfmt_elf.c, Linux v6.18.46, commit 1f99e9ab748f; see `mi_draw` above
   and `StackLayout.at_random_bytes`), and the bytes of the entry stack's
   last page above the block (`entry_slack`).  All four fields are quantified
   independently per binary in `Equivalence.strong_universal_T`.

   Three of the four have a window and appear in `valid_entry`; the draw has
   none, because every value of either of its halves is one a kernel can
   produce.  That asymmetry is the whole of what the field costs a consumer:
   a statement quantifying over entries covers more dimensions and gains no
   hypothesis to discharge.

   The two draws are ONE field rather than two because they are one thing:
   the bytes of the initial stack image that the kernel settles and this
   model does not.  Splitting them would put a second unconstrained field
   beside the first and change no statement.

   The register file needs no field: on Linux entry every register but sp is
   0 (argc/argv live on the stack), so `init_machine_state` pins them
   architecturally. -/
structure ExecEntry where
  /-- The initial stack pointer. -/
  en_sp        : word
  /-- The initial program break. -/
  en_brk       : word
  /-- The run's `mm->mmap_base`. -/
  en_mmap_base : word
  /-- The entry's two byte-level draws (AT_RANDOM and the slack). -/
  en_draw      : EntryDraw

/-- Everything observable about one binary on one input.  The record
    arguments are the three sources the run draws on: the ELF-derived image
    (`MemImageType.Image`), the values `execve` picked for this process
    (`ExecEntry`), and the caller-supplied inputs (`State.ProcInput`,
    declared next to `State.init_model`, the first function that consumes it,
    and validated by `valid_input` below); `lim` is the environment's backed
    anonymous-memory budget (`mi_alloc_limit` — a bare capacity in bytes, not
    a record: it is neither image data, nor an `execve` choice, nor caller
    input, and `Equivalence.strong_equiv` pins it per role).

    NOTE.  This is written as a `match` on the image and the
    `execve` entry so that `cbn [run …]` gets the underlying `init_config`
    application back as soon as those two arguments are concrete records.
    Lean's structure projections reduce on concrete records in exactly the
    same way, so the definition reads the fields directly; `simp [run]` and
    `cases img` therefore recover `init_config`. -/
def run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  let c0 := init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
  { bh_traces := obs_trace img.img_segments c0
    bh_errors := reaches_error img.img_segments c0
    bh_all_errors := all_traces_error img.img_segments c0
    bh_unmodeled := reaches_unmodeled img.img_segments c0 }

/- =========================================================================
   Spurious environment failures, per family: `SpuriousCfg` and `run_scfg`
   =========================================================================

   ** What is being parameterised

   Some syscall arms answer an errno the model cannot DERIVE from its state:
   `openat` of a file that exists may still fail with -ENOMEM or -EACCES,
   `dup` with -EMFILE, `mmap` with -ENOMEM while budget remains, `getrandom`
   with -EINTR.  Each such arm draws from a per-syscall list with
   `Syscall.errno_from` under an `alt` beside the answer the state does
   determine, so that the failure stays LIVE — a target that deleted the
   source's error handling would otherwise remain equivalent.  Under every
   statement above this section that is the only reading: the environment may
   refuse at any such call.

   That reading makes two things unprovable that a task may want.  An
   error-free statement about a program whose out-of-memory path aborts, when
   its allocations never come near the budget; and any `Classifier.decides`
   statement about a classifier that reads its input file, because a run on
   which the open is refused reaches neither verdict.  So a task chooses, per
   FAMILY of injected failure, between two readings:

     - MAY FAIL: the default reading, the one every statement above has;
     - FAILS ONLY IF FORCED: the arm's errno is admitted only where the
       model's state leaves no other answer.

   `SpuriousCfg` is that choice, one boolean per family, `true` meaning
   "may fail".  `may_fail_cfg` is the reading every existing statement keeps
   (`run_scfg_may_fail` below), `forced_only_cfg` is the other extreme, and
   `alloc_only_cfg b` is the one-switch form for the allocation family.  The
   configuration is a parameter of a STATEMENT, fixed by the sealed module
   type a checker ascribes (`Equivalence.SPEC_SCFG`); it is not a field of
   the model and not a quantified draw, so nothing under `Sys/` and nothing
   in `State` changes.

   ** The six families, and where "forced" comes from

   The table below (`injected_table`) lists every arm that injects, by syscall
   number, with its family and the list it draws from — the very lists the
   specs use, so the two cannot drift.  What "forced" means per family is not
   written anywhere as a state test; it is READ OFF THE SPEC by the
   definition of `spurious_refusal_cfg`, and this is what each family's
   forcing condition comes to:

     alloc  mmap, brk, mremap, mprotect   the shape's budget test fails,
                                          or no placement exists
     fs     openat, faccessat, unlinkat,  openat: no free descriptor;
            getcwd                        the others: never
     fd     dup, pipe2, socket,           no free descriptor (two for
            socketpair, accept, clone     pipe2 and socketpair; accept
                                          also when `Socket.conn_ix_exhausted`);
                                          clone: never
     net    bind, listen                  never
     cred   setuid, setgid, setresuid,    never; setsid's -EPERM after a
            setresgid, setsid             success is deterministic and
                                          keyed on `State.m_setsid_succeeded`
     intr   getrandom, nanosleep          never (the model delivers no
                                          signals)

   A family whose refusal is never forced simply loses the errno under
   forced-only.  `brk` is the one arm that refuses by VALUE rather than by
   errno — a grow or shrink that answers the OLD break — so its entry carries
   no errno list and `brk_refusal_b` names the refusal.

   ** How the filter is stated, and why it is exact

   `spurious_refusal_cfg cfg i m eff` holds when the syscall's family is
   forced-only in `cfg`, `eff` is one of that syscall's refusals, AND the
   spec admits at `(i, m)` some outcome that is NOT one — a success, or an
   errno the state determines.  A refusal is removed only where it was
   avoidable.

   So the filter is exact BY CONSTRUCTION rather than by mirroring each arm's
   branch structure.  An errno the state forces — the budget is spent, the
   descriptor table is full, `setsid` already succeeded — is the only answer
   at its state, so no non-refusal outcome exists there and it is kept.  An
   answer the state DETERMINES is never removed: if the spec admits it beside
   an injected errno at one state, then by the spec's own construction it is
   the answer the injection stands beside, and it is not a refusal.  A wrong
   or over-inclusive errno list can therefore only lose filtering; it can
   never remove an answer Linux is forced to give.  What the design pays for
   that is the third conjunct being an existential over spec outcomes rather
   than a boolean; see the KNOWN GAP below.

   ** The filtered run is a subset of `run`

   `sstep_cfg cfg` is `sstep` with one extra premise on the two constructors
   that consume a syscall outcome: the outcome is not a spurious refusal.  So
   every filtered step is a step (`sstep_cfg_sub`), every filtered trace,
   error and uncovered point is one of the run's (`obs_trace_cfg_sub`,
   `reaches_error_cfg_sub`, `reaches_unmodeled_cfg_sub`), and at
   `may_fail_cfg` the premise is vacuous and the two relations coincide
   (`sstep_cfg_may_fail`, `run_scfg_may_fail`).  Forced-only REMOVES
   executions and adds none.  It is also monotone in the configuration
   (`sstep_cfg_mono`): turning a family off removes steps and never adds one.

   ** KNOWN GAP: the executable checker certifies the may-fail reading

   `Checks.ExecutableSpecs` decides membership of ONE outcome in the spec, and
   `Checks.Progress` exhibits ONE admissible outcome per input — for `mmap`
   and `openat`, the errno.  Neither answers the question the forced-only
   filter asks: whether a NON-REFUSAL outcome exists at `(i, m)`.  For most
   families that is a descriptor-table test, but for `mmap` and `mremap` it is
   a placement question — is there a free page-aligned range below
   `State.alloc_top` — and nothing in the trusted tree computes one.
   `refusal_decided` below names exactly that question; `sstep_cfg_progress`
   shows the filtered run never gets stuck where it is answered, so a
   computable placement witness is what would close the gap for the allocation
   family.  Until then a proof made under forced-only answers the placement
   question itself, at the calls it reasons about, exactly as the simulation
   library already exhibits placements for the success path. -/

/-- The six families of injected environment failure. -/
inductive SpuriousFamily where
  | FamAlloc | FamFs | FamFd | FamNet | FamCred | FamIntr
  deriving DecidableEq, Repr

/-- One boolean per family: `true` = "always allowed to fail" (the reading
    every statement above this section has), `false` = "fails only if
    forced".  A record rather than a function so the generated checker can
    spell a configuration as a literal. -/
structure SpuriousCfg where
  sc_alloc : Bool
  sc_fs    : Bool
  sc_fd    : Bool
  sc_net   : Bool
  sc_cred  : Bool
  sc_intr  : Bool
  deriving DecidableEq, Repr

def may_fail_cfg : SpuriousCfg := ⟨true, true, true, true, true, true⟩
def forced_only_cfg : SpuriousCfg := ⟨false, false, false, false, false, false⟩

/-- The one-switch form: the allocation family alone, every other family left
    at may-fail. -/
def alloc_only_cfg (alloc_may_fail : Bool) : SpuriousCfg :=
  ⟨alloc_may_fail, true, true, true, true, true⟩

def family_may_fail (cfg : SpuriousCfg) (f : SpuriousFamily) : Bool :=
  match f with
  | .FamAlloc => cfg.sc_alloc
  | .FamFs    => cfg.sc_fs
  | .FamFd    => cfg.sc_fd
  | .FamNet   => cfg.sc_net
  | .FamCred  => cfg.sc_cred
  | .FamIntr  => cfg.sc_intr

/-- `cfg1` admits no family `cfg2` does not: the pointwise order on the six
    booleans.  `forced_only_cfg` is its least element and `may_fail_cfg` its
    greatest. -/
def cfg_le (cfg1 cfg2 : SpuriousCfg) : Prop :=
  ∀ f, family_may_fail cfg1 f = true → family_may_fail cfg2 f = true

theorem cfg_le_refl (cfg : SpuriousCfg) : cfg_le cfg cfg := fun _ h => h

theorem forced_only_cfg_least (cfg : SpuriousCfg) : cfg_le forced_only_cfg cfg := by
  intro f h
  cases f <;> exact absurd h (by decide)

theorem may_fail_cfg_greatest (cfg : SpuriousCfg) : cfg_le cfg may_fail_cfg := by
  intro f _
  cases f <;> rfl

/-- One injecting arm: the syscall number, its family, and the errnos its
    `Syscall.errno_from` draws from — the spec's own list, named rather than
    copied.

     `ia_no` is a `Nat`; the syscall number it is compared
    against comes from `bv_unsigned (in_sysno i)`, which is non-negative, so
    the two are compared with `=`. -/
structure InjectedArm where
  ia_no     : Nat
  ia_family : SpuriousFamily
  ia_errnos : List Int
  deriving DecidableEq, Repr

/-- Every arm of `Sys.SyscallTable.spec_table` that injects, SORTED BY
    SYSCALL NUMBER like that table and for the same reason (two changes that
    add two arms land at different lines).  `brk` refuses by value and
    carries no list; see `brk_refusal_b`.  `nanosleep`'s -EINTR and `setsid`'s
    -EPERM are injected by a bare `alt` rather than through a named list, so
    their lists are written here. -/
def injected_table : List InjectedArm :=
  [ ⟨ 17, .FamFs,   Sys.Fs.DPath.getcwd_errnos⟩            -- getcwd
  , ⟨ 23, .FamFd,   Sys.Fs.File.dup_errnos⟩                -- dup
  , ⟨ 35, .FamFs,   Sys.Fs.Namei.unlinkat_errnos⟩          -- unlinkat
  , ⟨ 48, .FamFs,   Sys.Fs.Open.faccessat_errnos⟩          -- faccessat
  , ⟨ 56, .FamFs,   Sys.Fs.Open.openat_errnos⟩             -- openat
  , ⟨ 59, .FamFd,   Sys.Fs.Pipe.pipe2_errnos⟩              -- pipe2
  , ⟨101, .FamIntr, [EINTR]⟩                              -- nanosleep
  , ⟨144, .FamCred, Sys.Kernel.Sys.setid_errnos true⟩      -- setgid
  , ⟨146, .FamCred, Sys.Kernel.Sys.setid_errnos true⟩      -- setuid
  , ⟨147, .FamCred, Sys.Kernel.Sys.setid_errnos true⟩      -- setresuid
  , ⟨149, .FamCred, Sys.Kernel.Sys.setid_errnos true⟩      -- setresgid
  , ⟨157, .FamCred, [EPERM]⟩                              -- setsid
  , ⟨198, .FamFd,   Sys.Net.Socket.socket_errnos⟩          -- socket
  , ⟨199, .FamFd,   Sys.Net.Socket.socketpair_reserve_errnos
                      ++ Sys.Net.Socket.socketpair_create_errnos⟩  -- socketpair
  , ⟨200, .FamNet,  Sys.Net.Socket.bind_errnos⟩            -- bind
  , ⟨201, .FamNet,  Sys.Net.Socket.listen_errnos⟩          -- listen
  , ⟨202, .FamFd,   Sys.Net.Socket.accept_errnos⟩          -- accept
  , ⟨214, .FamAlloc, []⟩                                  -- brk
  , ⟨216, .FamAlloc, Sys.Mm.Mremap.mremap_errnos⟩          -- mremap
  , ⟨220, .FamFd,   Sys.Kernel.Fork.clone_errnos⟩          -- clone
  , ⟨222, .FamAlloc, Sys.Mm.Mmap.mmap_errnos⟩              -- mmap
  , ⟨226, .FamAlloc, Sys.Mm.Mprotect.mprotect_errnos⟩      -- mprotect
  , ⟨242, .FamFd,   Sys.Net.Socket.accept_errnos⟩          -- accept4
  , ⟨278, .FamIntr, Sys.Drivers.Char.Random.getrandom_errnos⟩  -- getrandom
  , ⟨435, .FamFd,   Sys.Kernel.Fork.clone_errnos⟩          -- clone3
  ]

/-- Look a syscall number up in an injecting-arm table. -/
def lookup_injected : List InjectedArm → Nat → Option InjectedArm
  | [], _ => none
  | a :: r, n => if a.ia_no = n then some a else lookup_injected r n

/-- The injecting arm for a syscall number, keyed exactly as
    `Sys.Dispatch.dispatch` keys the spec table. -/
def injected_arm (no : Nat) : Option InjectedArm := lookup_injected injected_table no

/-- `r` is one of the errno returns in `es`. -/
def ret_in_errnos (es : List Int) (r : word) : Bool :=
  es.any (fun e => bv_eqb r (errno_ret e))

/-- `brk req` answered `ret` from the pre-step model `m`: a refusal iff `req`
    is a real request (neither the query nor an address below
    `Mmap.min_brk`, both of which the state answers with the old break), asks
    to MOVE the break, and the answer is the old break unmoved.  Mirrors the
    three paths of `Mmap.brk_r_ok`. -/
def brk_refusal_b (m : Model) (req ret : word) : Bool :=
  let h := m_vmmaps m
  let b := h.vm_brk
  !(Sys.Syscall.w_is0 req)
  && !(decide ((req.toNat : Int) < ((Sys.Mm.Mmap.min_brk h).toNat : Int)))
  && !(bv_eqb req b)
  && bv_eqb ret b

/-- Is the answer `ret` to the syscall `i` at model `m` one of its injected
    refusals?  For every arm but `brk`, one of the listed errnos; for `brk`,
    the old break on a request to move it.  A syscall with no injecting arm
    has no refusals. -/
def refusal_b (i : SyscallInput) (m : Model) (ret : word) : Bool :=
  let no := i.in_sysno.toNat
  if no = 214 then brk_refusal_b m (in_arg i 0) ret
  else match injected_arm no with
       | some a => ret_in_errnos a.ia_errnos ret
       | none => false

/-- Is the pending syscall `i` at model `m` a grant the BUDGET refuses?  Every
    `FamAlloc` arm of `injected_table`, each answered by the mark its own file
    defines beside its spec (`Mmap.brk_budget_refused_b`,
    `Mremap.mremap_budget_refused_b`, `Mmap.mmap_budget_refused_b`,
    `Mprotect.mprotect_budget_refused_b`) on the arguments
    `Sys.SyscallTable.spec_table` hands the arm; every other number is
    `false`.  Compare `refusal_b`, which asks whether a given ANSWER is a
    refusal; this asks whether the REQUEST is one the budget declines,
    whatever answer is then drawn.

    THE `false` IS THE DANGEROUS ANSWER: an allocation arm this dispatcher
    does not know is a silent false negative of the budget premise.  Two pins
    keep the enumeration complete.  `alloc_family_dispatched` proves that
    every number `injected_table` registers under `FamAlloc` is in
    `alloc_mark_sysnos`, and `alloc_budget_refused_b_outside` that the
    dispatcher answers `false` exactly off that list, so a fifth `FamAlloc`
    arm fails to build until the list and the dispatcher learn it.  What this
    tree cannot see is an arm that consults the budget without registering as
    injecting, so that rule is stated here instead: every file under `Sys/`
    that names a budget reader must define a `*_budget_refused_b` this
    dispatcher names. -/
def alloc_mark_sysnos : List Nat := [214, 216, 222, 226]

def alloc_budget_refused_b (i : SyscallInput) (m : Model) : Bool :=
  let no := i.in_sysno.toNat
  if no = 214 then Sys.Mm.Mmap.brk_budget_refused_b m (in_arg i 0)
  else if no = 216 then
    Sys.Mm.Mremap.mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) m
  else if no = 222 then
    Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) (in_arg i 4) (in_arg i 5) m
  else if no = 226 then
    Sys.Mm.Mprotect.mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  else false

/-! ## Classifying a budget refusal: oversize vs cumulative

    `alloc_budget_refused_b` records that a request was refused for
    budget, not why.  `alloc_refuse_reason` reads the same pre-state and
    request and gives `.RefuseOversize` when the request's charge alone
    exceeds `State.vm_limit`, and `.RefuseBudget` otherwise.  It adds no
    transition; each arm still answers its own refusal (-ENOMEM, or the
    unmoved break for `brk`).  The threshold is the budget, not a
    per-request cap.

    A premise built on `budget_only_refused_at` (below) still excludes: a
    cumulative refusal of a request that fits the budget alone, whatever
    controls its size; every first-touch refusal of a MAP_NORESERVE
    mapping; and a `brk` whose growth fits the budget but whose heap does
    not (the charge is the growth above the current break). -/
inductive RefuseReason : Type
  | RefuseBudget
  | RefuseOversize
  deriving DecidableEq, Repr

/-- The charge of the pending request: the byte growth above the current
    break for `brk`, the page-rounded length or new size for the others,
    and 0 for any other syscall.  The argument indices are those of
    `alloc_budget_refused_b`; the per-arm lemmas below tie this charge to
    each arm's gate. -/
def alloc_req_charge_bytes (i : SyscallInput) (m : Model) : Int :=
  let no := i.in_sysno.toNat
  if no = 214 then
    max 0 (((in_arg i 0).toNat : Int) - (((m_vmmaps m).vm_brk).toNat : Int))
  else if no = 216 then page_round_up_Z ((in_arg i 2).toNat : Int)
  else if no = 222 then page_round_up_Z ((in_arg i 1).toNat : Int)
  else if no = 226 then page_round_up_Z ((in_arg i 1).toNat : Int)
  else 0

/-- The classified budget refusal.  `none` exactly when the request is
    not budget-refused at all; otherwise the cause.  `.RefuseOversize`
    takes priority: a refused request whose charge alone exceeds the whole
    budget is classified oversize, however much budget is left. -/
def alloc_refuse_reason (i : SyscallInput) (m : Model) : Option RefuseReason :=
  if alloc_budget_refused_b i m then
    if (m_vmmaps m).vm_limit < alloc_req_charge_bytes i m then
      some .RefuseOversize  -- the request alone exceeds the budget
    else some .RefuseBudget -- refused only by cumulative use
  else none

/-- Faithfulness: the classifier refines `alloc_budget_refused_b` and
    changes nothing — it fires on exactly the configurations the mark
    already fires on, so no new input is excluded or admitted. -/
theorem alloc_refuse_reason_none_iff_not_refused (i : SyscallInput) (m : Model) :
    alloc_refuse_reason i m = none ↔ alloc_budget_refused_b i m = false := by
  unfold alloc_refuse_reason
  by_cases hb : alloc_budget_refused_b i m = true
  · rw [ite_eq_left hb]
    constructor
    · intro h
      split at h <;> simp at h
    · intro h
      simp [hb] at h
  · rw [ite_eq_right hb]
    have hf : alloc_budget_refused_b i m = false := by
      cases hv : alloc_budget_refused_b i m <;> simp_all
    rw [hf]
    simp

/-! ### The charge is the refusing gate's own charge, arm by arm

    For each `FamAlloc` arm: where its mark fires, the budget gate the
    arm consults is false when applied to `alloc_req_charge_bytes`.  For
    `brk` the gate is `vm_backing_used + charge ≤ vm_limit` verbatim;
    for the other arms the charge is the page-rounded size `n` each gate
    is applied to. -/
theorem alloc_req_charge_brk (i : SyscallInput) (m : Model)
    (Hno : i.in_sysno.toNat = 214)
    (Hb : alloc_budget_refused_b i m = true) :
    0 < alloc_req_charge_bytes i m
    ∧ Sys.Mm.Mmap.brk_budget_ok m (in_arg i 0)
        = decide (vm_backing_used m + alloc_req_charge_bytes i m
                  ≤ (m_vmmaps m).vm_limit)
    ∧ Sys.Mm.Mmap.brk_budget_ok m (in_arg i 0) = false := by
  unfold alloc_budget_refused_b at Hb
  rw [ite_eq_left Hno] at Hb
  unfold Sys.Mm.Mmap.brk_budget_refused_b at Hb
  dsimp only at Hb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at Hb
  obtain ⟨⟨⟨-, Hpos⟩, Hgt⟩, Hok⟩ := Hb
  rw [decide_eq_true_eq] at Hpos
  rw [decide_eq_true_eq] at Hgt
  rw [Bool.not_eq_true'] at Hok
  have hbrk : (((m_vmmaps m).vm_brk).toNat : Int) < ((in_arg i 0).toNat : Int) := Hgt
  have hgt : 0 < ((in_arg i 0).toNat : Int) - (((m_vmmaps m).vm_brk).toNat : Int) := by
    omega
  have hc : alloc_req_charge_bytes i m
      = ((in_arg i 0).toNat : Int) - (((m_vmmaps m).vm_brk).toNat : Int) := by
    unfold alloc_req_charge_bytes
    rw [ite_eq_left Hno]
    omega
  have hsz : (((in_arg i 0) - (m_vmmaps m).vm_brk).toNat : Int)
      = ((in_arg i 0).toNat : Int) - (((m_vmmaps m).vm_brk).toNat : Int) := by
    have hle : (m_vmmaps m).vm_brk ≤ in_arg i 0 := by
      rw [BitVec.le_def]
      have := bv_unsigned_range_u64 (in_arg i 0)
      have := bv_unsigned_range_u64 ((m_vmmaps m).vm_brk)
      omega
    rw [BitVec.toNat_sub_of_le hle]
    have hb := bv_unsigned_range_u64 ((m_vmmaps m).vm_brk)
    have hr := bv_unsigned_range_u64 (in_arg i 0)
    omega
  refine ⟨?_, ?_, Hok⟩
  · rw [hc]; exact hgt
  · unfold Sys.Mm.Mmap.brk_budget_ok
    dsimp only
    rw [hsz, hc]

/-- The `mremap` arm: the charge is the page-rounded new size, and where
    the mark fires neither resolution of the grow is budget-admitted at
    it. -/
theorem alloc_req_charge_mremap (i : SyscallInput) (m : Model)
    (Hno : i.in_sysno.toNat = 216)
    (Hb : alloc_budget_refused_b i m = true) :
    page_round_up_Z ((in_arg i 1).toNat : Int) < alloc_req_charge_bytes i m
    ∧ Sys.Mm.Mremap.mremap_inplace_grow_b m (in_arg i 0)
        (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))
        (BitVec.ofInt 64 (alloc_req_charge_bytes i m))
        (page_round_up_Z ((in_arg i 1).toNat : Int))
        (alloc_req_charge_bytes i m) = false
    ∧ Sys.Mm.Mremap.mremap_move_budget_b m (in_arg i 0)
        (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))
        (BitVec.ofInt 64 (alloc_req_charge_bytes i m)) = false := by
  have hc : alloc_req_charge_bytes i m = page_round_up_Z ((in_arg i 2).toNat : Int) := by
    unfold alloc_req_charge_bytes
    rw [ite_eq_right (by omega), ite_eq_left Hno]
  unfold alloc_budget_refused_b at Hb
  rw [ite_eq_right (by omega), ite_eq_left Hno] at Hb
  unfold Sys.Mm.Mremap.mremap_budget_refused_b at Hb
  dsimp only at Hb
  by_cases h1 : (!(((in_arg i 3).toNat : Int) == Sys.Uapi.MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left h1] at Hb; simp at Hb
  · rw [ite_eq_right h1] at Hb
    by_cases h2 : (!((((in_arg i 0).toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left h2] at Hb; simp at Hb
    · rw [ite_eq_right h2] at Hb
      by_cases h3 : Sys.Mm.Mremap.page_align_is0_b (in_arg i 2) = true
      · rw [ite_eq_left h3] at Hb; simp at Hb
      · rw [ite_eq_right h3] at Hb
        by_cases h4 : (TASK_SIZE : Int) < page_round_up_Z ((in_arg i 2).toNat : Int)
        · rw [ite_eq_left h4] at Hb; simp at Hb
        · rw [ite_eq_right h4] at Hb
          by_cases h5 : Sys.Mm.Mremap.page_align_is0_b (in_arg i 1) = true
          · rw [ite_eq_left h5] at Hb; simp at Hb
          · rw [ite_eq_right h5] at Hb
            by_cases h6 : (!(Sys.Mm.Mremap.mremap_source_b (m_vmmaps m) (in_arg i 0)
                             (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))
                             (page_round_up_Z ((in_arg i 1).toNat : Int))
                           && Sys.Mm.Mremap.mremap_backing_uniform_b m (in_arg i 0)
                                (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))))) = true
            · rw [ite_eq_left h6] at Hb; simp at Hb
            · rw [ite_eq_right h6] at Hb
              by_cases h7 : page_round_up_Z ((in_arg i 2).toNat : Int)
                  ≤ page_round_up_Z ((in_arg i 1).toNat : Int)
              · rw [ite_eq_left h7] at Hb; simp at Hb
              · rw [ite_eq_right h7] at Hb
                rw [Bool.not_eq_true'] at Hb
                obtain ⟨hip, hmv⟩ := Bool.or_eq_false_iff.mp Hb
                rw [hc]
                exact ⟨by omega, hip, hmv⟩

/-- The `mmap` arm: the charge is the page-rounded length, and where the
    mark fires ONE of the three budget gates the rw and anonymous shapes
    consult is false at it. -/
theorem alloc_req_charge_mmap (i : SyscallInput) (m : Model)
    (Hno : i.in_sysno.toNat = 222)
    (Hb : alloc_budget_refused_b i m = true) :
    Sys.Mm.Mmap.mmap_noreserve_backed_ok (in_arg i 3) m (alloc_req_charge_bytes i m) = false
    ∨ Sys.Mm.Mmap.mmap_fixed_rw_budget_ok (in_arg i 3) m (in_arg i 0)
        (BitVec.ofInt 64 (alloc_req_charge_bytes i m)) = false
    ∨ Sys.Mm.Mmap.mmap_fixed_rw_span_budget_ok (in_arg i 3) m (in_arg i 0)
        (BitVec.ofInt 64 (alloc_req_charge_bytes i m)) = false := by
  have hc : alloc_req_charge_bytes i m = page_round_up_Z ((in_arg i 1).toNat : Int) := by
    unfold alloc_req_charge_bytes
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left Hno]
  rw [hc]
  unfold alloc_budget_refused_b at Hb
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left Hno] at Hb
  unfold Sys.Mm.Mmap.mmap_budget_refused_b at Hb
  dsimp only at Hb
  -- The argument gates: `Hb` can be `true` only down the `else` side.
  have d1 : ¬((!Sys.Mm.Mmap.mmap_off_aligned_b (in_arg i 5)) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d1] at Hb
  have d2 : ¬((!Sys.Mm.Mmap.mmap_anon_b (in_arg i 3)) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d2] at Hb
  have d3 : ¬(Sys.Syscall.w_is0 (in_arg i 1) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d3] at Hb
  -- the anonymous shape: its gate IS the charge's
  by_cases h4 : Sys.Mm.Mmap.mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h4] at Hb
    rw [Bool.not_eq_true'] at Hb
    exact Or.inl Hb
  rw [ite_eq_right h4] at Hb
  have d5 : ¬(Sys.Mm.Mmap.mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d5] at Hb
  have d6 : ¬(Sys.Mm.Mmap.mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d6] at Hb
  by_cases h7 : Sys.Mm.Mmap.mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h7] at Hb
    -- the address gates of the placed rw request
    have e1 : ¬(two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right e1] at Hb
    have e2 : ¬(¬(((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int) ≤ alloc_top (m_vmmaps m))) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right e2] at Hb
    have e3 : ¬((!(((in_arg i 0).toNat : Int) % page_size == 0)) = true) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right e3] at Hb
    have e4 : ¬(¬(0 < ((in_arg i 0).toNat : Int))) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right e4] at Hb
    -- a contained request
    by_cases e5 : (region_free (m_vmmaps m).vm_reserved (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
        map_contains (m_vmmaps m).vm_maps (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))) = true
    · rw [ite_eq_left e5] at Hb
      rw [Bool.not_eq_true'] at Hb
      exact Or.inr (Or.inl Hb)
    rw [ite_eq_right e5] at Hb
    -- a request over free pages: the anonymous gate again
    by_cases e6 : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
        (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
    · rw [ite_eq_left e6] at Hb
      rw [Bool.not_eq_true'] at Hb
      exact Or.inl Hb
    rw [ite_eq_right e6] at Hb
    -- a spanning request
    by_cases e7 : region_free (m_vmmaps m).vm_reserved (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
    · rw [ite_eq_left e7] at Hb
      rw [Bool.not_eq_true'] at Hb
      exact Or.inr (Or.inr Hb)
    rw [ite_eq_right e7] at Hb
    simp at Hb
  rw [ite_eq_right h7] at Hb
  have d8 : ¬(Sys.Mm.Mmap.mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d8] at Hb
  by_cases h9 : Sys.Mm.Mmap.mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true
  · rw [ite_eq_left h9] at Hb
    have f1 : ¬(two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right f1] at Hb
    have f2 : ¬(¬(((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int) ≤ alloc_top (m_vmmaps m))) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right f2] at Hb
    have f3 : ¬((!(((in_arg i 0).toNat : Int) % page_size == 0)) = true) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right f3] at Hb
    have f4 : ¬(¬(0 < ((in_arg i 0).toNat : Int))) := by
      intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
    rw [ite_eq_right f4] at Hb
    by_cases f5 : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
        (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) = true
    · rw [ite_eq_left f5] at Hb
      rw [Bool.not_eq_true'] at Hb
      exact Or.inl Hb
    rw [ite_eq_right f5] at Hb
    simp at Hb
  rw [ite_eq_right h9] at Hb
  simp at Hb

/-- The `mprotect` arm: the charge is the page-rounded length, and where
    the mark fires the exposure's gate is false at it. -/
theorem alloc_req_charge_mprotect (i : SyscallInput) (m : Model)
    (Hno : i.in_sysno.toNat = 226)
    (Hb : alloc_budget_refused_b i m = true) :
    Sys.Mm.Mprotect.mprotect_budget_ok m (in_arg i 0)
      (BitVec.ofInt 64 (alloc_req_charge_bytes i m)) = false := by
  have hc : alloc_req_charge_bytes i m = page_round_up_Z ((in_arg i 1).toNat : Int) := by
    unfold alloc_req_charge_bytes
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left Hno]
  rw [hc]
  unfold alloc_budget_refused_b at Hb
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left Hno] at Hb
  unfold Sys.Mm.Mprotect.mprotect_budget_refused_b at Hb
  dsimp only at Hb
  have d1 : ¬(Sys.Mm.Mprotect.mprotect_grows_conflict_b (in_arg i 2) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d1] at Hb
  have d2 : ¬((!(((in_arg i 0).toNat : Int) % page_size == 0)) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d2] at Hb
  have d3 : ¬(Sys.Syscall.w_is0 (in_arg i 1) = true) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d3] at Hb
  have d4 : ¬(two_pow_64 ≤ ((in_arg i 0).toNat : Int) + page_round_up_Z ((in_arg i 1).toNat : Int)) := by
    intro hh; rw [ite_eq_left hh] at Hb; simp at Hb
  rw [ite_eq_right d4] at Hb
  by_cases h5 : Sys.Mm.Mprotect.mprotect_modeled_b (in_arg i 2) = true
  · rw [ite_eq_left h5] at Hb
    by_cases h6 : (map_contains (m_vmmaps m).vm_noaccess (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) &&
        map_contains (m_vmmaps m).vm_maps (in_arg i 0) (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))) = true
    · rw [ite_eq_left h6] at Hb
      rw [Bool.not_eq_true'] at Hb
      exact Hb
    rw [ite_eq_right h6] at Hb
    simp at Hb
  rw [ite_eq_right h5] at Hb
  simp at Hb

theorem lookup_injected_in : ∀ (t : List InjectedArm) (n : Nat) (a : InjectedArm),
    lookup_injected t n = some a → a ∈ t ∧ a.ia_no = n := by
  intro t
  induction t with
  | nil => intro n a h; exact absurd h (by simp [lookup_injected])
  | cons x r ih =>
    intro n a h
    by_cases hx : x.ia_no = n
    · simp only [lookup_injected, ite_eq_left hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨List.mem_cons_self .., hx⟩
    · simp only [lookup_injected, ite_eq_right hx] at h
      obtain ⟨h1, h2⟩ := ih n a h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- Every `FamAlloc` arm is dispatched: by case analysis over the table, so an
    arm added to it under `FamAlloc` breaks this proof until
    `alloc_mark_sysnos` and the dispatcher carry its number. -/
theorem alloc_family_dispatched (no : Nat) (a : InjectedArm)
    (H : injected_arm no = some a) (Hf : a.ia_family = .FamAlloc) :
    no ∈ alloc_mark_sysnos := by
  obtain ⟨Hin, rfl⟩ := lookup_injected_in _ _ _ H
  have hcheck : (injected_table.all (fun a =>
      !(decide (a.ia_family = .FamAlloc)) || alloc_mark_sysnos.contains a.ia_no))
      = true := by decide
  have h := List.all_eq_true.mp hcheck a Hin
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact absurd Hf (by simpa using h)
  · exact h

/-- ... every number ON the list is dispatched to its arm's mark — so a number
    added to `alloc_mark_sysnos` without a dispatcher arm goes red here rather
    than falling to the `false` default ... -/
theorem alloc_mark_sysnos_dispatched (i : SyscallInput) (m : Model) :
    (i.in_sysno.toNat = 214 ->
        alloc_budget_refused_b i m = Sys.Mm.Mmap.brk_budget_refused_b m (in_arg i 0))
    ∧ (i.in_sysno.toNat = 216 ->
        alloc_budget_refused_b i m
        = Sys.Mm.Mremap.mremap_budget_refused_b (in_arg i 0) (in_arg i 1)
            (in_arg i 2) (in_arg i 3) m)
    ∧ (i.in_sysno.toNat = 222 ->
        alloc_budget_refused_b i m
        = Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2)
            (in_arg i 3) (in_arg i 4) (in_arg i 5) m)
    ∧ (i.in_sysno.toNat = 226 ->
        alloc_budget_refused_b i m
        = Sys.Mm.Mprotect.mprotect_budget_refused_b (in_arg i 0) (in_arg i 1)
            (in_arg i 2) m) := by
  /- `simp [E]`, not `rw [E]`: rewriting the number builds an `Eq.rec`
     whose motive is the WHOLE unfolded four-arm chain, and the kernel
     answers "(kernel) deep recursion detected" on the term.  `simp`
     rewrites the same occurrence without packaging both branches — the
     `ite_eq_left`-vs-`simp only` distinction the Checks section records for
     the checkers, met here in a definition rather than a hypothesis. -/
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro E; simp [alloc_budget_refused_b, E])

/-- ... and the dispatcher answers `false` exactly off the list, which ties
    `alloc_mark_sysnos` to the numbers it tests. -/
theorem alloc_budget_refused_b_outside (i : SyscallInput) (m : Model)
    (Hout : i.in_sysno.toNat ∉ alloc_mark_sysnos) :
    alloc_budget_refused_b i m = false := by
  unfold alloc_budget_refused_b
  by_cases h1 : i.in_sysno.toNat = 214
  · exact absurd (by rw [h1]; decide) Hout
  · by_cases h2 : i.in_sysno.toNat = 216
    · exact absurd (by rw [h2]; decide) Hout
    · by_cases h3 : i.in_sysno.toNat = 222
      · exact absurd (by rw [h3]; decide) Hout
      · by_cases h4 : i.in_sysno.toNat = 226
        · exact absurd (by rw [h4]; decide) Hout
        · simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

/-- The syscall `i` belongs to a family `cfg` reads as forced-only. -/
def injected_family_off (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match injected_arm i.in_sysno.toNat with
  | some a => !(family_may_fail cfg a.ia_family)
  | none => false

/-- The one decision a forced-only family adds to a syscall step: is this
    outcome a refusal the state did not force?  Three conjuncts — the family
    is off, the answer is a refusal, and the spec admits a non-refusal answer
    at the same input and model.  The third is what makes the filter exact;
    see this section's header. -/
def spurious_refusal_cfg (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) : Prop :=
  injected_family_off cfg i = true
  ∧ refusal_b i m eff.eff_ret = true
  ∧ (∃ eff' m' evs',
        Specs.syscall_spec i m (.ok eff' m' evs')
        ∧ refusal_b i m eff'.eff_ret = false)

/-- The question the KNOWN GAP is about, stated once: at `(i, m)`, if the
    syscall's family is off in `cfg`, then either a non-refusal outcome exists
    or every admissible outcome is a refusal.  Vacuous for a family that may
    fail and for a syscall that injects nothing; not decidable in general
    inside this tree for the rest — for `mmap` it is the placement question —
    which is why `sstep_cfg_progress` takes it as a premise rather than
    proving it. -/
def refusal_decided (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) : Prop :=
  injected_family_off cfg i = true →
  (∃ eff' m' evs',
     Specs.syscall_spec i m (.ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false)
  ∨ (∀ eff' m' evs',
        Specs.syscall_spec i m (.ok eff' m' evs') → refusal_b i m eff'.eff_ret = true)

theorem injected_family_off_may_fail (i : SyscallInput) :
    injected_family_off may_fail_cfg i = false := by
  unfold injected_family_off
  cases h : injected_arm i.in_sysno.toNat with
  | none => rfl
  | some a =>
    have hall : ∀ f, family_may_fail may_fail_cfg f = true := by
      intro f; cases f <;> rfl
    simp only [hall a.ia_family, Bool.not_true]

/-- Under the may-fail reading nothing is spurious: that is what makes
    `may_fail_cfg` the reading every existing statement has. -/
theorem spurious_refusal_may_fail (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    ¬ spurious_refusal_cfg may_fail_cfg i m eff := by
  intro ⟨Hoff, _, _⟩
  rw [injected_family_off_may_fail] at Hoff
  exact absurd Hoff (by simp)

/-- A non-refusal outcome is never spurious, whatever the configuration. -/
theorem spurious_refusal_not_refusal (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (Hnr : refusal_b i m eff.eff_ret = false) :
    ¬ spurious_refusal_cfg cfg i m eff := by
  intro ⟨_, Hr, _⟩
  rw [Hnr] at Hr
  exact absurd Hr (by simp)

/-- ... and neither is any outcome of a family that may fail. -/
theorem spurious_refusal_family_on (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (Hon : injected_family_off cfg i = false) :
    ¬ spurious_refusal_cfg cfg i m eff := by
  intro ⟨Hoff, _, _⟩
  rw [Hon] at Hoff
  exact absurd Hoff (by simp)

/-- Turning families off only makes more outcomes spurious. -/
theorem spurious_refusal_mono (cfg1 cfg2 : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (Hle : cfg_le cfg1 cfg2)
    (H : spurious_refusal_cfg cfg2 i m eff) : spurious_refusal_cfg cfg1 i m eff := by
  obtain ⟨Hoff, Hr, Hex⟩ := H
  refine ⟨?_, Hr, Hex⟩
  unfold injected_family_off at Hoff ⊢
  cases h : injected_arm i.in_sysno.toNat with
  | none =>
    simp only [h] at Hoff
    exact Hoff
  | some a =>
    simp only [h] at Hoff ⊢
    have h2 : family_may_fail cfg2 a.ia_family = false := by simpa using Hoff
    have h1 : family_may_fail cfg1 a.ia_family = false := by
      cases h1' : family_may_fail cfg1 a.ia_family with
      | false => rfl
      | true =>
        rw [Hle _ h1'] at h2
        exact absurd h2 (by simp)
    simp [h1]

/- =========================================================================
   The filtered step relation
   ========================================================================= -/

/-- `sstep` under a configuration: every constructor is `sstep`'s, and the
    two that consume a syscall outcome additionally require the outcome not
    to be a spurious refusal.  The exit constructor needs no such premise —
    an exit is never a refusal — and neither does the fail-closed
    `Unmodeled` arm, which is not an outcome at all.

     The section binds `segs`, so the
    fully-applied form is `sstep_cfg cfg segs`; here `segs` leads, as it does
    for every other definition in this file. -/
inductive sstep_cfg (segs : List Segment) (cfg : SpuriousCfg) :
    config → List event → step_to → Prop where
  | instr (ms : machine_state) (model : Model) (ms' : machine_state) (model' : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step segs ms model = .MachineOk (ms', model')) :
      sstep_cfg segs cfg ⟨ms, model⟩ [] (.SNext ⟨ms', model'⟩)
  | instr_fault (ms : machine_state) (model : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step segs ms model = .MachineFault) :
      sstep_cfg segs cfg ⟨ms, model⟩ [] .SError
  | instr_unmodeled (ms : machine_state) (model : Model)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : mi_account_step segs ms model = .MachineUnmodeled) :
      sstep_cfg segs cfg ⟨ms, model⟩ [] .SError
  | syscall (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' model'' : Model) (evs : List event)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hns : ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff)
      (hh' : m_halted model' = none)
      (hmat : materialize_model_accesses model' (syscall_effect_accesses eff) = some model'') :
      sstep_cfg segs cfg ⟨ms, model⟩ evs
        (.SNext ⟨advance_past_svc (apply_effect ms eff), model''⟩)
  | syscall_materialization_fault (ms : machine_state) (model : Model) (x8 : word)
      (eff : SyscallEffect) (model' : Model) (evs : List event)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hns : ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff)
      (hh' : m_halted model' = none)
      (hmat : materialize_model_accesses model' (syscall_effect_accesses eff) = none) :
      sstep_cfg segs cfg ⟨ms, model⟩ [] .SError
  | exit (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' : Model) (evs : List event) (code : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hh' : m_halted model' = some code)
      (hk : m_killed model' = none) :
      sstep_cfg segs cfg ⟨ms, model⟩ (evs ++ [event.ExitEv code (m_fs model')])
        (.SNext ⟨ms, model'⟩)
  | killed (ms : machine_state) (model : Model) (x8 : word) (eff : SyscallEffect)
      (model' : Model) (evs : List event) (sig : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hk : m_killed model' = some sig) :
      sstep_cfg segs cfg ⟨ms, model⟩ (evs ++ [event.KillEv sig (m_fs model')])
        (.SNext ⟨ms, model'⟩)
  | syscall_unmodeled (ms : machine_state) (model : Model) (x8 : word)
      (hh : m_halted model = none)
      (hsvc : ms.ms_svc_pending = some x8)
      (hspec : Specs.syscall_spec (sys_input segs ms x8) model .unmodeled) :
      sstep_cfg segs cfg ⟨ms, model⟩ [] .SError

/-- SUBSET: every filtered step is a step. -/
theorem sstep_cfg_sub (segs : List Segment) (cfg : SpuriousCfg) :
    ∀ (c : config) (evs : List event) (r : step_to),
      sstep_cfg segs cfg c evs r → sstep segs c evs r := by
  intro c evs r H
  obtain ⟨ms, model⟩ := c
  cases H with
  | instr => exact sstep.instr _ _ _ _ (by assumption) (by assumption) (by assumption)
  | instr_fault => exact sstep.instr_fault _ _ (by assumption) (by assumption) (by assumption)
  | instr_unmodeled =>
    exact sstep.instr_unmodeled _ _ (by assumption) (by assumption) (by assumption)
  | syscall =>
    exact sstep.syscall _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption)
  | syscall_materialization_fault =>
    exact sstep.syscall_materialization_fault _ _ _ _ _ _ (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
  | exit =>
    exact sstep.exit _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption)
  | killed =>
    exact sstep.killed _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (by assumption)
  | syscall_unmodeled =>
    exact sstep.syscall_unmodeled _ _ _ (by assumption) (by assumption) (by assumption)

/-- MEANING: at `may_fail_cfg` the two relations coincide. -/
theorem sstep_cfg_may_fail (segs : List Segment) :
    ∀ (c : config) (evs : List event) (r : step_to),
      sstep segs c evs r ↔ sstep_cfg segs may_fail_cfg c evs r := by
  intro c evs r
  obtain ⟨ms, model⟩ := c
  constructor
  · intro H
    cases H with
    | instr => exact sstep_cfg.instr _ _ _ _ (by assumption) (by assumption) (by assumption)
    | instr_fault =>
      exact sstep_cfg.instr_fault _ _ (by assumption) (by assumption) (by assumption)
    | instr_unmodeled =>
      exact sstep_cfg.instr_unmodeled _ _ (by assumption) (by assumption) (by assumption)
    | syscall =>
      exact sstep_cfg.syscall _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
        (spurious_refusal_may_fail _ _ _) (by assumption) (by assumption)
    | syscall_materialization_fault =>
      exact sstep_cfg.syscall_materialization_fault _ _ _ _ _ _ (by assumption)
        (by assumption) (by assumption) (spurious_refusal_may_fail _ _ _) (by assumption)
        (by assumption)
    | exit =>
      exact sstep_cfg.exit _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption)
    | killed =>
      exact sstep_cfg.killed _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
        (by assumption)
    | syscall_unmodeled =>
      exact sstep_cfg.syscall_unmodeled _ _ _ (by assumption) (by assumption) (by assumption)
  · intro H
    exact sstep_cfg_sub segs may_fail_cfg _ _ _ H

/-- MONOTONE: a configuration that admits more families admits more steps. -/
theorem sstep_cfg_mono (segs : List Segment) (cfg1 cfg2 : SpuriousCfg) :
    ∀ (c : config) (evs : List event) (r : step_to),
      cfg_le cfg1 cfg2 → sstep_cfg segs cfg1 c evs r → sstep_cfg segs cfg2 c evs r := by
  intro c evs r Hle H
  obtain ⟨ms, model⟩ := c
  cases H with
  | instr => exact sstep_cfg.instr _ _ _ _ (by assumption) (by assumption) (by assumption)
  | instr_fault =>
    exact sstep_cfg.instr_fault _ _ (by assumption) (by assumption) (by assumption)
  | instr_unmodeled =>
    exact sstep_cfg.instr_unmodeled _ _ (by assumption) (by assumption) (by assumption)
  | syscall =>
    exact sstep_cfg.syscall _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (fun h => absurd (spurious_refusal_mono cfg1 cfg2 _ _ _ Hle h) (by assumption))
      (by assumption) (by assumption)
  | syscall_materialization_fault =>
    exact sstep_cfg.syscall_materialization_fault _ _ _ _ _ _ (by assumption)
      (by assumption) (by assumption)
      (fun h => absurd (spurious_refusal_mono cfg1 cfg2 _ _ _ Hle h) (by assumption))
      (by assumption) (by assumption)
  | exit =>
    exact sstep_cfg.exit _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption)
  | killed =>
    exact sstep_cfg.killed _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
      (by assumption)
  | syscall_unmodeled =>
    exact sstep_cfg.syscall_unmodeled _ _ _ (by assumption) (by assumption) (by assumption)

/-- PROGRESS, where the filter's question is answered: a configuration with a
    step has a filtered step.  The one case with content is a syscall outcome
    that the filter removes; then, by the third conjunct of
    `spurious_refusal_cfg`, a non-refusal outcome exists at the same input
    and model, and that outcome — never spurious — is a step of one of the
    three syscall shapes.  Deciding WHICH case one is in is the premise; see
    `refusal_decided`. -/
theorem sstep_cfg_progress (segs : List Segment) (cfg : SpuriousCfg) :
    ∀ (ms : machine_state) (model : Model) (evs : List event) (st : step_to),
      (∀ x8, ms.ms_svc_pending = some x8 →
        refusal_decided cfg (sys_input segs ms x8) model) →
      sstep segs ⟨ms, model⟩ evs st →
      ∃ evs' st', sstep_cfg segs cfg ⟨ms, model⟩ evs' st' := by
  intro ms model evs st Hdec H
  cases H with
  | instr _ _ _ _ hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.instr _ _ _ _ hh hsvc hstep⟩
  | instr_fault _ _ hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.instr_fault _ _ hh hsvc hstep⟩
  | instr_unmodeled _ _ hh hsvc hstep =>
    exact ⟨_, _, sstep_cfg.instr_unmodeled _ _ hh hsvc hstep⟩
  | syscall ms1 model1 x8 eff model' _ _ hh hsvc hspec hh' hmat =>
    by_cases hoff : injected_family_off cfg (sys_input segs ms x8) = true
    · rcases Hdec x8 hsvc hoff with ⟨eff', m', evs', hspec', hnr⟩ | Hall
      · have hns : ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff' :=
          spurious_refusal_not_refusal cfg _ _ _ hnr
        cases hm : m_halted m' with
        | some code =>
          cases hk : m_killed m' with
          | some sig =>
            exact ⟨_, _, sstep_cfg.killed _ _ _ _ _ _ _ hh hsvc hspec' hk⟩
          | none =>
            exact ⟨_, _, sstep_cfg.exit _ _ _ _ _ _ _ hh hsvc hspec' hm hk⟩
        | none =>
          cases hmat : materialize_model_accesses m' (syscall_effect_accesses eff') with
          | some m'' =>
            exact ⟨_, _, sstep_cfg.syscall _ _ _ _ _ _ _ hh hsvc hspec' hns hm hmat⟩
          | none =>
            exact ⟨_, _, sstep_cfg.syscall_materialization_fault _ _ _ _ _ _
              hh hsvc hspec' hns hm hmat⟩
      · refine ⟨_, _, sstep_cfg.syscall _ _ _ _ _ _ _ hh hsvc hspec (fun h => ?_) hh' hmat⟩
        obtain ⟨_, _, eff', m', evs', hspec', hnr⟩ := h
        rw [Hall _ _ _ hspec'] at hnr
        exact absurd hnr (by simp)
    · have hoff' : injected_family_off cfg (sys_input segs ms x8) = false := by
        cases h : injected_family_off cfg (sys_input segs ms x8) <;> simp_all
      exact ⟨_, _, sstep_cfg.syscall _ _ _ _ _ _ _ hh hsvc hspec
        (spurious_refusal_family_on cfg _ _ _ hoff') hh' hmat⟩
  | syscall_materialization_fault ms1 model1 x8 eff model' _ hh hsvc hspec hh' hmat =>
    by_cases hoff : injected_family_off cfg (sys_input segs ms x8) = true
    · rcases Hdec x8 hsvc hoff with ⟨eff', m', evs', hspec', hnr⟩ | Hall
      · have hns : ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff' :=
          spurious_refusal_not_refusal cfg _ _ _ hnr
        cases hm : m_halted m' with
        | some code =>
          cases hk : m_killed m' with
          | some sig =>
            exact ⟨_, _, sstep_cfg.killed _ _ _ _ _ _ _ hh hsvc hspec' hk⟩
          | none =>
            exact ⟨_, _, sstep_cfg.exit _ _ _ _ _ _ _ hh hsvc hspec' hm hk⟩
        | none =>
          cases hmat : materialize_model_accesses m' (syscall_effect_accesses eff') with
          | some m'' =>
            exact ⟨_, _, sstep_cfg.syscall _ _ _ _ _ _ _ hh hsvc hspec' hns hm hmat⟩
          | none =>
            exact ⟨_, _, sstep_cfg.syscall_materialization_fault _ _ _ _ _ _
              hh hsvc hspec' hns hm hmat⟩
      · refine ⟨_, _, sstep_cfg.syscall_materialization_fault _ _ _ _ _ _
          hh hsvc hspec (fun h => ?_) hh' hmat⟩
        obtain ⟨_, _, eff', m', evs', hspec', hnr⟩ := h
        rw [Hall _ _ _ hspec'] at hnr
        exact absurd hnr (by simp)
    · have hoff' : injected_family_off cfg (sys_input segs ms x8) = false := by
        cases h : injected_family_off cfg (sys_input segs ms x8) <;> simp_all
      exact ⟨_, _, sstep_cfg.syscall_materialization_fault _ _ _ _ _ _
        hh hsvc hspec (spurious_refusal_family_on cfg _ _ _ hoff') hh' hmat⟩
  | exit ms1 model1 x8 eff model' evs1 code hh hsvc hspec hh' hk =>
    exact ⟨_, _, sstep_cfg.exit _ _ _ _ _ _ _ hh hsvc hspec hh' hk⟩
  | killed ms1 model1 x8 eff model' evs1 sig hh hsvc hspec hk =>
    exact ⟨_, _, sstep_cfg.killed _ _ _ _ _ _ _ hh hsvc hspec hk⟩
  | syscall_unmodeled ms1 model1 x8 hh hsvc hspec =>
    exact ⟨_, _, sstep_cfg.syscall_unmodeled _ _ _ hh hsvc hspec⟩

/-- Kleene star of `sstep_cfg`. -/
inductive star_cfg (segs : List Segment) (cfg : SpuriousCfg) :
    config → List event → config → Prop where
  | refl (c : config) : star_cfg segs cfg c [] c
  | step (c1 : config) (evs : List event) (c2 : config) (tr : List event) (c3 : config)
      (h1 : sstep_cfg segs cfg c1 evs (.SNext c2))
      (h2 : star_cfg segs cfg c2 tr c3) :
      star_cfg segs cfg c1 (evs ++ tr) c3

theorem star_cfg_sub (segs : List Segment) (cfg : SpuriousCfg) :
    ∀ (c : config) (tr : List event) (c' : config),
      star_cfg segs cfg c tr c' → star segs c tr c' := by
  intro c tr c' H
  induction H with
  | refl c => exact star.refl c
  | step c1 evs c2 tr c3 h1 _ ih =>
    exact star.step c1 evs c2 tr c3 (sstep_cfg_sub segs cfg _ _ _ h1) ih

theorem star_cfg_may_fail (segs : List Segment) :
    ∀ (c : config) (tr : List event) (c' : config),
      star segs c tr c' ↔ star_cfg segs may_fail_cfg c tr c' := by
  intro c tr c'
  constructor
  · intro H
    induction H with
    | refl c => exact star_cfg.refl c
    | step c1 evs c2 tr c3 h1 _ ih =>
      exact star_cfg.step c1 evs c2 tr c3 ((sstep_cfg_may_fail segs _ _ _).mp h1) ih
  · intro H
    exact star_cfg_sub segs may_fail_cfg _ _ _ H

def obs_trace_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config)
    (tr : List event) : Prop :=
  ∃ tr' c, star_cfg segs cfg c0 tr' c ∧ is_prefix tr tr'

def reaches_error_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c evs, star_cfg segs cfg c0 tr c ∧ sstep_cfg segs cfg c evs .SError

inductive all_traces_error_cfg (segs : List Segment) (cfg : SpuriousCfg) : config → Prop where
  | intro (c : config)
      (hprog : ∃ evs to, sstep_cfg segs cfg c evs to)
      (hnext : ∀ evs c', sstep_cfg segs cfg c evs (.SNext c') →
        all_traces_error_cfg segs cfg c') :
      all_traces_error_cfg segs cfg c

def reaches_unmodeled_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ unmodeled_at segs c

/-- The filtered run removes executions and adds none: every trace, error and
    uncovered point of the filtered run is one of the run's.
    `all_traces_error_cfg` is deliberately absent from this list — it is a
    universal over successors, so fewer steps do not give it in either
    direction — and `Equivalence.equiv`'s escape is stated on it, which is one
    more reason a proof at one configuration says nothing at another. -/
theorem obs_trace_cfg_sub (segs : List Segment) (cfg : SpuriousCfg) (c0 : config)
    (tr : List event) (h : obs_trace_cfg segs cfg c0 tr) :
    obs_trace segs c0 tr := by
  obtain ⟨tr', c, hstar, hp⟩ := h
  exact ⟨tr', c, star_cfg_sub segs cfg _ _ _ hstar, hp⟩

theorem reaches_error_cfg_sub (segs : List Segment) (cfg : SpuriousCfg) (c0 : config)
    (h : reaches_error_cfg segs cfg c0) : reaches_error segs c0 := by
  obtain ⟨tr, c, evs, hstar, he⟩ := h
  exact ⟨tr, c, evs, star_cfg_sub segs cfg _ _ _ hstar,
    sstep_cfg_sub segs cfg _ _ _ he⟩

theorem reaches_unmodeled_cfg_sub (segs : List Segment) (cfg : SpuriousCfg) (c0 : config)
    (h : reaches_unmodeled_cfg segs cfg c0) : reaches_unmodeled segs c0 := by
  obtain ⟨tr, c, hstar, hu⟩ := h
  exact ⟨tr, c, star_cfg_sub segs cfg _ _ _ hstar, hu⟩

/-- ... and at `may_fail_cfg` each of the four is the unfiltered one. -/
theorem obs_trace_cfg_may_fail (segs : List Segment) (c0 : config) (tr : List event) :
    obs_trace segs c0 tr ↔ obs_trace_cfg segs may_fail_cfg c0 tr := by
  constructor
  · intro h
    obtain ⟨tr', c, hstar, hp⟩ := h
    exact ⟨tr', c, (star_cfg_may_fail segs _ _ _).mp hstar, hp⟩
  · intro h
    obtain ⟨tr', c, hstar, hp⟩ := h
    exact ⟨tr', c, (star_cfg_may_fail segs _ _ _).mpr hstar, hp⟩

theorem reaches_error_cfg_may_fail (segs : List Segment) (c0 : config) :
    reaches_error segs c0 ↔ reaches_error_cfg segs may_fail_cfg c0 := by
  constructor
  · intro h
    obtain ⟨tr, c, evs, hstar, he⟩ := h
    exact ⟨tr, c, evs, (star_cfg_may_fail segs _ _ _).mp hstar,
      (sstep_cfg_may_fail segs _ _ _).mp he⟩
  · intro h
    obtain ⟨tr, c, evs, hstar, he⟩ := h
    exact ⟨tr, c, evs, (star_cfg_may_fail segs _ _ _).mpr hstar,
      (sstep_cfg_may_fail segs _ _ _).mpr he⟩

theorem all_traces_error_cfg_may_fail (segs : List Segment) (c : config) :
    all_traces_error segs c ↔ all_traces_error_cfg segs may_fail_cfg c := by
  constructor
  · intro H
    induction H with
    | intro c hprog hnext ih =>
      refine all_traces_error_cfg.intro c ?_ ?_
      · obtain ⟨evs, to, hstep⟩ := hprog
        exact ⟨evs, to, (sstep_cfg_may_fail segs _ _ _).mp hstep⟩
      · intro evs' c' hss
        exact ih evs' c' ((sstep_cfg_may_fail segs _ _ _).mpr hss)
  · intro H
    induction H with
    | intro c hprog hnext ih =>
      refine all_traces_error.intro c ?_ ?_
      · obtain ⟨evs, to, hstep⟩ := hprog
        exact ⟨evs, to, (sstep_cfg_may_fail segs _ _ _).mpr hstep⟩
      · intro evs' c' hss
        exact ih evs' c' ((sstep_cfg_may_fail segs _ _ _).mp hss)

theorem reaches_unmodeled_cfg_may_fail (segs : List Segment) (c0 : config) :
    reaches_unmodeled segs c0 ↔ reaches_unmodeled_cfg segs may_fail_cfg c0 := by
  constructor
  · intro h
    obtain ⟨tr, c, hstar, hu⟩ := h
    exact ⟨tr, c, (star_cfg_may_fail segs _ _ _).mp hstar, hu⟩
  · intro h
    obtain ⟨tr, c, hstar, hu⟩ := h
    exact ⟨tr, c, (star_cfg_may_fail segs _ _ _).mpr hstar, hu⟩

/-- Being uncovered is a special case of erroring under every configuration,
    as it is under none: both uncovered shapes are premises of an `SError`
    transition that no filter touches. -/
theorem reaches_unmodeled_cfg_reaches_error_cfg (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) (h : reaches_unmodeled_cfg segs cfg c0) :
    reaches_error_cfg segs cfg c0 := by
  obtain ⟨tr, ⟨ms, model⟩, hstar, hh, h | h⟩ := h
  · obtain ⟨hsvc, hacc⟩ := h
    exact ⟨tr, ⟨ms, model⟩, [], hstar,
      sstep_cfg.instr_unmodeled ms model hh hsvc hacc⟩
  · obtain ⟨x8, hsvc, hspec⟩ := h
    exact ⟨tr, ⟨ms, model⟩, [], hstar,
      sstep_cfg.syscall_unmodeled ms model x8 hh hsvc hspec⟩

theorem all_traces_error_cfg_reaches_error_cfg (segs : List Segment) (cfg : SpuriousCfg) :
    ∀ c, all_traces_error_cfg segs cfg c → reaches_error_cfg segs cfg c := by
  intro c Hall
  induction Hall with
  | intro c hprog hnext ih =>
    obtain ⟨evs, to, hstep⟩ := hprog
    cases to with
    | SNext c' =>
      obtain ⟨tr, c2, err_evs, hstar, herr⟩ := ih evs c' hstep
      exact ⟨evs ++ tr, c2, err_evs,
        star_cfg.step c evs c' tr c2 hstep hstar, herr⟩
    | SError =>
      exact ⟨[], c, evs, star_cfg.refl c, hstep⟩

/-- `run` under a spurious-failure configuration: the same initial
    configuration, the same four observations, over the filtered step
    relation.  Written as the same `match` as `run` and for the same reason. -/
def run_scfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : behavior :=
  let c0 := init_config img.img_segments img.img_init_pc img.img_phdrs
    en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
  { bh_traces := obs_trace_cfg img.img_segments cfg c0
    bh_errors := reaches_error_cfg img.img_segments cfg c0
    bh_all_errors := all_traces_error_cfg img.img_segments cfg c0
    bh_unmodeled := reaches_unmodeled_cfg img.img_segments cfg c0 }

/-- Two behaviors that agree observation by observation.  `behavior` is a
    record of bare `Prop`s, so this is the relation under which `run` and
    `run_scfg may_fail_cfg` are the same thing — propositional equality of the
    records would need extensionality this tree does not assume. -/
def behavior_equiv (b1 b2 : behavior) : Prop :=
  (∀ tr, bh_traces b1 tr ↔ bh_traces b2 tr)
  ∧ (bh_errors b1 ↔ bh_errors b2)
  ∧ (bh_all_errors b1 ↔ bh_all_errors b2)
  ∧ (bh_unmodeled b1 ↔ bh_unmodeled b2)

theorem behavior_equiv_refl (b : behavior) : behavior_equiv b b :=
  ⟨fun _ => Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem behavior_equiv_sym (b1 b2 : behavior) (h : behavior_equiv b1 b2) :
    behavior_equiv b2 b1 := by
  obtain ⟨ht, he, ha, hu⟩ := h
  exact ⟨fun tr => (ht tr).symm, he.symm, ha.symm, hu.symm⟩

/-- MEANING PRESERVED: `run_scfg may_fail_cfg` is `run`, observation by
    observation.  This is what lets every statement above this section keep
    its text: it is the `may_fail_cfg` instance of its `[_scfg]` form
    (`Equivalence.strong_universal_T_scfg_may_fail` and its siblings). -/
theorem run_scfg_may_fail (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    behavior_equiv (run_scfg may_fail_cfg img lim en inp) (run img lim en inp) := by
  simp only [behavior_equiv, run_scfg, run]
  refine ⟨fun tr => (obs_trace_cfg_may_fail _ _ tr).symm, ?_, ?_, ?_⟩
  · exact (reaches_error_cfg_may_fail _ _).symm
  · exact (all_traces_error_cfg_may_fail _ _).symm
  · exact (reaches_unmodeled_cfg_may_fail _ _).symm

/-- The run with every avoidable allocation refusal removed and every other
    family left at may-fail: `alloc_may_fail = false`. -/
def run_nospurious (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    behavior :=
  run_scfg (alloc_only_cfg false) img lim en inp

/-- The one-switch form.  Written as an `if` on the literal so that
    `run_cfg true` is `run` BY CONVERSION — every statement and library lemma
    about `run` applies to the `true` instance with no bridge — and
    `run_cfg false` is `run_nospurious`.  A proof stated over `run_cfg b` for
    a variable `b` reaches the record form through `run_cfg_scfg`. -/
def run_cfg (alloc_may_fail : Bool) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : behavior :=
  if alloc_may_fail then run img lim en inp else run_nospurious img lim en inp

theorem run_cfg_true (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_cfg true img lim en inp = run img lim en inp := rfl

theorem run_cfg_false (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    run_cfg false img lim en inp = run_nospurious img lim en inp := rfl

theorem run_cfg_scfg (b : Bool) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    behavior_equiv (run_cfg b img lim en inp) (run_scfg (alloc_only_cfg b) img lim en inp) := by
  cases b with
  | false => exact behavior_equiv_refl _
  | true => exact behavior_equiv_sym _ _ (run_scfg_may_fail img lim en inp)

/-- SUBSET, at the level of behaviors: whatever the configuration, the filtered
    run's traces, errors and uncovered points are the run's. -/
theorem run_scfg_sub_traces (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (tr : List event)
    (h : bh_traces (run_scfg cfg img lim en inp) tr) :
    bh_traces (run img lim en inp) tr := by
  simp only [run_scfg, run] at h ⊢
  exact obs_trace_cfg_sub _ cfg _ _ h

theorem run_scfg_sub_errors (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h : bh_errors (run_scfg cfg img lim en inp)) :
    bh_errors (run img lim en inp) := by
  simp only [run_scfg, run] at h ⊢
  exact reaches_error_cfg_sub _ cfg _ h

theorem run_scfg_sub_unmodeled (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h : bh_unmodeled (run_scfg cfg img lim en inp)) :
    bh_unmodeled (run img lim en inp) := by
  simp only [run_scfg, run] at h ⊢
  exact reaches_unmodeled_cfg_sub _ cfg _ h

/-- The behavior-level images of the two containments `Run.run` realises,
    restated for the filtered run so that `Equivalence.error_free` keeps
    subsuming `Equivalence.modeled` under every configuration. -/
theorem run_scfg_unmodeled_errors (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h : bh_unmodeled (run_scfg cfg img lim en inp)) :
    bh_errors (run_scfg cfg img lim en inp) := by
  simp only [run_scfg] at h ⊢
  exact reaches_unmodeled_cfg_reaches_error_cfg _ cfg _ h

theorem run_scfg_all_errors_errors (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h : bh_all_errors (run_scfg cfg img lim en inp)) :
    bh_errors (run_scfg cfg img lim en inp) := by
  simp only [run_scfg] at h ⊢
  exact all_traces_error_cfg_reaches_error_cfg _ cfg _ h

/- =========================================================================
   The budget mark: where a run is refused for exceeding its budget
   =========================================================================

   `Equivalence.strong_universal_T_budgets` and its siblings state the
   flavour-pair obligation (the same program built plain and with a sanitizer)
   for the inputs on which the SOURCE run, under the source budget, never
   takes a budget-refused allocation.  This section defines that observable.
   It is a PREDICATE over the configurations a run reaches — not a trace
   event, which would enter trace equality and change what every statement
   above means, and not a state flag, which nothing could set on the
   first-touch path below, where the refusal IS the error transition and there
   is no successor state.  Nothing above this section changes.

   A configuration is budget-refused when the run is about to be declined for
   exceeding `State.vm_limit`, in one of three ways:

   - the pending INSTRUCTION touches a lazy page the budget cannot back: the
     interpreter answers `MachineOk` (the access itself is fine) and
     `State.materialize_model_accesses` answers `none`, which
     `State.materialize_accesses` does in exactly one case — a newly touched
     page would push the charge above the limit.  A `MachineFault` from the
     interpreter (a bad address, `ebreak`) is therefore NOT budget-refused,
     although both go to `SError` through `sstep_instr_fault`;
   - the pending SYSCALL is a grant the budget refuses:
     `alloc_budget_refused_b` on the request and the pre-state, a boolean each
     arm defines beside its spec as the negation of its own budget gate.  It
     reads the request and the state, never the answer: the arms keep an
     `alt` onto their errno list, so a refusal is always ADMISSIBLE, and what
     the mark says is that at this configuration nothing else is;
   - some admissible outcome of the pending syscall has an effect whose
     copy-in or copy-out touches a lazy page the budget cannot back — the
     `sstep_syscall_materialization_fault` premises.

   The first and third are premises of an `SError` transition
   (`budget_fault_instr_sstep_error`, `budget_fault_syscall_sstep_error`); the
   second is not an error at all — the program is answered -ENOMEM or the old
   break and goes on — which is why the premise is a separate observable
   rather than a reading of `bh_errors`.

   On a run with no MAP_NORESERVE mapping — every plain musl build —
   `State.m_vm_lazy` is empty at every reachable state and the two first-touch
   clauses are false (`materialize_model_accesses_no_lazy`), so discharging
   the premise is the grant clause at each ecall
   (`budget_refused_at_no_lazy_instr`,
   `budget_refused_at_no_lazy_syscall`). -/

def budget_refused_at (segs : List Segment) (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
  ( (c.cfg_ms.ms_svc_pending = none ∧
     ∃ report,
       step_accesses segs c.cfg_ms = .MachineOk report ∧
       materialize_model_accesses c.cfg_model report.accessed_ranges = none)
  ∨ (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
       ( alloc_budget_refused_b (sys_input segs c.cfg_ms x8) c.cfg_model = true
       ∨ ∃ (eff : SyscallEffect) (model' : Model) (evs : List event),
            Specs.syscall_spec (sys_input segs c.cfg_ms x8) c.cfg_model (.ok eff model' evs)
            ∧ m_halted model' = none
            ∧ materialize_model_accesses model' (syscall_effect_accesses eff) = none)) )

/-- The run can reach a budget-refused configuration. -/
def reaches_budget_refused (segs : List Segment) (c0 : config) : Prop :=
  ∃ tr c, star segs c0 tr c ∧ budget_refused_at segs c

theorem reaches_budget_refused_intro (segs : List Segment) (c : config)
    (h : budget_refused_at segs c) : reaches_budget_refused segs c :=
  ⟨[], c, star.refl c, h⟩

theorem reaches_budget_refused_star (segs : List Segment) (c0 : config) (tr : List event)
    (c : config) (Hstar : star segs c0 tr c)
    (hb : reaches_budget_refused segs c) : reaches_budget_refused segs c0 := by
  obtain ⟨tr', c', hstar', hb'⟩ := hb
  exact ⟨tr ++ tr', c', star_trans segs _ _ _ Hstar _ _ hstar', hb'⟩

/-- The two first-touch clauses are premises of an error transition. -/
theorem budget_fault_instr_sstep_error (segs : List Segment) (ms : machine_state)
    (model : Model) (report : access_report machine_state)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk report)
    (Hmat : materialize_model_accesses model report.accessed_ranges = none) :
    sstep segs ⟨ms, model⟩ [] .SError := by
  refine sstep.instr_fault ms model Hh Hsvc ?_
  simp only [mi_account_step, Hstep, Hmat]

theorem budget_fault_syscall_sstep_error (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word) (eff : SyscallEffect) (model' : Model)
    (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
    (Hh' : m_halted model' = none)
    (Hmat : materialize_model_accesses model' (syscall_effect_accesses eff) = none) :
    sstep segs ⟨ms, model⟩ [] .SError :=
  sstep.syscall_materialization_fault ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat

/-- Discharging the premise: an invariant of the reachable configurations
    that excludes the mark. -/
theorem star_invariant (segs : List Segment) (I : config → Prop)
    (Hstep : ∀ (c : config) (evs : List event) (c' : config),
      I c → sstep segs c evs (.SNext c') → I c') :
    ∀ (c0 : config) (tr : List event) (c : config),
      star segs c0 tr c → I c0 → I c := by
  intro c0 tr c Hstar
  induction Hstar with
  | refl c => exact fun h => h
  | step c1 evs c2 tr c3 h1 h2 ih => intro h; exact ih (Hstep _ _ _ h h1)

theorem never_budget_refused_ind (segs : List Segment) (I : config → Prop)
    (c0 : config) (H0 : I c0)
    (Hstep : ∀ (c : config) (evs : List event) (c' : config),
      I c → sstep segs c evs (.SNext c') → I c')
    (Hno : ∀ c, I c → ¬ budget_refused_at segs c) :
    ¬ reaches_budget_refused segs c0 := by
  rintro ⟨tr, c, Hstar, Hb⟩
  exact Hno c (star_invariant segs I Hstep c0 tr c Hstar H0) Hb

/-- With no lazy mapping, an instruction configuration is never budget-refused:
    the first-touch clause needs `none` where
    `materialize_model_accesses_no_lazy` answers `some`, and the other two
    need a pending syscall. -/
theorem budget_refused_at_no_lazy_instr (segs : List Segment) (ms : machine_state)
    (model : Model) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none) : ¬ budget_refused_at segs ⟨ms, model⟩ := by
  rintro ⟨_, h | h⟩
  · obtain ⟨_, report, _, hmat⟩ := h
    rw [materialize_model_accesses_no_lazy model report.accessed_ranges Hlazy] at hmat
    exact absurd hmat (by simp)
  · obtain ⟨x8, hx8, _⟩ := h
    rw [Hsvc] at hx8
    exact absurd hx8 (by simp)

/-- ... and a syscall configuration whose every outcome leaves no lazy mapping
    either is budget-refused exactly by the grant clause. -/
theorem budget_refused_at_no_lazy_syscall (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hlazy : ∀ (eff : SyscallEffect) (model' : Model) (evs : List event),
      Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
      m_vm_lazy model' = []) :
    (budget_refused_at segs ⟨ms, model⟩
     ↔ alloc_budget_refused_b (sys_input segs ms x8) model = true) := by
  constructor
  · rintro ⟨_, h | h⟩
    · obtain ⟨hnone, _⟩ := h
      rw [Hsvc] at hnone
      exact absurd hnone (by simp)
    · obtain ⟨y8, hy8, hb | ⟨eff, model', evs, hspec, _, hmat⟩⟩ := h
      · rw [Hsvc] at hy8
        obtain rfl := Option.some.inj hy8
        exact hb
      · rw [Hsvc] at hy8
        obtain rfl := Option.some.inj hy8
        rw [materialize_model_accesses_no_lazy model' (syscall_effect_accesses eff)
          (Hlazy eff model' evs hspec)] at hmat
        exact absurd hmat (by simp)
  · intro Hb
    exact ⟨Hh, Or.inr ⟨x8, Hsvc, Or.inl Hb⟩⟩

/-- The same reachability under a configuration: `star_cfg` in place of
    `star`, the mark unchanged.  The mark's instruction and grant clauses read
    the state and the request and see no configuration; its effect clause
    ranges over ALL the arm's admitted outcomes, including ones the
    configuration filters out, so under a configuration that clause can fire
    on the materialization fault of an outcome the configured run never takes
    — an over-approximation of "the configured run is about to be refused", in
    the safe direction (the premise is false more often, never true wrongly).
    What the configuration changes otherwise is WHICH configurations the run
    reaches: fewer, never more (`reaches_budget_refused_cfg_sub`), so the
    unfiltered premise discharges the configured one, and at `may_fail_cfg` the
    configured reachability is the unfiltered one
    (`reaches_budget_refused_cfg_may_fail`).

    Not for mremap: where its mark fires, the in-place resolution is never
    admitted, but the moved one is shown refused only at destinations that
    carry no backing metadata
    (`Checks.BudgetPremise.mremap_budget_refused_refuses_move`).  Its fit
    hypothesis and the protected ledger it reads are proved invariants
    (`Checks.MapsFit`, `Checks.NoaccessOwned`); the lazy-ledger half is
    not yet proved preserved.  On a state with empty lazy ledgers every
    admitted outcome is a refusal
    (`Checks.BudgetPremiseMremap.mremap_budget_refused_is_refusal_sys_inv`).
    On a state that broke the lazy-ledger half, the mark could fire where
    a move is still admitted, and under a forced-only configuration the
    filter could drop the marked refusal as spurious; the marked
    configuration is still reached, so the premise is unaffected. -/
def reaches_budget_refused_cfg (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ budget_refused_at segs c

theorem reaches_budget_refused_cfg_sub (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) (h : reaches_budget_refused_cfg segs cfg c0) :
    reaches_budget_refused segs c0 := by
  obtain ⟨tr, c, hstar, hb⟩ := h
  exact ⟨tr, c, star_cfg_sub segs cfg _ _ _ hstar, hb⟩

theorem reaches_budget_refused_cfg_may_fail (segs : List Segment) (c0 : config) :
    reaches_budget_refused segs c0
      ↔ reaches_budget_refused_cfg segs may_fail_cfg c0 := by
  constructor
  · rintro ⟨tr, c, hstar, hb⟩
    exact ⟨tr, c, (star_cfg_may_fail segs _ _ _).mp hstar, hb⟩
  · intro h
    exact reaches_budget_refused_cfg_sub segs may_fail_cfg c0 h

/-- The run-level form: the `match` of `run`, on the same initial
    configuration.  `Equivalence.source_within_budget` negates it. -/
def run_budget_refused (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  reaches_budget_refused img.img_segments
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- The configured run's form, the `match` of `run_scfg`. -/
def run_scfg_budget_refused (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  reaches_budget_refused_cfg img.img_segments cfg
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem run_scfg_budget_refused_sub (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h : run_scfg_budget_refused cfg img lim en inp) :
    run_budget_refused img lim en inp :=
  reaches_budget_refused_cfg_sub _ cfg _ h

theorem run_scfg_budget_refused_may_fail (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    run_budget_refused img lim en inp
      ↔ run_scfg_budget_refused may_fail_cfg img lim en inp :=
  reaches_budget_refused_cfg_may_fail _ _

/- =========================================================================
   Valid process inputs: argv and envp
   =========================================================================

   What `execve` hands a process — part of the Linux process model, not of
   any particular equivalence task.  The bounds keep the initial stack image
   comfortably inside the 8 MiB stack.  No byte-range clause (`b < 256`) is
   needed: the `byte` type enforces it.

   The other two `run` inputs: the initial file-system image is validated by
   `Fs.valid_fs`; the standard input stream (`State.InputStream`) needs no
   validity predicate at all — its elements are `byte`, and any colist of
   bytes, finite or infinite, is an input a process could really be handed. -/

/-- Validity predicate for the initial stack pointer: any 16-byte-aligned
    (riscv64 psABI entry guarantee) address in the window
    `[sp_window_lo, sp_window_hi]` (State.lean).  Quantified independently
    per binary in `Equivalence.strong_universal_T` — the model's ASLR. -/
def valid_sp (sp : word) : Prop :=
  sp_window_lo ≤ (sp.toNat : Int) ∧ (sp.toNat : Int) ≤ sp_window_hi ∧
  (sp.toNat : Int) % 16 = 0

/-- Validity predicate for the initial program break (`mi_init_brk`).  Its
    ASLR window is IMAGE-RELATIVE (unlike the SP's absolute window): any
    page-aligned address from the page-rounded image top
    (`State.reserved_top` of the LOAD reservations) up to `brk_aslr_max` above
    (covering the kernel's one-page gap plus up-to-1-GiB randomization,
    `arch_randomize_brk`/`randomize_page(_, SZ_1G)`).  Quantified
    independently per binary in `Equivalence.strong_universal_T` — the
    model's brk ASLR, mirroring `valid_sp`. -/
def valid_brk (segs : List Segment) (brk : word) : Prop :=
  reserved_top (segments_reserved segs) ≤ (brk.toNat : Int)
  ∧ (brk.toNat : Int) ≤ reserved_top (segments_reserved segs) + brk_aslr_max
  ∧ (brk.toNat : Int) % page_size = 0

/-- Validity predicate for the run's `mm->mmap_base` (`mi_mmap_base`): any
    page-aligned address in `[State.mmap_base_min, State.mmap_base_max]`.  The
    floor is the smallest base any covered kernel's top-down layout computes
    and the cap the largest; both are derived from mm/util.c's `mmap_base` on
    their own definitions, under two assumptions that module names: the
    top-down layout, and `vm.mmap_rnd_bits` at most 24 or a
    `stack_guard_gap` at most 0x4aba6a2ab000 bytes.
    `Checks.Cases.MmapBase.sv48_band_is_linux_set` proves both inclusions
    against a statement of that computation.  Quantified independently per
    binary in
    `Equivalence.strong_universal_T`, like `valid_sp` and `valid_brk`.

    WHAT IS UNREAD IS THE VALUE, NOT THIS PREDICATE, and the difference
    matters because it decides whether the apparatus can be deleted.  No spec
    arm reads `vm_mmap_base` — placement is admissibility alone — so the band
    constrains no placement the model admits.  But `valid_mmap_base` is the
    third conjunct of `valid_entry`, which `Equivalence.strong_universal_T`
    quantifies its entries under, and discharging it is a required step of the
    tree's anti-vacuity lemma `Equivalence.image_brk_satisfiable_entry`: that
    lemma exhibits an entry and must show its base admissible.  Delete the
    field and that proof silently loses a conjunct.  That is the whole reason,
    and it is about this PREDICATE rather than about the field's value: no
    reader of the value exists in either tier.

    The band is now CHECKED, not merely derived:
    `Checks.Cases.MmapBase.sv48_band_is_linux_set` proves it is exactly the
    set of bases a launch under the configuration that module names gives,
    so an error in either constant fails the build.  Outside the spec the
    ASan plan checker (`Common.AsanInit`) takes this predicate as a
    hypothesis and needs its floor; that is why the floor is not lowered
    to drop the assumptions (see `State.mmap_base_min`). -/

def valid_mmap_base (mbase : word) : Prop :=
  mmap_base_min ≤ (mbase.toNat : Int) ∧ (mbase.toNat : Int) ≤ mmap_base_max
  ∧ (mbase.toNat : Int) % page_size = 0

/-! ## The same three predicates for a DECLARED address-space size

    `valid_sp` and `valid_mmap_base` above are the Sv48 instances, in the
    literal numbers the rest of the tree was written against.  The two below
    take the size the task declares (`State.VaSize`) and read the window and
    the band off it, by the derivations `State.va_stack_top` cites.
    `Checks/Cases/VaSize.lean` pins that the `Sv48` instance is the
    literal one — `sv48_task_size_is_TASK_SIZE`, and the three window
    literals beside it (`sv48_window_lo_is_the_literal`,
    `sv48_window_hi_is_the_literal`, `sv48_mmap_base_max_is_the_literal`)
    — so the reading here is the pinned one and not a coincidence of
    numbers.
    `valid_brk` has no such twin: the break's window is image-relative and the
    kernel's `arch_randomize_brk` does not read the depth. -/

def valid_sp_va (v : VaSize) (sp : word) : Prop :=
  va_sp_window_lo v ≤ (sp.toNat : Int) ∧ (sp.toNat : Int) ≤ va_sp_window_hi v
  ∧ (sp.toNat : Int) % 16 = 0

def valid_mmap_base_va (v : VaSize) (mbase : word) : Prop :=
  va_mmap_base_min v ≤ (mbase.toNat : Int) ∧ (mbase.toNat : Int) ≤ va_mmap_base_max v
  ∧ (mbase.toNat : Int) % page_size = 0

theorem valid_sp_va_sv48 (sp : word) : valid_sp_va .Sv48 sp ↔ valid_sp sp := by
  unfold valid_sp_va valid_sp
  simp only [va_sp_window_lo, va_sp_window_hi, va_stack_top, sp_window_lo, sp_window_hi]
  constructor <;> intro h <;> omega

theorem valid_mmap_base_va_sv48 (mb : word) :
    valid_mmap_base_va .Sv48 mb ↔ valid_mmap_base mb := by
  unfold valid_mmap_base_va valid_mmap_base
  simp only [va_mmap_base_min, va_mmap_base_max, va_stack_top, mmap_base_max,
    mmap_base_min, sp_window_hi]

/-- Total bytes consumed by a list of argument strings (each string length + 1
    for the null terminator), in `Int` like the rest of the range arithmetic. -/
def total_arg_bytes (args : List (List byte)) : Int :=
  args.foldr (fun a acc => (a.length : Int) + 1 + acc) 0

/-- Validity predicate for argv lists.  At least one argument is required:
    modern Linux never delivers argc = 0 (kernel commit dcd46d897adb rewrites
    an empty `execve` argv to a single empty string), so a process may rely on
    argv[0] existing — though not on it being nonempty.

    THE FIFTH CLAUSE IS NOT A FACT ABOUT LINUX, and it is the only one here
    that is not.  The first four say what a kernel can deliver: Linux itself
    bounds argc, the total byte count and each string, and NUL is what
    terminates a string so no argument can contain one.  A real `execve`
    delivers "/etc/passwd" and ".." without complaint, and this clause
    excludes both.  It is a NARROWING OF THE THEOREM'S DOMAIN, written where
    the domain is stated, and it is here because of what it buys:
    `Sys.Fs.Open.openat_resolved_spec` declines a pathname with a separator in
    it, because answering it at all would mean answering it WRONGLY.  The
    whole-program examples in `Examples.cp_ns` and `Examples.headcp_ns` pass
    argv entries straight to `openat`, so without this clause that declined
    arm is reachable under `valid_input`, and since `Equivalence.modeled` is a
    conjunct of `strong_equiv`'s CONCLUSION rather than a hypothesis,
    `Equivalence.strong_universal_T` would be FALSE for both of them rather
    than merely narrower.

    IT IS ON THE TAIL, NOT THE WHOLE LIST, and that is load-bearing rather
    than tidy.  argv[0] conventionally holds a path — every shell launch puts
    one there — so a whole-list clause would restrict `strong_universal_T` to
    launches no shell performs.  Both examples read `nth 1` and `nth 2`, so the
    tail is enough.  On a one-element argv the clause is vacuous (`tail` of a
    singleton is `[]`), which is the right reading: a process launched with
    argv[0] alone opens nothing out of it.

    It is deliberately NOT written in terms of `openat`: a validity predicate
    that named one syscall's policy would go stale the moment the policy
    moved.  What it says is a property of the strings. -/
def valid_argv (argv : List (List byte)) : Prop :=
  (1 ≤ (argv.length : Int) ∧ (argv.length : Int) ≤ 1024)
  ∧ total_arg_bytes argv ≤ 2097152
  ∧ (∀ a ∈ argv, (a.length : Int) ≤ 131071)
  ∧ (∀ a ∈ argv, BitVec.ofInt 8 0 ∉ a)
  ∧ (∀ a ∈ argv.tail,
      Sys.Fs.Namei.path_has_slash a = false
      ∧ Fs.path_eqb a Sys.Fs.Namei.dotdot_path = false)

/-- Validity predicate for envp lists.  Same structural constraints as argv
    but with larger bounds: up to 256 variables, 131072 bytes total. -/
def valid_envp (envp : List (List byte)) : Prop :=
  (envp.length : Int) ≤ 256
  ∧ total_arg_bytes envp ≤ 131072
  ∧ (∀ e ∈ envp, (e.length : Int) ≤ 131071)
  ∧ (∀ e ∈ envp, BitVec.ofInt 8 0 ∉ e)

/-! ## The entry stack image fits inside the user address space

    `init_machine_state` lays `StackLayout.build_stack_bytes` down AT AND
    ABOVE `sp`: argc, the argv and envp pointer arrays, the auxv, the argument
    and environment strings, and the AT_RANDOM block all sit at higher
    addresses than the entry stack pointer.  So a placement is one a kernel
    could have produced only when that whole block ends at or below the TOP OF
    THE USER ADDRESS SPACE — `State.sp_window_hi`, which is riscv64's
    `STACK_TOP = DEFAULT_MAP_WINDOW = 1 << (MMAP_VA_BITS - 1)` =
    0x8000_0000_0000 wherever the kernel runs Sv48 or Sv57
    (arch/riscv/include/asm/processor.h `STACK_TOP`,
    arch/riscv/include/asm/pgtable.h `MMAP_VA_BITS`, Linux v6.18.46, commit
    1f99e9ab748f; the derivation is in `State.sp_window_hi`'s own comment).

    WHY IT IS STATED PER RUN, coupling the `execve` choice to the caller's
    input.  The block's length depends on argv and envp, which arrive in the
    `State.ProcInput`; `valid_sp` cannot see them, which is why this conjunct
    lives in `valid_entry` and why `valid_entry` takes the input.  The
    alternative — subtracting the WORST-CASE block (`entry_stack_span_max`,
    2238671 bytes) from `sp_window_hi` once and for all — stays an absolute
    window and needs no new argument, but it would EXCLUDE real placements: a
    kernel handed a small argv and envp with stack randomization off puts `sp`
    within a few hundred bytes of `STACK_TOP`, inside the band the worst case
    subtracts.  Narrowing the quantifier past what a kernel can produce is a
    soundness hole in the equivalence theorem — the excluded runs are real and
    the theorem stops covering them — whereas admitting an impossible
    placement only costs provability.  So the premise is the exact
    kernel-real condition, not the convenient over-approximation of it.

    `entry_stack_span` is an upper bound on the block's length written in this
    file's own vocabulary (`total_arg_bytes`), so `valid_entry` and the
    satisfiability lemmas reason about it without `StackLayout`'s layout
    arithmetic.  What ties it to the real layout is
    `PropExec.build_stack_bytes_within_span`, proved where that arithmetic
    lives; `StepTac.bsb_bound` is then derived from the same two facts rather
    than recomputing the sum, so there is one derivation and nothing to
    drift. -/
def entry_stack_span (argv envp : List (List byte)) : Int :=
  8                                    -- argc
  + 8 * (argv.length : Int) + 8        -- argv[] and its NULL
  + 8 * (envp.length : Int) + 8        -- envp[] and its NULL
  + (auxv_size : Int)                  -- the serialized auxv
  + total_arg_bytes argv               -- the argument strings
  + total_arg_bytes envp               -- the environment strings
  + 7                                  -- 8-alignment padding
  + 16                                 -- the AT_RANDOM block

def entry_stack_fits (sp : word) (argv envp : List (List byte)) : Prop :=
  (sp.toNat : Int) + entry_stack_span argv envp ≤ sp_window_hi

/-- The same ceiling under a declared size: `STACK_TOP` is the top of the user
    address space the stack can occupy under every depth, and it is
    `va_stack_top`, not `va_task_size`, because under Sv57 the two differ and
    the stack sits under the former. -/
def entry_stack_fits_va (v : VaSize) (sp : word)
    (argv envp : List (List byte)) : Prop :=
  (sp.toNat : Int) + entry_stack_span argv envp ≤ va_sp_window_hi v

theorem entry_stack_fits_va_sv48 (sp : word) (argv envp : List (List byte)) :
    entry_stack_fits_va .Sv48 sp argv envp ↔ entry_stack_fits sp argv envp := by
  unfold entry_stack_fits_va entry_stack_fits va_sp_window_hi va_stack_top sp_window_hi
  constructor <;> intro h <;> omega

/-- The span of a VALID input is bounded absolutely, by the `valid_argv` /
    `valid_envp` limits.  This is what keeps the new conjunct from becoming a
    second way to empty the entry quantifier (the failure mode
    `image_brk_satisfiable` exists to catch): the bottom of the sp window has
    two gigabytes of room above it and the widest admissible block needs
    2238671 bytes, so every valid input still has a valid entry —
    `Equivalence.image_brk_satisfiable_entry` proves exactly that. -/
def entry_stack_span_max : Int := 2238671

theorem total_arg_bytes_nonneg (args : List (List byte)) :
    0 ≤ total_arg_bytes args := by
  induction args with
  | nil => simp [total_arg_bytes]
  | cons a r ih =>
    have h : 0 ≤ (a.length : Int) := Int.natCast_nonneg _
    show 0 ≤ (a.length : Int) + 1 + total_arg_bytes r
    omega

theorem entry_stack_span_bound (argv envp : List (List byte))
    (Ha : valid_argv argv) (He : valid_envp envp) :
    0 ≤ entry_stack_span argv envp ∧ entry_stack_span argv envp ≤ entry_stack_span_max := by
  obtain ⟨⟨h1, h2⟩, h3, _, _, _⟩ := Ha
  obtain ⟨h4, h5, _, _⟩ := He
  have h6 := total_arg_bytes_nonneg argv
  have h7 := total_arg_bytes_nonneg envp
  have h8 : (0 : Int) ≤ (argv.length : Int) := Int.natCast_nonneg _
  have h9 : (0 : Int) ≤ (envp.length : Int) := Int.natCast_nonneg _
  unfold entry_stack_span entry_stack_span_max auxv_size
  omega

/-- Validity predicate for an `ExecEntry` — what `execve` may hand this binary
    ON THIS INPUT.  The stack pointer, the program break and the mmap base
    range over their windows (the break's is image-relative, hence the `img`
    argument), and the entry stack image that the `execve` choice and the
    input together determine has to fit below the top of the user address
    space (see `entry_stack_fits` — hence the `inp` argument).

    `en_draw` is DISCARDED, deliberately: neither half of the draw has a
    window to lie in, so every value is valid and the field contributes no
    conjunct.  A universal quantifier over valid entries therefore ranges over
    all 2^128 AT_RANDOM draws, and over every function the page above the
    block could hold, with nothing to discharge — which is why the field
    strengthens every statement in the tree that quantifies over an entry
    without changing one of their texts.  No ADDRESS moves with the draw
    either (`StackLayout.build_stack_bytes_split_random`,
    `entry_stack_image_block_prefix`), so `entry_stack_fits` stays a function
    of (sp, argv, envp) — and it still bounds the whole mapped region, page
    rounding included (`PropExec.entry_page_top_within_window`).

    THE WINDOW IS THE DECLARED SIZE'S.  `valid_entry_va` takes the size
    explicitly and `valid_entry` reads it off the input, so a statement
    quantified over `valid_input` — which pins `Sv48` — sees exactly the Sv48
    window (`valid_entry_sv48`), and one quantified over an Sv39 input sees
    the Sv39 window rather than a stack placed 256 GiB above the last address
    such a kernel has.  Nothing about the run's ANSWERS moves with the size:
    `run` is the Sv48 run whatever the input declares, and
    `Equivalence.strong_equiv_va` is where a statement under another
    declaration is refused rather than answered — see `State.VaSize` for what
    the arms implement and for the residual.

     A match on `img, en` would discard `en_draw`; the port
    reads the projections, which reduce on concrete records exactly as the
    match does. -/
def valid_entry_va (v : VaSize) (img : Image) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  valid_sp_va v en.en_sp ∧ valid_brk img.img_segments en.en_brk
  ∧ valid_mmap_base_va v en.en_mmap_base
  ∧ entry_stack_fits_va v en.en_sp inp.in_argv inp.in_envp

def valid_entry (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  valid_entry_va inp.in_va_size img en inp

/-- The Sv48 instance is the predicate the tree was written against, conjunct
    for conjunct.  Consumers that reason about the window under `valid_input`
    rewrite with this and go on as before. -/
theorem valid_entry_sv48 (img : Image) (en : ExecEntry) (inp : ProcInput)
    (Hv : inp.in_va_size = .Sv48) :
    (valid_entry img en inp
     ↔ valid_sp en.en_sp ∧ valid_brk img.img_segments en.en_brk
       ∧ valid_mmap_base en.en_mmap_base
       ∧ entry_stack_fits en.en_sp inp.in_argv inp.in_envp) := by
  unfold valid_entry
  rw [Hv]
  simp only [valid_entry_va, valid_sp_va_sv48, valid_mmap_base_va_sv48,
    entry_stack_fits_va_sv48]

/-- Validity predicate for the user and group a process is launched as — the
    credential half of a `State.ProcInput`, and the model's answer to "which
    user is this?" in the same sense `valid_sp` and `valid_brk` are its answer
    to "where is the stack?": a window the environment chooses from, not a
    value the model invents.

    An id is a 32-BIT value.  Every credential syscall declares its arguments
    `uid_t`/`gid_t`, so the kernel never sees more than 32 bits of one (see
    `Syscall.uid32`), and a process whose real id did not fit would be one no
    `getuid` could report.

    `(uid_t)-1` is EXCLUDED.  `make_kuid` maps it to `INVALID_UID` (Linux
    v6.18.46, commit 1f99e9ab748f, kernel/user_namespace.c, `make_kuid` — via
    the `KUIDT_INIT(-1)` sentinel `INVALID_UID` in include/linux/uidgid.h),
    which every id-setting path rejects with -EINVAL, so no process can hold
    it and no `execve` can produce one.  The model excludes it here rather
    than leaving `Kernel.Sys.setid_spec` to answer a state that cannot arise.

    WHAT THIS PREDICATE DOES NOT COVER, and does not need to: a SECURE-EXEC.
    That is excluded by CONSTRUCTION rather than by a clause here —
    `State.ProcInput` has no effective-id field, so `State.init_model` derives
    the effective and saved ids from the real ones, and a launch whose
    effective id differs cannot be stated.  A set-user-id or set-group-id
    binary, or one carrying file capabilities, starts with an effective id
    that differs from its real one, and libc then takes its secure-exec path —
    musl's `__init_libc` computes `libc.secure` from exactly that inequality
    and from `AT_SECURE`, and the path probes and sanitizes fds 0-2 with
    syscalls outside `Specs.modeled_sysnos`.  Admitting such a launch would
    make the model claim behavior for a startup it does not cover, so it is
    excluded here and `State.init_model` gives every run real, effective and
    saved ids that agree.  `StackLayout.auxv_entries` states the same
    restriction from the other side, as the reason its `AT_SECURE` is 0. -/
def valid_id (u : word) : Prop :=
  (u.toNat : Int) < 2 ^ 32 - 1

def valid_creds (inp : ProcInput) : Prop :=
  valid_id inp.in_uid ∧ valid_id inp.in_gid

/-- The soft RLIMIT_NOFILE a launch can really carry.  `do_prlimit` enforces
    `rlim_cur <= rlim_max` and refuses a NOFILE `rlim_max` above the live
    `sysctl_nr_open` (kernel/sys.c, Linux v6.18.46, commit 1f99e9ab748f), and
    it is the only writer that a running process can reach for this resource.
    Not the only writer of the ARRAY, which is a weaker and more useful fact,
    because the others are all at exec or boot: `setup_new_exec` writes
    `RLIMIT_STACK` (fs/exec.c), `do_coredump` writes `RLIMIT_CORE`
    (fs/coredump.c), `acct_pin_kill` writes `RLIMIT_FSIZE` (kernel/acct.c),
    `fork_init` writes `init_task`'s NPROC and SIGPENDING (kernel/fork.c), and
    the LSM `bprm_committing_creds` hooks — SELinux's
    `selinux_bprm_committing_creds` and AppArmor's — loop over ALL of
    `RLIM_NLIMITS`, NOFILE included, clamping each soft limit to
    `min(rlim_max, init_task's soft)` on a domain transition.  That last one
    is the reason this bound is a property of the LAUNCH rather than of the
    model: an LSM clamp has already happened by the time the run starts, and
    the field records where it landed.

    `sysctl_nr_open` is itself bounded by `sysctl_nr_open_max`, the smaller of
    INT_MAX and the pointer-sized division `~(size_t)0 / sizeof a pointer`,
    rounded down to a multiple of BITS_PER_LONG — 2^31 - 64 on LP64 (fs/file.c,
    wired as the `proc_douintvec_minmax` ceiling in fs/file_table.c).
    `INIT_RLIMITS` starts the init task at 1024 and fork copies an
    already-valid pair, so no live `rlim_cur` exceeds that bound.
    RLIM_INFINITY least of all: it is above `sysctl_nr_open` by construction,
    which is why this one resource has no unlimited case.

    A CLAUSE RATHER THAN SLACK.  `Fs.File.dup3_spec` reads this limit and
    ANSWERS from it — it does not decline on it, the way
    `Kernel.Groups.getgroups_spec` declines an over-long `in_groups` — so a
    larger range would not be extra coverage but extra IMPOSSIBLE traces,
    concretely answered.  What the clause does NOT carry is the soundness of
    the returned fd: that rests on the two success arms' own bounds, since the
    extracted checker is handed a model directly and never sees this
    predicate. -/
def valid_nofile (n : word) : Prop :=
  (n.toNat : Int) ≤ 2 ^ 31 - 64

/-- The blocked mask a process can be STARTED with.  SIGKILL and SIGSTOP are
    never in it, and the clause is here rather than in the spec because it is
    a property of how the process was launched: nothing
    `Kernel.Signal.rt_sigprocmask_spec` does can introduce those bits, so if
    they are absent on entry they are absent for the whole run.

    WHY IT HOLDS, AS AN ENUMERATION AND NOT AS A ONE-LINER.  The tempting
    reason — "every path that installs a mask strips them" — is FALSE, and
    kernel/signal.c says so directly above `sigprocmask`: "Unlike the
    user-mode sys_sigprocmask(), the kernel interface happily blocks
    'unblockable' signals like SIGKILL and friends."  What is true is that
    every path leaving a mask on a task that then RETURNS TO USERSPACE either
    strips the two bits or cannot set them (Linux v6.18.46, commit
    1f99e9ab748f):

      - `SYSCALL_DEFINE4(rt_sigprocmask)` strips `new_set` itself, before
        calling `sigprocmask` (kernel/signal.c);
      - `set_current_blocked` strips, and it is what `set_user_sigmask`
        (ppoll, pselect6, epoll_pwait, io_pgetevents, io_uring_enter),
        `sigsuspend`, sigreturn and handler setup all go through
        (kernel/signal.c);
      - `ptrace_setsigmask` strips (kernel/ptrace.c);
      - `force_sig_info_to_task` and `do_sigtimedwait` only CLEAR bits
        (kernel/signal.c);
      - PID 1 starts from `init_task`'s zeroed `.blocked` (init/init_task.c)
        and execve preserves whatever it inherits — fs/exec.c never names
        `blocked` — so the property is inductive along the whole process tree;
      - two writers assign `current->blocked` DIRECTLY, reaching neither
        strip.  fs/coda/upcall.c's `coda_block_signals` is `sigfillset` then
        `sigdelset` of SIGKILL, SIGSTOP and SIGINT, so it clears both bits
        itself and this conclusion survives it rather than resting on it;
        drivers/isdn/mISDN/stack.c's `mISDNStackd` does
        `sigfillset(&current->blocked)` with no strip at all, and is a kthread
        that never returns to userspace, so it is outside what this list
        quantifies over.  security/selinux/hooks.c's
        `selinux_bprm_committed_creds` only `sigemptyset`s;
      - the in-kernel `sigprocmask` windows that genuinely do set the two bits
        are THREE `sigfillset`s, and they are not all filesystem operations:
        `ocfs2_block_signals` (fs/ocfs2/super.c) and `__smb_send_rqst`
        (fs/smb/client/transport.c) are, and `ab8500_power_off`
        (drivers/mfd/ab8500-sysctrl.c) is a power-off path.  What they share
        is not the subsystem but the shape — the mask is restored on the next
        line or two, before the task can execute another syscall.
        fs/ceph/addr.c's `ceph_block_sigs` blocks everything but SIGKILL, so
        it sets one of the two bits, and restores the same way.

    IT IS AN ABSENCE ARGUMENT, so it rots the way absence arguments do: a
    future kernel that leaves either bit set on a task returning to userspace
    falsifies it.  The direction is safe — a clause here only NARROWS the
    environments the theorem speaks about, and can never make the model admit
    an answer Linux would not give — but a narrowed theorem is a weaker one,
    so the clause is worth deleting if it stops being true rather than working
    around.

    WHY IT IS WORTH STATING AT ALL, given that omitting it would be sound:
    `Kernel.Signal.rt_sigprocmask_spec` copies the entry mask back out through
    `oset` verbatim, so without this clause the model would admit a program
    that reads `oset`, finds SIGKILL blocked, and branches on it — a trace no
    Linux process has.  That is the second of this development's three
    priorities. -/
def valid_sigmask (inp : ProcInput) : Prop :=
  (inp.in_sigmask &&& BitVec.ofInt 64 Sys.Uapi.sig_kernel_only_mask) = BitVec.ofInt 64 0

/-- Validity predicate for the AT_HWCAP word the auxv publishes — the model's
    answer to "which hart is this?" in the same sense `valid_sp` is its answer
    to "where is the stack?": a set the environment chooses from, not a value
    the model invents.

    Exactly two words, and the argument that it is exactly these two is in
    `StackLayout`'s AT_HWCAP bullet, which reads it out of the kernel source.
    In outline: `riscv_get_elf_hwcap` masks the published word down to the
    single-letter extension bits (arch/riscv/kernel/cpufeature.c:1108,
    `RISCV_ISA_EXT_BASE` = 26 in arch/riscv/include/asm/hwcap.h:33) and
    `riscv_fill_hwcap` can only ever set seven of them — i m a f d c v
    (arch/riscv/kernel/cpufeature.c:1059-1065, Linux v6.18.46, commit
    1f99e9ab748f) — so the architecture's whole range is the subsets of
    {A,C,D,F,I,M,V}.  Six of those bits are then fixed by the ISA this model
    EXECUTES (`Riscv.Decode` is RV64IMAFD, `Riscv.DecodeC` adds C): a hart
    missing one of them would not run the instructions the semantics
    interprets at all.  The seventh, V, is free, because
    `RiscvSemantics.decode_exec_accesses` answers a word it cannot decode with
    `MachineUnmodeled` rather than a trap — the model does not claim the hart
    lacks V, so it must not publish a word that says so — and because the
    kernel produces both masks on one machine, clearing V whenever
    `riscv_v_vstate_ctrl_user_allowed()` is false
    (arch/riscv/kernel/cpufeature.c:1114-1115), which a process controls
    through `PR_RISCV_V_SET_CONTROL`.

    UNLIKE the other clauses of `valid_input`, this one WIDENS what the
    theorem must survive rather than narrowing it: an auxv with no AT_HWCAP
    entry at all is a vector no v6.18.46 kernel builds (`create_elf_tables`
    emits the entry unconditionally, fs/binfmt_elf.c:249).  A binary whose
    runtime dispatches on the V bit has to be equivalent under BOTH masks, and
    under `hwcap_rv64gcv` its vector path is a word the decoder returns `none`
    for, so the run is `MachineUnmodeled`.  That is the intended consequence:
    such a binary leaves the modeled surface instead of being proved to take a
    scalar path a real process would not have taken. -/
def valid_hwcap (h : word) : Prop :=
  h = hwcap_rv64gc ∨ h = hwcap_rv64gcv

/-- THE RANDOM DEVICE'S DECLARED STREAM NEVER ENDS.

    THIS IS THE ONE CLAUSE HERE THAT IS A FIX RATHER THAN A NARROWING, and the
    distinction is worth the paragraph.  `valid_argv`'s length and byte-range
    clauses exclude launches a kernel really performs, and pay priority three
    for priority one.  This one excludes a declaration that describes NO
    DEVICE: /dev/urandom does not run out.  `urandom_read_iter` is
    `get_random_bytes_user` over the imported iterator, and that loops until
    the iterator is drained — stopping early only where `copy_to_iter` copies
    short, or where a signal is pending at a page boundary — and the pool is
    never empty once initialised (drivers/char/random.c, Linux v6.18.46).  So a
    read of n bytes from it delivers n, always.  A finite `State.in_urandom` is
    not a device that behaved unusually; it is a device that does not exist.

    WHAT IT BUYS.  `Sys.Fs.ReadWrite.read_urandom` takes
    `State.rw_count_clamp count` bytes off the declared stream and DECLINES if
    fewer come back, because a short read from this device is not something
    the model has a term for.  That decline is reachable from a whole-program
    theorem — a program that opens the device and reads a fixed-size buffer
    meets it as soon as the declaration is shorter than the buffer — and a
    decline an example reaches makes its `Equivalence.strong_universal_T`
    FALSE rather than narrower.  With this clause the arm's `unmodeled` row is
    unreachable under `valid_input`, and it is KEPT rather than deleted
    because the arm is total over `State.InputStream` and a caller outside
    `valid_input` can still meet it.  The row is the record of exactly what
    this clause excludes.

    IT IS THE ONLY CLAUSE ON AN ENVIRONMENT STREAM, and the two that have none
    stay that way.  `State.in_stdin` and `State.in_net` end, really and often
    — a pipe closes, a peer sends FIN — and a program has to survive it, so a
    clause there would exclude the case the model exists to check.  The
    difference is not that this stream is more important; it is that ending is
    a REAL BEHAVIOUR of those two and not of this one.

    IT SAYS NOTHING ABOUT THE CONTENTS.  Not uniform, not unpredictable, not
    fresh — only that a read yields as many bytes as it asked for.  The bytes
    themselves are an arbitrary but fixed stream, a parameter of the execution
    like argv and the environment. -/
def valid_urandom (inp : ProcInput) : Prop :=
  stream_infinite inp.in_urandom

/-- Validity predicate for a `State.ProcInput`.  Three fields carry no clause,
    each because every value of its type is one a process could really be
    handed: the standard-input stream's elements are `byte`, so every colist
    of bytes is a stream, and a pipe that ENDS is a real pipe a program has to
    survive; every `State.NetQueue` is a network some environment could
    present; and `in_groups` is bounded where it is READ rather than here —
    `Kernel.Groups.getgroups_spec` declines a list longer than
    `Uapi.NGROUPS_MAX` and never reads an element, so a clause here would
    restrict the theorem without changing what it says.  `in_nofile` is the
    field that looks like the third of those and is not: it is bounded HERE,
    by `valid_nofile`, because the spec that reads it answers from it instead
    of declining on it.

    `in_urandom` LOOKS LIKE A FOURTH, and is not: see `valid_urandom` for why
    ending is a real behaviour of a pipe and not of the random device.

    `in_sigmask` is the one field constrained for the OPPOSITE reason: it is
    read back verbatim rather than bounded at its reader, so the clause is the
    only thing standing between the model and a mask no launch can produce.
    See `valid_sigmask`.

    WHY `Fs.fs_keys_relative` IS ON THE IMAGE AND NOT ON `Fs.valid_fs`.  The
    clause says the launch handed the process an image whose keys are
    CWD-RELATIVE: no key begins with "/".  It is a premise about the
    environment in the sense `valid_sigmask` is — no real launch contradicts
    it, because the file system a run starts from is the working directory it
    was started in, and a key there is a name relative to that directory — and
    the model cannot check it, because nothing in an `Fs.Fs` says where the
    image came from.

    It reads `State.in_image_fs`, the PRE-SEED image, rather than
    `State.in_fs`, and that is forced rather than stylistic.  `in_fs` is
    `State.fs_seed_tmp` of the image with the declared /tmp
    (`State.in_tmp`), and the seeding inserts each declared entry under the
    ABSOLUTE key "/tmp/<name>" — so the same clause on `in_fs` would be false
    for every input with a non-empty declaration and would silently delete
    those inputs from every theorem quantified here.

    WHAT IT BUYS.  `Fs.valid_fs` admits the key "/dev/null", and the three
    device arms of `Sys.Fs.Open` — and `Sys.Fs.Stat`'s lookup of an absolute
    pathname — answer `unmodeled` when the map holds such a key or a key under
    it.  Without this clause, a program that always opens /dev/null would have
    ONE pathological image, admitted by every statement's quantifier, on which
    every error-free claim about it is false, for a reason no process can
    meet.  With this clause those guards are unreachable:
    `device_paths_never_seeded` below proves no key of a seeded image is, or
    lives under, any of the three device paths, and the guards stay in the
    arms as the courtesy their comments say they are. -/
def valid_input (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

/-- The SAME predicate with the abort-path declaration turned on, and it is a
    separate definition rather than a parameter for the reason the two shapes
    of every other statement in this tree are separate: what a proof was made
    under has to be readable in the statement.

    THE TWO PREDICATES ARE EXHAUSTIVE and mutually exclusive on the field:
    `in_abort_terminal` is a bool, so a statement that quantifies over
    `valid_input` speaks about runs in which `tkill` (130) and `tgkill` (131)
    are declined exactly as they were before either had an arm, a statement
    that quantifies over `valid_input_abort` speaks about runs in which a
    SIGABRT the process sends itself ends it, and a statement that pins
    neither — quantifying over `valid_input_either` — asserts both.  There is
    no third stance and no way to leave the question open by accident, which
    is the whole point of the field being in the input rather than in a
    configuration a checker might forget to ascribe.

    WHY `valid_input` IS THE ONE THAT PINS `false`.  Every statement in this
    tree written before the abort path had an arm quantifies over
    `valid_input`, and pinning the field there is what keeps those statements
    saying what they said: with the declaration off, no reachable model has
    `State.m_abort_terminal` set, so `Kernel.Signal.tkill_spec` declines every
    call and no `State.KillEv` can appear in any trace
    (`sstep_off_no_kill`).  A task that wants the other reading asks for it by
    name. -/
def valid_input_abort (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

/-- Neither stance pinned: the clauses both share, and nothing about the
    declaration.  A statement quantified over this one is the CONJUNCTION of
    the two above — it has to hold whichever stance the task takes — which is
    what makes forgetting to choose the safe failure rather than the dangerous
    one. -/
def valid_input_either (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

theorem valid_input_either_of_valid_input (inp : ProcInput)
    (h : valid_input inp) : valid_input_either inp := by
  unfold valid_input at h
  unfold valid_input_either
  grind

theorem valid_input_either_of_valid_input_abort (inp : ProcInput)
    (h : valid_input_abort inp) : valid_input_either inp := by
  unfold valid_input_abort at h
  unfold valid_input_either
  grind

/-- The exhaustiveness the paragraph above claims, as a lemma rather than as a
    sentence: an input the shared clauses accept satisfies one of the two
    pinned predicates, because a bool has two values. -/
theorem valid_input_either_splits (inp : ProcInput) (h : valid_input_either inp) :
    valid_input inp ∨ valid_input_abort inp := by
  unfold valid_input_either at h
  cases hab : inp.in_abort_terminal with
  | true => exact Or.inr (by unfold valid_input_abort; grind)
  | false => exact Or.inl (by unfold valid_input; grind)

/-! ## The address-space declaration: the same predicate per size

    Separate definitions rather than a parameter, for the reason the abort
    stances above are: what a proof was made under has to be readable in the
    statement.  Every statement in this tree was written against the Sv48
    kernel, and `valid_input` (and both abort stances) pin the size there,
    which keeps those statements saying what they said; a task that runs on
    another kernel asks for it by name, and what it gets today is spelled out
    at `Equivalence.strong_equiv_va` and at `State.VaSize`.  The two other
    sizes are stated with the abort declaration OFF, the default stance; a
    task wanting both the abort path and another size has no predicate here
    yet, and the day one is needed it is written the way these are.

    `valid_input_va_any` pins the abort stance off and nothing about the size:
    a statement quantified over it holds under every size, so a task that says
    nothing about its kernel is held to all three readings rather than to the
    default. -/

def valid_input_sv39 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv39
  ∧ valid_urandom inp

def valid_input_sv57 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv57
  ∧ valid_urandom inp

def valid_input_va_any (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap
  ∧ inp.in_abort_terminal = false
  ∧ valid_urandom inp

theorem valid_input_va_size (inp : ProcInput) (h : valid_input inp) :
    inp.in_va_size = .Sv48 := by
  unfold valid_input at h
  grind

/-- THE ABORT DECLARATION, as an accessor rather than as a position.
    `valid_input` pins `State.in_abort_terminal` to `false` — that is what
    makes `Kernel.Signal.tkill_spec` decline every call under it, and
    therefore what makes a `State.KillEv` unreachable for every statement
    quantified over this predicate (`sstep_off_no_kill`).  Consumers want that
    one clause and nothing else.

    NAMED, BECAUSE THE POSITION MOVES.  This predicate grows a conjunct
    whenever the input class learns to say something new, and a caller that
    reached in by position (`intros inp (_ & … & H & _)`) then names a
    DIFFERENT clause rather than failing — it goes on compiling and quietly
    stops being about the declaration.  Callers should take this lemma
    instead, so that an insertion is one re-proof here and none anywhere else.

    The proof is itself position-independent: it splits every conjunction and
    lets `assumption` find the clause of the right shape, so an insertion does
    not re-break it either.  `valid_input_va_size` above and
    `valid_input_abort_va_size` below read the same way, for the same
    reason. -/
theorem valid_input_abort_terminal (inp : ProcInput) (h : valid_input inp) :
    inp.in_abort_terminal = false := by
  unfold valid_input at h
  grind

/-- THE RANDOM-STREAM CLAUSE, as an accessor rather than as a position, and
    for the reason above: it is the LAST conjunct today, so a caller that
    reached in by position would be the first thing the next insertion breaks.
    It is also the clause with no computational content — `stream_infinite` is
    coinductive-style (a `∀ n`, not a colist) — so a consumer that wants it
    wants it by name.

    `Checks.Examples.the_random_clause_is_what_the_fixture_carries` fires it
    in both directions: the fixtures satisfy it, and the empty declaration
    does not. -/
theorem valid_input_urandom (inp : ProcInput) (h : valid_input inp) :
    valid_urandom inp := by
  unfold valid_input valid_urandom at *
  grind

/-- The same clause under the declared stance, where it is `true`. -/
theorem valid_input_abort_abort_terminal (inp : ProcInput)
    (h : valid_input_abort inp) : inp.in_abort_terminal = true := by
  unfold valid_input_abort at h
  grind

/-- Both abort stances pin the same size. -/
theorem valid_input_abort_va_size (inp : ProcInput) (h : valid_input_abort inp) :
    inp.in_va_size = .Sv48 := by
  unfold valid_input_abort at h
  grind

theorem valid_input_va_any_of_valid_input (inp : ProcInput) (h : valid_input inp) :
    valid_input_va_any inp := by
  unfold valid_input at h
  unfold valid_input_va_any
  grind

theorem valid_input_va_any_of_valid_input_sv39 (inp : ProcInput)
    (h : valid_input_sv39 inp) : valid_input_va_any inp := by
  unfold valid_input_sv39 at h
  unfold valid_input_va_any
  grind

theorem valid_input_va_any_of_valid_input_sv57 (inp : ProcInput)
    (h : valid_input_sv57 inp) : valid_input_va_any inp := by
  unfold valid_input_sv57 at h
  unfold valid_input_va_any
  grind

/-- Exhaustiveness as a lemma: an input the shared clauses accept satisfies
    exactly one of the three pinned predicates, because the declaration has
    three values. -/
theorem valid_input_va_any_splits (inp : ProcInput) (h : valid_input_va_any inp) :
    valid_input inp ∨ valid_input_sv39 inp ∨ valid_input_sv57 inp := by
  unfold valid_input_va_any at h
  cases hv : inp.in_va_size with
  | Sv39 => exact Or.inr (Or.inl (by unfold valid_input_sv39; grind))
  | Sv48 => exact Or.inl (by unfold valid_input; grind)
  | Sv57 => exact Or.inr (Or.inr (by unfold valid_input_sv57; grind))

/-! ## The hardware-capability declaration: the same predicate per word

    `valid_hwcap` admits two words and THE DEFAULT STAYS THAT DISJUNCTION.
    The reason is the one its own comment gives: `RiscvSemantics`'s decoder
    answers a word it cannot decode with `MachineUnmodeled` rather than a
    trap, so the model does not claim the hart lacks V and must not publish a
    word that says so.  Nothing below weakens that.  What the two predicates
    add is the TASK's declaration — "the kernel this task runs under publishes
    THIS word" — in the shape `valid_input_sv39` gives the address-space
    declaration, and for the same reason: what a proof was made under has to
    be readable in the statement.

    NAMED PREDICATES RATHER THAN A PARAMETER.  A predicate parameterised by
    the word could be instantiated at a word `valid_hwcap` refuses — the zero
    the absent entry effectively delivered, an A-less mask, a mask with a
    letter `riscv_fill_hwcap` never assigns — and the resulting statement
    would hold VACUOUSLY, since no launch produces such an input.  Two
    definitions cannot be instantiated at all, and `valid_input_hwcap_splits`
    says the pair is exactly the default.

    WHY A TASK WOULD DECLARE.  Under the permissive default a statement ranges
    over both words, so a runtime that dispatches on the V bit must be
    equivalent under `hwcap_rv64gcv` too, and the first vector instruction it
    executes is a word `DecodeC.decodeAny` returns `none` for: the run is
    `MachineUnmodeled` and the statement is FALSE as issued.  That answer does
    not change here.  What changes is that a task can say which hart it runs
    on.  The case that motivates it is the PROBE: a binary that reads `vlenb`
    — a V-extension CSR — only to learn whether a vector unit is there.  That
    read DECODES, unlike the vector instruction; what declines it is
    `Sem.csr_slice`, which resolves only the fcsr aliases, so `Sem.exec_csr`
    answers `Sem.EIllegal` and the run is `MachineUnmodeled` all the same
    (`Checks.Cases.Hwcap` pins each level, and `Checks/Cases/Hwcap.lean`
    pins the composition itself as
    `the_vlenb_probe_leaves_the_modeled_surface`).  Under the
    permissive default every statement about such a binary is false; under
    `valid_input_hwcap_rv64gc` the advertised word has no V bit, the probe is
    never taken, and the statement is the one the task can prove.  The
    declaration is the TASK's claim about its environment, not the model's
    claim about the silicon, which is why it is a field of the input and a
    predicate over that field rather than anything the spec arms read.

    BOTH KEEP THE ABORT DECLARATION OFF AND THE SIZE AT Sv48, exactly as
    `valid_input_sv39` does.  The abort stance has its own pair below
    (`valid_input_abort_hwcap_rv64gc` and its twin), because a task asked for
    that cell.  A task wanting a declared word together with another
    address-space size, or with the stance left open, has no predicate here
    yet, and the day one is needed it is written the way these are. -/
def valid_input_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc
  ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

def valid_input_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv
  ∧ inp.in_abort_terminal = false
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

/-- Each declaration is a NARROWING of the default, so a statement quantified
    over `valid_input` is about every input either predicate accepts.  That
    direction is what makes the declaration a restriction on the task rather
    than a widening of the theorem. -/
theorem valid_input_of_valid_input_hwcap_rv64gc (inp : ProcInput)
    (h : valid_input_hwcap_rv64gc inp) : valid_input inp := by
  unfold valid_input_hwcap_rv64gc at h
  unfold valid_input valid_hwcap
  grind

theorem valid_input_of_valid_input_hwcap_rv64gcv (inp : ProcInput)
    (h : valid_input_hwcap_rv64gcv inp) : valid_input inp := by
  unfold valid_input_hwcap_rv64gcv at h
  unfold valid_input valid_hwcap
  grind

/-- …and the two are EXHAUSTIVE on the default, because `valid_hwcap` is a
    two-word disjunction and nothing else in `valid_input` mentions the field.
    This is the lemma that makes the default "the two" rather than "at least
    the two": there is no third word a statement quantified over `valid_input`
    would be held to and neither declaration covers. -/
theorem valid_input_hwcap_splits (inp : ProcInput) (h : valid_input inp) :
    valid_input_hwcap_rv64gc inp ∨ valid_input_hwcap_rv64gcv inp := by
  unfold valid_input at h
  unfold valid_hwcap at h
  unfold valid_input_hwcap_rv64gc valid_input_hwcap_rv64gcv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  rcases h8 with h8 | h8
  · exact Or.inl ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact Or.inr ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The declared word, read back out of the predicate.  A statement's consumer
    needs this to know WHICH word the auxv publishes under the declaration
    (`StackLayout.auxv_entries` carries `in_hwcap` verbatim), and
    `Checks/Cases/Hwcap.lean` fires it to say so, per declaration
    (`the_rv64gc_declaration_publishes_the_v_less_word` and its `rv64gcv`
    twin, both quantified over every input the declaration accepts). -/
theorem valid_input_hwcap_rv64gc_word (inp : ProcInput)
    (h : valid_input_hwcap_rv64gc inp) : inp.in_hwcap = hwcap_rv64gc := by
  unfold valid_input_hwcap_rv64gc at h
  grind

theorem valid_input_hwcap_rv64gcv_word (inp : ProcInput)
    (h : valid_input_hwcap_rv64gcv inp) : inp.in_hwcap = hwcap_rv64gcv := by
  unfold valid_input_hwcap_rv64gcv at h
  grind

/-- ** The same declaration under the ABORT stance

    The two predicates above pin the abort declaration OFF, because that is
    the stance `valid_input` pins and the one every statement written before
    the abort path had an arm quantifies over.  A task whose binary probes for
    a vector unit AND wants the abort path modeled needs the other cell, so it
    is written here rather than left for the day it is asked for: the
    conjuncts of `valid_input_abort` verbatim, with `valid_hwcap (in_hwcap
    inp)` replaced by the equation.

    WHICH CELLS EXIST AFTER THIS.  The declaration crosses with the abort
    stance and with nothing else.  `valid_input_either` gets no hwcap
    predicate — a statement that declines to choose a stance is the
    conjunction of the two that do, so a task wanting both a declared word and
    no stance proves the two declared statements — and neither do
    `valid_input_sv39`, `valid_input_sv57` or `valid_input_va_any`, because no
    task runs on another kernel and probes for V.  A task wanting one of those
    combinations has no predicate here yet, and the day one is needed it is
    written the way these are. -/
def valid_input_abort_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc
  ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

def valid_input_abort_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ Fs.valid_fs (in_fs inp)
  ∧ Fs.fs_keys_relative inp.in_image_fs
  ∧ valid_creds inp ∧ valid_nofile inp.in_nofile
  ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv
  ∧ inp.in_abort_terminal = true
  ∧ inp.in_va_size = .Sv48
  ∧ valid_urandom inp

theorem valid_input_abort_of_valid_input_abort_hwcap_rv64gc (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gc inp) : valid_input_abort inp := by
  unfold valid_input_abort_hwcap_rv64gc at h
  unfold valid_input_abort valid_hwcap
  grind

theorem valid_input_abort_of_valid_input_abort_hwcap_rv64gcv (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gcv inp) : valid_input_abort inp := by
  unfold valid_input_abort_hwcap_rv64gcv at h
  unfold valid_input_abort valid_hwcap
  grind

theorem valid_input_abort_hwcap_splits (inp : ProcInput) (h : valid_input_abort inp) :
    valid_input_abort_hwcap_rv64gc inp ∨ valid_input_abort_hwcap_rv64gcv inp := by
  unfold valid_input_abort at h
  unfold valid_hwcap at h
  unfold valid_input_abort_hwcap_rv64gc valid_input_abort_hwcap_rv64gcv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  rcases h8 with h8 | h8
  · exact Or.inl ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · exact Or.inr ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem valid_input_abort_hwcap_rv64gc_word (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gc inp) : inp.in_hwcap = hwcap_rv64gc := by
  unfold valid_input_abort_hwcap_rv64gc at h
  grind

theorem valid_input_abort_hwcap_rv64gcv_word (inp : ProcInput)
    (h : valid_input_abort_hwcap_rv64gcv inp) : inp.in_hwcap = hwcap_rv64gcv := by
  unfold valid_input_abort_hwcap_rv64gcv at h
  grind

/- =========================================================================
   The image premise, consumed: the device arms' guards are unreachable
   =========================================================================

   `valid_input`'s `Fs.fs_keys_relative` conjunct is a premise about the
   environment, and a premise earns its place by being USED.  What it is for is
   here: the three device arms of `Sys.Fs.Open` and the key lookup of
   `Sys.Fs.Stat.newfstatat_core_spec` each ask the initial file system whether
   it holds an absolute path, or something under it, and answer `unmodeled`
   when it does.  Under the premise it never does, so those branches are dead
   on every valid input and the guards stay in the arms as the courtesy their
   comments say they are — NO ARM IS CHANGED by this: the premise makes the
   guards dead, it does not delete them.

   The lemmas live here rather than in `State` because they name
   `Sys.Fs.Namei.fs_under` and the arms' own path constants, which sit above
   `State.lean`; the seeding half of the argument
   (`State.seeded_absolute_key_is_tmp`) is down there where the seeding is. -/

/-- THE ONE FACT THE ARMS NEED.  `p` begins with the separator and DIVERGES
    from the seeding prefix at a byte position both of them have.  Then no key
    of a seeded image is `p`, and none lives under it — so `Fs.fs_lookup`
    misses and `Sys.Fs.Namei.fs_under` is false.

    Both halves come from `State.seeded_absolute_key_is_tmp`: a key is
    relative, and then it does not even start the way `p` does, or the seeding
    minted it and it is `State.tmp_key n`, which agrees with
    `State.tmp_prefix` at position `i` where `p` does not.  The divergence is
    stated as an index rather than as "p is not under /tmp" because the
    `fs_under` half needs more than non-prefixhood: "/tmp" is not a /tmp key
    and yet every /tmp key lives under it. -/
theorem absolute_divergent_not_seeded (fs t : Fs.Fs) (r : Fs.path) (i : Nat)
    (a b : byte)
    (Hrel : Fs.fs_keys_relative fs)
    (Hp : (Fs.path_slash_byte :: r)[i]? = some a)
    (Ht : tmp_prefix[i]? = some b)
    (Hab : a ≠ b) :
    Fs.fs_lookup (fs_seed_tmp fs t) (Fs.path_slash_byte :: r) = none
    ∧ Sys.Fs.Namei.fs_under (fs_seed_tmp fs t) (Fs.path_slash_byte :: r) = false := by
  have Hi : i < (Fs.path_slash_byte :: r).length :=
    (List.getElem?_eq_some_iff.mp Hp).1
  have Hj : i < tmp_prefix.length := (List.getElem?_eq_some_iff.mp Ht).1
  have Hall := seeded_absolute_key_is_tmp t fs Hrel
  constructor
  · apply Fs.fs_lookup_none_of_keys
    rintro ⟨q, d⟩ hqd heq
    obtain hq | ⟨n, hq⟩ := Hall (q, d) hqd
    · rw [heq] at hq
      simp only [Fs.key_is_relative] at hq
      exact hq rfl
    · have hqp : q = Fs.path_slash_byte :: r := heq
      have hq' : q = tmp_key n := hq
      rw [hq'] at hqp
      have hx : (tmp_key n)[i]? = some b := by
        rw [tmp_key, List.getElem?_append_left Hj]
        exact Ht
      rw [hqp] at hx
      rw [Hp] at hx
      exact Hab (Option.some.inj hx)
  · apply Sys.Fs.Namei.fs_under_false_of_keys
    rintro ⟨q, d⟩ hqd
    change Sys.Fs.Namei.dir_prefixb (Fs.path_slash_byte :: r) q = false
    obtain hq | ⟨n, hq⟩ := Hall (q, d) hqd
    · cases q with
      | nil => rfl
      | cons c q' =>
        simp only [Fs.key_is_relative] at hq
        have hc : bv_eqb Fs.path_slash_byte c = false := by
          cases h : bv_eqb Fs.path_slash_byte c with
          | false => rfl
          | true => exact absurd ((Fs.bv_eqb_eq _ _).mp h).symm hq
        simp only [Sys.Fs.Namei.dir_prefixb, hc, Bool.false_and]
    · have hq' : q = tmp_key n := hq
      cases hd : Sys.Fs.Namei.dir_prefixb (Fs.path_slash_byte :: r) q with
      | false => rfl
      | true =>
        exfalso
        rw [hq'] at hd
        obtain ⟨rest, hrest⟩ := Sys.Fs.Namei.dir_prefixb_app _ _ hd
        have hx : (tmp_key n)[i]? = some b := by
          rw [tmp_key, List.getElem?_append_left Hj]
          exact Ht
        rw [hrest, List.getElem?_append_left Hi] at hx
        rw [Hp] at hx
        exact Hab (Option.some.inj hx)

/-- The three DEVICE paths of `Sys.Fs.Open`, each of which diverges from "/tmp/"
    at its second byte ('d', 'e', 'd' against 't').  This is the statement the
    arms' image guards are unreachable: each reads `fs_lookup (m_fs m) p` and,
    on `none`, `fs_under (m_fs m) p`, so both branches that answer `unmodeled`
    there are ruled out.  The paths are the arms' OWN constants, so a path that
    moves moves here too. -/
theorem device_paths_never_seeded (fs t : Fs.Fs) (p : Fs.path)
    (Hrel : Fs.fs_keys_relative fs)
    (Hin : p ∈ [Sys.Uapi.devnull_path, Sys.Fs.Open.localtime_path,
                Sys.Uapi.urandom_path]) :
    Fs.fs_lookup (fs_seed_tmp fs t) p = none
    ∧ Sys.Fs.Namei.fs_under (fs_seed_tmp fs t) p = false := by
  have Hd : (BitVec.ofInt 8 100) ≠ (BitVec.ofInt 8 116) := by decide
  have He : (BitVec.ofInt 8 101) ≠ (BitVec.ofInt 8 116) := by decide
  rcases List.mem_cons.mp Hin with rfl | Hin
  · exact absolute_divergent_not_seeded fs t _ 1 _ _ Hrel (by decide) (by decide) Hd
  rcases List.mem_cons.mp Hin with rfl | Hin
  · exact absolute_divergent_not_seeded fs t _ 1 _ _ Hrel (by decide) (by decide) He
  rcases List.mem_cons.mp Hin with rfl | Hin
  · exact absolute_divergent_not_seeded fs t _ 1 _ _ Hrel (by decide) (by decide) Hd
  · exact absurd Hin (by simp)

/-- The same, at a model whose file system is the run's initial one.

    `m` is any model carrying `State.in_fs inp` — the initial model
    `State.init_model` builds is one, and so is every later state that has not
    written the map.  Whether a LATER state can be one is a question about the
    write arms rather than about the premise: the only specs that mint a key
    are `Sys.Fs.Open`'s create arms, which sit behind the separator gate, and
    the /tmp arm, whose key is `State.tmp_key` of one component — so no
    run-time creation puts a device path in the map.  That is an argument
    about arms this lemma does not quantify over, so it is said here and not
    claimed by the statement. -/
theorem valid_input_device_guards_unreachable (inp : ProcInput) (m : Model) (p : Fs.path)
    (Hrel : Fs.fs_keys_relative inp.in_image_fs)
    (Hm : m_fs m = in_fs inp)
    (Hin : p ∈ [Sys.Uapi.devnull_path, Sys.Fs.Open.localtime_path,
                Sys.Uapi.urandom_path]) :
    Fs.fs_lookup (m_fs m) p = none ∧ Sys.Fs.Namei.fs_under (m_fs m) p = false := by
  rw [Hm]
  unfold in_fs
  exact device_paths_never_seeded _ _ p Hrel Hin

/-- `Sys.Fs.Stat.newfstatat_core_spec`'s half of the same fact.  That spec
    answers `unmodeled` when the path it was handed IS a key, and -ENOENT when
    it is not; under the premise every absolute pathname that is not a /tmp key
    misses, so the `unmodeled` branch is unreachable for it and the answer is
    the real -ENOENT.  Stated over the divergence index rather than over a list
    of paths, because `newfstatat` takes its path from the program rather than
    from a constant. -/
theorem valid_input_absolute_key_absent (inp : ProcInput) (m : Model) (r : Fs.path)
    (i : Nat) (a b : byte)
    (Hrel : Fs.fs_keys_relative inp.in_image_fs)
    (Hm : m_fs m = in_fs inp)
    (Hp : (Fs.path_slash_byte :: r)[i]? = some a)
    (Ht : tmp_prefix[i]? = some b)
    (Hab : a ≠ b) :
    Fs.fs_lookup (m_fs m) (Fs.path_slash_byte :: r) = none
    ∧ Sys.Fs.Namei.fs_under (m_fs m) (Fs.path_slash_byte :: r) = false := by
  rw [Hm]
  unfold in_fs
  exact absolute_divergent_not_seeded _ _ r i a b Hrel Hp Ht Hab

/-! ## Sanity checks

    There were no closed goals to re-use here, so these are added: they pin
    the computable pieces of the
    trace layer (the prefix predicate, the spurious-failure configuration
    order and injection table, the budget mark's syscall list, and the
    validity bounds) to concrete values, so a transcription error shows up
    as a failing `decide` rather than as a silently different theorem. -/

section Sanity

example : is_prefix [1, 2] [1, 2, 3] := by simp [is_prefix]

example : ¬ is_prefix [1, 3] [1, 2] := by simp [is_prefix]

example : forced_only_cfg ≠ may_fail_cfg := by decide

example : family_may_fail (alloc_only_cfg true) .FamAlloc = true := rfl

example : family_may_fail (alloc_only_cfg false) .FamAlloc = false := rfl

example : family_may_fail forced_only_cfg .FamCred = false := rfl

example : cfg_le forced_only_cfg may_fail_cfg :=
  fun f _ => by cases f <;> rfl

example : injected_arm 222 = some ⟨222, .FamAlloc, [ENOMEM]⟩ := by decide

example : injected_arm 101 = some ⟨101, .FamIntr, [EINTR]⟩ := by decide

example : injected_arm 1 = none := by decide

example : injected_arm 199
    = some ⟨199, .FamFd,
        Sys.Net.Socket.socketpair_reserve_errnos
          ++ Sys.Net.Socket.socketpair_create_errnos⟩ := by decide

example : alloc_mark_sysnos = [214, 216, 222, 226] := rfl

example : entry_stack_span_max = 2238671 := rfl

example : entry_stack_span [] [] = 8 + 8 + 8 + 160 + 7 + 16 := by decide

example : valid_nofile (BitVec.ofInt 64 1024) := by unfold valid_nofile; decide

example : ¬ valid_nofile (BitVec.ofInt 64 2147483647) := by
  unfold valid_nofile; decide

example : valid_id (BitVec.ofInt 64 1000) := by unfold valid_id; decide

example : ¬ valid_id (BitVec.ofInt 64 4294967295) := by unfold valid_id; decide

example : valid_hwcap hwcap_rv64gc := Or.inl rfl

example : ¬ valid_hwcap (BitVec.ofInt 64 0) := by unfold valid_hwcap; decide

example : valid_brk [] (BitVec.ofInt 64 0) := by unfold valid_brk; decide

example : ¬ valid_mmap_base (BitVec.ofInt 64 0) := by
  unfold valid_mmap_base; decide

end Sanity

/- =========================================================================
   The finer premise: budget refusals only, oversize ones not excluded
   ========================================================================= -/

/-- A refusal classified `.RefuseBudget` IS a refusal: the classifier
    only names the cause. -/
theorem refuse_reason_budget_implies_refused (i : SyscallInput) (m : Model)
    (h : alloc_refuse_reason i m = some .RefuseBudget) :
    alloc_budget_refused_b i m = true := by
  unfold alloc_refuse_reason at h
  by_cases hb : alloc_budget_refused_b i m = true
  · exact hb
  · rw [ite_eq_right hb] at h
    exact absurd h (by simp)

/-- `budget_refused_at` with the grant disjunct narrowed to
    `alloc_refuse_reason i m = some .RefuseBudget`; the two first-touch
    clauses are unchanged.  It implies `budget_refused_at`, so
    `¬ run_budget_only_refused` admits every input
    `¬ run_budget_refused` admits, and also those whose only refusal is
    oversize — one request whose charge alone exceeds the whole budget. -/
def budget_only_refused_at (segs : List Segment) (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
  ( (c.cfg_ms.ms_svc_pending = none ∧
     ∃ report,
       step_accesses segs c.cfg_ms = .MachineOk report ∧
       materialize_model_accesses c.cfg_model report.accessed_ranges = none)
  ∨ (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
       ( alloc_refuse_reason (sys_input segs c.cfg_ms x8) c.cfg_model = some .RefuseBudget
       ∨ ∃ (eff : SyscallEffect) (model' : Model) (evs : List event),
            Specs.syscall_spec (sys_input segs c.cfg_ms x8) c.cfg_model (.ok eff model' evs)
            ∧ m_halted model' = none
            ∧ materialize_model_accesses model' (syscall_effect_accesses eff) = none)) )

theorem budget_only_refused_at_implies (segs : List Segment) (c : config)
    (h : budget_only_refused_at segs c) : budget_refused_at segs c := by
  obtain ⟨Hh, Hd⟩ := h
  refine ⟨Hh, ?_⟩
  rcases Hd with ⟨Hnone, report, hstep, hmat⟩ | ⟨x8, hsvc, h | h⟩
  · exact Or.inl ⟨Hnone, report, hstep, hmat⟩
  · exact Or.inr ⟨x8, hsvc, Or.inl (refuse_reason_budget_implies_refused _ _ h)⟩
  · obtain ⟨eff, model', evs, hspec, hhalt, hmat⟩ := h
    exact Or.inr ⟨x8, hsvc, Or.inr ⟨eff, model', evs, hspec, hhalt, hmat⟩⟩

/-- The run can reach a configuration refused for budget only. -/
def reaches_budget_only_refused (segs : List Segment) (c0 : config) : Prop :=
  ∃ tr c, star segs c0 tr c ∧ budget_only_refused_at segs c

theorem reaches_budget_only_refused_implies (segs : List Segment) (c0 : config)
    (h : reaches_budget_only_refused segs c0) : reaches_budget_refused segs c0 := by
  obtain ⟨tr, c, hstar, hb⟩ := h
  exact ⟨tr, c, hstar, budget_only_refused_at_implies segs c hb⟩

/-- The run-level form of the finer premise, the `match` of `run`.
    `Equivalence.source_within_budget_only` negates it. -/
def run_budget_only_refused (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  reaches_budget_only_refused img.img_segments
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem run_budget_only_refused_implies (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) (h : run_budget_only_refused img lim en inp) :
    run_budget_refused img lim en inp :=
  reaches_budget_only_refused_implies _ _ h

/-- The configured form, over `star_cfg`, beside
    `reaches_budget_refused_cfg`.  The same lifts hold: to the configured
    released mark, to the unfiltered finer mark (a configuration removes
    executions and adds none), and the two agree at `may_fail_cfg`. -/
def reaches_budget_only_refused_cfg (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ budget_only_refused_at segs c

theorem reaches_budget_only_refused_cfg_implies (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) (h : reaches_budget_only_refused_cfg segs cfg c0) :
    reaches_budget_refused_cfg segs cfg c0 := by
  obtain ⟨tr, c, hstar, hb⟩ := h
  exact ⟨tr, c, hstar, budget_only_refused_at_implies segs c hb⟩

theorem reaches_budget_only_refused_cfg_sub (segs : List Segment) (cfg : SpuriousCfg)
    (c0 : config) (h : reaches_budget_only_refused_cfg segs cfg c0) :
    reaches_budget_only_refused segs c0 := by
  obtain ⟨tr, c, hstar, hb⟩ := h
  exact ⟨tr, c, star_cfg_sub segs cfg _ _ _ hstar, hb⟩

theorem reaches_budget_only_refused_cfg_may_fail (segs : List Segment) (c0 : config) :
    reaches_budget_only_refused segs c0
      ↔ reaches_budget_only_refused_cfg segs may_fail_cfg c0 := by
  constructor
  · rintro ⟨tr, c, hstar, hb⟩
    exact ⟨tr, c, (star_cfg_may_fail segs _ _ _).mp hstar, hb⟩
  · intro h
    exact reaches_budget_only_refused_cfg_sub segs may_fail_cfg c0 h

/-- The configured run's form of the finer premise, the `match` of
    `run_scfg`. -/
def run_scfg_budget_only_refused (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  reaches_budget_only_refused_cfg img.img_segments cfg
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem run_scfg_budget_only_refused_implies (cfg : SpuriousCfg) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : run_scfg_budget_only_refused cfg img lim en inp) :
    run_scfg_budget_refused cfg img lim en inp :=
  reaches_budget_only_refused_cfg_implies _ cfg _ h

theorem run_scfg_budget_only_refused_sub (cfg : SpuriousCfg) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h : run_scfg_budget_only_refused cfg img lim en inp) :
    run_budget_only_refused img lim en inp :=
  reaches_budget_only_refused_cfg_sub _ cfg _ h

theorem run_scfg_budget_only_refused_may_fail (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    run_budget_only_refused img lim en inp
      ↔ run_scfg_budget_only_refused may_fail_cfg img lim en inp :=
  reaches_budget_only_refused_cfg_may_fail _ _

end LinuxSem.LinuxProcessSem.Run
