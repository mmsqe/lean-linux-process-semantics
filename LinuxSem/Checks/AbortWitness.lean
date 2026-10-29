/-
  * LinuxSem.Checks.AbortWitness — an image that really aborts

  Not part of the trusted specification: this file is QA on the
  definitions, in the sense `Checks/Examples` describes, and it
  exists to close one specific gap in that file's abort-family
  statements.

  ** The gap

  `Equivalence.error_free_unkilled` is `Equivalence.error_free` plus
  "and it is not killed", and the abort-declared statement family is
  stated with it.  Two things suggest that the extra conjunct is doing
  work, and both stop short of a run:

  - `Equivalence.error_free_unkilled_bites` exhibits a `behavior` whose
    trace set contains a `State.KillEv`.  That behavior is HAND-WRITTEN.
    It shows the two PREDICATES differ on something of the right type;
    it does not show that any IMAGE separates them, and a `Run.behavior`
    is a record of bare `Prop`s, so nothing stops one being written
    that no `Run.run` returns.
  - `Equivalence.strong_universal_error_free_T_abort_refuted_by_abort`
    takes `Equivalence.dies_by_signal (Run.run …)` as a HYPOTHESIS.
    Without an image that discharges it, the abort family's refutation
    is stated conditionally and never fires.  A conditional refutation
    whose condition is never met is indistinguishable, from inside the
    development, from one whose condition is unsatisfiable.

  This file supplies the missing half: a concrete six-instruction image
  whose run reaches `State.KillEv`, and the two statements that fall
  out of it — `abrt_dies_by_signal`, which discharges the hypothesis,
  and `abrt_refutes_error_free_abort`, which is the refutation actually
  fired at a real image.  It is the abort-declared twin of
  `Checks.Examples.undecodable_image_refutes_error_free_equivalence`,
  and it is deliberately built the way that one is: at a valid entry,
  on a valid input, so that a statement quantified over those is really
  reached.

  ** Why an image is needed rather than a longer argument

  `Equivalence.dies_by_signal` is read off `Run.behavior`'s trace set,
  and `Run.run`'s trace set is `Run.obs_trace` of the initial
  configuration — an existential over `Run.star`.  So the only way to
  satisfy it is to walk a real execution, and walking one is what
  catches the things prose does not: that the tid the `tkill` names has
  to be the one the model CHOSE rather than a constant the image
  carries, that the choice is made by a syscall the program has to
  issue first, and that `Run.sstep_killed` rather than `Run.sstep_exit`
  is the rule that fires at the end.

  ** The program

  Six instructions at 0x100, the shortest that can abort under this
  model, written as the hex a loader would have produced:

  #<pre>
    addi a7, x0, 96     06000893   set_tid_address
    addi a0, x0, 0      00000513   tidptr = NULL
    ecall               00000073   -> a0 = the tid the model chose
    addi a7, x0, 130    08200893   tkill
    addi a1, x0, 6      00600593   SIGABRT
    ecall               00000073   -> killed
  #</pre>

  THE FIRST SYSCALL IS NOT CEREMONY.  `Kernel.Signal.tkill_self`
  declines with `Monad.unmodeled` while `State.m_tid` is `None`, and
  declines again unless the `pid` it is handed EQUALS the recorded tid.
  `Kernel.Fork.set_tid_address_spec` is what pins it, and it pins it to
  a value drawn with `Monad.choose` from the whole
  `Kernel.Fork.PID_MAX_ENVELOPE` window — the model cannot predict it,
  exactly as it cannot predict getrandom's bytes.  So no image can
  carry the right `pid` as an immediate.  What makes this program work
  is that `Run.apply_effect` writes the syscall's return value into a0
  and neither instruction between the two `ecall`s touches a0, so the
  tid flows from the kernel's answer straight into `tkill`'s first
  argument.  That is musl's own arrangement read back one level:
  `__init_tp` seeds `__pthread_self()->tid` from `set_tid_address`, and
  `raise` sends to it.

  The choice is why this file's `abrt_eff1` names 4242: any value in
  the window would do, this is one, and it is
  `Cases.Kernel.Signal.abort_tid` so that the fixture and the run agree.

  THE MASK IS THE OTHER PREMISE.  `abrt_input` launches with
  `State.in_sigmask` clear, so SIGABRT is not blocked and
  `Kernel.Signal.send_sigabrt` takes the `State.with_killed` branch
  rather than the `State.with_sigabrt_pending` one.  musl's real
  `raise` blocks first and dies on the mask restore two calls later;
  that longer path is deliberately NOT what this file
  walks — the shortest path to a `State.KillEv` is what a non-vacuity
  witness wants.

  ADMISSION REASON: what is pinned here is that a `Run.run`'s TRACE SET
  contains a
  `State.KillEv`, which is a statement about the model's own execution
  relation, not about anything a real run reveals.

  ** LOCAL HELPERS

  Six local helpers exist, named so that they cannot be mistaken for
  specification: `abrt_svc_none` / `abrt_svc_none2` (the pending-syscall
  field along the two instruction legs, which are otherwise closed by
  `reflexivity`), `abrt_t_zero` (a `replace`, named once), and
  `abrt_sigmask_not_blocked` / `check_tkill_kills` / `check_syscall_tkill`
  (the `tkill` checker at a variable model — see the route note below).
  No proof hole remains anywhere.

  ** ROUTE: assemble, do not reduce

  The run goes through machine states that still contain a variable
  (`abrt_msk k`'s `k`, and the abstracted memory of `abrt_s`/`abrt_t`),
  and a free variable inside the state blocks kernel reduction of the
  whole chain, so a `rfl`/`decide` replay of those steps does not
  terminate.  This file therefore ASSEMBLES the computation the way
  `Checks.Omni`'s `wloop_*` family does: `abrt_step`/`abrt_step2` are
  one `Checks.Omni.istep` per concrete `k` with the memory abstracted,
  the instruction transitions go through `Run.sstep.instr`, and the two
  syscall transitions go through `Run.sstep.syscall`/`Run.sstep.killed`
  with the checker's verdict supplied by `abrt_sc1`/`abrt_sc2` through
  `Checks.ExecutableSpecs.check_syscall_ok_iff`.  The verdicts
  themselves ARE closed computations — `abrt_sc1`, `abrt_sc2`,
  `abrt_sc1_admits_another_tid`, the two declines and the three
  `ms_svc_pending` pins are `rfl`/`decide` — because the checker reads
  only scalar fields (`m_abort_terminal`, `m_tid`, `m_sigmask`) and
  never the abstracted memory.

  THE ONE EXCEPTION is the second syscall: `check_send_sigabrt` tests
  `sigabrt_blocked (m_sigmask m)`, a `BitVec 64` conjunction over a mask
  field, and with the budget `lim` FREE that test does not reduce — the
  same limit, one field at a time.  So the
  verdict is ASSEMBLED there too: `abrt_sigmask_not_blocked` reduces the
  mask itself to `0` (where `lim` does not block the reduction),
  `check_tkill_kills` is the arm's walk at a model described by hypotheses,
  and `check_syscall_tkill` is the dispatcher at 130 —
  `Checks/Sys/DispatchCompute.lean` has no arm for that number.  The two
  verdicts `abrt_sc2` and `abrt_tkill_other_tid_declined` then follow from
  those three plus `rfl`/`decide` on the scalars.

  ** Spelling

  `Z` is `Int`; `bv n`/`word`/`byte` are `BitVec n`/`BitVec 64`/`BitVec 8`;
  `Z_to_bv n z` is `BitVec.ofInt n z`; `mkCfg ms model` is the `config`
  constructor `⟨ms, model⟩`; `SNext`/`SError` are
  `step_to.SNext`/`.SError`; `Ok`/`Unmodeled` are `.ok`/`.unmodeled`;
  `CheckOk`/`CheckUnmodeled` are `.CheckOk`/`.CheckUnmodeled`; `mkEffect`
  is `State.mkEffect`; `mkImage` is `Equivalence.mkImage`; an `Example`
  is spelled `theorem`;
  A closed computation on a CLOSED goal is `by decide` where the
  goal is a decidable equality and `by rfl` where it is not (a checker
  verdict carries a `Model`, which has no `DecidableEq`).
-/
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Examples
import LinuxSem.Checks.Omni
import LinuxSem.Checks.Cases.Kernel.Signal
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Omni
open LinuxSem.Checks.Cases.Kernel.Signal (abort_tid)
open LinuxSem.Checks.Examples (demo_entry)
open LinuxSem.LinuxProcessSem.Sys.Syscall (pid32 w_is0)
open LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
  (sig32 sigabrt_blocked pid_positive tkill_sig_valid)
open LinuxSem.LinuxProcessSem.Sys.Uapi (SIGABRT)
open LinuxSem.Checks.Sys.Kernel.Signal
  (check_tkill check_tkill_self check_send_sigabrt)
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Checks.AbortWitness

/- =========================================================================
   The image, the launch, and the two syscall answers
   ========================================================================= -/

def abrt_segment : Segment where
  seg_base := 0x100
  seg_size := 24
  seg_perms := "r-x"
  seg_bytes := ["930800061305000073000000930820089305600073000000"]

def abrt_segments : List Segment := [abrt_segment]

def abrt_image : Image := mkImage abrt_segments 0x100 demo_phdrs

/-- The same launch `Checks.Examples` runs its images on — one empty
    argument, no environment, an empty file system, end of input — with
    the two fields this file needs pinned: `State.in_sigmask` clear, so
    SIGABRT is deliverable, and `State.in_abort_terminal` SET, which is
    what `Run.valid_input_abort` asks for and what
    `Kernel.Signal.tkill_spec` tests first. -/
def abrt_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (BitVec.ofInt 64 0) demo_hwcap true .Sv48

theorem abrt_input_declares_abort : abrt_input.in_abort_terminal = true := rfl

/-- `Run.valid_input_abort`, proved the way
    `Checks.Examples.demo_input_valid` proves `Run.valid_input` — the same
    shared clauses, the same guarded arms, and the abort declaration this
    file is about rather than its negation.

    The eleven clauses come off `demo_input_valid` (the two
    literals are one field apart), and the declaration is supplied by
    `rfl`. -/
theorem abrt_input_valid : valid_input_abort abrt_input := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, h9, h10⟩ :=
    LinuxSem.Checks.Examples.demo_input_valid
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl, h9, h10⟩

/-- The entry is `Checks.Examples.demo_entry`, and it is valid here for
    the reason it is valid there: this image's only segment sits in the
    first page, so the same break base serves, and the fourth conjunct
    is decided by `Run.entry_stack_span_bound` from the argv and envp
    clauses alone — which `Run.valid_input_abort` carries in the same
    two positions `Run.valid_input` does. -/
theorem demo_entry_valid_abrt (inp : ProcInput)
    (Hvalid : valid_input_abort inp) : valid_entry abrt_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk abrt_image abrt_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

/- =========================================================================
   Walking the run
   ========================================================================= -/

/-- The states along the first leg, named by their step count, with the
    memory abstracted exactly as `Checks.Omni`'s `wloop_msk` family
    abstracts it: no instruction of this image writes memory, so every
    state on the way carries the initial one's. -/
def abrt_ms0 : machine_state :=
  init_machine_state abrt_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    abrt_input.in_argv abrt_input.in_envp abrt_input.in_uid abrt_input.in_hwcap

def abrt_msk (k : Nat) : machine_state :=
  match run_steps k abrt_segments abrt_ms0 with
  | some ms => ms
  | none => abrt_ms0

def abrt_s (k : Nat) : machine_state :=
  with_mem (abrt_msk k) abrt_ms0.ms_mem

def abrt_model (lim : Int) : Model :=
  init_model (segments_reserved abrt_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) lim abrt_input

def abrt_c (lim : Int) : config := ⟨abrt_s 0, abrt_model lim⟩

theorem abrt_config (lim : Int) :
    init_config abrt_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim abrt_input
    = abrt_c lim := by
  simp only [abrt_c, abrt_s, abrt_msk, run_steps]
  rw [← with_mem_eta abrt_ms0]
  rfl

theorem abrt_step : ∀ k, k < 3 → ∀ mem,
    RiscvSemantics.step abrt_segments (with_mem (abrt_msk k) mem)
      = .MachineOk (with_mem (abrt_msk (k + 1)) mem) := by
  intro k Hk mem
  rcases k with _ | _ | _ | k
  · istep
  · istep
  · istep
  · omega

/-- The pending-syscall field along the first three instructions: the
    `ecall` is only reached at step three. -/
theorem abrt_svc_none (k : Nat) (Hk : k < 3) : (abrt_s k).ms_svc_pending = none := by
  rcases k with _ | _ | _ | k <;> first | decide | omega

theorem abrt_instr_sstep (lim : Int) (k : Nat) (Hk : k < 3) :
    sstep abrt_segments ⟨abrt_s k, abrt_model lim⟩ []
      (.SNext ⟨abrt_s (k + 1), abrt_model lim⟩) := by
  have hstep : mi_account_step abrt_segments (abrt_s k) (abrt_model lim)
      = .MachineOk (abrt_s (k + 1), abrt_model lim) := by
    no_lazy
    simp only [abrt_s]
    rw [abrt_step k Hk abrt_ms0.ms_mem]
  exact sstep.instr _ _ _ _ rfl (abrt_svc_none k Hk) hstep

/-- Three instructions in -- the two `addi`s and the `ecall` itself, which
    is an ordinary instruction step that leaves the number pending -- the
    first syscall is at the door and its number is 96. -/
theorem abrt_svc3 : (abrt_s 3).ms_svc_pending = some (BitVec.ofInt 64 96) := by
  decide

/-- THE TID THE MODEL CHOOSES.  `Monad.choose` admits any value in the
    window, so this effect names one; `abrt_sc1` is the statement that
    the acceptor agrees it is admissible, and nothing below depends on
    which one it is. -/
def abrt_eff1 : SyscallEffect := mkEffect abort_tid [] []

theorem abrt_sc1 (lim : Int) :
    check_syscall (sys_input abrt_segments (abrt_s 3) (BitVec.ofInt 64 96)) abrt_eff1
      (abrt_model lim)
    = .CheckOk (with_tid abort_tid (abrt_model lim)) [] := by
  rfl

/-- The state the first syscall leaves: a0 holds the tid, and the pc has
    moved past the `ecall`.  This is where the second leg starts. -/
def abrt_t0 : machine_state :=
  advance_past_svc (apply_effect (abrt_s 3) abrt_eff1)

def abrt_tk (k : Nat) : machine_state :=
  match run_steps k abrt_segments abrt_t0 with
  | some ms => ms
  | none => abrt_t0

/-- The second leg abstracts ITS OWN memory rather than `abrt_ms0`'s.
    The two are equal — `abrt_eff1` carries no writes, copies, zeros or
    unmaps, and `Run.apply_effect` touches memory only through those —
    but naming `abrt_t0`'s is what lets `abrt_t 0` be `abrt_t0` by
    `Checks.Omni.with_mem_eta` alone, with no rewriting under
    `State.with_mem`. -/
def abrt_t (k : Nat) : machine_state :=
  with_mem (abrt_tk k) abrt_t0.ms_mem

theorem abrt_t_zero :
    abrt_t 0 = advance_past_svc (apply_effect (abrt_s 3) abrt_eff1) := by
  unfold abrt_t abrt_tk abrt_t0
  simp only [run_steps]
  exact (with_mem_eta _).symm

theorem abrt_syscall1_sstep (lim : Int) :
    sstep abrt_segments ⟨abrt_s 3, abrt_model lim⟩ []
      (.SNext ⟨abrt_t 0, with_tid abort_tid (abrt_model lim)⟩) := by
  rw [abrt_t_zero]
  refine sstep.syscall (ms := abrt_s 3) (model := abrt_model lim)
    (x8 := BitVec.ofInt 64 96) (eff := abrt_eff1)
    (model' := with_tid abort_tid (abrt_model lim))
    (model'' := with_tid abort_tid (abrt_model lim)) (evs := []) ?_ abrt_svc3 ?_ ?_ ?_
  · rfl
  · exact (check_syscall_ok_iff _ _ _ _ _).mp (abrt_sc1 lim)
  · rfl
  · apply materialize_model_accesses_no_lazy
    rfl

theorem abrt_step2 : ∀ k, k < 3 → ∀ mem,
    RiscvSemantics.step abrt_segments (with_mem (abrt_tk k) mem)
      = .MachineOk (with_mem (abrt_tk (k + 1)) mem) := by
  intro k Hk mem
  rcases k with _ | _ | _ | k
  · istep
  · istep
  · istep
  · omega

/-- The pending-syscall field along the second leg's three instructions. -/
theorem abrt_svc_none2 (k : Nat) (Hk : k < 3) : (abrt_t k).ms_svc_pending = none := by
  rcases k with _ | _ | _ | k <;> first | decide | omega

theorem abrt_instr2_sstep (lim : Int) (k : Nat) (Hk : k < 3) :
    sstep abrt_segments
      ⟨abrt_t k, with_tid abort_tid (abrt_model lim)⟩ []
      (.SNext ⟨abrt_t (k + 1), with_tid abort_tid (abrt_model lim)⟩) := by
  have hstep : mi_account_step abrt_segments (abrt_t k)
      (with_tid abort_tid (abrt_model lim))
      = .MachineOk (abrt_t (k + 1), with_tid abort_tid (abrt_model lim)) := by
    no_lazy
    simp only [abrt_t]
    rw [abrt_step2 k Hk abrt_t0.ms_mem]
  exact sstep.instr _ _ _ _ rfl (abrt_svc_none2 k Hk) hstep

/-- Three more instructions, and the second `ecall` is pending at 130. -/
theorem abrt_svc_tkill : (abrt_t 3).ms_svc_pending = some (BitVec.ofInt 64 130) := by
  decide

/-- The kill itself.  a0 carries the tid the first syscall returned, a1
    carries 6, and the post-model is `State.with_killed` — the same
    answer `Cases.Kernel.Signal.tkill_sigabrt_unblocked_kills` pins at a
    hand-built model, here reached from a real machine state whose
    registers the program put there. -/
def abrt_killed_model (lim : Int) : Model :=
  with_killed (BitVec.ofInt 64 6) (with_tid abort_tid (abrt_model lim))

/-! ### The two checker facts the `tkill` step reads

    The checker's own computation is not
    `rfl`-reducible here, because the model carries the run's budget `lim`
    as a FREE VARIABLE and the `sigabrt_blocked` test inside
    `check_send_sigabrt` reads it through a `BitVec 64` conjunction.  The two
    lemmas below split the work: the first turns the blocked-mask test into
    a scalar equality of the mask itself (where `lim` does not block the
    reduction), and the second is the arm's walk at a model described by
    hypotheses rather than by a term.  Neither is part of the
    specification. -/

theorem abrt_sigmask_not_blocked (lim : Int) :
    sigabrt_blocked (m_sigmask (with_tid abort_tid (abrt_model lim))) = false := by
  rw [show m_sigmask (with_tid abort_tid (abrt_model lim)) = BitVec.ofInt 64 0 from rfl]
  rfl

/-- `check_tkill`'s kill path at a model that declares the abort
    path, records `pid` as its tid, is sent SIGABRT, and does not block it.
    This is `Checks.Cases.Kernel.Signal.tkill_sigabrt_unblocked_kills` with
    a variable model and the four facts that make it that case. -/
theorem check_tkill_kills (pid sig : word) (m : Model)
    (hterm : m_abort_terminal m = true) (htid : m_tid m = some pid)
    (hpos : pid_positive pid = true) (hsig : sig = BitVec.ofInt 64 SIGABRT)
    (hblocked : sigabrt_blocked (m_sigmask m) = false) :
    check_tkill pid sig (mkEffect (BitVec.ofInt 64 0) [] []) m
      = .CheckOk (with_killed (BitVec.ofInt 64 SIGABRT) m) [] := by
  have hvalid : tkill_sig_valid (BitVec.ofInt 64 SIGABRT) = true := by decide
  rw [hsig]
  simp [check_tkill, check_tkill_self, check_send_sigabrt, hterm, htid, hpos, hvalid,
    hblocked]

/-- The dispatcher at the `tkill` number IS
    `Checks.Sys.Kernel.Signal.check_tkill`, the same fact
    `Checks.Sys.DispatchCompute.check_syscall_set_tid_address` states at 96
    (that file has no arm for 130). -/
theorem check_syscall_tkill (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : (i.in_sysno.toNat : Int) = 130) :
    check_syscall i eff m
      = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table
      (i.in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_tkill := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table,
      LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_tkill]

theorem abrt_sc2 (lim : Int) :
    check_syscall (sys_input abrt_segments (abrt_t 3) (BitVec.ofInt 64 130))
      (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_tid abort_tid (abrt_model lim))
    = .CheckOk (abrt_killed_model lim) [] := by
  have hpideq : pid32 (in_arg (sys_input abrt_segments (abrt_t 3)
      (BitVec.ofInt 64 130)) 0) = abort_tid := by decide
  have hsigeq : sig32 (in_arg (sys_input abrt_segments (abrt_t 3)
      (BitVec.ofInt 64 130)) 1) = BitVec.ofInt 64 SIGABRT := by decide
  rw [check_syscall_tkill _ _ _ (by decide), hpideq, hsigeq]
  exact check_tkill_kills abort_tid _ _
    rfl rfl (by decide) rfl (abrt_sigmask_not_blocked lim)

/-- The trace the run ends on. -/
def abrt_trace (lim : Int) : List event :=
  [event.KillEv (BitVec.ofInt 64 6) (m_fs (abrt_killed_model lim))]

theorem abrt_kill_sstep (lim : Int) :
    sstep abrt_segments
      ⟨abrt_t 3, with_tid abort_tid (abrt_model lim)⟩
      (abrt_trace lim)
      (.SNext ⟨abrt_t 3, abrt_killed_model lim⟩) := by
  simp only [abrt_trace]
  exact sstep.killed (ms := abrt_t 3) (model := with_tid abort_tid (abrt_model lim))
    (x8 := BitVec.ofInt 64 130) (eff := mkEffect (BitVec.ofInt 64 0) [] [])
    (model' := abrt_killed_model lim) (evs := []) (sig := BitVec.ofInt 64 6)
    rfl abrt_svc_tkill ((check_syscall_ok_iff _ _ _ _ _).mp (abrt_sc2 lim)) rfl

/-- The whole execution: two instructions, `set_tid_address`, two more
    instructions, `tkill`, and the process is dead. -/
theorem abrt_star (lim : Int) :
    star abrt_segments (abrt_c lim) (abrt_trace lim)
      ⟨abrt_t 3, abrt_killed_model lim⟩ := by
  refine star.step _ _ _ _ _ (abrt_instr_sstep lim 0 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_instr_sstep lim 1 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_instr_sstep lim 2 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_syscall1_sstep lim) ?_
  refine star.step _ _ _ _ _ (abrt_instr2_sstep lim 0 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_instr2_sstep lim 1 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_instr2_sstep lim 2 (by decide)) ?_
  refine star.step _ _ _ _ _ (abrt_kill_sstep lim) ?_
  exact star.refl _

/- =========================================================================
   What it buys
   ========================================================================= -/

/-- THE HYPOTHESIS, DISCHARGED.  This is the statement
    `Equivalence.strong_universal_error_free_T_abort_refuted_by_abort`
    takes as an assumption. -/
theorem abrt_dies_by_signal (lim : Int) :
    dies_by_signal (run abrt_image lim demo_entry abrt_input) := by
  refine ⟨abrt_trace lim, BitVec.ofInt 64 6, m_fs (abrt_killed_model lim), ?_, ?_⟩
  · show obs_trace abrt_segments
      (init_config abrt_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw lim abrt_input)
      (abrt_trace lim)
    rw [abrt_config]
    exact ⟨abrt_trace lim, ⟨abrt_t 3, abrt_killed_model lim⟩,
      abrt_star lim, is_prefix_refl _⟩
  · simp [abrt_trace]

/-- ... and therefore the abort family's bite is FIRED rather than
    stated.  `Equivalence.error_free_unkilled`'s second conjunct is what
    fails here: this run reaches no `Run.sstep` error at all — the model
    follows it to the end — so `Equivalence.error_free` alone would be
    SATISFIED by it, which is exactly the weakening
    `Equivalence.error_free_unkilled` exists to prevent.  A reader who
    wants the difference in one line has it here: the same run, accepted
    by one predicate and refused by the other. -/
theorem abrt_refutes_error_free_abort :
    ¬ strong_universal_error_free_T_abort abrt_image abrt_image := by
  apply strong_universal_error_free_T_abort_refuted_by_abort
    abrt_image abrt_image demo_entry demo_entry abrt_input
    (demo_entry_valid_abrt _ abrt_input_valid)
    (demo_entry_valid_abrt _ abrt_input_valid)
    abrt_input_valid
  exact (abrt_dies_by_signal source_alloc_limit)

/-- THE CONTROL, and it is the half that says the refutation above is
    about the ABORT rather than about the image.  The identical program
    is NOT refuted this way with the declaration clear, because with it
    clear `Kernel.Signal.tkill_spec` declines and the run never reaches
    a `State.KillEv` to be refuted by — it leaves the modeled surface
    instead.  So the two stances really do differ on this image, which
    is what `Run.valid_input` pinning `false` is worth. -/
def abrt_input_undeclared : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (BitVec.ofInt 64 0) demo_hwcap false .Sv48

theorem abrt_tkill_declined_undeclared :
    check_syscall (sys_input abrt_segments (abrt_t 3) (BitVec.ofInt 64 130))
      (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_tid abort_tid
         (init_model (segments_reserved abrt_segments) (BitVec.ofInt 64 0x1000)
            (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000)
            source_alloc_limit abrt_input_undeclared))
    = .CheckUnmodeled := by
  rfl

/-- THE DATA FLOW, PINNED.  Everything above rests on one claim about the
    program that a reader cannot check by looking at the trace: that
    `tkill`'s first argument is the value the FIRST syscall returned,
    rather than a constant the image carries.  These three say it.

    First, the argument really is the chosen tid at the second `ecall`.
    The image contains no 4242: a0 was last written by
    `Run.apply_effect`. -/
theorem abrt_tkill_pid_is_the_returned_tid :
    in_arg (sys_input abrt_segments (abrt_t 3) (BitVec.ofInt 64 130)) 0 = abort_tid := by
  decide

/-- Second, the value was a CHOICE and not a constant: the acceptor
    admits a different tid from the same state, so nothing in the model
    forced 4242.  If `Kernel.Fork.set_tid_address_spec` ever answered a
    fixed value, this would stop holding and the paragraph above would
    stop being true. -/
theorem abrt_sc1_admits_another_tid (lim : Int) :
    check_syscall (sys_input abrt_segments (abrt_s 3) (BitVec.ofInt 64 96))
      (mkEffect (BitVec.ofInt 64 1234) [] []) (abrt_model lim)
    = .CheckOk (with_tid (BitVec.ofInt 64 1234) (abrt_model lim)) [] := by
  rfl

/-- Third, the match is what the kill DEPENDED on.  The same call, the
    same registers, the same declaration -- and a model whose recorded
    tid is one greater -- is declined rather than fatal.  So the death
    above is not the arm firing at any declared state; it is the arm
    firing because the program sent the signal to ITSELF. -/
theorem abrt_tkill_other_tid_declined (lim : Int) :
    check_syscall (sys_input abrt_segments (abrt_t 3) (BitVec.ofInt 64 130))
      (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_tid (BitVec.ofInt 64 4243) (abrt_model lim))
    = .CheckUnmodeled := by
  rfl

/- =========================================================================
   The same refutation, in the classifier statement shape
   ========================================================================= -/

/-- WHY THIS IS HERE AND NOT ONLY IN THE BASELINE SHAPE.  A classifier
    task is stated over `Run.run_scfg` rather than `Run.run`, and the
    abort declaration has a family there too
    (`Equivalence.strong_universal_error_free_T_scfg_abort`).  Its bite
    needs an instance too, for the reason this file
    exists one shape up: a conditional refutation nobody has
    shown fires says nothing about whether the clause it names can ever
    be the one that fails.

    THE TRANSFER IS THE WHOLE PROOF, and it is one behaviour
    equivalence.  At `Run.may_fail_cfg` the filtered run and the plain
    run have the same traces (`Run.run_scfg_may_fail`), and
    `Equivalence.dies_by_signal` is read off `Run.bh_traces`, so it
    transports — which is what
    `Equivalence.dies_by_signal_behavior_equiv` is for.

    WHY `may_fail_cfg` RATHER THAN AN ARBITRARY CONFIGURATION: the
    filter only ever REMOVES executions (`Run.run_scfg_sub_traces`), so
    at a configuration that forces some family the kill could in
    principle be filtered out along with the run that reaches it.  What
    settles whether it is, is whether THIS image issues a syscall that
    configuration can refuse -- a number with no arm in
    `Run.injected_table` has nothing to inject, so no configuration
    refuses it.  This image issues `set_tid_address` and `tkill` and
    nothing else, and neither number is in that table, so no execution
    of it can be filtered and the witness would generalise to any
    configuration.  `may_fail_cfg` is stated because it is what a task
    gets by saying nothing, not because the wider claim would fail. -/
theorem abrt_dies_by_signal_scfg (lim : Int) :
    dies_by_signal (run_scfg may_fail_cfg abrt_image lim demo_entry abrt_input) := by
  apply (dies_by_signal_behavior_equiv _ _ (run_scfg_may_fail _ _ _ _)).mpr
  exact (abrt_dies_by_signal lim)

/-- ... and the classifier-shape refutation, fired rather than stated.
    The image is refuted against ITSELF, so the only clause that can
    fail is the one `Equivalence.error_free_unkilled` adds over
    `Equivalence.error_free`: the two runs are the same run, their trace
    sets are equal, and neither takes an error transition -- a followed
    abort is not an error.  That is the weakening the conjunct exists to
    stop, exhibited in the shape a classifier task is actually stated
    in. -/
theorem abrt_refutes_error_free_scfg_abort :
    ¬ strong_universal_error_free_T_scfg_abort may_fail_cfg abrt_image abrt_image := by
  apply strong_universal_error_free_T_scfg_abort_refuted_by_abort
    may_fail_cfg abrt_image abrt_image demo_entry demo_entry abrt_input
    (demo_entry_valid_abrt _ abrt_input_valid)
    (demo_entry_valid_abrt _ abrt_input_valid)
    abrt_input_valid
  exact (abrt_dies_by_signal_scfg source_alloc_limit)

end LinuxSem.Checks.AbortWitness
