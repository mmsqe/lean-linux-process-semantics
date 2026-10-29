/-
  * LinuxProcessSem.Checks.Examples — what the definitions MEAN

  Not part of the trusted specification: this file is QA on the
  definitions, written to be READ.

  ** What belongs here

  The syscall model has two checkers, and they answer different
  questions.  The extracted, verified acceptor can be folded over
  every syscall a real riscv64 run makes, so it decides *does Linux
  do what the model says*.  This file
  decides *does the model say what we meant*, on cases chosen by hand.

  A case earns its place here only if one real run cannot show it.  Four
  reasons recur, and each example below says which one applies:

  - it is UNIVERSALLY QUANTIFIED — a `∀` over admissible outcomes,
    which no finite set of traces can establish (the `theorem`s here);
  - it compares TWO RUNS — "these two programs emit the same events" is
    a statement about a pair of traces, and the acceptor folds over one
    trace per run and never compares across runs;
  - it pins MODEL-INTERNAL STATE, or a model CONSTANT, that no
    observation of a real execution reveals;
  - the environment cannot be made to produce it: a `CheckReject` needs
    a kernel behaving inadmissibly, which no truthful run shows, and
    the case here is where the rejected answer is named exactly.

  ** Types

  Event payload bytes are `byte` (`BitVec 8`, so the `< 256` side
  conditions are typed away and inc-cat's `(b + 1) mod 256` is just
  wrapping `BitVec 8` addition), channel ids / exit codes are `word`
  (`BitVec 64`), and the concrete checker inputs use `word`/`byte`
  literals.

  Spelling.  `Z` is `Int`; `bv n`/`word`/`byte` are
  `BitVec n`/`BitVec 64`/`BitVec 8`; `Z_to_bv n z` is `BitVec.ofInt n z`;
  `bv_unsigned a` is `(a.toNat : Int)`; `Ok`/`Unmodeled` are
  `.ok`/`.unmodeled`; `MachineOk`/`MachineFault`/`MachineUnmodeled` are
  the `machine_result` constructors of the same names; `SNext`/`SError`
  are `step_to.SNext`/`.SError`; `mkCfg ms model` is the `config`
  constructor `⟨ms, model⟩`; an `Example` is spelled `theorem`;
  A closed computation on a CLOSED goal is `by decide` where the
  goal is a decidable equality and `by rfl` where it is not (a
  `machine_result` carries no `DecidableEq`, so the `step` facts below
  are `rfl`, which works because the target constructor is closed).

  FIXTURES, and their names.  This file provides, in
  `LinuxSem.Checks.Examples`:

    `exit0_segment`, `exit0_segments`, `exit0_image`,
    `undecodable_segment`, `undecodable_segments`, `undecodable_image`,
    `demo_entry`, `demo_proc_input`, `exit_sysno`, `exits_c`,
    `demo_input_valid`, `demo_entry_valid_exit0`,
    `demo_entry_valid_undecodable`, `exit0_image_must_exit_zero`,
    `exits_c_must_exit_at`, `undecodable_step_unmodeled`,
    `undecodable_step_unmodeled_at_demo_entry`,
    `run_of_undecodable_image_is_unmodeled`,
    `run_of_undecodable_image_is_unmodeled_at_demo_entry`,
    `undecodable_image_emits_nothing`.

  Two names here are additions, and neither shadows a specification
  name: `demo_proc_input` (the fixture input above) and
  `is_prefix_cons_cons` (a one-step `Run.is_prefix` fact the definition
  below needs as a rewrite rule, because a `def` that returns a
  `Prop` has no `Decidable` instance for `decide` to consume).

  `demo_proc_input` is the name for the one-element-argv input
  that would otherwise be spelled out at each use site
  (`mkProcInput [[]] [] [] IEof demo_uid …`): it is the SAME term, so a
  consumer's own literal is definitionally equal to it, and
  `demo_input_valid` is the lemma that validates it.

  (`exits_c`, reused rather than redefined).  The definition already
  exists, at
  `LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c`,
  together with its soundness result `exits_c_must_exit_at` (in
  `Examples/PatchClassifyDemo/ExitsC.lean`).  This file therefore
  REUSES it: `exits_c` below is an `abbrev` for that function and
  `exits_c_must_exit_at` is that result, so there is ONE definition and
  ONE proof in the tree, under this module's names as well as the demo's.
  Consequence to be aware of: this module takes the demo as a dependency,
  so the dependency runs `Checks/Examples → Examples/PatchClassifyDemo/ExitsC`
  rather than the other way round.
-/
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
import LinuxSem.LinuxProcessSem.Bridge.Exit
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Sys.DispatchCompute
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.Examples.PatchClassifyDemo.ExitsC

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.DispatchCompute
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Checks.Examples

/- =========================================================================
   PART 1 — the EQUIVALENCE definition, on synthetic behaviors

   Trace sets written down by hand, so `Equivalence.equiv`'s verdicts can
   be read off without running a binary.
   ========================================================================= -/

/-- All prefixes of one maximal trace. -/
def prefixes (tr : List event) : List event → Prop :=
  fun t => is_prefix t tr

/-- A behavior with the given trace set, no reachable error, and
    therefore nothing unmodeled. -/
def pure_behavior (T : List event → Prop) : behavior :=
  { bh_traces := T, bh_errors := False, bh_all_errors := False,
    bh_unmodeled := False }

/-- A synthetic behavior that has at least one erroring execution.  The
    `all` parameter distinguishes "some execution errors" from "every
    execution errors", which is the quantifier boundary `equiv` must
    enforce. -/
def error_behavior (T : List event → Prop) (all : Prop) : behavior :=
  { bh_traces := T, bh_errors := True, bh_all_errors := all,
    bh_unmodeled := False }


/-! Two one-step facts about `Run.is_prefix`, stated as their own lemmas
    because the definition reduces to them definitionally and `simp`
    cannot fire on a `def` that returns a `Prop`. -/
theorem is_prefix_cons_cons {A : Type} {x y : A} {xs ys : List A} :
    is_prefix (x :: xs) (y :: ys) ↔ (x = y ∧ is_prefix xs ys) :=
  Iff.rfl

/-- If every source execution errors, the target is unconstrained. -/
theorem all_source_traces_error_frees_target :
    equiv (error_behavior (prefixes []) True)
          (error_behavior (prefixes [event.ExitEv 7 []]) True) :=
  Or.inl True.intro

/-- No existential escape: one source error is not
    enough when the source also has a non-error execution.  Even with
    identical observable prefix sets, an erroring target is rejected. -/
theorem one_source_trace_survives_rejects_erroring_target :
    ¬ equiv (error_behavior (prefixes [event.ExitEv 0 []]) False)
            (error_behavior (prefixes [event.ExitEv 0 []]) False) := by
  rintro (Hall | ⟨-, Htarget⟩)
  · exact Hall
  · exact Htarget True.intro

/-- The same mixed source can still be matched by an error-free target. -/
theorem one_source_trace_survives_accepts_safe_target :
    equiv (error_behavior (prefixes [event.ExitEv 0 []]) False)
          (pure_behavior (prefixes [event.ExitEv 0 []])) :=
  Or.inr ⟨fun _ => Iff.rfl, fun h => h⟩

/-- The operational universal predicate is non-vacuous: it always
    supplies an existential error witness as well. -/
theorem operational_all_errors_implies_may_error (segs : List Segment) (c : config) :
    all_traces_error segs c → reaches_error segs c :=
  all_traces_error_reaches_error segs c

/-- Same exit code — provable; different exit codes — disprovable. -/
theorem same_exit_code :
    equiv (pure_behavior (prefixes [event.ExitEv 42 []]))
          (pure_behavior (prefixes [event.ExitEv 42 []])) :=
  Or.inr ⟨fun _ => Iff.rfl, fun h => h⟩

theorem different_exit_code :
    ¬ equiv (pure_behavior (prefixes [event.ExitEv 42 []]))
            (pure_behavior (prefixes [event.ExitEv 7 []])) := by
  rintro (H | ⟨H, -⟩)
  · exact H
  · have HL : is_prefix [event.ExitEv 42 []] [event.ExitEv 42 []] := is_prefix_refl _
    have h := (H [event.ExitEv 42 []]).1 HL
    change is_prefix [event.ExitEv 42 []] [event.ExitEv 7 []] at h
    rw [is_prefix_cons_cons] at h
    exact absurd h.1 (by decide)

/-- Exit vs. silent divergence — disprovable.  This validates
    termination-as-an-event: the diverging program's prefix set is just
    `{[]}`, which is missing the `ExitEv` prefix. -/
theorem exit_vs_divergence :
    ¬ equiv (pure_behavior (prefixes [event.ExitEv 0 []]))
            (pure_behavior (prefixes [])) := by
  rintro (H | ⟨H, -⟩)
  · exact H
  · have HL : is_prefix [event.ExitEv 0 []] [event.ExitEv 0 []] := is_prefix_refl _
    have h := (H [event.ExitEv 0 []]).1 HL
    change is_prefix [event.ExitEv 0 []] [] at h
    exact h

/-- Channel liveness: stdout-write-then-diverge vs. diverge is
    disprovable, because channel bytes are observable as they happen.
    Contrast `file_write_emits_nothing` below — a write to a FILE emits
    no events, so file-write-then-diverge and diverge share the prefix
    set {[]} and ARE equivalent.  The file system is observed only at
    exit. -/
theorem write_then_diverge_vs_diverge :
    ¬ equiv (pure_behavior (prefixes [event.WriteEv 1 104]))
            (pure_behavior (prefixes [])) := by
  rintro (H | ⟨H, -⟩)
  · exact H
  · have HL : is_prefix [event.WriteEv 1 104] [event.WriteEv 1 104] := is_prefix_refl _
    have h := (H [event.WriteEv 1 104]).1 HL
    change is_prefix [event.WriteEv 1 104] [] at h
    exact h

/-- cat vs. byte-increment cat — the input-modeling test.  Idealized
    trace sets: `cat` echoes each byte it reads; `inc-cat` writes each
    byte plus one (mod 256 — which is just wrapping `byte` addition).
    Because `ReadEv` CARRIES the byte read, the trace
    `[ReadEv 0 0; WriteEv 1 0]` belongs to cat but not to inc-cat, and the
    two are distinguishable.  (If read events
    did not carry the byte, both programs would have the same
    `ReadEv; WriteEv b` traces — the design this example guards
    against.) -/
inductive cat_tr : List event → Prop where
  | cat_tr_nil : cat_tr []
  | cat_tr_rw (b : byte) (tr : List event) : cat_tr tr →
      cat_tr (event.ReadEv 0 b :: event.WriteEv 1 b :: tr)

inductive inc_tr : List event → Prop where
  | inc_tr_nil : inc_tr []
  | inc_tr_rw (b : byte) (tr : List event) : inc_tr tr →
      inc_tr (event.ReadEv 0 b :: event.WriteEv 1 (b + 1) :: tr)

def cat_behavior : behavior :=
  pure_behavior (fun t => ∃ tr, cat_tr tr ∧ is_prefix t tr)

def inc_behavior : behavior :=
  pure_behavior (fun t => ∃ tr, inc_tr tr ∧ is_prefix t tr)

theorem cat_vs_byte_increment_cat : ¬ equiv cat_behavior inc_behavior := by
  rintro (H | ⟨H, -⟩)
  · exact H
  · obtain ⟨tr, Hinc, Hpre⟩ :=
      (H [event.ReadEv 0 0, event.WriteEv 1 0]).1
        ⟨[event.ReadEv 0 0, event.WriteEv 1 0],
         cat_tr.cat_tr_rw 0 _ cat_tr.cat_tr_nil, is_prefix_refl _⟩
    cases Hinc with
    | inc_tr_nil =>
        change is_prefix [event.ReadEv 0 0, event.WriteEv 1 0] [] at Hpre
        exact Hpre
    | inc_tr_rw b tr' _ =>
        change is_prefix [event.ReadEv 0 0, event.WriteEv 1 0]
          [event.ReadEv 0 b, event.WriteEv 1 (b + 1)] at Hpre
        rw [is_prefix_cons_cons, is_prefix_cons_cons] at Hpre
        obtain ⟨hr, hw, -⟩ := Hpre
        injection hr with _ hb
        injection hw with _ h1
        rw [← hb] at h1
        exact absurd h1 (by decide)

/- =========================================================================
   `Equivalence.modeled` is a NEGATIVE statement — `¬ bh_unmodeled` — so
   it would be free, and worthless, if `Run.reaches_unmodeled` could
   never hold.  These examples show it can, at both levels: a machine
   state the model declines to interpret, and a whole `run` whose
   `bh_unmodeled` holds and which therefore FAILS the `modeled` clause
   of `Equivalence.strong_equiv`.  (Compare
   `Run.reaches_unmodeled_reaches_error` for the other direction: being
   unmodeled is strictly rarer than erroring.)

   The image is a four-byte executable segment holding 0xffffffff, a
   word this development's decoder does not decode.
   ========================================================================= -/

def undecodable_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["ffffffff"]

def undecodable_segments : List Segment := [undecodable_segment]

/-- The one-element-argv process input the run-level statements below
    use, named once.  The thirteen-place `mkProcInput`
    literal would otherwise be spelled out at each use site; every such
    literal is this term.

    The launching user is an ORDINARY one, the group is a DIFFERENT
    number from the user (a state where the two coincide cannot tell a
    `getgid` wired to `cr_uid` from one wired to `cr_gid`), the random
    stream is the default endless one (which is what `valid_urandom`
    demands), and the accept queue is `net_silent`. -/
def demo_proc_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) demo_hwcap false .Sv48

theorem undecodable_word_is_not_decoded :
    decodeAny (BitVec.ofInt 32 0xffffffff) = none := by decide

/-- A concrete image's program-header record, reused by the auxv checks
    in part 5: the shape `elf-snapshot` emits for a static
    riscv64 binary whose phdr table sits at file offset 64 in the first
    LOAD segment (mapped at 0x10000), with 6 ELF64 program headers. -/
theorem undecodable_step_unmodeled :
    RiscvSemantics.step undecodable_segments
      (init_machine_state undecodable_segments 0x100 demo_phdrs
         (BitVec.ofInt 64 65536) demo_draw [[]] [] demo_uid demo_hwcap)
    = .MachineUnmodeled := by rfl

/-- …and therefore the run is NOT modeled.  Any `strong_universal_T`
    naming this image as its source is unprovable, however the target is
    chosen — which is exactly the vacuity the clause exists to block. -/
theorem run_of_undecodable_image_is_unmodeled :
    bh_unmodeled (run (mkImage undecodable_segments 0x100 demo_phdrs)
                    demo_limit
                    ⟨BitVec.ofInt 64 65536, BitVec.ofInt 64 1048576,
                     BitVec.ofInt 64 mmap_base_max, demo_draw⟩
                    demo_proc_input) := by
  show reaches_unmodeled undecodable_segments
    (init_config undecodable_segments 0x100 demo_phdrs (BitVec.ofInt 64 65536)
      (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 mmap_base_max) demo_draw
      demo_limit demo_proc_input)
  refine reaches_unmodeled_intro _ _ _ rfl rfl ?_
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [demo_proc_input, mkProcInput]
  rw [undecodable_step_unmodeled]

theorem run_of_undecodable_image_refutes_modeled :
    ¬ modeled
        (run (mkImage undecodable_segments 0x100 demo_phdrs)
           demo_limit
           ⟨BitVec.ofInt 64 65536, BitVec.ofInt 64 1048576,
            BitVec.ofInt 64 mmap_base_max, demo_draw⟩
           demo_proc_input) := by
  intro H
  exact H run_of_undecodable_image_is_unmodeled

/- =========================================================================
   PART 1 (continued) — the extracted acceptor's outcomes, read back as
   `Run.sstep` transitions.

   UNIVERSALLY QUANTIFIED — a `∀` over every input the acceptor can be
   handed, which no finite set of traces establishes.

   `ExecutableSpecs` does not import `Run`, so nothing it proves can
   mention `sstep`: its theorems reach `syscall_spec` and
   `syscall_post_model`, but cannot say that the accounting it applies
   IS the accounting the run performs.  These three say it in the one
   place that can see both.

   What that buys, exactly: they run acceptor-to-run only, so ADDING or
   ALTERING a premise of a syscall `sstep` constructor breaks one of them,
   while DELETING a premise, or adding a laxer constructor, does not.  The
   simulation proofs in `Common/` also break on the first kind; these
   make the break land on a proof naming `check_syscall_for_run`, so it
   cannot be repaired by updating the simulations while the extracted
   acceptor keeps the old accounting.

   `SError` carries no reason, so the two error theorems pin the run's
   verdict and not which constructor delivered it -- that is named only in
   their proofs.

   `CheckReject` has no companion.  What it wants is a NEGATIVE statement
   -- a rejected effect admits no syscall `sstep` -- which follows from
   `check_syscall_complete_ok` by inversion and is not written yet.
   ========================================================================= -/

theorem checker_ok_is_run_step (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model'' : Model) (evs : List event)
    (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : check_syscall_for_run (sys_input segs ms x8) eff model
      = some (.CheckOk model'' evs)) :
    (m_halted model'' = none ∧
      sstep segs ⟨ms, model⟩ evs
        (.SNext ⟨advance_past_svc (apply_effect ms eff), model''⟩))
    ∨ (∃ code,
        m_halted model'' = some code ∧ m_killed model'' = none ∧
        sstep segs ⟨ms, model⟩ (evs ++ [event.ExitEv code (m_fs model'')])
          (.SNext ⟨ms, model''⟩))
    ∨ (∃ sig,
        m_killed model'' = some sig ∧
        sstep segs ⟨ms, model⟩ (evs ++ [event.KillEv sig (m_fs model'')])
          (.SNext ⟨ms, model''⟩)) := by
  obtain ⟨model', Hspec, Hpost⟩ :=
    (check_syscall_for_run_ok_iff _ _ _ _ _).mp Hchk
  rcases hhalt : m_halted model' with _ | code
  · rw [syscall_post_model_running _ _ hhalt] at Hpost
    obtain ⟨-, -, -, -, -, hproc, -⟩ := materialize_model_accesses_frame _ _ _ Hpost
    refine Or.inl ⟨?_, sstep.syscall ms model x8 eff model' model'' evs Hh Hsvc Hspec hhalt Hpost⟩
    unfold m_halted at hhalt ⊢
    rw [hproc, hhalt]
  · rw [syscall_post_model_halted _ _ _ hhalt] at Hpost
    have hpost : model'' = model' := (Option.some.inj Hpost).symm
    rw [hpost]
    cases hkill : m_killed model' with
    | some sig =>
        exact Or.inr (Or.inr
          ⟨sig, rfl, sstep.killed ms model x8 eff model' evs sig Hh Hsvc Hspec hkill⟩)
    | none =>
        exact Or.inr (Or.inl
          ⟨code, hhalt, rfl, sstep.exit ms model x8 eff model' evs code Hh Hsvc Hspec hhalt hkill⟩)

theorem checker_fault_is_run_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect)
    (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : check_syscall_for_run (sys_input segs ms x8) eff model = none) :
    sstep segs ⟨ms, model⟩ [] .SError := by
  obtain ⟨model', evs, Hspec, Hhalt, Hfault⟩ :=
    (check_syscall_for_run_fault_iff _ _ _).mp Hchk
  exact sstep.syscall_materialization_fault ms model x8 eff model' evs Hh Hsvc Hspec Hhalt Hfault

theorem checker_unmodeled_is_run_error (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect)
    (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : check_syscall_for_run (sys_input segs ms x8) eff model = some .CheckUnmodeled) :
    sstep segs ⟨ms, model⟩ [] .SError := by
  have H : syscall_spec (sys_input segs ms x8) model .unmodeled :=
    (check_syscall_for_run_unmodeled_iff _ _ _).mp Hchk
  exact sstep.syscall_unmodeled ms model x8 Hh Hsvc H

/- =========================================================================
   PART 2 — model-level lemmas about the SPECS

   Every statement here is a `∀` over admissible outcomes: it says
   what NO execution may do.  One run exhibits one outcome, so it
   can never establish any of them.
   ========================================================================= -/

/-- ** `wait4` must stop answering once something can create a child

    `Kernel.Exit.wait4_spec` answers -ECHILD, and that answer is only
    correct for a caller that has nothing to reap.  Something can create
    a child, so
    these are not vacuous: `Kernel.Fork.clone_resolve`'s success
    branch applies `State.with_children`, so a `clone` or `clone3` that
    returns a pid lands in a model with `State.m_has_children` set, and
    the two lemmas below constrain a state a modeled trace really reaches
    rather than quantifying over an empty one.  `Kernel.Fork` pays for
    that here, by setting the field.  Every other arm owes the same — a
    `ptrace` that attaches, or anything else that acquires something to
    reap: apply `State.with_children`, or a `wait4_spec` still answering
    -ECHILD stops compiling here.

    Without this, the failure is silent and it is a PRIORITY 2 defect
    rather than a decline: a process that really has a live child would
    get -ECHILD from the model, which Linux never returns for it, while
    the two answers Linux does give (a bare 0 under WNOHANG, or the
    child's pid) would both be rejected.  A model admitting a trace Linux
    cannot produce.

    WHY THESE LIVE HERE AND NOT BESIDE `wait4`'s OTHER LEMMAS.  The rest
    of them are in `Checks.ProcessCreation`, which is exactly the file a
    change that gives a number a creating arm has to edit, and such a
    change can delete a guard there as a natural part of making it.  A
    guard the guarded party can remove is not a guard.  Nothing about adding a process-creation arm
    requires touching this file.

    Which of the four reasons at the top of this file: the THIRD, it pins
    model-internal state (`State.m_has_children`) that no observation of
    a real execution reveals — one run reaches the set state
    for one model and one pid, never for every
    model — and the FIRST, a `∀` over every model and every
    argument shape. -/
theorem wait4_with_a_child_is_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (Hno : (i.in_sysno.toNat : Int) = 260)
    (Hch : m_has_children m = true) :
    check_syscall i eff m = .CheckUnmodeled := by
  rw [check_syscall_wait4 i eff m Hno]
  -- Every guard's answer is `.CheckUnmodeled`, so `m_has_children m = true`
  -- decides the whole chain: the last `if` collapses to the same value as
  -- each of the three arms above it.
  simp only [check_wait4, ite_eq_left Hch, ite_self]

/-- ...and the half that names the wrong answer directly: with a child,
    -ECHILD is not merely undecided, it is not admitted at all.  This is
    the one that fails loudly if `wait4_spec`'s gate is dropped while
    something still sets the field. -/
theorem wait4_with_a_child_admits_no_answer (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : (i.in_sysno.toNat : Int) = 260)
    (Hch : m_has_children m = true) :
    ¬ syscall_spec i m (.ok eff m' evs) := by
  intro H
  have h := check_syscall_complete_ok i eff m m' evs H
  rw [wait4_with_a_child_is_unmodeled i eff m Hno Hch] at h
  exact nomatch h

/- =========================================================================
   PART 6 — must-terminate: a binary that exits 0, and one that cannot

   `MustExit.must_exit_with` is a statement about the whole run tree —
   EVERY resolution of the nondeterminism halts with the named code,
   none errors, none diverges — so it is admission reason 1 twice over:
   a `∀` over admissible outcomes on the positive side, and the
   negation of one on the refutation side.  One run exhibits a
   single outcome and can establish neither.

   `MustExit` itself proves the predicate's introduction and refutation
   rules against ABSTRACT configurations, which pins what the definition
   means without showing that any image meets it.  Both run-level cases
   are here instead: an image that satisfies it, and one that refutes it.
   The positive one matters most, because the predicate's premises are
   easy to write and hard to meet all at once — a predicate no image
   satisfies would have made every downstream statement about
   classifiers vacuously safe.  The image is about as small as such a
   program gets: three instructions, no memory traffic, ending in
   exit(0).
   ========================================================================= -/

/- ** Reading the exit syscall back out of the relational spec

    This sub-part is proof INFRASTRUCTURE rather than examples: five
    lemmas over one definition, inverting `Specs.syscall_spec` at the
    exit syscall number.  An image-level termination proof needs them and
    no earlier statement in this file does.

    `Common/ExitSim` proves the same facts for the example binaries,
    and this file cannot use them: `Common` sits ON
    TOP of `LinuxSem`, so the dependency would run
    backwards.  Keeping the duplicate small is the mitigation — all five
    are consequences of `Exit.exit_spec` having exactly one outcome
    shape.

    They are also deliberately named APART from their `Common/ExitSim`
    counterparts, none reusing a name from there.  Two identical
    statements under one name in two theories is how a divergence hides:
    a file that imported both would get last-import-wins shadowing with
    nothing to notice if one copy were later edited, and the shadowing
    would be silent precisely while the two agree. -/

/-- The syscall numbers that route to `Exit.exit_spec`: exit (93) and
    exit_group (94), which the dispatcher gives the same spec.

    Definitionally `Bridge.Exit.exit_number`, which is where the
    dispatcher lemmas below read it; kept as its own name because that is
    what the statements are about. -/
abbrev exit_sysno (no : word) : Prop :=
  (no.toNat : Int) = 93 ∨ (no.toNat : Int) = 94

/-- At either number the dispatcher IS the exit spec.  The whole of
    `Dispatch.dispatch` at a known number is a table lookup that reduces,
    so both directions are one rewrite. -/
theorem exit_dispatch_iff (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event)
    (Hno : exit_sysno i.in_sysno) :
    syscall_spec i m o ↔ exit_spec (in_arg i 0) i m o :=
  (Bridge.Exit.exit_dispatch_denotes i m o Hno).trans
    (Bridge.Exit.exit_spec_denotes i m o).symm

/-- The exit spec admits an outcome — the run is not stuck at the ecall.
    `Run.sstep.exit` needs this to fire. -/
theorem exit_dispatch_admits (i : SyscallInput) (m : Model)
    (Hno : exit_sysno i.in_sysno) :
    syscall_spec i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
          (with_halted (in_arg i 0 &&& BitVec.ofInt 64 255) m) []) :=
  (exit_dispatch_iff i m _ Hno).mpr (exit_spec_ok (in_arg i 0) i m)

/-- ... and admits NO OTHER.  This is the uniqueness that turns "some
    execution exits 0" into "every execution does": the exit spec is a
    `set_halted` followed by a return, with no `choose` anywhere, so the
    post-model, the effect and the event list are all forced. -/
theorem exit_dispatch_forced (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : exit_sysno i.in_sysno)
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    eff = mkEffect (BitVec.ofInt 64 0) [] [] ∧
    m' = with_halted (in_arg i 0 &&& BitVec.ofInt 64 255) m ∧ evs = [] := by
  have h' : (.ok eff m' evs : Outcome SyscallEffect Model event)
      = evaluate exit_clause i m :=
    (Bridge.Exit.exit_dispatch_normal_form i m _ Hno).mp Hspec
  simp only [evaluate, exit_clause, Outcome.ok.injEq] at h'
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

/- The consequence the run tree cares about: every admissible exit
   outcome HALTS, with the low byte of the status as
   `Sys/Kernel/Exit` masks it.  It is what rules out
   `Run.sstep_syscall` and `Run.sstep_syscall_materialization_fault` at
   an exit ecall — both require a post-model that is still running. -/
/-- The same, for the OTHER terminal field: an exit's post-model is
    `State.with_halted`'s, so it is not a killed one — which is what
    keeps `Run.sstep_exit` and `Run.sstep_killed` apart at an `exit`
    ecall. -/
theorem exit_dispatch_not_killed (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : exit_sysno i.in_sysno)
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    m_killed m' = none := by
  obtain ⟨-, rfl, -⟩ := exit_dispatch_forced i m eff m' evs Hno Hspec
  exact m_killed_with_halted _ m

theorem exit_dispatch_halts (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : exit_sysno i.in_sysno)
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    m_halted m' = some (in_arg i 0 &&& BitVec.ofInt 64 255) := by
  obtain ⟨-, rfl, -⟩ := exit_dispatch_forced i m eff m' evs Hno Hspec
  exact m_halted_with_halted _ m

/-- Exit is inside the modeled surface, so `Run.sstep_syscall_unmodeled`
    cannot fire at it either.  With the two above this closes every
    error route out of an exit ecall. -/
theorem exit_dispatch_modeled (i : SyscallInput) (m : Model)
    (Hno : exit_sysno i.in_sysno) :
    ¬ syscall_spec i m .unmodeled := by
  intro H
  have h' : (.unmodeled : Outcome SyscallEffect Model event) = evaluate exit_clause i m :=
    (Bridge.Exit.exit_dispatch_normal_form i m _ Hno).mp H
  simp [evaluate, exit_clause] at h'

/- =========================================================================
   A fuel-bounded executable witness for `MustExit.must_exit_at`

   A straight-line binary that ends in exit is checked by RUNNING it:
   `exits_c` walks `RiscvSemantics.step` until a syscall is pending, and
   then asks whether it is an exit carrying the right code.  Written as
   a `Bool` on purpose — the machine states it passes through stay
   inside the computation, so its value is a `decide` and never a term
   in a goal.

   This is the same shape as `Common/ExitSim`'s `sim_c`, for the same
   reason, landing on a different predicate.

   The definition and its soundness result are NOT restated here: see
   this file's header, the `exits_c` note.  `exits_c` lives at
   `Examples.PatchClassifyDemo.Verdicts.exits_c`, and
   `exits_c_must_exit_at` at
   `Examples.PatchClassifyDemo.Verdicts.exits_c_must_exit_at` (file
   `ExitsC.lean`).  The two names below are those, so there is one
   definition and one proof in the tree.
   ========================================================================= -/

/-- `exits_c`, reused from the demo (see the header note). -/
abbrev exits_c : List Segment → word → Nat → machine_state → Bool :=
  LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c

/-- ** `exits_c` is sound for `MustExit.must_exit_at`.**

    A program `exits_c` accepts really has NO other execution.  Both
    premises on the model are needed and both are discharged by `rfl` at
    an initial configuration: a halted model would put the configuration
    in the base case with whatever code it already carries, and a model
    with lazy anonymous mappings could take the accounting fault
    transition (`Run.mi_account_step_no_lazy` is what erases accounting
    here, and it is also what keeps the model FIXED across an
    instruction step, so the induction hypothesis applies unchanged).

    The conclusion is written `⟨ms, model⟩`, not
    `mkCfg ms model`: `mkCfg` is `⟨·, ·⟩` in `Common/AsanAcct`, which is
    outside this file's dependency graph, and the two are definitionally
    equal, so the statement reads the same either way. -/
theorem exits_c_must_exit_at (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      m_halted model = none → m_vm_lazy model = [] →
      exits_c segs code fuel ms = true → must_exit_at segs code ⟨ms, model⟩ :=
  LinuxSem.Examples.PatchClassifyDemo.Verdicts.exits_c_must_exit_at segs code

/- =========================================================================
   The image, and the entry a real `execve` could have chosen

   Three instructions at 0x100, written out as the hex the loader would
   have produced: `addi a7, x0, 93` (0x05d00893), `addi a0, x0, 0`
   (0x00000513), `ecall` (0x00000073), little-endian.  The program makes
   no memory access at all beyond its own instruction fetches, which is
   what keeps the statements below short: nothing depends on the stack
   the entry describes, though they are still proved at one concrete
   entry rather than quantified over them.
   ========================================================================= -/

def exit0_segment : Segment where
  seg_base := 0x100
  seg_size := 12
  seg_perms := "r-x"
  seg_bytes := ["9308d0051305000073000000"]

def exit0_segments : List Segment := [exit0_segment]

def exit0_image : Image := mkImage exit0_segments 0x100 demo_phdrs

/-- The undecodable image from part 1, as a `MemImageType.Image`: the
    same `undecodable_segments` those examples run. -/
def undecodable_image : Image :=
  mkImage undecodable_segments 0x100 demo_phdrs

/-- An `execve` placement that really satisfies `Run.valid_entry` —
    unlike the fixture entry used by the earlier examples, whose stack
    pointer (65536) sits far below `State.sp_window_lo` and which those
    examples never had to validate.  Validity is what the statements
    below need: `Classifier.agree` quantifies its trace comparison over
    VALID entries only, so a refutation that named an invalid one would
    refute nothing. -/
def demo_entry : ExecEntry :=
  ⟨BitVec.ofInt 64 0x7fff80000000, BitVec.ofInt 64 0x1000,
   BitVec.ofInt 64 mmap_base_max, demo_draw⟩

/-- Both images put their only segment inside the first page, so both
    reserve exactly that page and the same break base is valid for
    either.  These two are premises for the statements below rather than
    cases in their own right; as cases they would be admission reason 3,
    since the three windows `Run.valid_entry` checks against are model
    constants no observation of a running process reveals.

    Stated for EVERY valid input rather than at the one below, because
    that is what is true: `Run.valid_entry`'s fourth conjunct asks that
    the entry stack image fit under `State.sp_window_hi`, `demo_entry`
    puts `sp` at `State.sp_window_lo`, and `Run.entry_stack_span_bound`
    caps a valid input's image at `Run.entry_stack_span_max` — 2238671
    bytes against the window's two gigabytes.  Naming the input here
    instead would say less and would have to be restated at each use. -/
theorem demo_entry_valid_exit0 (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry exit0_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk exit0_image exit0_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

theorem demo_entry_valid_undecodable (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry undecodable_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    refine ⟨by omega, by omega, by decide⟩
  · unfold valid_brk undecodable_image undecodable_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    refine ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

/-- `Run.valid_mmap_base`'s cap, pinned from outside (reason 3: the band
    is a model constant no trace reveals).  `State.mmap_base_max` is the
    base a v6.18.46 kernel computes with randomisation off — `STACK_TOP -
    MIN_GAP`, mm/util.c `mmap_base` — and one page above it no kernel
    computes.  The third value is the top of the default 18-bit band
    (8 MiB rlimit, `PF_RANDOMIZE`); it is an ordinary real-kernel
    draw, so the band must admit it. -/
theorem mmap_base_cap_admitted : valid_mmap_base (BitVec.ofInt 64 0x7ffff8000000) := by
  unfold valid_mmap_base mmap_base_min mmap_base_max sp_window_hi page_size
  rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
  refine ⟨by decide, by decide, by decide⟩

theorem mmap_base_above_cap_rejected :
    ¬ valid_mmap_base (BitVec.ofInt 64 (0x7ffff8000000 + 4096)) := by
  unfold valid_mmap_base mmap_base_min mmap_base_max sp_window_hi page_size
  rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
  intro h
  omega

theorem mmap_base_default_band_top_admitted :
    valid_mmap_base (BitVec.ofInt 64 0x7fffbf701000) := by
  unfold valid_mmap_base mmap_base_min mmap_base_max sp_window_hi page_size
  rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
  refine ⟨by decide, by decide, by decide⟩

/-- The process input the statements below run on is a valid one — one
    empty argument, no environment, an empty file system, end of input.
    Needed for the same reason the entry validity is: the obligations
    quantify over VALID inputs, so a refutation naming an invalid one
    would refute nothing.

    (proof).  The clauses close one at a time, in the
    order `valid_input` states them, which is also how
    `Checks.Cases.VaSize`'s `sized_input_va_any` does it.  The two
    FILE SYSTEM clauses are vacuous rather than numeric: `State.in_fs` is
    the image with the (empty) private `/tmp` seeded, and both are the
    empty list.  The random-stream clause is
    `StateStreams.default_urandom_infinite`, and the hwcap clause picks
    the left disjunct, `Prelude.demo_hwcap` being `hwcap_rv64gc`. -/
theorem demo_input_valid : valid_input demo_proc_input := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [demo_proc_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [demo_proc_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [demo_proc_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [demo_proc_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [demo_proc_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [demo_proc_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [demo_proc_input, mkProcInput]
    decide
  · unfold valid_hwcap
    simp [demo_proc_input, mkProcInput, demo_hwcap]
  · simp [demo_proc_input, mkProcInput]
  · simp [demo_proc_input, mkProcInput]
  · unfold valid_urandom
    simp [demo_proc_input, mkProcInput, default_urandom_infinite]

/-- THE RANDOM-STREAM CLAUSE, FIRED IN BOTH DIRECTIONS.  Admission
    reason 2: the clause is on the LAUNCH's declaration, and one run
    declares one stream.

    THE POSITIVE HALF says the fixture above really carries the clause
    rather than passing it by accident: `State.mkProcInput` fills
    `State.in_urandom` with `State.default_urandom`, which is endless.
    THE NEGATIVE HALF is the point of the clause: the SAME launch with
    `State.IEof` in that field is not a valid input at all.  That is
    exactly what the clause excludes — the declaration under which
    `Sys.Fs.ReadWrite.read_urandom` declines, which
    `Checks.Cases.Fs.Open.urandom_stream_runs_out` keeps as a literal.
    Without the negative half the clause could be satisfied by every
    input and nothing would notice. -/
theorem the_random_clause_is_what_the_fixture_carries :
    valid_urandom demo_proc_input
    ∧ ¬ valid_input
          (ProcInput.mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups
                            net_silent default_nofile (BitVec.ofInt 64 0) demo_hwcap
                            false .Sv48 IEof []) := by
  refine ⟨?_, ?_⟩
  · unfold valid_urandom
    simp [demo_proc_input, mkProcInput, default_urandom_infinite]
  · intro H
    exact stream_infinite_not_eof (valid_input_urandom _ H)

/-- ** The two witnesses

    UNIVERSALLY QUANTIFIED (admission reason 1): every execution of this
    image from this entry halts with exit code 0, which is a claim about
    the whole run tree.  It is the first place a concrete image SATISFIES
    `MustExit.must_exit_with`: up to here the predicate had refutations
    and introduction rules stated of abstract configurations, and a
    predicate nothing satisfies would have made every one of those
    refutations free. -/
theorem exit0_image_must_exit_zero :
    must_exit_with verdict_accept exit0_image demo_limit demo_entry demo_proc_input := by
  show must_exit_at exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit
      demo_proc_input)
  refine exits_c_must_exit_at exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  decide

/-- ... and the other side.  UNIVERSALLY QUANTIFIED (reason 1) again, as
    the negation of one: the undecodable image errors on its first fetch,
    and `MustExit.must_exit_with` forbids an error anywhere in the tree,
    at every code — so this refutes exit 0 and exit 1 alike.  The route
    is the one `MustExit.must_exit_with_refuted_by_error` was written
    for, through `Equivalence.run_unmodeled_errors`: leaving the modeled
    surface is a special case of erroring. -/
theorem undecodable_image_refutes_must_exit :
    ¬ must_exit_with verdict_accept undecodable_image demo_limit
        ⟨BitVec.ofInt 64 65536, BitVec.ofInt 64 1048576,
         BitVec.ofInt 64 mmap_base_max, demo_draw⟩
        demo_proc_input :=
  must_exit_with_refuted_by_error verdict_accept undecodable_image demo_limit _ _
    (run_unmodeled_errors _ _ _ _ run_of_undecodable_image_is_unmodeled)

/- ** Two runs that do not agree

    COMPARES TWO RUNS (admission reason 2): `Classifier.agree` is a
    statement about a pair of trace sets, and the acceptor folds over
    one trace per run.

    The refutation goes through the trace conjunct rather than through
    the three error iffs, and that is not an accident: refuting an
    existential-over-entries iff needs a claim about EVERY valid entry of
    one image, while the trace conjunct is universally quantified over
    entry pairs and so one valid pair refutes it.  Here the pair is
    `demo_entry` against itself. -/

/-- The undecodable image is unmodeled on its first fetch at
    `demo_entry` too, exactly as `undecodable_step_unmodeled` shows at the
    older fixture entry: the fetch reads the segment image, which
    none of the three `execve` placements touches. -/
theorem undecodable_step_unmodeled_at_demo_entry :
    RiscvSemantics.step undecodable_segments
      (init_machine_state undecodable_segments 0x100 demo_phdrs
         (BitVec.ofInt 64 0x7fff80000000) demo_draw [[]] [] demo_uid demo_hwcap)
    = .MachineUnmodeled := by rfl

/-- A configuration the model declines to interpret has no successor at
    all: `Run.sstep_instr` needs `Run.mi_account_step` to have answered
    `MachineOk`, and every syscall constructor needs a pending syscall
    number. -/
theorem unmodeled_no_next (segs : List Segment) (ms : machine_state) (model : Model)
    (evs : List event) (c' : config) :
    ms.ms_svc_pending = none →
    mi_account_step segs ms model = .MachineUnmodeled →
    ¬ sstep segs ⟨ms, model⟩ evs (.SNext c') := by
  intro Hsvc Hacc hss
  cases hss <;> simp_all

/-- ... and therefore emits nothing: the only `Run.star` from it is the
    empty one, so its whole trace set is the empty trace.  This is the
    negative half the trace comparison needs, and it is not available
    from `Run.reaches_error` — erroring says the run CAN fault, not that
    it emitted nothing on the way. -/
theorem no_next_obs_trace_nil (segs : List Segment) (c0 : config) (tr : List event) :
    (∀ evs c', ¬ sstep segs c0 evs (.SNext c')) →
    obs_trace segs c0 tr →
    tr = [] := by
  intro Hno htr
  obtain ⟨tr', c, hstar, hp⟩ := htr
  cases hstar with
  | refl =>
      cases tr with
      | nil => rfl
      | cons e t => exact absurd hp (by simp [is_prefix])
  | step c1 evs c2 tr' c3 hss hrest => exact absurd hss (Hno evs c2)

/-- This one is UNIVERSALLY QUANTIFIED (admission reason 1) rather than
    a two-run comparison like the banner above it: it quantifies over one
    run's whole trace set, which no fold of one observed trace can
    establish.  It is the half of the comparison that says what the
    undecodable image does NOT emit. -/
theorem undecodable_image_emits_nothing (tr : List event) :
    bh_traces (run undecodable_image demo_limit demo_entry demo_proc_input) tr →
    tr = [] := by
  intro Htr
  have Htr' : obs_trace undecodable_segments
      (init_config undecodable_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw demo_limit
        demo_proc_input) tr := Htr
  refine no_next_obs_trace_nil undecodable_segments _ tr ?_ Htr'
  intro evs c'
  refine unmodeled_no_next undecodable_segments _ _ evs c' rfl ?_
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [demo_proc_input, mkProcInput]
  rw [undecodable_step_unmodeled_at_demo_entry]

/-- The exit-0 image and the undecodable image do not agree on this
    input: one of them has a trace ending in `State.ExitEv`, and the
    other has no trace but the empty one.  The
    `MustExit.must_exit_with_realizes`
    step is what turns "must exit 0" into an observable event — without
    it, must-termination and trace equality would be statements about
    different things. -/
theorem exit0_disagrees_with_undecodable :
    ¬ agree exit0_image undecodable_image demo_limit demo_proc_input := by
  intro Hagree
  obtain ⟨Htraces, -⟩ := Hagree
  obtain ⟨tr, fs, Hexit⟩ :=
    must_exit_with_realizes verdict_accept exit0_image demo_limit demo_entry
      demo_proc_input exit0_image_must_exit_zero
  have h2 : bh_traces (run undecodable_image demo_limit demo_entry demo_proc_input)
      (tr ++ [event.ExitEv verdict_accept fs]) :=
    ((Htraces demo_entry demo_entry (demo_entry_valid_exit0 _ demo_input_valid)
      (demo_entry_valid_undecodable _ demo_input_valid))
      (tr ++ [event.ExitEv verdict_accept fs])).1 Hexit
  have h3 := undecodable_image_emits_nothing _ h2
  cases tr with
  | nil => exact absurd h3 (by simp)
  | cons e t => exact absurd h3 (by simp)

/-- ** The error-free obligation, refuted at run level

    UNIVERSALLY QUANTIFIED (admission reason 1), as the negation of one:
    `Equivalence.strong_universal_error_free_T` says no execution of either
    binary faults, on any valid input at any valid entry, and one
    faulting execution at one valid triple is enough to refute it.  The
    image is compared against ITSELF, which the error-free shape does not
    make free — unlike `Equivalence.equiv`, which an all-erroring source
    satisfies against any target, this shape is refuted BY the error
    (`Equivalence.strong_equiv_error_free_no_all_errors_escape` is the
    definition-level form).

    This is the witness `Equivalence`'s non-vacuity comment on the
    error-free shape points at.  It needs the
    same fetch fact at the ASLR-valid entry, this time at
    `State.source_alloc_limit` rather than `demo_limit` — the budget the
    error-free obligation seeds the source run with. -/
theorem run_of_undecodable_image_is_unmodeled_at_demo_entry :
    bh_unmodeled (run undecodable_image source_alloc_limit demo_entry demo_proc_input) := by
  show reaches_unmodeled undecodable_segments
    (init_config undecodable_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw
      source_alloc_limit demo_proc_input)
  refine reaches_unmodeled_intro _ _ _ rfl rfl ?_
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [demo_proc_input, mkProcInput]
  rw [undecodable_step_unmodeled_at_demo_entry]

/-- The abort-declared twin of this one is
    `Checks.AbortWitness.abrt_refutes_error_free_abort`, and it is a
    separate file only because it needs `Checks.Omni`'s stepping
    helpers, which are downstream of this one.  The two are worth
    reading together: this refutation goes through the ERROR conjunct
    (the image is unmodeled on its first fetch), and that one through
    the KILLED conjunct `Equivalence.error_free_unkilled` adds, on an
    image the model follows to the end without erroring once. -/
theorem undecodable_image_refutes_error_free_equivalence :
    ¬ strong_universal_error_free_T undecodable_image undecodable_image :=
  strong_universal_error_free_refuted_by_source_error undecodable_image undecodable_image
    demo_entry demo_entry demo_proc_input
    (demo_entry_valid_undecodable _ demo_input_valid)
    (demo_entry_valid_undecodable _ demo_input_valid)
    demo_input_valid
    (run_unmodeled_errors _ _ _ _ run_of_undecodable_image_is_unmodeled_at_demo_entry)

end LinuxSem.Checks.Examples
