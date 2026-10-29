/-
  * LinuxSem.Checks.GatedSize — a two-gate partition, worked out

  Not part of the trusted specification: QA on the definitions in
  [EquivalenceDefinition.GatedSize], in the style of [Checks/Examples]
  and [Checks/EntryStackFits].

  [EquivalenceDefinition.GatedSize] states that a list of gate images
  cuts the finite input space into disjoint, exhaustive parts, and
  proves it of ABSTRACT images.  Nothing there exhibits a gate.  A
  partition of the input space that no pair of real programs is ever
  shown to produce would be a definition satisfied by nothing, and the
  disjointness lemmas would be free.  So this file runs the definitions
  on two concrete riscv64 binaries and one concrete input, and shows
  all three slice shapes inhabited:

  - PART 1 — the two verdicts.  Two three-instruction images, one
    exiting 0 and one exiting 1.  The accepting verdict is proved for
    EVERY entry the kernel could have chosen, which is what
    [Classifier.accepts] quantifies over; the refusal is proved from
    ONE valid entry, which is all a refutation needs.
  - PART 2 — the three shapes, each inhabited by reordering the same
    two gates: the FIRST slice, a LATER slice (whose earlier gate
    really does refuse), and the RESIDUE.
  - PART 3 — disjointness, applied rather than restated: the concrete
    slice facts of Part 2 are fed to
    [GatedSize.slices_disjoint_accept_accept] and
    [GatedSize.slices_disjoint_accept_rest], and what comes back is a
    refutation of the other slices at this input.
  - PART 4 — [GatedSize.slices_exhaustive] instantiated at each of
    those gate lists, with the per-gate decidability hypothesis
    discharged from Part 1 rather than assumed.  Then the one-program
    case: no gates, one part, the whole input space.
  - PART 5 — the vacuity route the trusted file names, shown biting a
    concrete partition: one image with no valid entry, placed among
    the gates, empties the residue even though the gate beside it
    genuinely refuses every input.
  - PART 6 — the weight bound, refuted concretely at two inputs whose
    cores differ, and carried across
    [GatedSize.weight_bound_pred_of_classifier] to the classifier
    reading it generalises, then SATISFIED at the one-program slice,
    whose complement is empty and whose bound is therefore [0].
  - PART 7 — the two per-slice obligations refuted on a concrete image
    pair.  Both shapes get a positive and a negative case here:
    [GatedSize.gated_slice_T] and [GatedSize.gated_slice_error_free_T]
    hold of every predicate for a pair proved equivalent outright
    (Part 4), and both are refuted outright by the undecodable image
    (Part 7).
  - PART 8 — the same partition and the same obligations under a
    spurious-failure configuration.  The two verdicts are proved again
    at the pinned reading rather than carried over, and Part 7's two
    refutations are proved at EVERY [Run.SpuriousCfg] rather than at
    one.

  Shape: [Classifier.accepts] is a [forall] over every
  valid [Run.ExecEntry] ending in [MustExit.must_exit_with], itself a
  claim about a whole run tree, and no finite set of traces establishes
  either.  A real run shows one execution of one of these binaries; it
  cannot show all of them, and it has no notion of a slice at all.

  The images and the entry are the ones [Checks/Examples] already
  built — [Checks.Examples.exit0_image] and [Checks.Examples.demo_entry],
  with [Checks.Examples.exits_c_must_exit_at] as the evaluator that
  discharges the run tree — reused rather than rebuilt.  Only the
  exit-1 twin is new.  Part 8 needs a second evaluator for the pinned
  reading, [Checks.SpuriousCfg.exits_c_must_exit_at_cfg], which is the
  same [Checks.Examples.exits_c] over [Run.sstep_cfg]; that is the one
  dependency this file adds beyond [Checks/Examples].

  Spelling, and the one place the proofs change shape.

  [Z] is [Int], [Q] is [Rat], `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, and
  the records become structures, so `mkFinProcInput ...` /
  `mkImage ...` literals are structure literals here.  `List.Forall_nil`
  and `List.Forall_cons` are not Lean's: [slice_accept] and
  [slice_rest] use `∀ G' ∈ prev, ...` rather than a `Forall`, so their
  `Forall_nil`/`Forall_cons` steps become `intro`-steps over
  [List.not_mem_nil] and [List.mem_cons].  `1%Q` is `(1 : Rat)`.

  THE CLOSED-COMPUTATION STEPS OF PARTS 1 AND 8 DO NOT REPLAY AS `decide`.
  A free variable anywhere inside the machine state blocks kernel
  reduction of the whole `RiscvSemantics.step` chain, and every `accepts`
  goal has the entry's `sp` and `draw` free.  So the two evaluators are
  ASSEMBLED from
  the generic step lemmas instead — [Examples.PatchClassifyDemo.Verdicts]'
  `step_addi_a7`, `step_addi_a0_0`, `step_addi_a0_1`, `step_ecall`,
  `exits_c_succ_none`, `exits_c_succ_exit`, over the memory-abstracted
  initial state `demo_init_state` and `init_machine_state_abstracts`.
  Each step is then a rewrite and each remaining fetch a `rfl`, exactly
  as [Checks/Omni.lean]'s `exit0_exits_c` does it.  The exit-0 direction
  reuses that landed lemma — `exit0_exits_c` in `Checks.Omni`, at
  `Checks.Examples.exit0_segments`, which is this file's image — and the
  exit-1 direction is [exit1_exits_c] below, its twin at
  [exit1_segments], written out because [Checks.Omni] has no exit-1
  analogue and the image here is a different one from
  `PatchClassifyDemo`'s exit-1 program (same instructions, base 0x100
  rather than 0x10000).

  The other two closed-computation steps in Part 6 (`gated_demo_fin_stdin_valid`,
  `gated_demo_cores_differ`) are ordinary closed computations and stay
  computations: the first is [FinInput.valid_fin_input_stdin_irrelevant]
  applied rather than a re-run of the eleven clauses, and the second is
  `decide` on the one field that differs.
-/
import LinuxSem.Checks.Examples
import LinuxSem.Checks.SpuriousCfg
import LinuxSem.Checks.Omni
import LinuxSem.EquivalenceDefinition.GatedSize

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Checks
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Examples
open LinuxSem.Checks.SpuriousCfg
open LinuxSem.Examples.PatchClassifyDemo.Verdicts (step_addi_a7 step_addi_a0_1
  step_addi_a0_0 step_ecall exits_c_succ_none exits_c_succ_exit
  init_machine_state_abstracts demo_init_state)
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Measure
open LinuxSem.EquivalenceDefinition.GatedSize

namespace LinuxSem.Checks.GatedSize

/- =========================================================================
   PART 1 — two gates, and what each one answers
   ========================================================================= -/

/-- The refusing gate: [Checks.Examples.exit0_image]'s program with one
    immediate changed.  Three instructions at 0x100, as the hex the
    loader would have produced — `addi a7, x0, 93` (0x05d00893),
    `addi a0, x0, 1` (0x00100513), `ecall` (0x00000073), little-endian.
    Same base, same size, same program headers as the exit-0 image, so
    the two are interchangeable everywhere [Run.valid_entry] is
    concerned and the only difference between them is the verdict. -/
def exit1_segment : Segment where
  seg_base := 0x100
  seg_size := 12
  seg_perms := "r-x"
  seg_bytes := ["9308d0051305100073000000"]

def exit1_segments : List Segment := [exit1_segment]
def exit1_image : Image := mkImage exit1_segments 0x100 demo_phdrs

/-- The input the whole file runs on: one empty argument, no
    environment, an empty file system, no standard input.  A
    [FinInput.FinProcInput], because that is what a slice predicate is
    defined on; [FinInput.to_proc_input] carries it to the
    [State.ProcInput] the runs consume, and
    [gated_demo_to_proc_input] pins that the two agree by
    computation rather than by the reader's eye. -/
def gated_demo_fin : FinProcInput :=
  ⟨[[]], [], [], [], demo_uid, demo_gid, demo_groups, net_silent,
   default_nofile, BitVec.ofInt 64 0, demo_hwcap, false, .Sv48, [], []⟩

theorem gated_demo_to_proc_input :
    to_proc_input gated_demo_fin = demo_proc_input := rfl

/-- It is a VALID finite input, which every statement below needs: an
    obligation quantified over valid inputs is refuted by nothing else,
    and a slice containing only invalid inputs is a slice no program is
    ever asked about. -/
theorem gated_demo_fin_valid : valid_fin_input gated_demo_fin := by
  unfold valid_fin_input
  rw [gated_demo_to_proc_input]
  exact demo_input_valid

/-- The exit-1 image really is startable at
    [Checks.Examples.demo_entry] on this input.  Copied from
    [Checks.Examples.demo_entry_valid_exit0] because the two images have
    the same reservation, and needed for the refusal below: a refutation
    of [Classifier.accepts] that named an INVALID entry would refute
    nothing, since the definition never quantified over it.

    "The same reservation" is not merely a resemblance of
    the two images here: [Run.valid_entry] reads nothing of a segment
    but its base, size and permissions, so the exit-1 image's validity
    obligation is the exit-0 one by conversion.  The eighteen-line proof
    is therefore taken from where the tree already has it. -/
theorem demo_entry_valid_exit1 (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry exit1_image demo_entry inp :=
  demo_entry_valid_exit0 inp Hvalid

/-- The exit-1 program, end to end: three steps, then the pending exit.
    The assembled twin of [Checks.Omni.exit0_exits_c], needed because
    this file's image is not that one (see the header's note on why
    these steps do not replay): the same four rewrites, at [exit1_segments] and
    [verdict_reject]. -/
theorem exit1_exits_c (sp : word) (rnd : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) :
    exits_c exit1_segments verdict_reject 8
      (init_machine_state exit1_segments 0x100 demo_phdrs sp rnd argv envp uid hw)
    = true := by
  obtain ⟨mem, rom, hms⟩ :=
    init_machine_state_abstracts exit1_segments 0x100 demo_phdrs sp rnd argv envp uid hw
  rw [hms]
  let st0 : machine_state := demo_init_state 0x100 sp mem rom
  let st1 : machine_state := { st0 with
      ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st0.ms_regs
      ms_pc_val := st0.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st2 : machine_state := { st1 with
      ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 1) st1.ms_regs
      ms_pc_val := st1.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st3 : machine_state := { st2 with ms_svc_pending := some (BitVec.ofInt 64 93) }
  have hpc0 : st0.ms_pc_val = BitVec.ofInt 64 0x100 := rfl
  have hf0 : fetch_word exit1_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x05d00893) := rfl
  have h1 : step exit1_segments st0 = .MachineOk st1 :=
    step_addi_a7 exit1_segments st0 _ hpc0 hf0
  have hpc1 : st1.ms_pc_val = BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 := rfl
  have hf1 : fetch_word exit1_segments (BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00100513) := rfl
  have h2 : step exit1_segments st1 = .MachineOk st2 :=
    step_addi_a0_1 exit1_segments st1 _ hpc1 hf1
  have hpc2 : st2.ms_pc_val
      = BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4 := rfl
  have hf2 : fetch_word exit1_segments
      (BitVec.ofInt 64 0x100 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000073) := rfl
  have ha7 : ms_reg st2 17 = BitVec.ofInt 64 93 := rfl
  have h3 : step exit1_segments st2 = .MachineOk st3 :=
    step_ecall exit1_segments st2 _ hpc2 hf2 ha7
  have hp0 : st0.ms_svc_pending = none := rfl
  have hp1 : st1.ms_svc_pending = none := rfl
  have hp2 : st2.ms_svc_pending = none := rfl
  have hp3 : st3.ms_svc_pending = some (BitVec.ofInt 64 93) := rfl
  have hg : ms_gpr st3 0 = BitVec.ofInt 64 1 := rfl
  have hcode : ms_gpr st3 0 &&& BitVec.ofInt 64 255 = verdict_reject := by
    rw [hg]; decide
  have e0 : exits_c exit1_segments verdict_reject 8 st0
      = exits_c exit1_segments verdict_reject 7 st1 :=
    exits_c_succ_none _ _ 7 st0 st1 hp0 h1
  have e1 : exits_c exit1_segments verdict_reject 7 st1
      = exits_c exit1_segments verdict_reject 6 st2 :=
    exits_c_succ_none _ _ 6 st1 st2 hp1 h2
  have e2 : exits_c exit1_segments verdict_reject 6 st2
      = exits_c exit1_segments verdict_reject 5 st3 :=
    exits_c_succ_none _ _ 5 st2 st3 hp2 h3
  have e3 : exits_c exit1_segments verdict_reject 5 st3 = true :=
    exits_c_succ_exit _ _ 4 st3 _ hp3 (Or.inl rfl) hcode
  rw [e0, e1, e2, e3]

/-- The accepting verdict, AT EVERY ENTRY.  [Classifier.accepts] is a
    [forall] over entries, so one entry would not do it, and this is the
    direction the definition makes hard: the program must exit 0 however
    [execve] placed its stack, break and mmap base, and whatever 16
    AT_RANDOM bytes it drew.  It is provable here
    for the reason [Checks.Examples]'s header gives for the same
    program — it makes no memory access at all beyond its own
    instruction fetches — so all four entry fields are left as VARIABLES
    and the fuel evaluator reduces past them.  A gate that consulted its
    stack pointer, or read the bytes AT_RANDOM points at, would leave the
    reduction stuck on one, which is the honest outcome rather than a
    slow one.

    Note the budget: [Classifier.classifier_alloc_limit], the one
    [Classifier.accepts] runs a gate at, not
    [Cases.Prelude.demo_limit] and not either of the two roles'
    budgets that [Equivalence.strong_equiv] hardwires. -/
theorem gate_exit0_accepts : accepts exit0_image gated_demo_fin := by
  intro en _
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  show must_exit_at exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd
      classifier_alloc_limit (to_proc_input gated_demo_fin))
  refine exits_c_must_exit_at exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  rw [gated_demo_to_proc_input]
  exact LinuxSem.Checks.Omni.exit0_exits_c sp rnd _ _ _ _

/-- ... and the refusal.  Exiting 1 at ONE valid entry is enough, which
    is the asymmetry [Classifier.accepts]'s [forall] creates and
    [Classifier.rejects_by_exit1] is the introduction rule for: the step
    from "exits 1 here" to "does not accept" runs through
    [MustExit.must_exit_with_exclusive] against
    [Classifier.verdict_accept_neq_reject]. -/
theorem gate_exit1_rejects : rejects exit1_image gated_demo_fin := by
  refine rejects_by_exit1 exit1_image gated_demo_fin demo_entry
    gated_demo_fin_valid ?_ ?_
  · rw [gated_demo_to_proc_input]
    exact demo_entry_valid_exit1 demo_proc_input demo_input_valid
  · show must_exit_at exit1_segments verdict_reject
      (init_config exit1_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_brk
        demo_entry.en_mmap_base demo_entry.en_draw
        classifier_alloc_limit (to_proc_input gated_demo_fin))
    refine exits_c_must_exit_at exit1_segments verdict_reject 8 _ _
      (m_halted_init_model _ _ _ _ _ _) rfl ?_
    rw [gated_demo_to_proc_input]
    exact exit1_exits_c _ _ _ _ _ _

theorem gate_exit1_refuses : ¬ accepts exit1_image gated_demo_fin :=
  gate_exit1_rejects.2

/- =========================================================================
   PART 2 — all three slice shapes, inhabited
   ========================================================================= -/

/-- The three gate lists.  The same two images in three arrangements,
    which is enough to put this one input in each of the three shapes in
    turn — a slice is a property of the input AND the list, and reading
    it off one fixed list would show at most one shape. -/
def gates_accept_first : List Image := [exit0_image, exit1_image]
def gates_accept_second : List Image := [exit1_image, exit0_image]
def gates_refuse_all : List Image := [exit1_image, exit1_image]

/-- THE FIRST SLICE: the leading gate accepts, and there is no earlier
    gate to refuse. -/
theorem slice_first_inhabited : slice_accept [] exit0_image gated_demo_fin := by
  refine ⟨gate_exit0_accepts, ?_⟩
  intro G' Hin
  exact absurd Hin (List.not_mem_nil)

/-- A LATER SLICE, and the interesting one: the accepting gate is
    reached only because the gate before it refuses, and that refusal is
    proved rather than assumed.  This is the shape a submission's second
    program is measured on. -/
theorem slice_second_inhabited :
    slice_accept [exit1_image] exit0_image gated_demo_fin := by
  refine ⟨gate_exit0_accepts, ?_⟩
  intro G' Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  subst Hin
  exact gate_exit1_refuses

/-- THE RESIDUE: every gate refuses, so the input falls through to the
    final program, which has no gate of its own. -/
theorem slice_residue_inhabited : slice_rest gates_refuse_all gated_demo_fin := by
  intro G' Hin
  simp only [gates_refuse_all, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact gate_exit1_refuses
  · exact gate_exit1_refuses

/- =========================================================================
   PART 3 — disjointness, applied
   ========================================================================= -/

/-- The trusted disjointness lemmas, used the way a consumer uses them:
    a concrete slice fact goes in and a refutation of a competing slice
    comes out.  Here [GatedSize.slices_disjoint_accept_accept] turns
    "this input is in the second slice of [gates_accept_second]" into
    "it is not in the first", with no further computation on the
    binaries — the leading gate's refusal is already recorded in the
    slice fact. -/
theorem slice_first_of_accept_second_refuted :
    ¬ slice_accept [] exit1_image gated_demo_fin := by
  intro Hfirst
  exact slices_disjoint_accept_accept [] exit1_image [exit1_image] exit0_image
    gated_demo_fin (by simp) Hfirst slice_second_inhabited

/-- ... and [GatedSize.slices_disjoint_accept_rest] empties the residue
    of [gates_accept_first] at this input: an input the leading gate
    accepts never reaches the final program. -/
theorem residue_of_accept_first_refuted :
    ¬ slice_rest gates_accept_first gated_demo_fin := by
  intro Hrest
  exact slices_disjoint_accept_rest [] exit0_image gates_accept_first
    gated_demo_fin (by simp [gates_accept_first]) slice_first_inhabited Hrest

/-- The same in the other arrangement: the input is in the second slice
    of [gates_accept_second], so it is not in that list's residue
    either. -/
theorem residue_of_accept_second_refuted :
    ¬ slice_rest gates_accept_second gated_demo_fin := by
  intro Hrest
  exact slices_disjoint_accept_rest [exit1_image] exit0_image
    gates_accept_second gated_demo_fin (by simp [gates_accept_second])
    slice_second_inhabited Hrest

/- =========================================================================
   PART 4 — exhaustiveness, instantiated
   ========================================================================= -/

/-- The per-gate decidability hypothesis [GatedSize.slices_exhaustive]
    asks for, discharged for these gates at this input from Part 1
    rather than assumed.  This is the point of stating excluded middle
    as a hypothesis: for a gate whose verdict is actually settled, the
    instance is a proof, and nothing classical enters the file. -/
theorem gates_accept_first_decidable (G : Image) (Hin : G ∈ gates_accept_first) :
    accepts G gated_demo_fin ∨ ¬ accepts G gated_demo_fin := by
  simp only [gates_accept_first, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact Or.inl gate_exit0_accepts
  · exact Or.inr gate_exit1_refuses

theorem gates_refuse_all_decidable (G : Image) (Hin : G ∈ gates_refuse_all) :
    accepts G gated_demo_fin ∨ ¬ accepts G gated_demo_fin := by
  simp only [gates_refuse_all, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact Or.inr gate_exit1_refuses
  · exact Or.inr gate_exit1_refuses

/-- Exhaustiveness landing in the LEFT disjunct, with the decomposition
    it hands back read off: the accepting gate is the head, its prefix
    is empty, and the slice is the one Part 2 exhibited. -/
theorem gates_accept_first_exhaustive :
    (∃ prev G suffix,
       gates_accept_first = prev ++ G :: suffix ∧ slice_accept prev G gated_demo_fin)
    ∨ slice_rest gates_accept_first gated_demo_fin :=
  slices_exhaustive gates_accept_first gated_demo_fin gates_accept_first_decidable

/-- ... and landing in the RIGHT one: with every gate refusing, the
    input is in the residue and no decomposition exists.  Both halves
    are asserted, because the disjunction alone would be satisfied by
    the wrong side. -/
theorem gates_refuse_all_exhaustive :
    ((∃ prev G suffix,
       gates_refuse_all = prev ++ G :: suffix ∧ slice_accept prev G gated_demo_fin)
     ∨ slice_rest gates_refuse_all gated_demo_fin)
    ∧ ¬ (∃ prev G suffix,
          gates_refuse_all = prev ++ G :: suffix
          ∧ slice_accept prev G gated_demo_fin) := by
  refine ⟨slices_exhaustive gates_refuse_all gated_demo_fin gates_refuse_all_decidable, ?_⟩
  intro ⟨prev, G, suffix, Heq, Hacc⟩
  have Hin : G ∈ gates_refuse_all := by rw [Heq]; simp
  simp only [gates_refuse_all, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact gate_exit1_refuses Hacc.1
  · exact gate_exit1_refuses Hacc.1

/-- The one-program case, which is where the whole family has to agree
    with the ungated measure: no gates, one part, and that part is the
    entire input space.  A submission that declares no gates is asked
    for exactly [Equivalence.strong_universal_T] restricted to the
    finite inputs, by [GatedSize.gated_slice_of_universal] at
    [P := slice_rest []]. -/
theorem one_program_residue_is_everything : slice_rest [] gated_demo_fin :=
  slice_rest_nil gated_demo_fin

theorem one_program_obligation_is_the_baseline (Src A : Image)
    (H : strong_universal_T Src A) : gated_slice_T Src A (slice_rest []) :=
  gated_slice_of_universal Src A _ H

/-- ... and the error-free twin, which is owed for the same reason: a
    task that keeps [Equivalence.strong_universal_error_free_T] rather
    than the baseline gets the one-program case back on the same terms,
    with no separate scheme and no weaker obligation. -/
theorem one_program_error_free_obligation_is_the_baseline (Src A : Image)
    (H : strong_universal_error_free_T Src A) :
    gated_slice_error_free_T Src A (slice_rest []) :=
  gated_slice_error_free_of_universal Src A _ H

/- =========================================================================
   PART 5 — the vacuity route, biting a concrete partition
   ========================================================================= -/

/-- What an image that does not load does to a partition, shown against
    a gate that really works.  [Gbad] is quantified rather than
    exhibited, because the tree carries no concrete image for which
    [Run.valid_entry] is empty at a valid input — [Run.valid_sp] and
    [Run.valid_mmap_base] do not depend on the image, and
    [Equivalence.image_brk_satisfiable_entry] inhabits the rest for a
    well-formed one.  The hypothesis is exactly
    [Classifier.accepts_vacuous_no_entries]'s, and everything else here
    is concrete.

    First half: such an image ACCEPTS, so its slice is the whole residue
    left by the gates before it.  The direction is the one a reader gets
    backwards — "no valid entry" is not "accepts nothing". -/
theorem vacuous_gate_swallows_the_residue (Gbad : Image)
    (Hno : ∀ en, ¬ valid_entry Gbad en (to_proc_input gated_demo_fin)) :
    slice_accept [exit1_image] Gbad gated_demo_fin := by
  refine (slice_accept_vacuous_no_entries [exit1_image] Gbad gated_demo_fin Hno).2 ?_
  intro G' Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  subst Hin
  exact gate_exit1_refuses

/-- Second half, and the one that costs a checker: the residue is now
    EMPTY at this input, even though [exit1_image] beside it genuinely
    refuses every input it is offered.  The final program is never asked
    about this input at all, and its [GatedSize.gated_slice_T]
    obligation holds with nothing established about its binary.

    The remedy is not in this layer: a consuming checker ascribes
    [Equivalence.IMAGE_WF] to every gate image it names, which is what
    [Measure]'s header already requires for the classifier image and
    [Equivalence]'s for the two compared ones. -/
theorem vacuous_gate_empties_the_residue (Gbad : Image)
    (Hno : ∀ en, ¬ valid_entry Gbad en (to_proc_input gated_demo_fin)) :
    ¬ slice_rest [exit1_image, Gbad] gated_demo_fin :=
  slice_rest_vacuous_no_entries [exit1_image, Gbad] Gbad gated_demo_fin
    (by simp) Hno

/- =========================================================================
   PART 6 — the weight bound, refuted concretely
   ========================================================================= -/

/-- A second valid input, differing from the first only in its standard
    input.  [FinInput.valid_fin_input] says nothing about [fin_stdin]
    ([FinInput.valid_fin_input_stdin_irrelevant]), so it is valid for
    the same reason the first is; and standard input is part of the
    CORE, so the two cores differ, which is what
    [GatedSize.weight_bound_pred_refutable] asks for. -/
def gated_demo_fin_stdin : FinProcInput :=
  ⟨[[]], [], [], [BitVec.ofInt 8 65], demo_uid, demo_gid, demo_groups, net_silent,
   default_nofile, BitVec.ofInt 64 0, demo_hwcap, false, .Sv48, [], []⟩

theorem gated_demo_fin_stdin_valid : valid_fin_input gated_demo_fin_stdin :=
  valid_fin_input_stdin_irrelevant gated_demo_fin [BitVec.ofInt 8 65]
    gated_demo_fin_valid

theorem gated_demo_cores_differ :
    fin_core gated_demo_fin ≠ fin_core gated_demo_fin_stdin := by
  intro H
  have h := congrArg FinCore.core_stdin H
  simp only [fin_core, gated_demo_fin, gated_demo_fin_stdin] at h
  exact absurd h (by decide)

/-- The exit-1 gate refuses the second input too, for the same reason
    and at the same entry: the program never reads standard input, so
    the fuel evaluator closes it unchanged. -/
theorem gate_exit1_refuses_stdin :
    ¬ accepts exit1_image gated_demo_fin_stdin := by
  refine (rejects_by_exit1 exit1_image gated_demo_fin_stdin demo_entry
    gated_demo_fin_stdin_valid ?_ ?_).2
  · exact demo_entry_valid_exit1 _ gated_demo_fin_stdin_valid
  · show must_exit_at exit1_segments verdict_reject
      (init_config exit1_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_brk
        demo_entry.en_mmap_base demo_entry.en_draw
        classifier_alloc_limit (to_proc_input gated_demo_fin_stdin))
    refine exits_c_must_exit_at exit1_segments verdict_reject 8 _ _
      (m_halted_init_model _ _ _ _ _ _) rfl ?_
    exact exit1_exits_c _ _ _ _ _ _

/-- Two valid inputs with distinct cores outside the predicate refute
    the unit bound.  So a [GatedSize.weight_bound_pred_T] claim is a
    real restriction on how much of the input space can sit outside a
    slice — not something every predicate and every distribution
    satisfies — and this is the concrete instance of that. -/
theorem unit_bound_refuted_at_exit1_gate :
    ¬ weight_bound_pred_T (accepts exit1_image) (fun _ => 1) 1 1 :=
  weight_bound_pred_refutable (accepts exit1_image) gated_demo_fin
    gated_demo_fin_stdin gated_demo_fin_valid gate_exit1_refuses
    gated_demo_fin_stdin_valid gate_exit1_refuses_stdin gated_demo_cores_differ

/-- ... and the same refutation read back as a [Measure.weight_bound_T]
    one, through [GatedSize.weight_bound_pred_of_classifier].  This is
    the bridge working in the direction a consumer needs it: the two
    statements are the same statement at
    [P := Classifier.accepts C], so a refutation of either is a
    refutation of both, and the gated measure does not weaken the bound
    the ungated one asked for. -/
theorem unit_bound_refuted_as_classifier_bound :
    ¬ weight_bound_T exit1_image (fun _ => 1) 1 1 := by
  intro Hbound
  exact unit_bound_refuted_at_exit1_gate
    ((weight_bound_pred_of_classifier exit1_image (fun _ => 1) 1 1).1 Hbound)

/-- THE BOUND IS SATISFIABLE, and at the one-program slice it is
    satisfiable at [0].  Part 6's refutation on its own would leave open
    that [GatedSize.weight_bound_pred_T] is a predicate nothing meets,
    which would make the refutation free; this is the other half.

    The instance is the one-program case again, and the number is not a
    vacuity: [GatedSize.slice_rest []] is the WHOLE input space
    ([one_program_residue_is_everything]), so its complement is empty,
    so no admissible list exists to weigh and the bound is [0] rather
    than merely small.  Reading that as evidence about a binary would be
    the mistake — it is evidence about the PARTITION, and it is exactly
    what a consumer needs when it charges unproven mass at the dearest
    slice: with one program there is no unproven mass.

    It holds for EVERY weight and every declared total, because the
    proof never looks at either.  The list is empty by
    [GatedSize.slice_rest_nil], and an empty sum is [0]. -/
theorem one_program_bound_pred_at_zero (w : FinProcInput → Rat) (M : Rat) :
    weight_bound_pred_T (slice_rest []) w M 0 := by
  intro l _ Hall
  cases l with
  | nil =>
      show sum_weights w [] ≤ 0 * M
      rw [sum_weights_nil, Rat.zero_mul]
      exact Rat.le_refl
  | cons f l =>
      exfalso
      obtain ⟨_, Hout⟩ := Hall f (List.mem_cons_self ..)
      exact Hout (slice_rest_nil f)

/-- The same bound at any multiplier a task might declare, through
    [GatedSize.weight_bound_pred_mono] — the trusted monotonicity lemma
    applied rather than restated.  [0 <= M] is the hypothesis that lemma
    needs and cannot get from anywhere else, for the reason [Measure]'s
    header gives: [M] is declared, not summed, so nothing forces it to
    agree in sign with the weights it is the total of. -/
theorem one_program_bound_pred_at_any (w : FinProcInput → Rat) (M b : Rat)
    (HM : 0 ≤ M) (Hb : 0 ≤ b) : weight_bound_pred_T (slice_rest []) w M b :=
  weight_bound_pred_mono (slice_rest []) w M 0 b HM Hb
    (one_program_bound_pred_at_zero w M)

/- =========================================================================
   PART 7 — both per-slice obligations refuted on a concrete image pair
   ========================================================================= -/

/-- [GatedSize.gated_slice_refuted] and its error-free twin, applied.
    The image is [Checks.Examples.undecodable_image] run against itself:
    its first instruction fetch leaves the modeled surface, at the
    ASLR-valid [Checks.Examples.demo_entry] and at
    [State.source_alloc_limit] — which is the budget both slice
    obligations seed the SOURCE run with, and the reason
    [Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry]
    is stated at that budget rather than at
    [Cases.Prelude.demo_limit].

    The predicate is [GatedSize.slice_rest []], the whole input space, so
    the refutation is at the widest slice.  By
    [GatedSize.gated_slice_mono] a refutation there does NOT carry to a
    narrower one — monotonicity runs the other way — which is why the
    input is exhibited rather than left abstract: it is [gated_demo_fin]
    that must be in the slice, and it is.

    Refuting the baseline shape goes through the [Equivalence.modeled]
    conjunct, which is the one the error-free shape does not have. -/
theorem undecodable_refutes_the_slice :
    ¬ gated_slice_T undecodable_image undecodable_image (slice_rest []) := by
  refine gated_slice_refuted undecodable_image undecodable_image (slice_rest [])
    gated_demo_fin demo_entry demo_entry gated_demo_fin_valid
    (slice_rest_nil gated_demo_fin) ?_ ?_ ?_
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · intro ⟨Hmodeled, _⟩
    exact Hmodeled (by
      rw [gated_demo_to_proc_input]
      exact run_of_undecodable_image_is_unmodeled_at_demo_entry)

/-- ... and the error-free shape, refuted at the same triple by the same
    fetch.  The route differs, and the difference is the point: there is
    no [Equivalence.modeled] conjunct to fail, so the refutation goes
    through SOURCE ERROR-FREEDOM instead, via
    [Equivalence.run_unmodeled_errors] — leaving the modeled surface is
    a special case of erroring, and the error-free shape forbids
    erroring outright.  This is the concrete witness that
    [GatedSize.gated_slice_error_free_T] is a real obligation and not
    merely a second name for the first. -/
theorem undecodable_refutes_the_error_free_slice :
    ¬ gated_slice_error_free_T undecodable_image undecodable_image (slice_rest []) := by
  refine gated_slice_error_free_refuted undecodable_image undecodable_image
    (slice_rest []) gated_demo_fin demo_entry demo_entry gated_demo_fin_valid
    (slice_rest_nil gated_demo_fin) ?_ ?_ ?_
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · intro ⟨Hsrc, _, _⟩
    exact Hsrc (by
      rw [gated_demo_to_proc_input]
      exact run_unmodeled_errors _ _ _ _
        run_of_undecodable_image_is_unmodeled_at_demo_entry)

/- =========================================================================
   PART 8 — the same partition and the same obligations, under a
   spurious-failure configuration
   ========================================================================= -/

/- [EquivalenceDefinition.GatedSize]'s configuration section states two
    things that pull in opposite directions, and this part runs both on
    the concrete images so a reader can see they really do:

    - the GATES are read under [Run.forced_only_cfg] whatever the task
      chose ([Classifier.accepts_fo]), so Part 1's two verdicts are
      re-established at the pinned reading rather than carried over.
      Carrying them over is not impossible — [Classifier.accepts_fo_of_accepts]
      does it given [Classifier.classifier_decided] — but that premise
      has no proof for these images either, so re-proving is the shorter
      route rather than the only one;
    - the PROGRAMS are judged under the task's [cfg], so Part 7's
      refutations have to hold at EVERY [cfg] rather than at one.

    Both work out here, and for different reasons.  The verdicts survive
    the pin because these two binaries make no syscall but [exit], which
    belongs to no family ([Checks.SpuriousCfg.exit_has_no_family]), so no
    filter touches either run.  The refutations survive every
    configuration because the undecodable image leaves the modeled
    surface on its FIRST FETCH, which is an instruction step, and the
    filter touches no instruction step. -/

/-- The accepting verdict at the pinned reading, at every entry.
    [Checks.SpuriousCfg.exits_c_must_exit_at_cfg] is the evaluator, and
    it is the same [Checks.Examples.exits_c] over [Run.sstep_cfg]. -/
theorem gate_exit0_accepts_fo : accepts_fo exit0_image gated_demo_fin := by
  intro en _
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  show must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept
    (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd
      classifier_alloc_limit (to_proc_input gated_demo_fin))
  refine exits_c_must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  rw [gated_demo_to_proc_input]
  exact LinuxSem.Checks.Omni.exit0_exits_c sp rnd _ _ _ _

/-- ... and the refusal, from ONE valid entry, through
    [Classifier.rejects_fo_by_exit1]. -/
theorem gate_exit1_rejects_fo : rejects_fo exit1_image gated_demo_fin := by
  refine rejects_fo_by_exit1 exit1_image gated_demo_fin demo_entry
    gated_demo_fin_valid ?_ ?_
  · rw [gated_demo_to_proc_input]
    exact demo_entry_valid_exit1 demo_proc_input demo_input_valid
  · show must_exit_at_cfg forced_only_cfg exit1_segments verdict_reject
      (init_config exit1_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_brk
        demo_entry.en_mmap_base demo_entry.en_draw
        classifier_alloc_limit (to_proc_input gated_demo_fin))
    refine exits_c_must_exit_at_cfg forced_only_cfg exit1_segments verdict_reject 8 _ _
      (m_halted_init_model _ _ _ _ _ _) rfl ?_
    rw [gated_demo_to_proc_input]
    exact exit1_exits_c _ _ _ _ _ _

theorem gate_exit1_refuses_fo : ¬ accepts_fo exit1_image gated_demo_fin :=
  gate_exit1_rejects_fo.2

/-- The three slice shapes, inhabited at the pinned reading, by the same
    three arrangements of the same two gates. -/
theorem slice_first_inhabited_fo : slice_accept_fo [] exit0_image gated_demo_fin := by
  refine ⟨gate_exit0_accepts_fo, ?_⟩
  intro G' Hin
  exact absurd Hin (List.not_mem_nil)

theorem slice_second_inhabited_fo :
    slice_accept_fo [exit1_image] exit0_image gated_demo_fin := by
  refine ⟨gate_exit0_accepts_fo, ?_⟩
  intro G' Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  subst Hin
  exact gate_exit1_refuses_fo

theorem slice_residue_inhabited_fo : slice_rest_fo gates_refuse_all gated_demo_fin := by
  intro G' Hin
  simp only [gates_refuse_all, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact gate_exit1_refuses_fo
  · exact gate_exit1_refuses_fo

/-- Disjointness applied at the pinned reading, the way a consumer uses
    it: a concrete slice fact goes in and a refutation of a competing
    slice comes out. -/
theorem residue_of_accept_first_refuted_fo :
    ¬ slice_rest_fo gates_accept_first gated_demo_fin := by
  intro Hrest
  exact slices_disjoint_accept_rest_fo [] exit0_image gates_accept_first
    gated_demo_fin (by simp [gates_accept_first]) slice_first_inhabited_fo Hrest

/-- Exhaustiveness at the pinned reading, with the per-gate hypothesis
    discharged from the two verdicts above rather than assumed — the
    same point Part 4 makes, and the reason excluded middle stays a
    hypothesis rather than becoming a postulate of the file. -/
theorem gates_accept_first_decidable_fo (G : Image) (Hin : G ∈ gates_accept_first) :
    accepts_fo G gated_demo_fin ∨ ¬ accepts_fo G gated_demo_fin := by
  simp only [gates_accept_first, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with rfl | rfl
  · exact Or.inl gate_exit0_accepts_fo
  · exact Or.inr gate_exit1_refuses_fo

theorem gates_accept_first_exhaustive_fo :
    (∃ prev G suffix,
       gates_accept_first = prev ++ G :: suffix
       ∧ slice_accept_fo prev G gated_demo_fin)
    ∨ slice_rest_fo gates_accept_first gated_demo_fin :=
  slices_exhaustive_fo gates_accept_first gated_demo_fin gates_accept_first_decidable_fo

/-- THE VACUITY ROUTE IS NOT CLOSED BY THE PIN, which is the half of
    Part 5 a reader might hope the configuration layer repaired.  A gate
    image with no valid entry still ACCEPTS every input under
    [Run.forced_only_cfg] — the route runs through the entry quantifier,
    which no configuration touches — so it still swallows the residue
    the earlier gates left. -/
theorem vacuous_gate_swallows_the_residue_fo (Gbad : Image)
    (Hno : ∀ en, ¬ valid_entry Gbad en (to_proc_input gated_demo_fin)) :
    slice_accept_fo [exit1_image] Gbad gated_demo_fin := by
  refine (slice_accept_fo_vacuous_no_entries [exit1_image] Gbad gated_demo_fin Hno).2 ?_
  intro G' Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  subst Hin
  exact gate_exit1_refuses_fo

/-- The one-program case under a configuration: a submission that
    declares no gates is asked for exactly
    [Equivalence.strong_universal_T_scfg] at its own configuration,
    restricted to the finite inputs.  The configured twin of
    [one_program_obligation_is_the_baseline], and the [cfg] is shared
    between hypothesis and conclusion because there is no lemma taking
    one configuration to another. -/
theorem one_program_residue_is_everything_fo : slice_rest_fo [] gated_demo_fin :=
  slice_rest_fo_nil gated_demo_fin

theorem one_program_obligation_is_the_baseline_scfg (cfg : SpuriousCfg) (Src A : Image)
    (H : strong_universal_T_scfg cfg Src A) :
    gated_slice_T_scfg cfg Src A (slice_rest_fo []) :=
  gated_slice_T_scfg_of_universal cfg Src A _ H

theorem one_program_error_free_obligation_is_the_baseline_scfg (cfg : SpuriousCfg)
    (Src A : Image) (H : strong_universal_error_free_T_scfg cfg Src A) :
    gated_slice_error_free_T_scfg cfg Src A (slice_rest_fo []) :=
  gated_slice_error_free_T_scfg_of_universal cfg Src A _ H

/-- The undecodable image is uncovered under EVERY configuration at this
    entry and this input.  Turning a family off removes executions and
    carries nothing down for free, so this cannot be inherited from
    [Checks.Examples.run_of_undecodable_image_is_unmodeled_at_demo_entry]
    — but it does not need to be: the fetch that leaves the modeled
    surface is the FIRST step, an instruction step, and no filter
    touches an instruction step.  The witness is the empty
    [Run.star_cfg], which exists at every [cfg]. -/
theorem undecodable_unmodeled_scfg_at_demo_entry (cfg : SpuriousCfg) :
    bh_unmodeled (run_scfg cfg undecodable_image source_alloc_limit demo_entry
                    (to_proc_input gated_demo_fin)) := by
  rw [gated_demo_to_proc_input]
  show reaches_unmodeled_cfg undecodable_segments cfg
    (init_config undecodable_segments 0x100 demo_phdrs demo_entry.en_sp
      demo_entry.en_brk demo_entry.en_mmap_base demo_entry.en_draw
      source_alloc_limit demo_proc_input)
  refine ⟨[], _, star_cfg.refl _, ?_⟩
  refine ⟨m_halted_init_model _ _ _ _ _ _, Or.inl ⟨rfl, ?_⟩⟩
  show mi_account_step undecodable_segments
    (init_machine_state undecodable_segments 0x100 demo_phdrs demo_entry.en_sp
      demo_entry.en_draw demo_proc_input.in_argv demo_proc_input.in_envp
      demo_proc_input.in_uid demo_proc_input.in_hwcap)
    (init_model (segments_reserved undecodable_segments) demo_entry.en_brk
      demo_entry.en_mmap_base demo_entry.en_sp source_alloc_limit demo_proc_input)
    = .MachineUnmodeled
  rw [mi_account_step_no_lazy _ _ _ rfl]
  simp only [demo_proc_input, mkProcInput, demo_entry]
  rw [undecodable_step_unmodeled_at_demo_entry]

/-- Part 7's two refutations, now at every configuration.  The baseline
    shape fails through the [Equivalence.modeled] conjunct and the
    error-free shape through source error-freedom, which is the same
    split the unparameterized pair makes and for the same reason: the
    error-free shape has no [Equivalence.modeled] conjunct to fail.

    Quantified over [cfg] rather than stated at one, which is what says
    the configured obligation is a real claim wherever a task lands
    rather than only under may-fail. -/
theorem undecodable_refutes_the_slice_scfg (cfg : SpuriousCfg) :
    ¬ gated_slice_T_scfg cfg undecodable_image undecodable_image (slice_rest_fo []) := by
  refine gated_slice_T_scfg_refuted cfg undecodable_image undecodable_image
    (slice_rest_fo []) gated_demo_fin demo_entry demo_entry gated_demo_fin_valid
    (slice_rest_fo_nil gated_demo_fin) ?_ ?_ ?_
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · intro ⟨Hmodeled, _⟩
    exact Hmodeled (undecodable_unmodeled_scfg_at_demo_entry cfg)

theorem undecodable_refutes_the_error_free_slice_scfg (cfg : SpuriousCfg) :
    ¬ gated_slice_error_free_T_scfg cfg undecodable_image undecodable_image
        (slice_rest_fo []) := by
  refine gated_slice_error_free_T_scfg_refuted cfg undecodable_image undecodable_image
    (slice_rest_fo []) gated_demo_fin demo_entry demo_entry gated_demo_fin_valid
    (slice_rest_fo_nil gated_demo_fin) ?_ ?_ ?_
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · exact demo_entry_valid_undecodable _ gated_demo_fin_valid
  · intro ⟨Hsrc, _, _⟩
    exact Hsrc (run_scfg_unmodeled_errors cfg undecodable_image source_alloc_limit
      demo_entry (to_proc_input gated_demo_fin)
      (undecodable_unmodeled_scfg_at_demo_entry cfg))

end LinuxSem.Checks.GatedSize
