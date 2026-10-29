/-
  * LinuxProcessSem.Checks.Cases.VaSize — the declared address-space size, instance by instance

  Worked cases over the `VaSize` block of `State` and the per-size entry
  predicates of `Run`.  The declaration is a value of the input, so
  what there is to pin is (i) that the [Sv48] instance is the literal
  constants the rest of the tree was written against, derived rather
  than copied; (ii) that a wrong declaration is refused for the RIGHT
  reason -- at the entry, by the declared window, and at the
  statement, by the conjunct [Equivalence.strong_equiv_va] puts in
  front of [strong_equiv] -- and not answered with the Sv48 limit;
  and (iii) that the unpinned predicate accepts exactly what
  the three pinned ones accept, so the sealed family
  ([Equivalence.SPEC_VA_ANY] and its siblings) says what its name says.

  `Checks.Examples` keeps what is not per-syscall and
  re-exports this module.

  Spelling.  `Z` is `Int`, `word` is `BitVec 64`, `Z_to_bv 64 z` is
  `BitVec.ofInt 64 z`, `bv_unsigned w` is `(w.toNat : Int)`, and the
  record projections the prelude applies as functions (`img_segments img`)
  are dot notation here (`img.img_segments`) — [valid_entry] is
  spelled with projections rather than with a `match img, en with`, and
  [valid_entry_sv48] is the same biconditional (see its own note).

  Proofs.  Every goal below is a closed decidable proposition, so it
  closes by `decide`, or by `rfl` where it holds by definition.  Each is
  a closed evaluation on `Int` literals, not the super-linear kind of
  computation that has to be restructured.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Checks.Cases.VaSize

/-! ## (i) The Sv48 instance is today's constants

    [va_sp_window_lo] and [va_mmap_base_max] are DERIVED from the stack
    top by the formulas [State.sp_window_lo]'s and [State.mmap_base_max]'s
    notes give; these pins compare the derivation with the literal, so a
    slip in either direction shows up here rather than in a window that
    quietly moved.  The ones that hold by definition ([va_task_size Sv48]
    is `TASK_SIZE`) are documentary and say so. -/

theorem sv48_task_size_is_TASK_SIZE : va_task_size .Sv48 = TASK_SIZE := by
  rfl  -- by definition

theorem sv48_task_size_is_2_47 : va_task_size .Sv48 = 2 ^ 47 := by
  decide

/-- [va_stack_top] is the window's top by definition (`State.va_sp_window_hi`
    IS it), so this is documentary. -/
theorem sv48_stack_top_is_the_window_top : va_stack_top .Sv48 = sp_window_hi := by
  rfl

theorem sv48_window_lo_is_the_literal : va_sp_window_lo .Sv48 = sp_window_lo := by
  decide

theorem sv48_window_hi_is_the_literal : va_sp_window_hi .Sv48 = sp_window_hi := by
  decide

theorem sv48_mmap_base_max_is_the_literal : va_mmap_base_max .Sv48 = mmap_base_max := by
  decide

theorem sv48_mmap_base_min_is_the_literal : va_mmap_base_min .Sv48 = mmap_base_min := by
  rfl  -- by definition

/-- The predicates, not only the numbers: under an [Sv48] input,
    [Run.valid_entry] is the literal predicate conjunct for conjunct
    ([Run.valid_entry_sv48]), fired here at the fixture input so the
    lemma is seen to apply to the inputs the examples use.

    [Run.valid_entry] is stated in projection form rather than as a
    `match img, en with`, and the draw field is discarded in both
    spellings, so this is the same biconditional with the match spelled
    out — [valid_entry_sv48] at the fixture's declaration. -/
theorem demo_entry_predicate_is_the_sv48_one (img : Image) (en : ExecEntry)
    (fs0 : Fs.Fs) (s : InputStream) :
    valid_entry img en (demo_input fs0 s)
    ↔ valid_sp en.en_sp ∧ valid_brk img.img_segments en.en_brk
      ∧ valid_mmap_base en.en_mmap_base
      ∧ entry_stack_fits en.en_sp (demo_input fs0 s).in_argv
          (demo_input fs0 s).in_envp :=
  valid_entry_sv48 img en (demo_input fs0 s) rfl

/-! ## Sv57 shares the window and differs in the limit

    [MMAP_VA_BITS] saturates at 48 (arch/riscv/include/asm/pgtable.h,
    Linux v6.18.46, commit 1f99e9ab748f), so an Sv57 kernel places its
    stack and its mmap base where an Sv48 one does and differs only in
    [TASK_SIZE_64].  Both halves pinned, because a change that moved the
    window with the limit would be wrong in exactly the way this file
    exists to catch. -/
theorem sv57_window_is_sv48s :
    va_sp_window_lo .Sv57 = va_sp_window_lo .Sv48
    ∧ va_sp_window_hi .Sv57 = va_sp_window_hi .Sv48
    ∧ va_mmap_base_min .Sv57 = va_mmap_base_min .Sv48
    ∧ va_mmap_base_max .Sv57 = va_mmap_base_max .Sv48 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem sv57_task_size_is_2_56 : va_task_size .Sv57 = 2 ^ 56 := by
  decide

theorem sv57_limit_is_not_sv48s : va_task_size .Sv57 ≠ va_task_size .Sv48 := by
  decide

/-- Under Sv39 the two coincide: [STACK_TOP = TASK_SIZE = 2^38]. -/
theorem sv39_top_is_the_whole_space :
    va_task_size .Sv39 = 2 ^ 38 ∧ va_stack_top .Sv39 = 2 ^ 38 := by
  constructor <;> decide

theorem sv39_window :
    va_sp_window_lo .Sv39 = 0x3f80000000 ∧ va_sp_window_hi .Sv39 = 0x4000000000 := by
  constructor <;> decide

/-! ## (ii) A wrong declaration is red for the right reason

    AT THE ENTRY: the bottom of the Sv48 window is a placement every
    example uses, and the Sv39 window refuses it -- it lies 254 GiB
    above the last address an Sv39 process has -- while the Sv57 window
    admits it.  The refusal is by the window's upper bound, which is the
    reason the model would give ([Run.valid_sp_va]). -/
def sv48_window_bottom : word := BitVec.ofInt 64 sp_window_lo

theorem sv48_window_bottom_valid_under_sv48 : valid_sp_va .Sv48 sv48_window_bottom := by
  unfold valid_sp_va sv48_window_bottom
  decide

theorem sv48_window_bottom_refused_under_sv39 : ¬ valid_sp_va .Sv39 sv48_window_bottom := by
  unfold valid_sp_va sv48_window_bottom
  decide

theorem sv48_window_bottom_valid_under_sv57 : valid_sp_va .Sv57 sv48_window_bottom := by
  unfold valid_sp_va sv48_window_bottom
  decide

/-- AT AN ADDRESS: 2^40 is inside the Sv48 user space and past the whole
    of the Sv39 one.  Today's [State.access_okb] admits a range there --
    it compares against the Sv48 [TASK_SIZE] -- so an Sv39 run that
    reached it would be ANSWERED wrongly, which is why such a run is
    declined before it can ask.  This pair is the reason for the
    decline, stated as the two numbers.

    The comparison is the `Bool` `zltb`, i.e. `decide (· < ·)`, so the
    statement keeps its `= true` shape instead of restating the goal as
    a `Prop`. -/
theorem an_sv48_address_beyond_sv39 :
    access_okb (BitVec.ofInt 64 (2 ^ 40)) 8 = true
    ∧ (decide (va_task_size .Sv39 < 2 ^ 40) : Bool) = true := by
  constructor <;> decide

/-- AT THE STATEMENT: the fixture input under each declaration.  The
    three differ in the declaration alone. -/
def sized_input (v : VaSize) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) demo_hwcap false v

/-- Under Sv39 or Sv57 the sealed predicate is refused whatever the
    images and entries -- its first conjunct is false -- and under Sv48
    it is [strong_equiv] itself, so nothing here touches what every other
    example proves.  [Run.run] is deliberately NOT consulted on the
    refused side: it is the Sv48 run whatever the input declares, which
    is a known limitation of the model, and these pins are about the
    statements that stand in front of it. -/
theorem sv39_statement_refused (s t : Image) (en_s en_t : ExecEntry) :
    ¬ strong_equiv_va s t en_s en_t (sized_input .Sv39) := by
  intro h
  exact absurd h.1 (by decide)

theorem sv57_statement_refused (s t : Image) (en_s en_t : ExecEntry) :
    ¬ strong_equiv_va s t en_s en_t (sized_input .Sv57) := by
  intro h
  exact absurd h.1 (by decide)

/-- THE CONTROL for the two refusals above: with the same images, the
    same entries and the same input except for the declaration, the
    sealed predicate is not refused -- it IS the equivalence question,
    whatever its answer -- so what the refusals bite on is the
    declaration and nothing else about the triple.  Documentary in
    form: it is [Equivalence.strong_equiv_va_sv48] at the fixture input,
    and takes no entry or validity hypothesis because none is needed
    for the conclusion. -/
theorem sv48_statement_is_strong_equiv (s t : Image) (en_s en_t : ExecEntry) :
    strong_equiv_va s t en_s en_t (sized_input .Sv48)
    ↔ strong_equiv s t en_s en_t (sized_input .Sv48) :=
  strong_equiv_va_sv48 s t en_s en_t (sized_input .Sv48) rfl

/-! ## (iii) The unpinned predicate admits what each instance admits

    The three sized inputs are valid under [valid_input_va_any], each is
    valid under exactly its own pinned predicate, and the split lemma
    sends each to the right one.  The shared-clause proof is the one
    [Checks.Examples.demo_input_valid] uses, and it never mentions the
    declaration, which is the point: the size is the only clause the
    three predicates disagree on.

    The shared clauses are discharged clause by clause rather than by
    one structural hammer over the list.  The fixture here is a fixed
    record, so each clause is closed on its own: the two
    argument clauses, the credential, nofile, sigmask and capability
    clauses, and the abort-stance clause are closed comparisons once the
    record literal is unfolded, and the random-stream clause is
    [StateStreams.default_urandom_infinite].  The two FILE SYSTEM
    clauses are vacuous rather than numeric: [State.in_fs] is the image
    with the (empty) private `/tmp` seeded, and both are the empty list,
    so [Fs.valid_fs] and [Fs.fs_keys_relative] have nothing to range
    over.  (The SIZE clause is absent from [valid_input_va_any] by
    definition — that is what "unpinned" means.) -/
theorem sized_input_va_any (v : VaSize) : valid_input_va_any (sized_input v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [sized_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [sized_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [sized_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [sized_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [sized_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [sized_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [sized_input, mkProcInput]
    decide
  · unfold valid_hwcap
    simp [sized_input, mkProcInput, demo_hwcap]
  · simp [sized_input, mkProcInput]
  · unfold valid_urandom
    simp [sized_input, mkProcInput, default_urandom_infinite]

theorem sized_sv48_valid : valid_input (sized_input .Sv48) := by
  obtain ⟨a, b, c, k, d, e, f, g, h, u⟩ := sized_input_va_any .Sv48
  exact ⟨a, b, c, k, d, e, f, g, h, rfl, u⟩

theorem sized_sv39_valid : valid_input_sv39 (sized_input .Sv39) := by
  obtain ⟨a, b, c, k, d, e, f, g, h, u⟩ := sized_input_va_any .Sv39
  exact ⟨a, b, c, k, d, e, f, g, h, rfl, u⟩

theorem sized_sv57_valid : valid_input_sv57 (sized_input .Sv57) := by
  obtain ⟨a, b, c, k, d, e, f, g, h, u⟩ := sized_input_va_any .Sv57
  exact ⟨a, b, c, k, d, e, f, g, h, rfl, u⟩

theorem each_instance_refuses_the_others :
    ¬ valid_input (sized_input .Sv39) ∧ ¬ valid_input (sized_input .Sv57)
    ∧ ¬ valid_input_sv39 (sized_input .Sv48) ∧ ¬ valid_input_sv39 (sized_input .Sv57)
    ∧ ¬ valid_input_sv57 (sized_input .Sv48) ∧ ¬ valid_input_sv57 (sized_input .Sv39) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h
     simp only [valid_input, valid_input_sv39, valid_input_sv57, sized_input,
       mkProcInput] at h
     grind)

theorem va_any_splits_each_to_its_own :
    (valid_input (sized_input .Sv48) ∨ valid_input_sv39 (sized_input .Sv48)
     ∨ valid_input_sv57 (sized_input .Sv48))
    ∧ (valid_input (sized_input .Sv39) ∨ valid_input_sv39 (sized_input .Sv39)
        ∨ valid_input_sv57 (sized_input .Sv39))
    ∧ (valid_input (sized_input .Sv57) ∨ valid_input_sv39 (sized_input .Sv57)
        ∨ valid_input_sv57 (sized_input .Sv57)) := by
  refine ⟨?_, ?_, ?_⟩ <;> exact valid_input_va_any_splits _ (sized_input_va_any _)

/-! ## The sealed statements, fired

    On the empty image -- which [Equivalence.image_brk_satisfiable]
    accepts, so its entry predicates are inhabited under every
    declaration -- the Sv39 and Sv57 statements are refuted, and so is
    the one that pins nothing, because it is their conjunction.  These
    are the refutations [Equivalence.strong_universal_T_sv39_refuted]
    states conditionally, with the condition discharged: a task sealed
    against [SPEC_SV39] today is refused by a theorem, not by a remark. -/
def empty_image : Image := mkImage [] 0 demo_phdrs

theorem empty_image_brk_satisfiable :
    image_brk_satisfiable empty_image.img_segments = true := by
  decide

theorem sv39_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_sv39 empty_image empty_image := by
  obtain ⟨en, Hen⟩ := image_brk_satisfiable_entry_va empty_image (sized_input .Sv39)
    (sized_input_va_any .Sv39) empty_image_brk_satisfiable
  exact strong_universal_T_sv39_refuted empty_image empty_image en en
    (sized_input .Sv39) Hen Hen sized_sv39_valid

theorem sv57_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_sv57 empty_image empty_image := by
  obtain ⟨en, Hen⟩ := image_brk_satisfiable_entry_va empty_image (sized_input .Sv57)
    (sized_input_va_any .Sv57) empty_image_brk_satisfiable
  exact strong_universal_T_sv57_refuted empty_image empty_image en en
    (sized_input .Sv57) Hen Hen sized_sv57_valid

/-- The same image under the Sv48 input is a control: the refutation
    lemma cannot even be applied to it -- its declaration is not Sv39 --
    and the sealed predicate there is [strong_equiv], so whether the
    Sv48 statement holds of the empty image is the equivalence question
    and not the declaration. -/
theorem empty_image_sv48_is_the_equivalence_question (en_s en_t : ExecEntry) :
    strong_equiv_va empty_image empty_image en_s en_t (sized_input .Sv48)
    ↔ strong_equiv empty_image empty_image en_s en_t (sized_input .Sv48) :=
  strong_equiv_va_sv48 empty_image empty_image en_s en_t (sized_input .Sv48) rfl

theorem va_any_statement_refuted_on_the_empty_image :
    ¬ strong_universal_T_va_any empty_image empty_image := by
  intro H
  have H' := (strong_universal_T_va_any_splits empty_image empty_image).mp H
  exact sv39_statement_refuted_on_the_empty_image H'.2.1

end LinuxSem.Checks.Cases.VaSize
