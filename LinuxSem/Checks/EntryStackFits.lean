/-
  * LinuxSem.Checks.EntryStackFits — what the entry-stack ceiling buys

  Not part of the trusted specification: QA on the definitions, in the
  style of [Checks/Examples] and [Checks/VmMapsDisjoint].

  [Run.valid_entry] has a conjunct, [Run.entry_stack_fits], saying
  the initial stack image ends at or below [State.sp_window_hi] — the
  top of the user address space the declared VA environment provides
  (riscv64's [STACK_TOP], derived on [State.sp_window_hi]).  A premise
  that excluded nothing would be no premise, and a premise that
  excluded a real kernel placement would be a soundness hole in
  [Equivalence.strong_universal_T] rather than a fix, so both
  directions are pinned here:

  - PART 1, the conjunct BITES: placements [Run.valid_sp] admits and
    no kernel can produce are refused — at the window's top
    endpoint, and in its interior for an argv near the [valid_argv]
    limit.
  - PART 2, the conjunct EXCLUDES NOTHING REAL: [near_top_sp], a
    stack pointer just below the top of the address space, is still
    admitted.  Its offset is stated once, at that definition, and so
    is what it does and does not claim: it is the MODEL's minimal
    image rounded up, not a placement a kernel produces, and the real
    placements it stands in for are argued there.  This is the
    direction an alternative — subtracting the worst-case
    image from [sp_window_hi] once and for all — would get
    wrong, and Part 2 says so with the arithmetic rather than in
    prose.
  - PART 3, the SPAN is not slack: [Run.entry_stack_span] is the bound
    [entry_stack_fits] is stated against, and an over-estimate there
    would silently reintroduce Part 2's exclusion.  It is attained
    exactly at the minimal input.
  - PART 4, what the conjunct does to the statements ABOVE it: an
    entry-inhabitation hypothesis may only be asked at the VALID
    inputs.  Over all inputs it is unsatisfiable — an argv nothing
    bounds outruns the whole sp window — so a lemma taking the
    unrestricted form would be dead rather than strong.  Part 4 is
    the negative that keeps
    [EquivalenceDefinition.Classifier.decides_accepts_iff] and its two
    siblings from taking that form.

  Shape: every lemma here is a [forall] over admissible entries and
  inputs, and the arguments turn on the sp window, which is a model
  constant no run reveals.

  Notation.  [Z] is [Int], [N] is [Nat], [word] and [byte] come from
  `Riscv.Prelude`, and `Z_to_bv 64 z` is `BitVec.ofInt 64 z`.  The two
  rewrites `Z_to_bv_unsigned` and `bv_wrap_small` are one lemma here,
  [bv_unsigned_Z_to_bv_u64] (its home is `StateVm`):
  `((BitVec.ofInt 64 z).toNat : Int) = z` under the side condition
  `0 ≤ z ∧ z < 2^64`.  `bv_unsigned w` is `(w.toNat : Int)`;
  `repeat x n` is `List.replicate n x`; `Nat.pow` is `^`.  Records are
  structures, so `mkEntry sp brk mb rnd` is the literal
  `⟨sp, brk, mb, rnd⟩`.  The two `reflexivity` goals that mix a
  concrete layout with a variable [PhdrInfo]/[word] do not close by
  conversion — `List.length` of `a ++ b` with a variable `b` is not
  definitionally `length a + length b` — so they are computed with
  `simp` over the length lemmas the layout file proves
  (`length_auxv_bytes`, `length_at_random_bytes`); the arithmetic ones
  stay `by decide`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.FinInput
import LinuxSem.EquivalenceDefinition.Classifier

namespace LinuxSem.Checks.EntryStackFits

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier

/- =========================================================================
   PART 1 — the conjunct bites
   ========================================================================= -/

/-- The span is positive whatever the input: the argc word, the two NULL
    terminators, the auxv and the AT_RANDOM block are there even for an
    empty argv and envp.  Everything in Part 1 rests on this, so it is
    stated once rather than re-derived. -/
theorem entry_stack_span_pos (argv envp : List (List byte)) :
    (191 : Int) ≤ entry_stack_span argv envp := by
  have hargv := total_arg_bytes_nonneg argv
  have henvp := total_arg_bytes_nonneg envp
  have hla : (0 : Int) ≤ (argv.length : Int) := Int.natCast_nonneg _
  have hle : (0 : Int) ≤ (envp.length : Int) := Int.natCast_nonneg _
  have haux : (auxv_size : Int) = 160 := by decide
  unfold entry_stack_span
  rw [haux]
  omega

/-- The top of the sp window is a 16-byte-aligned address inside it, so
    [valid_sp] admits it — the premise without the conjunct. -/
theorem valid_sp_admits_window_top : valid_sp (BitVec.ofInt 64 sp_window_hi) := by
  unfold valid_sp
  rw [bv_unsigned_Z_to_bv_u64 sp_window_hi ⟨by decide, by decide⟩]
  unfold sp_window_lo sp_window_hi
  decide

/-- ...and [entry_stack_fits] refuses it, for EVERY input.  An [sp] at
    [STACK_TOP] puts argc itself at the first address above the user
    address space; there is no argv or envp small enough to rescue it.
    This is the endpoint case, and the one that makes the pair above a
    proof that the conjunct removes something rather than a restatement
    of [valid_sp]. -/
theorem entry_stack_fits_refuses_window_top (argv envp : List (List byte)) :
    ¬ entry_stack_fits (BitVec.ofInt 64 sp_window_hi) argv envp := by
  intro H
  unfold entry_stack_fits at H
  have hpos := entry_stack_span_pos argv envp
  rw [bv_unsigned_Z_to_bv_u64 sp_window_hi ⟨by decide, by decide⟩] at H
  simp only [sp_window_hi] at H
  omega

/-- And the same refusal read through [Run.valid_entry] itself, which is
    the predicate [Equivalence.strong_universal_T] quantifies over.  The
    lemma above is about [entry_stack_fits] in isolation, so it survives
    the conjunct being dropped from [valid_entry] — this one does not,
    and it is what makes the file a test of the change rather than of a
    definition beside it. -/
theorem valid_entry_refuses_window_top (img : Image) (brk mb : word)
    (rnd : EntryDraw) (inp : ProcInput) :
    ¬ valid_entry img ⟨BitVec.ofInt 64 sp_window_hi, brk, mb, rnd⟩ inp := by
  obtain ⟨segs, pc, ph⟩ := img
  have hgen : ∀ v : VaSize,
      valid_entry_va v ⟨segs, pc, ph⟩
        ⟨BitVec.ofInt 64 sp_window_hi, brk, mb, rnd⟩ inp → False := by
    intro v H
    cases v with
    | Sv39 =>
      -- Sv39: the top of the Sv48 window is 254 GiB above the Sv39 one,
      -- so the window itself refuses it before the ceiling is asked
      simp only [valid_entry_va, valid_sp_va] at H
      obtain ⟨⟨-, Hhi, -⟩, -, -, -⟩ := H
      simp only [va_sp_window_hi, va_stack_top, sv39_task_size] at Hhi
      rw [bv_unsigned_Z_to_bv_u64 sp_window_hi ⟨by decide, by decide⟩] at Hhi
      simp only [sp_window_hi] at Hhi
      omega
    | Sv48 =>
      simp only [valid_entry_va] at H
      obtain ⟨-, -, -, Hfits⟩ := H
      exact entry_stack_fits_refuses_window_top _ _
        ((entry_stack_fits_va_sv48 _ _ _).mp Hfits)
    | Sv57 =>
      -- Sv57 shares the Sv48 ceiling
      simp only [valid_entry_va] at H
      obtain ⟨-, -, -, Hfits⟩ := H
      simp only [entry_stack_fits_va, va_sp_window_hi, va_stack_top] at Hfits
      exact entry_stack_fits_refuses_window_top _ _ Hfits
  intro H
  exact hgen inp.in_va_size H

/-- The conjunct bites in the INTERIOR of the window too, not only at its
    endpoint: a megabyte below the top is a placement a kernel really can
    choose, but not while carrying an argv near the [valid_argv] limit of
    2097152 bytes — those strings would run past the last user address.
    Stated over all such [sp] and argv rather than at a witness, because
    the claim is about the band and not about one address. -/
theorem entry_stack_fits_refuses_interior (sp : word) (argv envp : List (List byte))
    (Hsp : sp_window_hi - 1048576 ≤ (sp.toNat : Int))
    (Hargv : (1048576 : Int) ≤ total_arg_bytes argv) :
    ¬ entry_stack_fits sp argv envp := by
  intro H
  unfold entry_stack_fits entry_stack_span at H
  have henvp := total_arg_bytes_nonneg envp
  have hla : (0 : Int) ≤ (argv.length : Int) := Int.natCast_nonneg _
  have hle : (0 : Int) ≤ (envp.length : Int) := Int.natCast_nonneg _
  have haux : (auxv_size : Int) = 160 := by decide
  rw [haux] at H
  omega

/- =========================================================================
   PART 2 — the conjunct excludes nothing a kernel can produce
   ========================================================================= -/

/-- The minimal input Linux delivers: argc = 1 with an empty argv[0] (the
    kernel rewrites an empty [execve] argv to exactly this, commit
    dcd46d897adb — see [valid_argv]) and no environment.  Its stack image
    is 216 bytes. -/
def minimal_argv : List (List byte) := [[]]
def minimal_envp : List (List byte) := []

theorem minimal_span : entry_stack_span minimal_argv minimal_envp = 216 := by decide

/-- 224 bytes below the top of the address space: 16-byte aligned, inside
    the sp window, and enough room for that 216-byte image.  224 is the
    MODEL's minimal image rounded up, not a kernel measurement, and no
    kernel puts [sp] exactly here — Linux writes a larger block than this
    model does.  [create_elf_tables] emits 16 unconditional
    [NEW_AUX_ENT]s and expands riscv's [ARCH_DLINFO] on top of them,
    which adds [AT_SYSINFO_EHDR] and eight cache-descriptor entries,
    against [StackLayout]'s 10; it also pushes the [AT_EXECFN] pathname
    string.  So a real entry [sp] with randomization off lands some
    hundreds of bytes lower than this.  What this
    witness is for is the COMPARISON in
    [worst_case_ceiling_would_refuse_a_real_placement] below: with
    [PF_RANDOMIZE] clear, [randomize_stack_top] returns
    [PAGE_ALIGN(STACK_TOP)] unchanged (mm/util.c, Linux v6.18.46, commit
    1f99e9ab748f), and [setup_arg_pages] page-aligns back over
    [arch_align_stack]'s subtraction (fs/exec.c, same tree), so the entry
    [sp] a kernel really produces for a small argv and envp is within a
    few hundred bytes of [sp_window_hi] — far above
    [sp_window_hi - entry_stack_span_max], which is the line the absolute
    alternative would draw.  The witness is model-side; the placements it
    stands in for are not. -/
def near_top_sp : word := BitVec.ofInt 64 (sp_window_hi - 224)

theorem near_top_sp_unsigned : (near_top_sp.toNat : Int) = sp_window_hi - 224 := by
  unfold near_top_sp
  rw [bv_unsigned_Z_to_bv_u64 (sp_window_hi - 224) ⟨by decide, by decide⟩]

theorem valid_sp_near_top : valid_sp near_top_sp := by
  unfold valid_sp
  rw [near_top_sp_unsigned]
  unfold sp_window_lo sp_window_hi
  decide

theorem entry_stack_fits_admits_near_top :
    entry_stack_fits near_top_sp minimal_argv minimal_envp := by
  unfold entry_stack_fits
  rw [near_top_sp_unsigned, minimal_span]
  omega

/-- What Part 2 is really about.  The alternative to a per-run premise is
    an absolute one: keep [valid_entry] blind to the input and subtract
    the worst-case image ([entry_stack_span_max], the
    [valid_argv]/[valid_envp] limits) from [sp_window_hi] instead.  That
    is a smaller change and needs no new argument — and it refuses
    [near_top_sp], and with it the whole 2238671-byte band beneath
    [sp_window_hi] that a kernel with randomization off and a small argv
    and envp places [sp] inside.  Refusing
    it would not cost provability, it would cost COVERAGE: the excluded
    runs are real, and [strong_universal_T] would stop saying anything
    about them.  That asymmetry is why the premise is stated per run. -/
theorem worst_case_ceiling_would_refuse_a_real_placement :
    ((near_top_sp.toNat : Int) > sp_window_hi - entry_stack_span_max)
    ∧ ((near_top_sp.toNat : Int) + entry_stack_span minimal_argv minimal_envp
        ≤ sp_window_hi) := by
  rw [near_top_sp_unsigned, minimal_span]
  unfold entry_stack_span_max sp_window_hi
  omega

/- =========================================================================
   PART 3 — the span is the image's size, not a comfortable over-estimate
   ========================================================================= -/

/-- [entry_stack_fits] is stated against [entry_stack_span] rather than
    against [build_stack_bytes] itself, so that [Run] can reason about it
    without [StackLayout]'s layout arithmetic.  That is only safe while
    the span stays an upper bound ([PropExec.build_stack_bytes_within_span])
    that is not slack: every byte of slack is a byte of the address space
    the premise refuses to let a real image use, i.e. Part 2's exclusion
    creeping back in a smaller size.

    At the minimal input the bound is ATTAINED — the span is the image's
    length exactly, for every program-header record, stack pointer and
    uid, none of which change the auxv's size.  So the near-top placement
    Part 2 admits is admitted because the image really fits, not because
    the bound happens to be generous there. -/
theorem entry_stack_span_attained_at_the_minimum (ph : PhdrInfo) (sp : word)
    (uid hw : word) (rnd : EntryDraw) :
    ((build_stack_bytes ph sp minimal_argv minimal_envp uid hw rnd).length : Int)
      = entry_stack_span minimal_argv minimal_envp := by
  have hlen : (build_stack_bytes ph sp minimal_argv minimal_envp uid hw rnd).length
      = 216 := by
    simp only [build_stack_bytes, minimal_argv, minimal_envp, len_word,
      string_addrs, flatten_strings, length_auxv_bytes, auxv_size,
      length_at_random_bytes, word_le8, List.length_append,
      List.length_cons, List.length_nil, List.length_replicate,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]
  rw [hlen]
  decide

/- =========================================================================
   PART 4 — the conjunct bounds where an inhabitation hypothesis may be asked
   ========================================================================= -/

/-! [Run.valid_entry] takes the input because [entry_stack_fits] reads
    argv and envp, and that has a consequence for every statement built
    on top of it: "this image has a valid entry" is a claim about an
    IMAGE AND AN INPUT TOGETHER, never about an image alone.  A
    hypothesis quantifying it over all inputs is therefore not a strong
    assumption but an unsatisfiable one, and a lemma carrying it proves
    nothing about anything.

    That is the shape
    [forall g, exists en, valid_entry C en
    (to_proc_input g)], over every [FinInput.FinProcInput] whether valid
    or not.  This part is the negative test for that mistake — it
    exhibits the input no image can serve — together with the positive
    pin that the per-valid-input form that
    [EquivalenceDefinition.Classifier.decides_accepts_iff],
    [decides_rejects_iff] and [decides_accepts_or_rejects] take is the one
    [Equivalence.image_brk_satisfiable_entry] actually produces.

    Shape, as the file header says: a [forall] over images and
    entries, and an argument that turns on [State.sp_window_lo] and
    [State.sp_window_hi], model constants no run reveals. -/

/-- The witness: an argv of 268435457 empty strings.  Its argv POINTER
    ARRAY alone is 8 * 268435457 = 2147483656 bytes, eight more than the
    2147483648-byte sp window ([State.sp_window_hi] - [State.sp_window_lo]),
    so no stack pointer [valid_sp] admits leaves room for it — the
    strings themselves, and the rest of the block, are not even needed
    for the contradiction.  Empty strings rather than long ones keeps
    the arithmetic in the pointer array, where it can be read off the
    length; [Nat.pow] rather than a numeral keeps the [nat] out of
    unary. -/
def oversized_argv : List (List byte) :=
  List.replicate (2 ^ 28 + 1) []

theorem oversized_argv_length : (oversized_argv.length : Int) = 268435457 := by
  unfold oversized_argv
  rw [List.length_replicate]
  decide

/-- [hwcap_rv64gc] rather than a zero word, and the choice is not
    cosmetic: this witness exists to be REFUSED, and it has to be refused
    for its argv.  A zero hwcap is not a word [Run.valid_hwcap] admits, so
    an input carrying one would be rejected whatever its argv did, and the
    lemma below would hold for a reason it does not state. -/
def oversized_input : FinProcInput :=
  { fin_argv := oversized_argv
    fin_envp := []
    fin_image_fs := []
    fin_stdin := []
    fin_uid := BitVec.ofInt 64 0
    fin_gid := BitVec.ofInt 64 0
    fin_groups := []
    fin_net := net_silent
    fin_nofile := BitVec.ofInt 64 0
    fin_sigmask := BitVec.ofInt 64 0
    fin_hwcap := hwcap_rv64gc
    fin_abort_terminal := false
    fin_va_size := .Sv48
    fin_urandom := []
    fin_tmp := [] }

/-- The band the POINTER ARRAY alone excludes, stated over every [sp],
    argv and envp rather than at the witness: 268435457 argv entries need
    2147483656 bytes of [char *] before a single string is written, eight
    more than the sp window is wide, so no [Run.valid_sp] stack pointer
    can carry them.  Abstract arguments also keep [lia] away from the
    witness list below, which is a closed term nothing should reduce. -/
theorem entry_stack_fits_refuses_oversized_argc (sp : word)
    (argv envp : List (List byte))
    (Hlo : sp_window_lo ≤ (sp.toNat : Int))
    (Hargc : (268435457 : Int) ≤ (argv.length : Int)) :
    ¬ entry_stack_fits sp argv envp := by
  intro H
  unfold entry_stack_fits entry_stack_span at H
  have hargv := total_arg_bytes_nonneg argv
  have henvp := total_arg_bytes_nonneg envp
  have hle : (0 : Int) ≤ (envp.length : Int) := Int.natCast_nonneg _
  have haux : (auxv_size : Int) = 160 := by decide
  rw [haux] at H
  simp only [sp_window_hi] at H
  simp only [sp_window_lo] at Hlo
  omega

/-- THE NEGATIVE TEST.  No image whatever has a valid entry at every
    finite input, so the unrestricted inhabitation hypothesis is false
    for every [C] and a lemma taking it can be applied to nothing.
    Stated over [C] rather than at a witness image: the failure is in the
    input, and no image can repair it. -/
theorem no_image_has_an_entry_for_every_input (C : Image) :
    ¬ (∀ g : FinProcInput, ∃ en, valid_entry C en (to_proc_input g)) := by
  intro H
  obtain ⟨segs, pc, ph⟩ := C
  obtain ⟨⟨sp, brk, mb, rnd⟩, Hen⟩ := H oversized_input
  unfold valid_entry at Hen
  -- The declared size is read off the witness; on this one it is `Sv48`.
  change valid_entry_va .Sv48 ⟨segs, pc, ph⟩ ⟨sp, brk, mb, rnd⟩
    (to_proc_input oversized_input) at Hen
  obtain ⟨⟨Hlo, -⟩, -, -, Hfits⟩ := Hen
  simp only [va_sp_window_lo, va_stack_top] at Hlo
  have Hlo' : sp_window_lo ≤ (sp.toNat : Int) := by
    simp only [sp_window_hi] at Hlo
    simp only [sp_window_lo]
    omega
  have Hargc : (268435457 : Int)
      ≤ ((to_proc_input oversized_input).in_argv.length : Int) := by
    show (268435457 : Int) ≤ (oversized_argv.length : Int)
    rw [oversized_argv_length]
    omega
  exact entry_stack_fits_refuses_oversized_argc sp _ _ Hlo' Hargc
    ((entry_stack_fits_va_sv48 sp _ _).mp Hfits)

/-- ...and the input that kills it is one the per-valid-input form never
    asks about, which is what makes the restriction a fix rather than a
    dodge: [Run.valid_argv] caps argc at 1024. -/
theorem oversized_input_is_not_valid : ¬ valid_fin_input oversized_input := by
  intro H
  unfold valid_fin_input valid_input at H
  obtain ⟨⟨⟨-, Hlen⟩, -⟩, -⟩ := H
  -- `rfl` here is a weak-head unfolding of the record projection
  -- through `to_proc_input`; it never looks inside `oversized_argv`.  A
  -- `simp` here would leave the kernel a conversion it settles at the end
  -- by computing the witness list's `length` in unary.
  have Hargv : (to_proc_input oversized_input).in_argv = oversized_argv := rfl
  rw [Hargv, oversized_argv_length] at Hlen
  omega

/-- THE POSITIVE PIN, in two steps.  First: the well-formedness
    assertion a checker makes about the classifier image really does
    yield the per-valid-input hypothesis — [image_brk_satisfiable_entry]
    needs [Run.valid_input] for the input, and [FinInput.valid_fin_input]
    is exactly that of [FinInput.to_proc_input], so nothing is bridged
    here. -/
theorem image_brk_satisfiable_gives_the_per_valid_input_hypothesis
    (C : Image)
    (H : image_brk_satisfiable C.img_segments = true) :
    ∀ g : FinProcInput, valid_fin_input g →
      ∃ en, valid_entry C en (to_proc_input g) := by
  intro g Hg
  exact image_brk_satisfiable_entry C (to_proc_input g) Hg H

/-- Second: that is the hypothesis
    [EquivalenceDefinition.Classifier.decides_accepts_iff] consumes.  The
    lemma is stated so that it typechecks only while the classifier
    lemma takes the per-valid-input form — restore the unrestricted one
    and this file stops building, which is the point of pinning it here
    rather than describing it in a comment. -/
theorem decides_accepts_iff_takes_the_per_valid_input_hypothesis
    (C : Image) (spec : ProcInput → Prop)
    (Hdec : decides C spec)
    (Hwf : image_brk_satisfiable C.img_segments = true) :
    ∀ f : FinProcInput, valid_fin_input f →
      (accepts C f ↔ spec (to_proc_input f)) := by
  intro f Hf
  exact decides_accepts_iff C spec Hdec
    (image_brk_satisfiable_gives_the_per_valid_input_hypothesis C Hwf) f Hf

end LinuxSem.Checks.EntryStackFits
