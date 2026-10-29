/-
  * EquivalenceDefinition.HaltsAllowed — one binary halts with an allowed status

  TRUST BOUNDARY: this file is part of the trusted specification.
  Proof files never edit it.  A top-level check that ascribes against
  [SPEC_HALTS_ALLOWED] and its siblings depends on the definitions
  here remaining fixed, exactly as the baseline check depends on
  [Equivalence].

  ** What the statement says

  For ONE binary, every trace the spec admits for it — at every
  [execve] placement the model allows, on every input
  [Run.valid_input] allows, and under the refusal premise the statement is
  issued with — HALTS, through the [exit_group] path, with a status in
  a set the task declares.  It is [MustExit.must_exit_in] quantified
  over the entries and the inputs, and nothing else.

  ** What it excludes, and this is the whole content

  - NON-TERMINATION.  [MustExit.must_exit_in_at] is inductive.  A
    binary with an infinite execution cannot satisfy it, however many
    of its other executions exit.
  - A STUCK EXECUTION.  The progress premise.  A configuration with no
    successor at all would otherwise pass vacuously.
  - THE ERROR TRANSITION, and therefore anything unmodeled
    ([MustExit.must_exit_in_no_error], [MustExit.must_exit_in_modeled]).
    A binary that runs off the edge of the model does not halt with an
    allowed status; it fails to have a meaning here at all.
  - DEATH BY SIGNAL.  [MustExit.must_exit_in_at]'s halted case carries
    [State.m_killed = None], and
    [MustExit.must_exit_in_at_refuted_by_kill] is the refutation.

  THERE IS NO ABORT STANCE IN THIS FILE, and that is a decision rather
  than an omission.  [Equivalence]'s statement families come in two
  cells, one under [Run.valid_input] and one under
  [Run.valid_input_abort], because for a RELATIONAL claim a declared
  abort is a behaviour two binaries may legitimately share.  Here it
  cannot be: a declared abort is a death by signal, which is the exact
  outcome this statement exists to forbid, so an abort-declared cell
  would be a statement no aborting binary could satisfy and every
  non-aborting one already does — the undeclared statement over again,
  with a premise that changes nothing.  A task that wants to allow an
  abort wants a different predicate, not a stance on this one.

  ** How it sits beside the statements that were already here

  [Equivalence.strong_universal_T] is RELATIONAL and COMPARATIVE: it
  says two binaries behave alike, and says nothing about what either
  one does.  A pair of binaries that both loop forever satisfies it.
  This statement is UNARY and ABSOLUTE: it is about one binary and it
  names an outcome.  Neither implies the other, and that is why this
  is a separate family rather than a corollary — carrying an absolute
  termination claim through an equivalence would need the claim on one
  side to start with.

  [Classifier.classifier_total_T] is the closest relative: the same
  [MustExit.must_exit_at] shape, on one binary, with the answer
  quantified as a disjunction over TWO codes
  ([Classifier.verdict_accept] and [Classifier.verdict_reject]) on
  FINITE inputs.  The difference is not only the arity of the code
  set.  A disjunction of two [must_exit_at]s asks each execution tree
  to be uniform — one code for the whole tree — and
  [MustExit.must_exit_in] does not: a binary that exits 0 on one
  resolution of the nondeterminism and 1 on another satisfies
  [halts_allowed_T [0; 1]] and satisfies [classifier_total_T] at
  neither verdict.  That is the right reading for a task that asks
  "does it terminate cleanly" and the wrong one for a task that asks
  "what is the answer", which is why both statements exist.

  ** The allowed set, and the shipped instance

  The set is a [list word] and membership is [In], so a concrete set is
  a closed term the example side can decide by computation
  ([status_allowed] is that decision, [status_allowed_In] its
  soundness).  [AnyExit] is the widest set the model can ever need:
  every status in [0 .. 255], as words.  It is the set a task picks
  when it cares only that the binary terminates cleanly and not what
  it says, and [any_exit_covers_masked_status] is why nothing wider is
  meaningful — the only writer of [State.m_halted] is
  [Sys.Kernel.Exit.exit_spec], which stores
  [bv_and code (Z_to_bv 64 255)], so every status the model can record
  is already a byte.

  The mask is the kernel's own, not this model's invention:
  [SYSCALL_DEFINE1(exit, int, error_code)] calls
  [do_exit((error_code&0xff)<<8)] and
  [SYSCALL_DEFINE1(exit_group, int, error_code)] calls
  [do_group_exit((error_code & 0xff) << 8)], so the seven high bytes
  of the argument are discarded before any status exists (kernel/exit.c).
  [MustExit]'s header carries the wait-side half and the argument that
  [Sys.Kernel.Exit.exit_spec] is the only arm that writes the field.

  -  `Module Type` has no Lean counterpart, so — exactly as
    `Equivalence.lean` does for `SPEC`, `SPURIOUS_CFG` and `BUDGETS` —
    each one becomes a `structure`: the functor ARGUMENTS become
    structure parameters and each `Parameter` becomes a field.  The
    ascription a generated Checker performs is then the ascription of
    that structure, so a proof made at another allowed set still fails
    to type-check.
  - `Module AnyExit <: ALLOWED_EXITS` becomes the definition
    `AnyExit : ALLOWED_EXITS`, and `AnyExit.codes` is DEFINITIONALLY
    `byte_codes` (structures are transparent), which is what
    `any_exit_covers` below trades on.
  - `Z` is `Int`, `word` is `BitVec 64`, `list` is `List`, `In x l` is
    `x ∈ l`, `existsb p l` is `l.any p`, `bv_and a b` is `a &&& b`,
    `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, and `bv_unsigned w` is
    `(w.toNat : Int)` (Run.lean's convention), so the bounds in
    `bv_and_255_range` are stated in `Int` over that cast.
  - `Z_to_bv_bv_unsigned` is `ofInt_toNat` below, the round trip
    `BitVec.ofInt 64 (w.toNat : Int) = w`.
-/
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit

open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.HaltsAllowed

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open behavior

/- =========================================================================
   The three readings of the statement
   ========================================================================= -/

/-- THE UNCONFIGURED READING.  Every execution the unfiltered step
    relation admits, at the shipped source budget.  This is what a task
    gets by saying nothing about spurious refusals, and it is the
    STRONGEST of the three: [Run.may_fail_cfg] admits every execution any
    configuration does. -/
def halts_allowed_T (S : List word) (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    must_exit_in S img source_alloc_limit en inp

/-- THE CONFIGURED READING, pinned to a spurious-failure configuration
    the way [Equivalence.strong_universal_T_scfg] is.  The reason a task
    wants it is the one [Classifier]'s forced-only section gives,
    restated for this statement: under a
    reading where an [open] may be refused without cause, a binary that
    reads a file does not terminate cleanly on the refused execution —
    it gets an answer it was not written for — so an absolute
    termination claim about it is false for a reason that has nothing to
    do with the binary.  Under [Run.forced_only_cfg] the avoidable
    refusals are gone and what remains is the claim worth making. -/
def halts_allowed_T_scfg (cfg : SpuriousCfg) (S : List word)
    (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    must_exit_in_scfg cfg S img source_alloc_limit en inp

/-- THE BUDGET READING.  [Equivalence.SpecScfgBudgets] abstracts the two
    budgets and takes [Equivalence.source_within_budget_scfg] as a
    premise; this mirrors it FOR ONE IMAGE, so there is one budget and
    one premise rather than a pair.

    The premise is the same one and it is there for the same reason: a
    run the allocator refuses for want of budget reaches no exit at all,
    and holding a binary to an absolute termination claim on such an
    input would be holding it to the model's memory ceiling rather
    than to anything it does.  [Equivalence.source_within_budget_scfg]
    is the CONFIGURED form of the premise, which is the weaker one — an
    input refused only along an execution the configuration removes is
    an input this statement still covers.

    There is no [Equivalence.BUDGETS.headroom] obligation to discharge
    here, because headroom is a relation between a source budget and a
    target budget and this statement has one image.  The sealing surface
    below still takes a whole [Equivalence.BUDGETS] and reads
    [lim_source] off it, so that a one-image statement and the two-image
    statement a task states beside it are pinned to the SAME constant
    rather than to two that happen to agree. -/
def halts_allowed_T_scfg_budgets (cfg : SpuriousCfg) (lim : Int)
    (S : List word) (img : Image) : Prop :=
  ∀ en inp,
    valid_entry img en inp →
    valid_input inp →
    source_within_budget_scfg cfg lim img en inp →
    must_exit_in_scfg cfg S img lim en inp

/- =========================================================================
   How the three readings relate
   ========================================================================= -/

/-- At [Run.may_fail_cfg] the configured reading is the unconfigured
    one, exactly as [Equivalence.strong_universal_T_scfg] is
    [Equivalence.strong_universal_T] there.  The default a task gets by
    saying nothing about a configuration is therefore not a silent
    weakening. -/
theorem halts_allowed_T_scfg_may_fail (S : List word) (img : Image) :
    halts_allowed_T_scfg may_fail_cfg S img ↔ halts_allowed_T S img := by
  constructor
  · intro H en inp Hen Hinp
    exact (must_exit_in_scfg_may_fail S img source_alloc_limit en inp).mp
      (H en inp Hen Hinp)
  · intro H en inp Hen Hinp
    exact (must_exit_in_scfg_may_fail S img source_alloc_limit en inp).mpr
      (H en inp Hen Hinp)

/-- The configured reading is MONOTONE downward in the configuration,
    wherever the filter's question is answered: a claim under a bigger
    configuration is a claim under a smaller one.  The premise is
    [MustExit.run_decided], the known gap of [Run.lean]'s spurious-failure
    section, at the run. -/
theorem halts_allowed_T_scfg_mono (cfg1 cfg2 : SpuriousCfg) (S : List word)
    (img : Image) (Hle : cfg_le cfg1 cfg2)
    (Hdec : ∀ en inp, valid_entry img en inp → valid_input inp →
      run_decided cfg1 img source_alloc_limit en inp)
    (H : halts_allowed_T_scfg cfg2 S img) :
    halts_allowed_T_scfg cfg1 S img := by
  intro en inp Hen Hinp
  exact must_exit_in_scfg_mono cfg1 cfg2 S img source_alloc_limit en inp Hle
    (Hdec en inp Hen Hinp) (H en inp Hen Hinp)

/-- The constant-pinned configured statement implies the budget one at
    the same constant, with the premise DROPPED — never the converse.
    This is [Equivalence.strong_universal_T_scfg_budgets_of_scfg]'s
    direction and it holds for the same reason: a statement that needs
    no premise implies the one that takes it. -/
theorem halts_allowed_T_scfg_budgets_of_scfg (cfg : SpuriousCfg)
    (S : List word) (img : Image) (H : halts_allowed_T_scfg cfg S img) :
    halts_allowed_T_scfg_budgets cfg source_alloc_limit S img := by
  intro en inp Hen Hinp _
  exact H en inp Hen Hinp

/-- Widening the allowed set weakens every reading.  Only this
    direction: a task that wants the narrower set has to prove it. -/
theorem halts_allowed_T_mono (S1 S2 : List word) (img : Image)
    (Hsub : ∀ code, code ∈ S1 → code ∈ S2) (H : halts_allowed_T S1 img) :
    halts_allowed_T S2 img := by
  intro en inp Hen Hinp
  exact must_exit_in_mono S1 S2 img source_alloc_limit en inp Hsub
    (H en inp Hen Hinp)

theorem halts_allowed_T_scfg_mono_set (cfg : SpuriousCfg) (S1 S2 : List word)
    (img : Image) (Hsub : ∀ code, code ∈ S1 → code ∈ S2)
    (H : halts_allowed_T_scfg cfg S1 img) :
    halts_allowed_T_scfg cfg S2 img := by
  intro en inp Hen Hinp
  exact must_exit_in_scfg_mono_set cfg S1 S2 img source_alloc_limit en inp Hsub
    (H en inp Hen Hinp)

/-- The single-code statement is the singleton set: a binary proved to
    exit with one status halts allowably for every set containing it. -/
theorem halts_allowed_T_of_must_exit_with (S : List word) (code : word)
    (img : Image)
    (H : ∀ en inp, valid_entry img en inp → valid_input inp →
      must_exit_with code img source_alloc_limit en inp)
    (Hin : code ∈ S) : halts_allowed_T S img := by
  intro en inp Hen Hinp
  exact must_exit_with_in S code img source_alloc_limit en inp
    (H en inp Hen Hinp) Hin

/- =========================================================================
   What the statement buys, and how it is refuted
   ========================================================================= -/

theorem halts_allowed_T_no_error (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (H : halts_allowed_T S img)
    (Hen : valid_entry img en inp) (Hinp : valid_input inp) :
    ¬ bh_errors (run img source_alloc_limit en inp) :=
  must_exit_in_no_error S img source_alloc_limit en inp (H en inp Hen Hinp)

theorem halts_allowed_T_modeled (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (H : halts_allowed_T S img)
    (Hen : valid_entry img en inp) (Hinp : valid_input inp) :
    ¬ bh_unmodeled (run img source_alloc_limit en inp) :=
  must_exit_in_modeled S img source_alloc_limit en inp (H en inp Hen Hinp)

/-- THE GUARD.  A statement nobody can trip is a statement that says
    nothing, so this is the analogue of
    [MustExit.must_exit_with_realizes]: whatever satisfies
    [halts_allowed_T] really emits an [State.ExitEv], and the status it
    carries is really in [S].  Both halves matter — without the [In]
    conjunct the guard would be tripped by a run that exits with
    anything at all. -/
theorem halts_allowed_T_realizes (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (H : halts_allowed_T S img)
    (Hen : valid_entry img en inp) (Hinp : valid_input inp) :
    ∃ tr code fs,
      code ∈ S
      ∧ bh_traces (run img source_alloc_limit en inp)
          (tr ++ [event.ExitEv code fs]) :=
  must_exit_in_realizes S img source_alloc_limit en inp (H en inp Hen Hinp)

/-- NEGATIVE, the error route. -/
theorem halts_allowed_T_refuted_by_error (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (Hen : valid_entry img en inp)
    (Hinp : valid_input inp)
    (Herr : bh_errors (run img source_alloc_limit en inp)) :
    ¬ halts_allowed_T S img := by
  intro H
  exact must_exit_in_refuted_by_error S img source_alloc_limit en inp Herr
    (H en inp Hen Hinp)

/-- NEGATIVE, the SIGNAL route, and it is the refutation that separates
    this statement from error-freedom: a run that aborts errors nowhere
    — the model follows it to the end — so
    [Equivalence.error_free] is satisfied by it and this is not. -/
theorem halts_allowed_T_refuted_by_kill (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (Hen : valid_entry img en inp)
    (Hinp : valid_input inp)
    (Hk : run_reaches_killed img source_alloc_limit en inp) :
    ¬ halts_allowed_T S img := by
  intro H
  exact must_exit_in_refuted_by_kill S img source_alloc_limit en inp Hk
    (H en inp Hen Hinp)

/-- NEGATIVE, the wrong-status route: a valid triple whose run REACHES a
    configuration halted with a status the set does not contain.  The
    budget is [State.source_alloc_limit] rather than a variable, because
    that is the one [halts_allowed_T] fixes and a variable would only
    have to be equated with it at every use.

  the Lean statement reads the same fields off the two records, which reduce
    identically (`MustExit.must_exit_in` is built the same way). -/
theorem halts_allowed_T_refuted_by_wrong_status (S : List word) (img : Image)
    (en : ExecEntry) (inp : ProcInput) (tr : List event) (c' : config)
    (code : word) (Hen : valid_entry img en inp) (Hinp : valid_input inp)
    (Hstar : star img.img_segments
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw source_alloc_limit inp)
      tr c')
    (Hh : m_halted c'.cfg_model = some code) (Hnin : code ∉ S) :
    ¬ halts_allowed_T S img := by
  intro H
  have Hme : must_exit_in S img source_alloc_limit en inp := H en inp Hen Hinp
  exact must_exit_in_at_wrong_code img.img_segments S code c' Hh Hnin
    (must_exit_in_at_star img.img_segments S
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw source_alloc_limit inp)
      tr c' Hme Hstar)

/- =========================================================================
   The allowed set as a module, and the shipped instance
   ========================================================================= -/

/-- Membership decided by computation, for the example side: a concrete
    set is a closed list and a concrete status a closed word, so
  [`decide`] answers.  [status_allowed_In] is the half a proof
    consumes; [In_status_allowed] is there so the two readings cannot
    drift. -/
def status_allowed (S : List word) (code : word) : Bool :=
  S.any (fun c => bv_eqb c code)

theorem status_allowed_In (S : List word) (code : word)
    (H : status_allowed S code = true) : code ∈ S := by
  unfold status_allowed at H
  obtain ⟨c, Hin, Heq⟩ := List.any_eq_true.mp H
  have hceq : c = code := by simpa [bv_eqb] using Heq
  rw [← hceq]
  exact Hin

theorem In_status_allowed (S : List word) (code : word) (H : code ∈ S) :
    status_allowed S code = true := by
  unfold status_allowed
  exact List.any_eq_true.mpr ⟨code, H, by simp [bv_eqb]⟩

/-- The allowed set a task is stated under, as a module so that it is a
    functor ARGUMENT of the sealing surface, the way
    [Equivalence.SPURIOUS_CFG] and [Equivalence.BUDGETS] are: the
    generated Checker instantiates it beside the image, and the
    ascription fails on a proof made at any other set. -/
structure ALLOWED_EXITS where
  codes : List word

/-- Every status in [0 .. 255], as words. -/
def byte_codes : List word :=
  (List.range 256).map (fun n => BitVec.ofInt 64 (Int.ofNat n))

theorem in_byte_codes (z : Int) (Hz : 0 ≤ z ∧ z < 256) :
    BitVec.ofInt 64 z ∈ byte_codes := by
  unfold byte_codes
  refine List.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
  · have hz : (z.toNat : Int) < 256 := by
      rw [Int.toNat_of_nonneg Hz.1]
      exact Hz.2
    rw [List.range_eq_range', List.mem_range']
    exact ⟨z.toNat, by omega, by simp⟩
  · congr 1
    exact Int.toNat_of_nonneg Hz.1

/-- The status [Sys.Kernel.Exit.exit_spec] stores is the low byte of the
    argument, and the low byte of anything is a byte. -/
theorem bv_and_255_range (a : word) :
    0 ≤ ((a &&& BitVec.ofInt 64 255).toNat : Int)
    ∧ ((a &&& BitVec.ofInt 64 255).toNat : Int) < 256 := by
  have h255 : (BitVec.ofInt 64 255 : word).toNat = 255 := by decide
  have hlt : (a &&& BitVec.ofInt 64 255).toNat < 256 := by
    rw [BitVec.toNat_and, h255]
    exact Nat.and_lt_two_pow a.toNat (y := 255) (n := 8) (by decide)
  exact ⟨Int.natCast_nonneg _, by omega⟩

/- `Z_to_bv_bv_unsigned`: `BitVec.ofInt 64` round-trips a `word`'s unsigned
   value — the canonical `BvBase.ofInt_toNat`, imported and
   opened here. -/

/-- THE COVERAGE CLAIM.  Every value [State.m_halted] can ever hold is in
    [byte_codes], so [AnyExit] below is not merely a wide set: it is the
    set no [exit_group] status can escape.  The argument that
    [Sys.Kernel.Exit.exit_spec] is the only writer of the field is
    [MustExit]'s header, which also names the dozen other call sites of
    [State.with_halted] and says why each of them preserves this. -/
theorem any_exit_covers_masked_status (a : word) :
    (a &&& BitVec.ofInt 64 255) ∈ byte_codes := by
  rw [← ofInt_toNat (a &&& BitVec.ofInt 64 255)]
  exact in_byte_codes _ (bv_and_255_range a)

def AnyExit : ALLOWED_EXITS where
  codes := byte_codes

theorem any_exit_covers (a : word) :
    (a &&& BitVec.ofInt 64 255) ∈ AnyExit.codes :=
  any_exit_covers_masked_status a

/- =========================================================================
   The sealed surfaces
   ========================================================================= -/

/-- The unconfigured surface.  ONE image, unlike [Equivalence.SPEC]'s
    two, and an allowed set beside it. -/
structure SPEC_HALTS_ALLOWED (Codes : ALLOWED_EXITS) (Target : MemImage) where
  halts_allowed : halts_allowed_T Codes.codes
    (mkImage Target.loaded_segments Target.init_pc Target.phdrs)

/-- The configured surface, with the configuration a functor argument
    the way [Equivalence.SPEC_SCFG] has it. -/
structure SPEC_HALTS_ALLOWED_SCFG (Cfg : SPURIOUS_CFG) (Codes : ALLOWED_EXITS)
    (Target : MemImage) where
  halts_allowed : halts_allowed_T_scfg Cfg.cfg Codes.codes
    (mkImage Target.loaded_segments Target.init_pc Target.phdrs)

/-- The configured, budget-abstracted surface.  It takes a whole
    [Equivalence.BUDGETS] and reads [lim_source] off it — see
    [halts_allowed_T_scfg_budgets]'s header for why the pair rather than
    a bare [Z]. -/
structure SPEC_HALTS_ALLOWED_SCFG_BUDGETS (Cfg : SPURIOUS_CFG) (B : BUDGETS)
    (Codes : ALLOWED_EXITS) (Target : MemImage) where
  halts_allowed : halts_allowed_T_scfg_budgets Cfg.cfg B.lim_source Codes.codes
    (mkImage Target.loaded_segments Target.init_pc Target.phdrs)

/-! ## Sanity checks on the computable parts

  these are port checks (per the porting conventions) pinning the two computations
  the prose above claims: `status_allowed` decides a concrete set, and `byte_codes`
  really is the 256 statuses `exit` can record, with the masked argument of any word
  landing in it. -/

example : status_allowed [BitVec.ofInt 64 0, BitVec.ofInt 64 1]
    (BitVec.ofInt 64 1) = true := by decide

example : status_allowed [BitVec.ofInt 64 0, BitVec.ofInt 64 1]
    (BitVec.ofInt 64 2) = false := by decide

example : byte_codes.length = 256 := by simp [byte_codes]

example : (BitVec.ofInt 64 300 &&& BitVec.ofInt 64 255) = BitVec.ofInt 64 44 := by
  decide

set_option maxRecDepth 10000 in
example : (BitVec.ofInt 64 300 &&& BitVec.ofInt 64 255) ∈ AnyExit.codes := by
  decide

end LinuxSem.EquivalenceDefinition.HaltsAllowed
