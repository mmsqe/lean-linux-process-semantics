/-
  * LinuxProcessSem.Checks.Cases.Hwcap — the declared AT_HWCAP word, word by word

  Worked cases over the hardware-capability block of `Run`
  ([Run.valid_hwcap] and the declared predicates beside it), the way
  [Checks.Cases.VaSize] covers the address-space one.  The
  declaration is a value of the input, so what there is to pin is
  (i) that the DEFAULT is the two words and not one of them —
  [Run.valid_input_hwcap_splits] fired on the fixtures; (ii) that a
  wrong declaration is refused for the RIGHT reason, at the word and
  not at some other clause, and that both declarations refuse a word
  no kernel publishes; (iii) that the auxv entry the entry stack
  writes carries the DECLARED word under each declaration, so the
  declaration is about what the process can see; and (iv) the reason
  the declaration exists at all — that a V-extension PROBE leaves the
  modeled surface, so an advertised-V run of a binary carrying one is
  [MachineUnmodeled] even though the binary vectorises nothing.

  WHAT IS NOT HERE.  The sealed statement families
  ([Equivalence.SPEC_HWCAP_RV64GC] and the surfaces beside it) get no
  refutation, because unlike the per-size families there is nothing
  to refute: both words are words the spec arms carry, the statements
  stand behind the UNGATED [Equivalence.strong_equiv], and whether
  either holds of a given image pair is the equivalence question.  The
  split lemmas over the statements are proved where they are stated
  and need no fixture; (vi) below fires the ones for the three BUDGET
  cells, and pins the SHAPE of those lemmas
  where a later edit has to keep it -- which is all a firing without
  a fixture can do, and (vi) says so.

  `Checks.Examples` keeps what is not per-syscall and
  re-exports this module.

  Spelling.  `Z` is `Int`, `word` is `BitVec 64`, `Z_to_bv n z` is
  `BitVec.ofInt n z`, `bv_unsigned w` is `(w.toNat : Int)`,
  `decode_any` is `decodeAny`, `Sem.csr_slice` is `csr_slice`, and the
  `Csr CSR_RS` operand is written `Instr.csr CsrOp.RS`.  A record field
  is read by dot notation (`inp.in_hwcap`) — the same projection applied
  as a function.

  Proofs.  A closed equality whose two sides are the same term up to
  evaluation closes by `rfl`.  The refutations of a wrong declaration go
  through `Run`'s projection lemmas
  ([Run.valid_input_hwcap_rv64gc_word] and its siblings), which name the
  capability conjunct on its own, and the resulting word inequality
  closes by `decide` on `BitVec 64`.

  The `∀ segs st` family.  The examples that quantify
  over a segment list and a machine state
  ([the_vlenb_probe_leaves_the_modeled_surface],
  [the_guarded_vector_word_leaves_the_modeled_surface] and
  [a_scalar_word_beside_them_is_modeled], beside the two decodability
  pins that need no state at all) are NOT the expensive kind of
  `MachineUnmodeled` claim
  and should not be read as one.  [RiscvSemantics.decode_exec_accesses]
  at a closed word computes: [decodeAny] decides, and for the `vlenb`
  read [Sem.exec] reaches `csr_slice` — which resolves only the fcsr
  aliases — and answers `EIllegal core`.  `EIllegal` is a constructor
  that CARRIES the core and never inspects it, and
  [RiscvSemantics.interp_eff_accesses] maps it to `MachineUnmodeled`
  without touching `core` or `mem`, so `segs` and `st` stay inert and
  kernel reduction closes the goal (`rfl`; `nomatch` for the negative
  one).  A `forall segs st` over `sstep` would need a real derivation —
  this one is a closed computation BECAUSE the decline happens before
  any state is read.

  Assumption set.  Every
  theorem below is proved outright, so the kernel's assumption set is
  empty.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
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

namespace LinuxSem.Checks.Cases.Hwcap

/-! ## The fixture

    The fixture input of [Checks.Cases.VaSize] with the AT_HWCAP word
    varied instead of the size: the declaration is the only field that
    moves, so everything below that bites, bites on it. -/
def hwcap_input (h : word) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) h false .Sv48

/-- The word the fixtures of this TREE launch with -- [Cases.Prelude]'s
    [demo_hwcap], not the [hwcap_input] above, which takes its word as a
    parameter and never mentions it -- said once here so the examples
    below can be read without opening that file: it is the mask WITHOUT
    V.  Documentary — it holds by definition. -/
theorem the_trees_launch_word_is_the_v_less_mask : demo_hwcap = hwcap_rv64gc :=
  rfl

/-! ## (i) The default is the two, and each declaration holds of its own word

    Each pinned predicate is proved at its own word by the same
    shared-clause proof [Checks.Examples.demo_input_valid] uses, which
    never mentions the capability word; only the capability conjunct —
    the eighth — differs, and it closes by `rfl` rather than by picking
    a side of a disjunction, which is the whole difference between a
    declaration and the default.

    The shared clauses are discharged one at a time rather than by a
    per-fixture hammer.  The fixture is a fixed record, so the same
    conjuncts go through separately: the
    numeric clauses are closed comparisons once [mkProcInput] is
    unfolded, the file-system clauses are vacuous because the image and
    its private `/tmp` are both empty, and the random-stream clause is
    [StateStreams.default_urandom_infinite]. -/
theorem hwcap_input_gc_declared :
    valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [hwcap_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [hwcap_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [hwcap_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [hwcap_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_urandom
    simp [hwcap_input, mkProcInput, default_urandom_infinite]

theorem hwcap_input_gcv_declared :
    valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [hwcap_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [hwcap_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [hwcap_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [hwcap_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [hwcap_input, mkProcInput]
    decide
  · unfold valid_urandom
    simp [hwcap_input, mkProcInput, default_urandom_infinite]

/-- Both words are admitted by the DEFAULT, which is what makes a
    statement issued without a declaration a statement about both harts.
    Derived from the declared predicates rather than reproved, so the
    narrowing lemmas are exercised on a concrete input. -/
theorem both_words_are_valid_under_the_default :
    valid_input (hwcap_input hwcap_rv64gc)
    ∧ valid_input (hwcap_input hwcap_rv64gcv) :=
  ⟨valid_input_of_valid_input_hwcap_rv64gc _ hwcap_input_gc_declared,
   valid_input_of_valid_input_hwcap_rv64gcv _ hwcap_input_gcv_declared⟩

/-- …and the split lemma sends each fixture to its OWN declaration, which
    is the exhaustiveness claim fired rather than stated: the default
    admits no third word, so a task held to [Run.valid_input] is held to
    exactly these two readings.

    STATED AS THE CONJUNCTION, not as a disjunction per fixture.  A disjunction
    would say only that SOME declaration catches each fixture, and a
    split lemma that always answered the left arm would satisfy it; the
    conclusion here names which arm, and the proof still runs through
    [Run.valid_input_hwcap_splits] rather than around it -- the wrong arm
    is closed by the word, on the spot. -/
theorem the_default_splits_each_fixture_to_its_own :
    valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gc)
    ∧ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gcv) := by
  constructor
  · rcases valid_input_hwcap_splits _ (valid_input_of_valid_input_hwcap_rv64gc _
        hwcap_input_gc_declared) with H | H
    · exact H
    · exact absurd (valid_input_hwcap_rv64gcv_word _ H) (by decide)
  · rcases valid_input_hwcap_splits _ (valid_input_of_valid_input_hwcap_rv64gcv _
        hwcap_input_gcv_declared) with H | H
    · exact absurd (valid_input_hwcap_rv64gc_word _ H) (by decide)
    · exact H

/-! ## (ii) A wrong declaration is red, and for the word

    Each declaration refuses the OTHER word.  The refutation reads the
    capability conjunct and nothing else, and the control for it is
    [both_words_are_valid_under_the_default] above: the same fixture with
    the same every other field satisfies the default under both words, so
    what these refuse is the declaration. -/
theorem each_declaration_refuses_the_other_word :
    ¬ valid_input_hwcap_rv64gc (hwcap_input hwcap_rv64gcv)
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input hwcap_rv64gc) := by
  constructor
  · intro H
    exact absurd (valid_input_hwcap_rv64gc_word _ H) (by decide)
  · intro H
    exact absurd (valid_input_hwcap_rv64gcv_word _ H) (by decide)

/-- …and BOTH refuse the words outside the pair, which is what keeps a
    declaration a declaration rather than a free parameter: the zero an
    absent AT_HWCAP entry effectively delivers, the A-less mask
    [0x112C], and [0x40112D], which sets a letter [riscv_fill_hwcap]
    never assigns.  The same words [Cases.Prelude]'s
    [valid_hwcap_refuses_the_absent_entrys_zero] and
    [valid_hwcap_refuses_masks_no_kernel_publishes] pin against the
    default, so the declarations refuse exactly where the default does
    and not more. -/
theorem both_declarations_refuse_a_word_outside_the_pair :
    ¬ valid_input_hwcap_rv64gc (hwcap_input (BitVec.ofInt 64 0))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (BitVec.ofInt 64 0))
    ∧ ¬ valid_input_hwcap_rv64gc (hwcap_input (BitVec.ofInt 64 0x112C))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (BitVec.ofInt 64 0x112C))
    ∧ ¬ valid_input_hwcap_rv64gc (hwcap_input (BitVec.ofInt 64 0x40112D))
    ∧ ¬ valid_input_hwcap_rv64gcv (hwcap_input (BitVec.ofInt 64 0x40112D)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro H
     first
      | exact absurd (valid_input_hwcap_rv64gc_word _ H) (by decide)
      | exact absurd (valid_input_hwcap_rv64gcv_word _ H) (by decide))

/-- THE DEFAULT refuses them too, on the same fixture, which is the
    control that the refusals above are not an artifact of the
    declarations being narrow: no launch carries these words at all. -/
theorem the_default_refuses_a_word_outside_the_pair :
    ¬ valid_input (hwcap_input (BitVec.ofInt 64 0))
    ∧ ¬ valid_input (hwcap_input (BitVec.ofInt 64 0x112C))
    ∧ ¬ valid_input (hwcap_input (BitVec.ofInt 64 0x40112D)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (intro H
     rcases valid_input_hwcap_splits _ H with H1 | H1
     · exact absurd (valid_input_hwcap_rv64gc_word _ H1) (by decide)
     · exact absurd (valid_input_hwcap_rv64gcv_word _ H1) (by decide))

/-! ## (iii) The declared word is the word the process is handed

    A declaration that the auxv did not carry would be a claim about
    nothing.  [Cases.Prelude.auxv_hwcap_is_exactly_the_launch_word] says
    the AT_HWCAP entry carries the launch's word for every launch; under
    each declaration that word is the declared one, and this is that
    composition, stated once per declaration.  Quantified over every
    input the declaration accepts, so it is a claim about the
    declaration and not about the fixture.

    WHICH LEVEL THIS STOPS AT, so a reader does not over-read it: the
    claim is about [StackLayout.auxv_entries], the entry LIST, not about
    the bytes [StackLayout.build_stack_bytes] lays down.  The tie from
    the list to those bytes is [Cases.Prelude]'s
    [auxv_publishes_the_hart_capabilities], and it is made at the
    concrete [demo_hwcap] rather than for every word.  That is the
    strength [Cases.Prelude] already had; nothing here weakens it and
    nothing here extends it. -/
theorem the_rv64gc_declaration_publishes_the_v_less_word (inp : ProcInput)
    (ph : PhdrInfo) (at_random : word) (H : valid_input_hwcap_rv64gc inp) :
    (auxv_entries ph at_random inp.in_uid inp.in_hwcap).filter
        (fun e => bv_eqb e.1 AT_HWCAP)
      = [(AT_HWCAP, hwcap_rv64gc)] := by
  rw [auxv_hwcap_is_exactly_the_launch_word]
  rw [valid_input_hwcap_rv64gc_word inp H]

theorem the_rv64gcv_declaration_publishes_the_v_word (inp : ProcInput)
    (ph : PhdrInfo) (at_random : word) (H : valid_input_hwcap_rv64gcv inp) :
    (auxv_entries ph at_random inp.in_uid inp.in_hwcap).filter
        (fun e => bv_eqb e.1 AT_HWCAP)
      = [(AT_HWCAP, hwcap_rv64gcv)] := by
  rw [auxv_hwcap_is_exactly_the_launch_word]
  rw [valid_input_hwcap_rv64gcv_word inp H]

/-! ## (iv) THE REASON THE DECLARATION EXISTS: the probe is unmodeled

    A runtime that wants to know whether it has a vector unit reads
    [vlenb], a V-extension CSR, and that read is `csrr t0, vlenb` --
    CSRRS with rd = t0, rs1 = x0 and csr = 0xC22, the word [0xC22022F3].

    IT IS NOT THE DECODER THAT DECLINES IT.  The word is a structurally
    ordinary Zicsr access and [DecodeC.decode_any] decodes it, which is
    worth pinning because the obvious guess -- that a V-extension probe
    is undecodable the way a vector instruction is -- is wrong, and a
    reader who assumed it would look for the decline in the wrong place.
    The decline is one level further in: [Sem.csr_slice] resolves only
    the fcsr aliases, so [Sem.exec_csr] answers [Sem.EIllegal],
    which [RiscvSemantics.interp_eff_accesses] reports as
    [MachineUnmodeled] -- the ISA semantics declining to say, not the
    architecture trapping.  Each level is pinned below, and then the
    composition of them.

    That is why the DECLARATION is the task's rather than the model's.
    Under the permissive default a statement about a binary carrying
    this probe ranges over [hwcap_rv64gcv] as well, the probe is taken,
    and the statement is false as issued even though the binary never
    vectorises anything.  Under [Run.valid_input_hwcap_rv64gc] the
    advertised word has no V bit, the probe is never reached, and the
    statement is the one such a task can prove.  Nothing here claims the
    hart lacks a vector unit; it claims the KERNEL published a word
    without the bit, which is a fact about the launch. -/
theorem the_vlenb_probe_decodes_as_an_ordinary_csr_read :
    decodeAny (BitVec.ofInt 32 0xC22022F3)
      = some (Instr.csr CsrOp.RS (5 : BitVec 5) (0 : BitVec 5) (3106 : BitVec 12),
              (4 : Int)) :=
  rfl

theorem the_model_resolves_no_vlenb_csr : csr_slice (BitVec.ofInt 12 0xC22) = none := by
  decide

theorem the_vlenb_probe_leaves_the_modeled_surface (segs : List Segment)
    (st : machine_state) :
    decode_exec_accesses segs st (BitVec.ofInt 32 0xC22022F3) = .MachineUnmodeled :=
  rfl

/-- …and so does the vector work the probe would be guarding, by the
    OTHER route: a `vsetvli`, [0x0C0072D7], is a word the decoder does
    not decode at all.  Taken together the routes are what the declaration
    rests on -- that neither the probe nor the work it guards is modeled --
    rather than a claim about one encoding or one mechanism. -/
theorem a_vector_word_is_not_decoded_at_all :
    decodeAny (BitVec.ofInt 32 0x0C0072D7) = none :=
  rfl

theorem the_guarded_vector_word_leaves_the_modeled_surface (segs : List Segment)
    (st : machine_state) :
    decode_exec_accesses segs st (BitVec.ofInt 32 0x0C0072D7) = .MachineUnmodeled :=
  rfl

/-- THE CONTROL: the model is not answering [MachineUnmodeled] to
    everything.  A scalar word beside them -- `addi t0, zero, 0`,
    [0x00000293] -- is modeled, so what the declines above are about
    is the instruction and not the pin. -/
theorem a_scalar_word_beside_them_is_modeled (segs : List Segment)
    (st : machine_state) :
    decode_exec_accesses segs st (BitVec.ofInt 32 0x00000293) ≠ .MachineUnmodeled := by
  intro H
  nomatch H

/-! ## (v) The abort stance carries the same declaration

    [Run.valid_input_abort_hwcap_rv64gc] and its twin are the cell for
    a binary that probes for a vector unit AND wants the abort path
    modeled.  The fixture is the one above with the
    declaration flipped, so the only field that differs from the
    default-stance fixtures is [State.in_abort_terminal] and the pins
    below bite on the capability word exactly as the ones above do. -/
def hwcap_abort_input (h : word) : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
              default_nofile (BitVec.ofInt 64 0) h true .Sv48

theorem hwcap_abort_input_gc_declared :
    valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [hwcap_abort_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [hwcap_abort_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [hwcap_abort_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [hwcap_abort_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_urandom
    simp [hwcap_abort_input, mkProcInput, default_urandom_infinite]

theorem hwcap_abort_input_gcv_declared :
    valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · unfold valid_argv total_arg_bytes
    simp [hwcap_abort_input, mkProcInput]
  · unfold valid_envp total_arg_bytes
    simp [hwcap_abort_input, mkProcInput]
  · unfold Fs.valid_fs in_fs fs_seed_tmp
    simp [hwcap_abort_input, mkProcInput, Fs.fs_sorted]
  · unfold Fs.fs_keys_relative
    simp [hwcap_abort_input, mkProcInput]
  · unfold valid_creds valid_id
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_nofile
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_sigmask
    simp only [hwcap_abort_input, mkProcInput]
    decide
  · unfold valid_urandom
    simp [hwcap_abort_input, mkProcInput, default_urandom_infinite]

/-- The abort-stance split lemma, fired, and naming which arm catches
    each fixture for the reason the default-stance one does: the abort
    default admits the two words and no third, so a task that declares
    the stance and not the word is held to both readings of the hart. -/
theorem the_abort_default_splits_each_fixture_to_its_own :
    valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
    ∧ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gcv) := by
  constructor
  · rcases valid_input_abort_hwcap_splits _
        (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _
          hwcap_abort_input_gc_declared) with H | H
    · exact H
    · exact absurd (valid_input_abort_hwcap_rv64gcv_word _ H) (by decide)
  · rcases valid_input_abort_hwcap_splits _
        (valid_input_abort_of_valid_input_abort_hwcap_rv64gcv _
          hwcap_abort_input_gcv_declared) with H | H
    · exact absurd (valid_input_abort_hwcap_rv64gc_word _ H) (by decide)
    · exact H

theorem each_abort_declaration_refuses_the_other_word :
    ¬ valid_input_abort_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gcv)
    ∧ ¬ valid_input_abort_hwcap_rv64gcv (hwcap_abort_input hwcap_rv64gc) := by
  constructor
  · intro H
    exact absurd (valid_input_abort_hwcap_rv64gc_word _ H) (by decide)
  · intro H
    exact absurd (valid_input_abort_hwcap_rv64gcv_word _ H) (by decide)

/-- THE AXES ARE INDEPENDENT, and this is the pin that says so: the
    declaration of the word does not carry the declaration of the
    stance, in either direction.  Without it the declared predicates
    could have collapsed onto each other without any example noticing.

    The ninth conjunct is read out of the conjunction on its own; it IS
    `in_abort_terminal`, so the proof is that one conjunct with the
    record field written out. -/
theorem the_word_declaration_does_not_carry_the_stance :
    ¬ valid_input_hwcap_rv64gc (hwcap_abort_input hwcap_rv64gc)
    ∧ ¬ valid_input_abort_hwcap_rv64gc (hwcap_input hwcap_rv64gc) := by
  constructor
  · intro H
    exact absurd H.2.2.2.2.2.2.2.2.1 (by decide)
  · intro H
    exact absurd H.2.2.2.2.2.2.2.2.1 (by decide)

/-! ## (vi) The budget cells' split lemmas, their shape pinned

    The statement-level splits for the three budget cells
    -- the unconfigured budget shells under each stance, and the
    configured one with the stance off -- fired once each, plain and
    error-free.  Their splits are held to a shape here and not only
    where they are stated.

    WHAT THESE PIN, AND WHAT THEY DO NOT.  As a proposition each one is
    its split lemma with the `<->` unfolded and the backward half
    uncurried, so it establishes NO NEW FACT, and no instantiation of
    it could go red: it quantifies over all image pairs, including the
    pairs where every statement it names is false.  That makes these
    WEAKER than the fixture firings above, which run a concrete input
    through a split and can fail on the input.  What they pin is the
    SHAPE of the split lemma, at a site a later edit has to keep
    compiling:

    - both declared statements are named independently in the example's
      own type, so a split lemma whose two arms collapsed onto one
      statement stops typechecking here -- [proj1] would carry
      [A -> B /\ B] into a goal of [A -> B /\ C];
    - both directions of the `<->` are named, so dropping a half breaks
      it;
    - renaming or deleting a split lemma breaks it, which is the one of
      the three a bare [Check] would also catch.

    WHAT A BITING PIN WOULD BE, AND WHY IT IS NOT HERE.  An
    instantiation at an image pair for which the undeclared statement
    is PROVED, so the forward half hands back two declared statements
    about a real binary.  `Checks.Omni` proves the constant-pinned
    and configured statements for [Checks.Examples.exit0_image], and the
    budget-abstracted ones are reachable from those through
    [Equivalence.strong_universal_T_budgets_of_pinned] -- but that
    firing has to live downstream of `Checks.Omni`, and [Omni]
    imports [Checks.Examples], which re-exports this file.  This
    section cannot reach it. -/
theorem the_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_T_budgets ls lt s t
     → strong_universal_T_budgets_hwcap_rv64gc ls lt s t
        ∧ strong_universal_T_budgets_hwcap_rv64gcv ls lt s t)
    ∧ (strong_universal_T_budgets_hwcap_rv64gc ls lt s t
        → strong_universal_T_budgets_hwcap_rv64gcv ls lt s t
        → strong_universal_T_budgets ls lt s t) := by
  constructor
  · exact (strong_universal_T_budgets_hwcap_splits ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_T_budgets_hwcap_splits ls lt s t).mpr ⟨Hgc, Hgcv⟩

theorem the_error_free_budgets_cell_is_exactly_its_two_declarations
    (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_budgets ls lt s t
     → strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t
        ∧ strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t)
    ∧ (strong_universal_error_free_T_budgets_hwcap_rv64gc ls lt s t
        → strong_universal_error_free_T_budgets_hwcap_rv64gcv ls lt s t
        → strong_universal_error_free_T_budgets ls lt s t) := by
  constructor
  · exact (strong_universal_error_free_T_budgets_hwcap_splits ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_error_free_T_budgets_hwcap_splits ls lt s t).mpr
      ⟨Hgc, Hgcv⟩

theorem the_abort_budgets_cell_is_exactly_its_two_declarations (ls lt : Int) (s t : Image) :
    (strong_universal_T_budgets_abort ls lt s t
     → strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t
        ∧ strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t)
    ∧ (strong_universal_T_budgets_abort_hwcap_rv64gc ls lt s t
        → strong_universal_T_budgets_abort_hwcap_rv64gcv ls lt s t
        → strong_universal_T_budgets_abort ls lt s t) := by
  constructor
  · exact (strong_universal_T_budgets_abort_hwcap_splits ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_T_budgets_abort_hwcap_splits ls lt s t).mpr ⟨Hgc, Hgcv⟩

theorem the_error_free_abort_budgets_cell_is_exactly_its_two_declarations
    (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_budgets_abort ls lt s t
     → strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t
        ∧ strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t)
    ∧ (strong_universal_error_free_T_budgets_abort_hwcap_rv64gc ls lt s t
        → strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv ls lt s t
        → strong_universal_error_free_T_budgets_abort ls lt s t) := by
  constructor
  · exact (strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_error_free_T_budgets_abort_hwcap_splits ls lt s t).mpr
      ⟨Hgc, Hgcv⟩

theorem the_scfg_budgets_cell_is_exactly_its_two_declarations (cfg : SpuriousCfg)
    (ls lt : Int) (s t : Image) :
    (strong_universal_T_scfg_budgets cfg ls lt s t
     → strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        ∧ strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t)
    ∧ (strong_universal_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        → strong_universal_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t
        → strong_universal_T_scfg_budgets cfg ls lt s t) := by
  constructor
  · exact (strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_T_scfg_budgets_hwcap_splits cfg ls lt s t).mpr ⟨Hgc, Hgcv⟩

theorem the_error_free_scfg_budgets_cell_is_exactly_its_two_declarations
    (cfg : SpuriousCfg) (ls lt : Int) (s t : Image) :
    (strong_universal_error_free_T_scfg_budgets cfg ls lt s t
     → strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        ∧ strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t)
    ∧ (strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc cfg ls lt s t
        → strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv cfg ls lt s t
        → strong_universal_error_free_T_scfg_budgets cfg ls lt s t) := by
  constructor
  · exact (strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t).mp
  · intro Hgc Hgcv
    exact (strong_universal_error_free_T_scfg_budgets_hwcap_splits cfg ls lt s t).mpr
      ⟨Hgc, Hgcv⟩

end LinuxSem.Checks.Cases.Hwcap
