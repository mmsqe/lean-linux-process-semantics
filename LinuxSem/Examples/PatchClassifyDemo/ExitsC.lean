/-
  * Examples.PatchClassifyDemo.ExitsC — the six symbolic `exits_c`
    premises, PROVED

  DEMO FILE (not part of the trusted specification).  `Verdicts` proves
  the six verdicts by per-instruction symbolic execution; this file proves
  the same six through `exits_c`'s symbolic premise.  The six `exits_c`
  statements are:

  `O1_exits_c (sp : word) (mem rom : word → Option byte) :`
        exits_c O1m.loaded_segments verdict_reject 8
  (demo_init_state O1m.init_pc sp mem rom) = true... (O2, P1, P2, C1, C2)

  All six are proved below, with no new postulate and no change to the
  statements.  This file exists so the proof is in the tree even though
  `Verdicts` is wired for the OTHER route (the per-instruction symbolic
  execution of `O1_step_*` / `must_exit_at_instr`), which proves the same
  six verdicts without `exits_c` at all.

  ** Why the direct route does not work

  Four facts, established by experiment on this tree; each one is why the
  proof below has the shape it has.

  1. `rfl` does NOT reduce `exits_c ... = true` when `sp`, `mem` or `rom`
     is a VARIABLE — and it does reduce it when all three are closed
     (that is `*_exits_c_closed` in `Verdicts`, at `sp = 0`,
     `mem = rom = none`).  The blocker is not `decide`'s free-variable
     restriction as such: any free variable inside the `machine_state`
     stops the kernel's reduction of the whole chain, while every closed
     ingredient in it (the fetch, the decoder, the interpreter) reduces
  fine on its own.  So no VM-evaluation route handles the free
  variables, and the chain has to be ASSEMBLED, not evaluated.

  2. `RiscvSemantics.step` needs the SEGMENT LIST concrete — the fetch is
     a `find_segment` plus a hex decode — so no lemma below is stated at a
     variable `segs`.  What does factor out is the fetched WORD: once the
     word is known, the decoder and the interpreter decide everything, and
     the word is exactly what distinguishes the two programs from each
     other.  So the four `step_*` lemmas take the fetch as a HYPOTHESIS,
     which is a closed fact discharged by `rfl` at each use site, and they
     are shared by both segment lists — one copy per INSTRUCTION, not per
     image.

  3. `simp only` on the WHOLE `exits_c` goal does not reduce the fetch.
     The definition unfolds into a `match` on `RiscvSemantics.step` whose
     discriminant holds a partially applied `step_accesses`, and nothing
     reduces it in that position: not `simp`, not `dsimp only`, not
     `unfold`, and not `rw` (rewriting a `match` discriminant is a
     dependent rewrite, and the `Eq.rec` it leaves behind does not compute
     either).  `exits_c_succ_none` / `exits_c_succ_exit` are therefore the
     two ONE-LEVEL unfoldings of `exits_c` — pure `match` iota over a
     known step, no computation — and the chain is four `rw`s.

  4. The pc is kept SYMBOLIC: a successor's pc is written
     `st.ms_pc_val + BitVec.ofInt 64 4`, never as a numeral, so no `BitVec`
     numeral identity (`BitVec.eq_of_toNat_eq`) is needed anywhere.  The
     next fetch is stated at that same sum, and `rfl` discharges it: a
     fetch at a SUM of literals computes, even though the sum is not
     normalised to a numeral.  That is what removes the whole
     `BitVec.eq_of_toNat_eq` step from this proof.

  ** What is in the file

  In order: the two one-level unfoldings; the four `step_*` lemmas; the two
  `exits_c` computations (`exits_c_exit1_reject`, `exits_c_exit0_accept`);
  the six `X_exits_c` ascriptions transported from them; a "the check
  bites" fact showing the computation reaches `false` for the wrong code;
  the soundness engine `exits_c_must_exit_at`; the generic
  `must_exit_everywhere_of_exits_c`; and then the whole verdict list
  re-derived by this route — the six `must_exit_*` verdicts, the two
  wrong-code refutations, the two realization lemmas and the eight
  error-free/modeled facts — each a library lemma away from the verdict it
  comes from.  The `_via_exits_c` suffix keeps them clear of `Verdicts`'
  identically-stated theorems: they are the SAME propositions, proved
  twice, and the two proofs share no computation.

  The engine needs two facts about `Run.sstep` (`must_exit_at_instr` and
  `must_exit_at_exit_pending`), and both are `Verdicts`' — they invert the
  seven-arm step relation once, and this file consumes them rather than
  repeating the inversion.

  Cost: the whole file typechecks in a couple of seconds.  `simp only` on
  the unfolded `step` alone is ~1 s per instruction; that is the price of
  the four word-specific lemmas and it is paid once for both programs.

  `exits_c_must_exit_at` concludes `must_exit_at segs code ⟨ms, model⟩`
  rather than naming `mkCfg ms model`: `mkCfg` is `⟨·, ·⟩` in
  `Common.AsanAcct`, which is outside this file's dependency graph, and the
  two are definitionally equal, so the two spellings differ by one delta.

  Every `have` of the form `(x == 0) = false`, `by decide` on
  a closed `BitVec` identity, or `hval : 0 + signExtend 64 imm = ofInt 64
  imm` is a CONCRETE computation on literals, not a hypothesis about the
  machine: they are the reductions `simp only` needs supplied explicitly
  because `simp only` does not carry Lean's default `BitVec` simp set.
-/

import LinuxSem.Examples.PatchClassifyDemo.Verdicts

set_option autoImplicit false
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Verdicts

open Images

/- =========================================================================
   The two one-level unfoldings of `exits_c`

   Everything else in this file is about producing the `step` and the
   pending-syscall facts these two consume.
   ========================================================================= -/

/-- ** One level of `exits_c`, with no pending syscall: the step is a
    rewriting rule, so the `match` reduces without any fetch being
    computed.  This is the shape the whole chain is built from. -/
theorem exits_c_succ_none (segs : List Segment) (code : word) (fuel : Nat)
    (ms : machine_state) (ms' : machine_state)
    (hpend : ms.ms_svc_pending = none)
    (hstep : step segs ms = .MachineOk ms') :
    exits_c segs code (fuel + 1) ms = exits_c segs code fuel ms' := by
  simp only [exits_c, hpend, hstep]

/-- ... and the terminal one: a pending exit syscall carrying `code`. -/
theorem exits_c_succ_exit (segs : List Segment) (code : word) (fuel : Nat)
    (ms : machine_state) (x8 : word)
    (hpend : ms.ms_svc_pending = some x8)
    (hno : (x8.toNat : Int) = 93 ∨ (x8.toNat : Int) = 94)
    (hcode : ms_gpr ms 0 &&& BitVec.ofInt 64 255 = code) :
    exits_c segs code (fuel + 1) ms = true := by
  obtain h93 | h94 := hno
  · have hd : decide ((x8.toNat : Int) = 93) = true := by rw [h93]; rfl
    simp only [exits_c, hpend, hd, Bool.true_or, Bool.true_and, hcode, beq_self_eq_true]
  · have hd : decide ((x8.toNat : Int) = 93) = false := by
      rw [show (x8.toNat : Int) = 94 from h94]
      rfl
    have hd94 : decide ((x8.toNat : Int) = 94) = true := by rw [h94]; rfl
    simp only [exits_c, hpend, hd, hd94, Bool.false_or, Bool.true_and, hcode, beq_self_eq_true]




/-- `addi a7, x0, 93` at `addr`, over an arbitrary segment list and an
    arbitrary state: everything after the fetch is decided by the WORD, so
    the fetch is a hypothesis and the lemma is shared by both programs. -/
theorem step_addi_a7 (segs : List Segment) (st : machine_state) (addr : word)
    (hpc : st.ms_pc_val = addr)
    (hf : fetch_word segs addr = some (BitVec.ofInt 32 0x05d00893)) :
    step segs st
      = .MachineOk { st with
          ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st.ms_regs
          ms_pc_val := st.ms_pc_val + BitVec.ofInt 64 4
          ms_svc_pending := none } := by
  have hx17 : (BitVec.toNat (17 : reg) == 0) = false := by decide
  have hx00 : (BitVec.toNat (0 : reg) == 0) = true := by decide
  have hne : is_ecall (BitVec.ofInt 32 0x05d00893) = false := by decide
  have hdec : decodeAny (BitVec.ofInt 32 0x05d00893)
      = some (Instr.opImm .ADD (17 : reg) (0 : reg) (93 : BitVec 12), 4) := by decide
  have hval : (0 : word) + BitVec.signExtend 64 (93 : BitVec 12)
      = BitVec.ofInt 64 93 := by decide
  simp only [RiscvSemantics.step, step_accesses, drop_access_report, decode_exec_accesses,
    ms_pc, hpc, hf, hne, hdec, exec, rset, rget, is_x0, alu64, reg_get, mkAccessReport,
    interp_eff_accesses, with_pc, with_regs, bvmapSet, bvmap_set, bvmapGet, bvmap_get,
    reduceIte, Bool.false_eq_true, hx17, hx00, bv_key, alu, w0, sext, hval, ms_reg]

/-- ... the same for `addi a0, x0, 1`. -/
theorem step_addi_a0_1 (segs : List Segment) (st : machine_state) (addr : word)
    (hpc : st.ms_pc_val = addr)
    (hf : fetch_word segs addr = some (BitVec.ofInt 32 0x00100513)) :
    step segs st
      = .MachineOk { st with
          ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 1) st.ms_regs
          ms_pc_val := st.ms_pc_val + BitVec.ofInt 64 4
          ms_svc_pending := none } := by
  have hx10 : (BitVec.toNat (10 : reg) == 0) = false := by decide
  have hx00 : (BitVec.toNat (0 : reg) == 0) = true := by decide
  have hne : is_ecall (BitVec.ofInt 32 0x00100513) = false := by decide
  have hdec : decodeAny (BitVec.ofInt 32 0x00100513)
      = some (Instr.opImm .ADD (10 : reg) (0 : reg) (1 : BitVec 12), 4) := by decide
  have hval : (0 : word) + BitVec.signExtend 64 (1 : BitVec 12)
      = BitVec.ofInt 64 1 := by decide
  simp only [RiscvSemantics.step, step_accesses, drop_access_report, decode_exec_accesses,
    ms_pc, hpc, hf, hne, hdec, exec, rset, rget, is_x0, alu64, reg_get, mkAccessReport,
    interp_eff_accesses, with_pc, with_regs, bvmapSet, bvmap_set, bvmapGet, bvmap_get,
    reduceIte, Bool.false_eq_true, hx10, hx00, bv_key, alu, w0, sext, hval, ms_reg]

/-- ... and for `ecall`: the pending slot is filled with a7 and nothing else
    in the machine moves. -/
theorem step_ecall (segs : List Segment) (st : machine_state) (addr : word)
    (hpc : st.ms_pc_val = addr)
    (hf : fetch_word segs addr = some (BitVec.ofInt 32 0x00000073))
    (ha7 : ms_reg st 17 = BitVec.ofInt 64 93) :
    step segs st = .MachineOk { st with ms_svc_pending := some (BitVec.ofInt 64 93) } := by
  have hec : is_ecall (BitVec.ofInt 32 0x00000073) = true := by decide
  simp only [RiscvSemantics.step, step_accesses, drop_access_report, decode_exec_accesses,
    ms_pc, hpc, hf, hec, ha7, reduceIte, mkAccessReport, drop_access_report]

/-- ... and `addi a0, x0, 0`. -/
theorem step_addi_a0_0 (segs : List Segment) (st : machine_state) (addr : word)
    (hpc : st.ms_pc_val = addr)
    (hf : fetch_word segs addr = some (BitVec.ofInt 32 0x00000513)) :
    step segs st
      = .MachineOk { st with
          ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 0) st.ms_regs
          ms_pc_val := st.ms_pc_val + BitVec.ofInt 64 4
          ms_svc_pending := none } := by
  have hx10 : (BitVec.toNat (10 : reg) == 0) = false := by decide
  have hx00 : (BitVec.toNat (0 : reg) == 0) = true := by decide
  have hne : is_ecall (BitVec.ofInt 32 0x00000513) = false := by decide
  have hdec : decodeAny (BitVec.ofInt 32 0x00000513)
      = some (Instr.opImm .ADD (10 : reg) (0 : reg) (0 : BitVec 12), 4) := by decide
  have hval : (0 : word) + BitVec.signExtend 64 (0 : BitVec 12)
      = BitVec.ofInt 64 0 := by decide
  simp only [RiscvSemantics.step, step_accesses, drop_access_report, decode_exec_accesses,
    ms_pc, hpc, hf, hne, hdec, exec, rset, rget, is_x0, alu64, reg_get, mkAccessReport,
    interp_eff_accesses, with_pc, with_regs, bvmapSet, bvmap_set, bvmapGet, bvmap_get,
    reduceIte, Bool.false_eq_true, hx10, hx00, bv_key, alu, w0, sext, hval, ms_reg]

/-- The exit-1 program, end to end: three steps, then the pending exit. -/
theorem exits_c_exit1_reject (sp : word) (mem rom : word → Option byte) :
    exits_c exit1_image_segments verdict_reject 8 (demo_init_state demo_init_pc sp mem rom)
      = true := by
  let st0 : machine_state := demo_init_state demo_init_pc sp mem rom
  let st1 : machine_state := { st0 with
      ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st0.ms_regs
      ms_pc_val := st0.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st2 : machine_state := { st1 with
      ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 1) st1.ms_regs
      ms_pc_val := st1.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st3 : machine_state := { st2 with ms_svc_pending := some (BitVec.ofInt 64 93) }
  have hpc0 : st0.ms_pc_val = BitVec.ofInt 64 0x10000 := rfl
  have hf0 : fetch_word exit1_image_segments (BitVec.ofInt 64 0x10000)
      = some (BitVec.ofInt 32 0x05d00893) := rfl
  have h1 : step exit1_image_segments st0 = .MachineOk st1 :=
    step_addi_a7 exit1_image_segments st0 _ hpc0 hf0
  have hpc1 : st1.ms_pc_val = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 := rfl
  have hf1 : fetch_word exit1_image_segments (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00100513) := rfl
  have h2 : step exit1_image_segments st1 = .MachineOk st2 :=
    step_addi_a0_1 exit1_image_segments st1 _ hpc1 hf1
  have hpc2 : st2.ms_pc_val
      = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4 := rfl
  have hf2 : fetch_word exit1_image_segments
      (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000073) := rfl
  have ha7 : ms_reg st2 17 = BitVec.ofInt 64 93 := rfl
  have h3 : step exit1_image_segments st2 = .MachineOk st3 :=
    step_ecall exit1_image_segments st2 _ hpc2 hf2 ha7
  have hp0 : st0.ms_svc_pending = none := rfl
  have hp1 : st1.ms_svc_pending = none := rfl
  have hp2 : st2.ms_svc_pending = none := rfl
  have hp3 : st3.ms_svc_pending = some (BitVec.ofInt 64 93) := rfl
  have hg : ms_gpr st3 0 = BitVec.ofInt 64 1 := rfl
  have hcode : ms_gpr st3 0 &&& BitVec.ofInt 64 255 = verdict_reject := by
    rw [hg]; decide
  have e0 : exits_c exit1_image_segments verdict_reject 8 st0
      = exits_c exit1_image_segments verdict_reject 7 st1 :=
    exits_c_succ_none _ _ 7 st0 st1 hp0 h1
  have e1 : exits_c exit1_image_segments verdict_reject 7 st1
      = exits_c exit1_image_segments verdict_reject 6 st2 :=
    exits_c_succ_none _ _ 6 st1 st2 hp1 h2
  have e2 : exits_c exit1_image_segments verdict_reject 6 st2
      = exits_c exit1_image_segments verdict_reject 5 st3 :=
    exits_c_succ_none _ _ 5 st2 st3 hp2 h3
  have e3 : exits_c exit1_image_segments verdict_reject 5 st3 = true :=
    exits_c_succ_exit _ _ 4 st3 _ hp3 (Or.inl rfl) hcode
  rw [e0, e1, e2, e3]

/-- The exit-0 program, end to end: three steps, then the pending exit. -/
theorem exits_c_exit0_accept (sp : word) (mem rom : word → Option byte) :
    exits_c exit0_image_segments verdict_accept 8 (demo_init_state demo_init_pc sp mem rom)
      = true := by
  let st0 : machine_state := demo_init_state demo_init_pc sp mem rom
  let st1 : machine_state := { st0 with
      ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st0.ms_regs
      ms_pc_val := st0.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st2 : machine_state := { st1 with
      ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 0) st1.ms_regs
      ms_pc_val := st1.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st3 : machine_state := { st2 with ms_svc_pending := some (BitVec.ofInt 64 93) }
  have hpc0 : st0.ms_pc_val = BitVec.ofInt 64 0x10000 := rfl
  have hf0 : fetch_word exit0_image_segments (BitVec.ofInt 64 0x10000)
      = some (BitVec.ofInt 32 0x05d00893) := rfl
  have h1 : step exit0_image_segments st0 = .MachineOk st1 :=
    step_addi_a7 exit0_image_segments st0 _ hpc0 hf0
  have hpc1 : st1.ms_pc_val = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 := rfl
  have hf1 : fetch_word exit0_image_segments (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000513) := rfl
  have h2 : step exit0_image_segments st1 = .MachineOk st2 :=
    step_addi_a0_0 exit0_image_segments st1 _ hpc1 hf1
  have hpc2 : st2.ms_pc_val
      = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4 := rfl
  have hf2 : fetch_word exit0_image_segments
      (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000073) := rfl
  have ha7 : ms_reg st2 17 = BitVec.ofInt 64 93 := rfl
  have h3 : step exit0_image_segments st2 = .MachineOk st3 :=
    step_ecall exit0_image_segments st2 _ hpc2 hf2 ha7
  have hp0 : st0.ms_svc_pending = none := rfl
  have hp1 : st1.ms_svc_pending = none := rfl
  have hp2 : st2.ms_svc_pending = none := rfl
  have hp3 : st3.ms_svc_pending = some (BitVec.ofInt 64 93) := rfl
  have hg : ms_gpr st3 0 = BitVec.ofInt 64 0 := rfl
  have hcode : ms_gpr st3 0 &&& BitVec.ofInt 64 255 = verdict_accept := by
    rw [hg]; decide
  have e0 : exits_c exit0_image_segments verdict_accept 8 st0
      = exits_c exit0_image_segments verdict_accept 7 st1 :=
    exits_c_succ_none _ _ 7 st0 st1 hp0 h1
  have e1 : exits_c exit0_image_segments verdict_accept 7 st1
      = exits_c exit0_image_segments verdict_accept 6 st2 :=
    exits_c_succ_none _ _ 6 st1 st2 hp1 h2
  have e2 : exits_c exit0_image_segments verdict_accept 6 st2
      = exits_c exit0_image_segments verdict_accept 5 st3 :=
    exits_c_succ_none _ _ 5 st2 st3 hp2 h3
  have e3 : exits_c exit0_image_segments verdict_accept 5 st3 = true :=
    exits_c_succ_exit _ _ 4 st3 _ hp3 (Or.inl rfl) hcode
  rw [e0, e1, e2, e3]

/-! The six ascriptions, transported from the two computations

  Stated of the image they are about; the proof is
  `exits_c_exit1_reject` or `exits_c_exit0_accept` transported across
    `Xm.loaded_segments` and `Xm.init_pc`.  Six statements, TWO
    computations: the demo's six images are two segment lists, and the exit
    codes pair one-to-one with them.  Exactly the discipline `Images`
    follows for the six `IMAGE_WF` checks, and for the same reason: the
  six statements are what the verdicts need, only the computation is
  shared.

  Each of these is the `exits_c` form of one of the six verdicts
  `Verdicts` proves by the per-instruction route. -/

/-- `O1`'s: the exit-1 program at `verdict_reject`. -/
theorem O1_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c O1m.loaded_segments verdict_reject 8
      (demo_init_state O1m.init_pc sp mem rom) = true :=
  exits_c_exit1_reject sp mem rom

/-- `O2`'s: the exit-0 program at `verdict_accept`. -/
theorem O2_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c O2m.loaded_segments verdict_accept 8
      (demo_init_state O2m.init_pc sp mem rom) = true :=
  exits_c_exit0_accept sp mem rom

/-- `P1`'s: the exit-0 program at `verdict_accept`. -/
theorem P1_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c P1m.loaded_segments verdict_accept 8
      (demo_init_state P1m.init_pc sp mem rom) = true :=
  exits_c_exit0_accept sp mem rom

/-- `P2`'s: the exit-0 program at `verdict_accept`. -/
theorem P2_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c P2m.loaded_segments verdict_accept 8
      (demo_init_state P2m.init_pc sp mem rom) = true :=
  exits_c_exit0_accept sp mem rom

/-- `C1`'s: the exit-1 computation.  One of the two classifier images the
    `PatchClassifySpec` header warns is easiest to forget and worst to
    omit. -/
theorem C1_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c C1m.loaded_segments verdict_reject 8
      (demo_init_state C1m.init_pc sp mem rom) = true :=
  exits_c_exit1_reject sp mem rom

/-- `C2`'s: the exit-1 computation. -/
theorem C2_exits_c (sp : word) (mem rom : word → Option byte) :
    exits_c C2m.loaded_segments verdict_reject 8
      (demo_init_state C2m.init_pc sp mem rom) = true :=
  exits_c_exit1_reject sp mem rom

/-! ## The checks bite, at the symbolic form too

    A `∀ sp mem rom, ... = true` is worth nothing if the same computation
    would say `true` of a wrong program, so the two programs are told
    apart at this level as well: the exit-0 program does NOT satisfy the
    exit-1 premise.  This is the symbolic analogue of `Verdicts`'
    `O1_does_not_exit_zero`, and it is a computation, not a refutation
    through `must_exit_at`. -/

/-- `exits_c` is not blind to the exit status: the same run that reaches
    `true` at `verdict_reject` reaches `false` at `verdict_accept`. -/
theorem exits_c_exit1_ne_accept (sp : word) (mem rom : word → Option byte) :
    exits_c exit1_image_segments verdict_accept 8
      (demo_init_state demo_init_pc sp mem rom) = false := by
  let st0 : machine_state := demo_init_state demo_init_pc sp mem rom
  let st1 : machine_state := { st0 with
      ms_regs := bvmapSet (17 : reg) (BitVec.ofInt 64 93) st0.ms_regs
      ms_pc_val := st0.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st2 : machine_state := { st1 with
      ms_regs := bvmapSet (10 : reg) (BitVec.ofInt 64 1) st1.ms_regs
      ms_pc_val := st1.ms_pc_val + BitVec.ofInt 64 4
      ms_svc_pending := none }
  let st3 : machine_state := { st2 with ms_svc_pending := some (BitVec.ofInt 64 93) }
  have hpc0 : st0.ms_pc_val = BitVec.ofInt 64 0x10000 := rfl
  have hf0 : fetch_word exit1_image_segments (BitVec.ofInt 64 0x10000)
      = some (BitVec.ofInt 32 0x05d00893) := rfl
  have h1 : step exit1_image_segments st0 = .MachineOk st1 :=
    step_addi_a7 exit1_image_segments st0 _ hpc0 hf0
  have hpc1 : st1.ms_pc_val = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 := rfl
  have hf1 : fetch_word exit1_image_segments (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00100513) := rfl
  have h2 : step exit1_image_segments st1 = .MachineOk st2 :=
    step_addi_a0_1 exit1_image_segments st1 _ hpc1 hf1
  have hpc2 : st2.ms_pc_val
      = BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4 := rfl
  have hf2 : fetch_word exit1_image_segments
      (BitVec.ofInt 64 0x10000 + BitVec.ofInt 64 4 + BitVec.ofInt 64 4)
      = some (BitVec.ofInt 32 0x00000073) := rfl
  have ha7 : ms_reg st2 17 = BitVec.ofInt 64 93 := rfl
  have h3 : step exit1_image_segments st2 = .MachineOk st3 :=
    step_ecall exit1_image_segments st2 _ hpc2 hf2 ha7
  have hp0 : st0.ms_svc_pending = none := rfl
  have hp1 : st1.ms_svc_pending = none := rfl
  have hp2 : st2.ms_svc_pending = none := rfl
  have hp3 : st3.ms_svc_pending = some (BitVec.ofInt 64 93) := rfl
  have hg : ms_gpr st3 0 = BitVec.ofInt 64 1 := rfl
  have hcode : ((ms_gpr st3 0 &&& BitVec.ofInt 64 255) == verdict_accept) = false := by
    rw [hg]; decide
  have e0 : exits_c exit1_image_segments verdict_accept 8 st0
      = exits_c exit1_image_segments verdict_accept 7 st1 :=
    exits_c_succ_none _ _ 7 st0 st1 hp0 h1
  have e1 : exits_c exit1_image_segments verdict_accept 7 st1
      = exits_c exit1_image_segments verdict_accept 6 st2 :=
    exits_c_succ_none _ _ 6 st1 st2 hp1 h2
  have e2 : exits_c exit1_image_segments verdict_accept 6 st2
      = exits_c exit1_image_segments verdict_accept 5 st3 :=
    exits_c_succ_none _ _ 5 st2 st3 hp2 h3
  have hd : decide (((BitVec.ofInt 64 93).toNat : Int) = 93) = true := by decide
  have e3 : exits_c exit1_image_segments verdict_accept 5 st3 = false := by
    simp only [exits_c, hp3, hd, Bool.true_or, hcode, Bool.and_false]
  rw [e0, e1, e2, e3]

/- =========================================================================
   The soundness engine: `exits_c` accepts only programs that must exit
   ========================================================================= -/

/-- ** `exits_c` is sound for `MustExit.must_exit_at`.**

  The induction: at every fuel level either a syscall is
    already pending — and then the exit arm is the only successor, so
    `must_exit_at_exit_pending` (from `Verdicts`) closes the level — or it
    is not, and then `exits_c` can only be `true` because `step` answered
    `.MachineOk ms'` and the recursive call is `true`, so
    `must_exit_at_instr` (also from `Verdicts`) hands the level to the
    induction hypothesis.  The two `.MachineFault`/`.MachineUnmodeled`
    arms are `false`, and `false = true` is the contradiction that rules
    them out.

    The model is where the two hypotheses go: `m_halted model = none`
    keeps the `halted` base case out of the way (a pre-halted model would
    satisfy `must_exit_at` at ANY code) and `m_vm_lazy model = []` is what
    turns the accounting step into the bare instruction step
    (`mi_account_step_no_lazy`), so the successor configuration's model is
    the SAME model and the induction hypothesis applies to it.

  The conclusion is written `⟨ms, model⟩`, not `mkCfg ms model`: `mkCfg`
  is `⟨·, ·⟩` in `Common.AsanAcct`, which is outside this file's import
  graph.  The two are definitionally equal, so the two spellings differ
  by one delta.

    Cost: the two hard inversions are `Verdicts`' and are reused; this
    induction is a handful of lines per fuel level. -/

theorem exits_c_must_exit_at (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model),
      m_halted model = none → m_vm_lazy model = [] →
      exits_c segs code fuel ms = true → must_exit_at segs code ⟨ms, model⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms model _ _ h
      simp only [exits_c] at h
      exact absurd h (by simp)
  | succ n ih =>
      intro ms model hh hlazy h
      cases hp : ms.ms_svc_pending with
      | some x8 =>
          have h' : ((decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
              && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)) = true := by
            simpa only [exits_c, hp] using h
          rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
            decide_eq_true_eq, beq_iff_eq] at h'
          obtain ⟨h93 | h94, hcode⟩ := h'
          · exact must_exit_at_exit_pending segs ms model x8 code hh hp (Or.inl h93) hcode
          · exact must_exit_at_exit_pending segs ms model x8 code hh hp (Or.inr h94) hcode
      | none =>
          cases hstep : step segs ms with
          | MachineOk ms' =>
              have hrec : exits_c segs code n ms' = true := by
                simp only [exits_c, hp, hstep] at h
                exact h
              have hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
                rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
              exact must_exit_at_instr segs ms ms' model code hh hp hacc
                (ih ms' model hh hlazy hrec)
          | MachineFault =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)
          | MachineUnmodeled =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)

/-- ** The generic form, and the lemma this file exists for.**

    A program whose fuel-bounded execution reaches `exit(code)` with the
    stack pointer, the writable memory and the read-only backing left
    abstract must exit with that code at EVERY entry, on EVERY input, at
    EVERY budget.

    `init_machine_state_abstracts` is what lets the three abstract
    components through: every `Run.init_machine_state` is
    `demo_init_state pc sp mem rom` at SOME pair, so quantifying over the
    pair covers the entry and the whole `ProcInput`.  The model's two
    premises are the library's `m_halted_init_model` and this file's
    `init_model_no_lazy`, and neither mentions the budget — which is why
    `lim` is universally quantified here and every consumer (the patch
    obligation at each role's limit, the classifier obligations at
    `Classifier.classifier_alloc_limit`) can use the same theorem. -/
theorem must_exit_everywhere_of_exits_c (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (code : word) (fuel : Nat)
    (H : ∀ sp mem rom, exits_c segs code fuel (demo_init_state pc sp mem rom) = true) :
    ∀ (lim : Int) (en : ExecEntry) (inp : ProcInput),
      must_exit_with code (mkImage segs pc ph) lim en inp := by
  intro lim en inp
  obtain ⟨mem, rom, hms⟩ :=
    init_machine_state_abstracts segs pc ph en.en_sp en.en_draw
      inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  show must_exit_at segs code
    (init_config segs pc ph en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)
  rw [show init_config segs pc ph en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
      = ⟨demo_init_state pc en.en_sp mem rom,
          init_model (segments_reserved segs) en.en_brk en.en_mmap_base en.en_sp lim inp⟩
      from by rw [init_config, hms]]
  exact exits_c_must_exit_at segs code fuel (demo_init_state pc en.en_sp mem rom)
    (init_model (segments_reserved segs) en.en_brk en.en_mmap_base en.en_sp lim inp)
    (m_halted_init_model _ _ _ _ _ _)
    (init_model_no_lazy _ _ _ _ _ _)
    (H _ mem rom)

/-! ## The six verdicts, by the `exits_c` route

    These are the SAME statements `Verdicts` proves by symbolic execution of
    the three instructions.  Proving them twice is the point of this file:
    the two routes share no computation, so a reader who trusts neither
  tactic can compare them, and the `exits_c` route is the symbolic one. -/

theorem O1_must_exit_one_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject O1_image lim en inp :=
  must_exit_everywhere_of_exits_c O1m.loaded_segments O1m.init_pc O1m.phdrs
    verdict_reject 8 (fun sp mem rom => O1_exits_c sp mem rom) lim en inp

theorem O2_must_exit_zero_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept O2_image lim en inp :=
  must_exit_everywhere_of_exits_c O2m.loaded_segments O2m.init_pc O2m.phdrs
    verdict_accept 8 (fun sp mem rom => O2_exits_c sp mem rom) lim en inp

theorem P1_must_exit_zero_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept P1_image lim en inp :=
  must_exit_everywhere_of_exits_c P1m.loaded_segments P1m.init_pc P1m.phdrs
    verdict_accept 8 (fun sp mem rom => P1_exits_c sp mem rom) lim en inp

theorem P2_must_exit_zero_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_accept P2_image lim en inp :=
  must_exit_everywhere_of_exits_c P2m.loaded_segments P2m.init_pc P2m.phdrs
    verdict_accept 8 (fun sp mem rom => P2_exits_c sp mem rom) lim en inp

theorem C1_must_exit_one_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject C1_image lim en inp :=
  must_exit_everywhere_of_exits_c C1m.loaded_segments C1m.init_pc C1m.phdrs
    verdict_reject 8 (fun sp mem rom => C1_exits_c sp mem rom) lim en inp

theorem C2_must_exit_one_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_with verdict_reject C2_image lim en inp :=
  must_exit_everywhere_of_exits_c C2m.loaded_segments C2m.init_pc C2m.phdrs
    verdict_reject 8 (fun sp mem rom => C2_exits_c sp mem rom) lim en inp

/-!... and the rest of the list, each one library lemma away from
    the six above: the wrong-code refutations (so the code argument is not
    decoration), the realization lemmas (so no verdict is satisfied by a run
    that says nothing), and the error-free/modeled facts. -/

theorem O1_realizes_exit_one_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ∃ tr fs, bh_traces (run O1_image lim en inp) (tr ++ [event.ExitEv verdict_reject fs]) :=
  must_exit_with_realizes verdict_reject O1_image lim en inp
    (O1_must_exit_one_via_exits_c lim en inp)

theorem P1_realizes_exit_zero_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ∃ tr fs, bh_traces (run P1_image lim en inp) (tr ++ [event.ExitEv verdict_accept fs]) :=
  must_exit_with_realizes verdict_accept P1_image lim en inp
    (P1_must_exit_zero_via_exits_c lim en inp)

theorem P1_error_free_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run P1_image lim en inp) :=
  must_exit_with_no_error verdict_accept P1_image lim en inp
    (P1_must_exit_zero_via_exits_c lim en inp)

theorem P2_error_free_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run P2_image lim en inp) :=
  must_exit_with_no_error verdict_accept P2_image lim en inp
    (P2_must_exit_zero_via_exits_c lim en inp)

theorem O1_error_free_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run O1_image lim en inp) :=
  must_exit_with_no_error verdict_reject O1_image lim en inp
    (O1_must_exit_one_via_exits_c lim en inp)

theorem O2_error_free_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_errors (run O2_image lim en inp) :=
  must_exit_with_no_error verdict_accept O2_image lim en inp
    (O2_must_exit_zero_via_exits_c lim en inp)

theorem P1_modeled_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run P1_image lim en inp) :=
  must_exit_with_modeled verdict_accept P1_image lim en inp
    (P1_must_exit_zero_via_exits_c lim en inp)

theorem P2_modeled_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run P2_image lim en inp) :=
  must_exit_with_modeled verdict_accept P2_image lim en inp
    (P2_must_exit_zero_via_exits_c lim en inp)

theorem O1_modeled_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run O1_image lim en inp) :=
  must_exit_with_modeled verdict_reject O1_image lim en inp
    (O1_must_exit_one_via_exits_c lim en inp)

theorem O2_modeled_via_exits_c (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_unmodeled (run O2_image lim en inp) :=
  must_exit_with_modeled verdict_accept O2_image lim en inp
    (O2_must_exit_zero_via_exits_c lim en inp)


end Verdicts

end LinuxSem.Examples.PatchClassifyDemo


