/-
  * Common.SymTac — the per-block tactic wrapper around [Common.SymExec].

  EXPLORATION / PROTOTYPE.

  [Common/SymExec] proves the theorem; this file is what makes it
  cheap to USE.  Applying [sym_exec_sound] by hand costs ~30 lines of
  mechanical boilerplate per block (build the entry [sym_state], build
  [st_ok] from the goal's machine state, evaluate the exit state and the
  side-condition list, destruct the conclusion, re-attach the resulting
  [msteps] to whichever chain relation the goal is in, read the exit
  registers back through [regs_ok]).  At that price a straight line has
  to be ~40 instructions long before it pays for itself, which is only
  true of a crt entry sequence.

  [sym_block] does all of it in one tactic call.  What is left for the
  caller is exactly the mathematical content:

    sym_block segs, fuel, dirs, reads, pins, pvals, rvals, R, H
    -- the side conditions the block assumed, in order
    -- one goal per pinned register
    -- the chain goal advanced to the state the executor stopped at

  and, when the block is pure ALU/control (the common case), the first
  two groups are empty and the whole block is ONE line.

  THE ARGUMENTS.

  - [segs]  — the image's segment list (the same one the fetch lemmas use).
  - [fuel]  — an upper bound on the number of instructions to run.  The
    executor stops on its own at the first thing it does not model, so
    over-estimating costs only evaluation time.
  - [dirs]  — the branch script: one [Bool] per branch the run meets.
    Each one becomes an [SCBr] side condition, so nothing is assumed.
  - [reads] — the read script: an [expr] NAMING each value the block
    loads out of the base memory, in the order the executor meets them.
    Empty (or exhausted) means "call it a fresh variable", the only
    option before; naming a reloaded return address [.ELit 0x11020] is
    what lets the [ret] two instructions later resolve, which is the
    difference between stopping at every musl wrapper epilogue and
    running through it.  Either way the obligation is the same
    [SCReadBase].
  - [pins]  — [(register, expr)] pairs describing what the caller
    already knows about the entry register file.  The entry state is
    otherwise [sr_id] ("every register is its own variable"), which is
    already enough for sp-relative addressing: [EVar 2] IS a legal
    symbolic base.  A pin is needed when a register's value has to be a
    literal for the run to continue — a [jalr] return address, a global
    pointer used as an absolute address.
  - [pvals] — the values of the [EVar 32], [EVar 33], … the pins
    mention, in index order.  Pinning [sp] to [EVar 32] with
    [pvals = [BitVec.ofInt 64 (bv_unsigned rsp - 32)]] is how a frame
    base enters the block as a symbolic-but-named quantity.
  - [rvals] — the values of the words the block READS out of the base
    memory, in the order the executor meets them (each one raises an
    [SCReadBase] obligation).  Their indices continue after [pvals]'.
  - [R], [H] — the names to bind the exit register file and its
    [regs_ok] fact to.  [H] is what [sym_regs] reads the block's
    results out of.

  THE VALUATION.  [E] is always [Eplus regs (pvals ++ rvals)]: below
  32 it is the ENTRY register file, at and above 32 it is the caller's
  list.  Nothing else is ever needed, and — this is the point — the
  valuation is a term the executor never sees.  Everything the executor
  reduces ([sym_exec], [sr_pins], [sr_get]) is closed deep syntax:
  [Int] literals, register indices, the memory image.  No [BitVec]
  variable can reach it, which is the trap [Common/StepTac]'s [bveq]
  docstring describes.

  WHAT STOPS A BLOCK.  The executor hands the state back at the first
  instruction it does not model, and [sym_block] then leaves the goal
  at exactly that pc for the tactic layer.  In the example proofs the
  three reasons that actually fire are, in order of frequency:
  [ecall]; a [jalr] whose target register is not a literal (a [ret] at
  the top of a block, before anything has written [ra]); and the narrow
  accesses [sh] and the SIGN-EXTENDING [lb]/[lh].

  The narrow-access list is worth stating precisely, because the
  zero-extending loads and the wider stores DO go through, and a reader
  who assumes otherwise gives up on the reflective route for a block
  that would have run.  [sym_step]'s store arm takes [SZ1]/[SZ4]/[SZ8],
  so [sb]/[sw]/[sd] are all modelled and only [sh] ([SZ2]) is not.  Its
  load arm splits: a read that MISSES the store log takes [SZ8] signed,
  [SZ4]/[SZ2]/[SZ1] unsigned, and [SZ4] signed through [mkSext32] — so
  [ld]/[lwu]/[lhu]/[lbu]/[lw] all go through there and only the
  sign-extending [lb]/[lh] are missing — while a read that HITS the log
  is [SZ8] signed only, a slot being read back whole.

  **(b) Tactic fidelity.**  Each  `Ltac` is a Lean `macro` or
  `elab` of the same name and arity.  Argument lists are
  COMMA-separated (Lean has no space-separated tactic application), and
  `first | a | b` starts each alternative on its own line (a quotation
  cannot break a line before the first `|`).  The individual docstrings
  mark what changed; the systematic deviations are:
  1. *`vm_compute`-based normalizers* ([sym_z_lit], [sym_z_norm],
     [sym_lit_norm], [sym_pc_Z], [sym_pc_lit], and the `Z_to_bv 5`
     respelling inside [sym_env_norm]).  These exist because `simp`/`dsimp`
     will not reduce a `Z`-projection over a vm-cast numeral, and `rewrite`
     cannot match a closed redex whose reduction needs conversion.  Lean's elaborator has neither problem: `decide`,
     `rfl`, `omega` and `simp` all reduce closed terms, and
     `BitVec.ofInt 64 0x11020` IS the numeral literal
     `(0x11020 : word)` up to conversion.  This is the same
     policy [Common/StepTac] applies to [wlit]/[norm_pc]/[imm_norm].
  2. *Reflective evaluation* ([sym_block], [sym_block_ex]).  
     `eval vm_compute in (sym_exec …)` computes the exit state in the
     tactic's meta-language.  Lean's equivalent is
     `Lean.Meta.reduceAll` at `.all` transparency over the closed executor
     application, which is EXACTLY as constrained as `vm_compute`: the
     segment list must be a closed term, and the valuation must stay
     out of it.  (`reduceAll`, not `whnf`: `whnf` stops at the head
     constructor and leaves the state's FIELDS as lazy redexes — an
     unreduced `if bv_eqb rd 0` in `s_regs`, for one — which the kernel
     then has to reduce again at every occurrence, and which `sym_regs`
     cannot close either.)  This tree's `sym_block` does that (see
     [symBlockCore]); the computed exit state is spliced into the goal
     as a literal, and the soundness application
     (`SymExec.sym_exec_ex`) is built at the meta level.  The 
     `[Hsc | Hst | …]` assert tower becomes a sequence of
     `MVarId.note`s (`assert` followed by `intro1P`, so the hypotheses
     really do land in the caller's context — `assert` alone only turns
     the goal into a `∀`), and the goals the caller sees appear in the
     same order: side conditions, then pins, then the advanced chain
     goal.
  3.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.Footprint
import LinuxSem.Common.SymExec
import LinuxSem.Common.SymBranch
import LinuxSem.Common.StepTac
import LinuxSem.Common.ExitSim
import LinuxSem.Common.StreamSim
import LinuxSem.Common.WallSim
import LinuxSem.Common.DrainSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.ShapeAlg

namespace LinuxSem.Common.SymTac

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.SymExec
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StoreOk
open LinuxSem.Common.Footprint

open Lean Meta Elab Tactic

/-- `List α` as an `Expr` (for the expected types of `sym_block`'s arguments). -/
private def listTy (α : Expr) : Expr := mkApp (mkConst ``List [.zero]) α

/-- `α × β` as an `Expr`. -/
private def prodTy (α β : Expr) : Expr := mkApp2 (mkConst ``Prod [.zero, .zero]) α β

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Context {fx : FPState}.`: the machine-state
    projections this file reasons about (`getr`, `mkst`, `st_ok`) live in an
    `FPState` section in this tree.

    `Common/SymExec.lean` instantiates that section with a LOCAL
    INSTANCE `symexec_fx : FPState := fx0` rather than abstracting over it, so
    `SymExec.st_ok` and `SymExec.regs_ok` are stated at `fx0` and carry no
    instance argument at all.  This file therefore pins the same instance —
    abstracting here would make every `st_ok` in `sym_block`'s goals a
    different term from the one `sym_exec_sound` speaks about.  A downstream
    block proof whose machine state is `mkst` at some other FP state must
    first move to `fx0` (the FP state at process entry), which is where a
    concrete-binary block starts anyway. -/
local instance symtac_fx : FPState := fx0

/-! ## 1. Pinning entry registers -/

/-- Apply a list of `(register, expr)` pins to a symbolic register file.
    Left to right, so a later pin of the same register wins. -/
def sr_pins : List (reg × expr) → List expr → List expr
  | [], sr => sr
  | (r, e) :: rest, sr => sr_pins rest (sr_upd sr (ridx r) e)

/-- The caller's side of a pin list: each pinned register really does hold
    the value its `expr` denotes.

     `Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps`;
    the repo-wide spelling of `List.Forall` is the membership form below. -/
def pins_ok (E : env) (regs : BvMap word) (ps : List (reg × expr)) : Prop :=
  ∀ p ∈ ps, getr regs p.1 = edenot E p.2

/-- The empty pin list asks for nothing.   -/
theorem pins_ok_nil (E : env) (regs : BvMap word) : pins_ok E regs [] := by
  intro p hp
  simp at hp

/-- One-`cons` shape of the pin obligation.   -/
theorem pins_ok_cons (E : env) (regs : BvMap word) (p : reg × expr)
    (ps : List (reg × expr)) :
    pins_ok E regs (p :: ps)
      ↔ (getr regs p.1 = edenot E p.2 ∧ pins_ok E regs ps) := by
  constructor
  · intro H
    refine ⟨H p (by simp), ?_⟩
    intro q hq
    exact H q (by simp [hq])
  · rintro ⟨Hh, Ht⟩ q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Hh
    · exact Ht q hq

theorem regs_ok_pins (E : env) (ps : List (reg × expr)) (sr : List expr)
    (regs : BvMap word) (Hr : regs_ok E sr regs) (Hp : pins_ok E regs ps) :
    regs_ok E (sr_pins ps sr) regs := by
  induction ps generalizing sr with
  | nil => exact Hr
  | cons p rest ih =>
    obtain ⟨r, e⟩ := p
    have Hh : getr regs r = edenot E e := Hp (r, e) (by simp)
    have Ht : pins_ok E regs rest := by
      intro q hq
      exact Hp q (by simp [hq])
    exact ih (sr_upd sr (ridx r) e) (regs_ok_pin E sr regs r e Hr Hh) Ht

/-! ## 2. Value normalization for the post-state reader -/

/-- A `mv rd,rs` is `addi rd,rs,0`; the smart constructor cannot fold it
    (the base is symbolic), so EVERY register copy in a compiled prologue
    denotes as `alu64 .ADD x 0`.  One lemma collapses all of them, which is
    why `sym_regs` can read a shuffled argument register back without a
    per-instruction script. -/
theorem alu64_add_0 (x : word) : alu64 .ADD x (BitVec.ofInt 64 0) = x := by
  rw [alu_add, v_add_eq]
  exact BitVec.add_zero x

/-- The corresponding 32-bit identity, for a `sext.w`/`addiw rd,rs,0`. -/
theorem aluw_add_0 (x : word) :
    sext 64 (alu32 .ADD (low32 x) (low32 (BitVec.ofInt 64 0))) = v_lw x := by
  rw [low32_lit, alu32_add_0]
  exact b_lw_val x

/-- The word-op counterpart of `alu_add`/`alu_sub`/... .  The executor's
    `EAluw op a (.ELit k)` denotes as
    `sext 64 (alu32 op (low32 a) (low32 (BitVec.ofInt 64 k)))`, and NO library
    lemma is stated against that spelling: `PropExec.w_addiw` takes the
    immediate as a `BitVec 12` under a `sext 32`, which is the shape the
    per-instruction step lemmas produce, not the one a reflective block
    leaves behind.  Without this rule every `addiw`/`sext.w` a block
    executes has to be re-derived at its use site — and `addiw` is how
    every 32-bit C expression compiles.
-/
theorem aluw_addi_lit (a : word) (k : Int) :
    sext 64 (alu32 .ADD (low32 a) (low32 (BitVec.ofInt 64 k))) = v_addiw a k := by
  rw [low32_lit,
    sext_ofInt32 (alu32 .ADD (low32 a) (BitVec.ofInt 32 k)) ((a.toNat : Int) + k)
      (by simp only [alu32, alu, low32_eq_ofInt]; bv_omega)]
  rfl

/-- The four denotation projections, as REWRITE rules.  `cbn`'s delta list
    cannot be used for these: `adenot`/`bdenot` unfold to a `v_addi` that is
    already in normal form, so `cbn` judges the step unproductive and leaves
    the projection folded — the resulting goal then mentions `adenot`, which
    no library lemma is stated against. -/
theorem bdenot_var (E : env) (n : Nat) : bdenot E (.SBVar n) = E n := rfl

theorem bdenot_lit (E : env) : bdenot E .SBLit = BitVec.ofInt 64 0 := rfl

theorem edenot_lit (E : env) (z : Int) : edenot E (.ELit z) = BitVec.ofInt 64 z := rfl

theorem edenot_var (E : env) (n : Nat) : edenot E (.EVar n) = E n := rfl

/-- `v_addi` IS `BitVec.ofInt 64 (bv_unsigned x + i)` definitionally (that is
    how `SeqExec.v_addi_m` and `StepTac.v_addi_nneg_t` are proved by `rfl`);
    as a rewrite rule with the displacement a VARIABLE it normalizes any
    offset, where `StepTac.sp_norm` only knows the six negative constants it
    has named lemmas for.  A reflectively executed block produces whatever
    displacement the compiler chose. -/
theorem v_addi_Z (x : word) (i : Int) :
    v_addi x i = BitVec.ofInt 64 ((x.toNat : Int) + i) := rfl

theorem adenot_var (E : env) (n : Nat) (k : Int) :
    adenot E (SA (.SBVar n) k) = BitVec.ofInt 64 ((E n).toNat + k) := by
  unfold adenot bdenot
  rw [v_addi_eq, ← ofInt64_ofNat_add]

theorem adenot_lit (E : env) (k : Int) : adenot E (SA .SBLit k) = BitVec.ofInt 64 k := by
  unfold adenot bdenot
  rw [v_addi_eq]
  simp

/-!     These two `iff`s are this tree's form of that peel: `simp only [..]`
    reduces a batch to a conjunction of individual `sc_denot` goals, one per
    emitted side condition.  () -/

theorem scs_denot_nil (segs : List Segment) (base : word → Option byte) (E : env) :
    scs_denot segs base E [] ↔ True := by
  constructor
  · intro _; trivial
  · intro _ s hs
    simp at hs

theorem scs_denot_cons (segs : List Segment) (base : word → Option byte) (E : env)
    (s : sidecond) (l : List sidecond) :
    scs_denot segs base E (s :: l)
      ↔ (sc_denot segs base E s ∧ scs_denot segs base E l) := by
  constructor
  · intro H
    exact ⟨H s (by simp), fun x hx => H x (by simp [hx])⟩
  · rintro ⟨Hh, Ht⟩ x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Hh
    · exact Ht x hx

/-!  These exist to steer reduction away from the projections `cbn` used to
    handle; `simp only` is what steers it here.  See the header's fidelity
    notes. -/

/-- `cbn [Eplus … a_base a_off e_addr e_width e_val]`: put a valuation
    application and the record projections into constructor form. -/
macro "sym_env_cbn" : tactic =>
  `(tactic|
    simp (config := { failIfUnchanged := false }) only
      [Eplus, ridx, saddr.a_base, saddr.a_off, sentry.e_addr, sentry.e_width,
       sentry.e_val, Prod.fst, Prod.snd, List.getD, List.length, List.nil_append,
       List.cons_append, List.append_nil])

/-- Reduce an `Eplus` application to the thing it actually is: an entry
    register read below 32, a caller-supplied value at or above it, and
    normalize the address projections with it.

     ends with a `repeat match goal with
    |- context [getr ?rs (Z_to_bv 5 ?z)] => … replace (Z_to_bv 5 z) with l`
    loop, re-spelling the index as the numeral literal the library uses.  In
    Lean `BitVec.ofInt 5 8` IS `(8 : reg)` up to conversion, so the loop has
    nothing to do; it is documented here rather than emitted. -/
macro "sym_env_norm" : tactic =>
  `(tactic|
    simp (config := { failIfUnchanged := false }) only
      [Eplus, ridx, saddr.a_base, saddr.a_off, sentry.e_addr, sentry.e_width,
       sentry.e_val, Prod.fst, Prod.snd, List.getD, List.length, List.nil_append,
       List.cons_append, List.append_nil,
       adenot_var, adenot_lit, bdenot_var, bdenot_lit, edenot_lit, edenot_var,
       u_Z_to_bv64_0])

/-- `sym_z_lit k`: guard that `k` is a *literal* `Z`
    (`Z0`/`Zpos`/`Zneg`), used to keep the `sym_z_norm` rewrites from firing
    on a symbolic displacement.  Lean has no such three-way constructor, so
    the guard is a closedness/nat-literal check on the `Int` term. -/
elab "sym_z_lit " k:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm k none
  let e ← instantiateMVars e
  if e.isAppOf ``Int.negSucc || e.isAppOf ``Int.ofNat || e.isRawNatLit then
    pure ()
  else
    throwError "sym_z_lit: {e} is not a closed Int literal"

/-- Fold the literal displacements a chain of `addi`s leaves behind and
    collapse the `0 + k` an absolute address arrives as.

     is a four-arm `match goal with … replace … by lia` loop
    over `context [Z_to_bv 64 (0 + ?k)]`, `(a - k1 + k2)`, `(a + k1 + k2)`
    and `(a + (Zneg p))`.  Those are `Int`-arithmetic identities on literals,
    so `omega`/`simp` close them by conversion in Lean, and the terms
    themselves are already in the normal form the rewrites would produce.
-/
macro "sym_z_norm" : tactic => `(tactic| skip)

/-- Put every address the symbolic layer produced into the canonical
    `BitVec.ofInt 64 (bv_unsigned base + k)` spelling the example proofs state
    their frame slots in, and collapse the `(BitVec.ofInt 64 _).toNat`
    projections that leaves. -/
macro "sym_addr_norm" : tactic =>
  `(tactic|
    (imm_norm
     simp (config := { failIfUnchanged := false }) only
       [v_addi_Z, Eplus, ridx, saddr.a_base, saddr.a_off,
        sentry.e_addr, sentry.e_width, sentry.e_val, Prod.fst, Prod.snd,
        List.getD, List.length, List.nil_append, List.cons_append, List.append_nil,
        adenot_var, adenot_lit, bdenot_var, bdenot_lit, edenot_lit, edenot_var,
        u_Z_to_bv64_0]
     u_norm))

/-- Re-spell a CLOSED stored word as the numeral literal the example proofs
    use.  A stored return address arrives from the executor as
    `BitVec.ofInt 64 69664` and has to read back as `0x11020 : word` for the
    tactic layer's `rdn_wbytes_hit8` to close by `rfl`.

    `BitVec.ofInt 64 69664` and `(0x11020 : word)` are the same
    `BitVec` value up to conversion, so the re-spelling is a no-op; the
     scoping note (only rewrite inside `word_to_le_bytes` arguments,
    never in an exported statement) therefore cannot be violated here
    either. -/
macro "sym_lit_norm" : tactic => `(tactic| skip)

/-- Normalize a symbolic value into the `v_*` shapes the tactic library
    (`StepTac.sp_norm`, `bveq`, `getr_resolve`) expects.  Extends
    `SymExec.sym_val_norm` with the `mv` identities and the valuation. -/
macro "sym_norm" : tactic =>
  `(tactic|
    simp (config := { failIfUnchanged := false }) only
      [edenot, sr_get, ridx, bv_eqb, sym_state.s_regs, sym_state.s_pc,
       sym_state.s_log, sym_state.s_next, branch_taken,
       alu64_add_0, aluw_add_0, aluw_addi_lit,
       alu_add, alu_sub, alu_and, alu_or, alu_xor,
       alu_slt, alu_sltu, alu_sll, alu_srl, alu_sra,
       v_add_lit, v_sub_lit, v_addi_Z, Eplus, saddr.a_base, saddr.a_off,
       sentry.e_addr, sentry.e_width, sentry.e_val, Prod.fst, Prod.snd,
       List.getD, List.length, List.nil_append, List.cons_append, List.append_nil,
       adenot_var, adenot_lit, bdenot_var, bdenot_lit, edenot_lit, edenot_var,
       u_Z_to_bv64_0])

/-- Unfold the store log's denotation into the `wbytes` chain the tactic
    layer's read lemmas (`rdn_wbytes_hit8`, `rdn_wbytes_disjoint`,
    `rdn_wbytes_below`) are stated against, with the addresses in canonical
    form and the stored constants in literal form. -/
macro "sym_mem_norm" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only
               [mem_denot, sentry.e_addr, sentry.e_width, sentry.e_val]
             sym_norm
             sym_lit_norm))

/-- Peel a right-nested conjunction into its leaves.  () -/
syntax "sym_split_ands" : tactic
macro_rules
  | `(tactic| sym_split_ands) => `(tactic| first | (apply And.intro <;> sym_split_ands) | skip)

/-! ## 3. Attaching an `msteps` to whichever chain relation the goal is in -/

/-- The chain relation that had no `msteps`-prepending lemma yet.  Same
    two-line induction as `CatSim.msteps_to_wexit`. -/
theorem msteps_to_exit (segs : List Segment) (code : word) (ms ms' : machine_state)
    (H : msteps segs ms ms') (He : ExitSim.to_exit segs code ms') :
    ExitSim.to_exit segs code ms := by
  induction H with
  | mst_refl ms => exact He
  | mst_step ms ms1 ms2 hsvc hstep _ ih =>
    exact ExitSim.to_exit.te_step ms ms1 hsvc hstep (ih He)

/-- The write-pending counterpart. -/
theorem msteps_to_wr (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms ms' : machine_state) (H : msteps segs ms ms')
    (Hw : StreamSim.to_wr segs LH bs ms') : StreamSim.to_wr segs LH bs ms :=
  StreamSim.msteps_to_wr segs LH bs ms ms' H Hw

/-- The loop-body goal of `StreamSim`: "this state runs to SOME loop head".
    Prepending an `msteps` to it is what lets a block run all the way to the
    loop head and then close by `mst_refl`, instead of guessing the target
    state into an `exists` before the block has produced its register file. -/
theorem msteps_lh_next (segs : List Segment) (LH : machine_state → Prop)
    (ms ms' : machine_state) (H : msteps segs ms ms')
    (HL : StreamSim.lh_next segs LH ms') : StreamSim.lh_next segs LH ms := by
  obtain ⟨m, Hm, Hl⟩ := HL
  exact ⟨m, msteps_trans segs ms ms' m H Hm, Hl⟩

/-- The model side conditions carried by `ShapeAlg.rz_msteps` but not the
    other chain relations do not: a silent machine step is only admissible
    from a NON-halted model with no lazy mappings.  In a `realizes`
    derivation these are always either hypotheses in context or literals,
    and the model is often wrapped in the allocator's model transformers —
    which preserve both fields. -/
macro "sym_halted" : tactic =>
  `(tactic|
    first
    | rfl
    | assumption
    | (try (rw [MmapSim.mmap_model_halted, MmapSim.munmap_model_halted])
       first
       | rfl
       | assumption)
    | (try (simp (config := { failIfUnchanged := false }) only
              [m_halted, MmapSim.mmap_model, MmapSim.munmap_model, config.cfg_model])
       first
       | rfl
       | assumption))

macro "sym_no_lazy" : tactic =>
  `(tactic|
    (try (simp (config := { failIfUnchanged := false }) only [config.cfg_model])
     repeat (first
             | rw [MmapSim.mmap_model_lazy]
             | apply MmapSim.munmap_model_no_lazy)
     first
     | rfl
     | assumption))

/-- Prepend a run of ordinary instruction steps to the current chain goal.
    Mirrors `StepTac.chain_step` one level up: same set of relations,
    `msteps` instead of a single `step`.

    The `ShapeAlg.realizes` case is what lets a `sym_block` run directly
    inside a shape-algebra derivation instead of inside one of the bespoke
    `to_*` relations.  It is `ShapeAlg.rz_msteps` with its model premises
    pre-discharged by `sym_halted` and `sym_no_lazy`, so that this
    alternative leaves the SAME two goals as every other one (`msteps`, then
    the advanced chain goal) and `chain_mst; [exact Hms | ]` keeps working
    verbatim. -/
macro "chain_mst" : tactic =>
  `(tactic|
    first
    | apply CatSim.msteps_to_wexit
    | apply MmapSim.msteps_twm
    | apply MmapSim.msteps_twm_tail
    | apply MmapSim.msteps_tmw
    | apply StreamSim.msteps_to_rd
    | apply msteps_to_wr
    | apply WallSim.msteps_to_wall_tail
    | apply WallSim.msteps_to_wallexit
    | apply DrainSim.msteps_to_rd
    | apply DrainSim.msteps_to_out
    | apply msteps_to_exit
    | apply msteps_lh_next
    | (apply ShapeAlg.rz_msteps; all_goals (first | sym_halted | sym_no_lazy | skip))
    | apply msteps_trans)

/-- Regression: the `realizes` alternative really does leave the two goals
    `chain_mst`'s callers expect, in that order. -/
theorem chain_mst_realizes (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (T : ShapeAlg.TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hms : msteps segs ms ms')
    (Hr : ShapeAlg.realizes segs (ShapeAlg.mkCfg ms' model) T) :
    ShapeAlg.realizes segs (ShapeAlg.mkCfg ms model) T := by
  chain_mst <;> (first | exact Hms | exact Hr)

/-- ... and through an allocator's model transformer, which is the shape
    `DrainAlg.rz_mmap_drain`'s success continuation hands the per-binary
    layer. -/
theorem chain_mst_realizes_mmap (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (a n : word) (T : ShapeAlg.TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hms : msteps segs ms ms')
    (Hr : ShapeAlg.realizes segs (ShapeAlg.mkCfg ms' (MmapSim.mmap_model a n model)) T) :
    ShapeAlg.realizes segs (ShapeAlg.mkCfg ms (MmapSim.mmap_model a n model)) T := by
  chain_mst <;> (first | exact Hms | exact Hr)

/-! ## 4. Reading a block's post-state back -/

/-- Close a goal that `sym_regs` has reduced.  Four spellings occur: already
    syntactically equal; two `BitVec.ofInt 64` terms whose arguments differ
    by `Int` arithmetic; the same over an OPEN `sp` window; and a closed
    `BitVec` equation between two literal forms.  Note the order: `bveq` is
    LAST, because it is the only alternative that reaches evaluation, and an
    open `BitVec` goal is exactly where that is most expensive. -/
macro "sym_close" : tactic =>
  `(tactic|
    first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; u_norm; omega)
    | bveq)

/-- Resolve every `getr R r` in the current goal through the exit `regs_ok`
    fact `H`, reduce the symbolic register file (closed deep syntax only —
    the valuation is not part of it) and normalize the result.

    This is the counterpart of `getr_resolve`: after a `sym_block`
    the register file is an opaque `R`, and this is how a fact about it is
    read out.
-/
macro "sym_regs " H:term : tactic =>
  `(tactic|
    (getr_resolve
     regupd_resolve
     (try (rw [← getr_nz _ _ (by reg_neq_tac)]))
     rw [$H _]
     simp (config := { failIfUnchanged := false }) only
       [sr_get, ridx, bv_eqb, List.getD, List.getD_cons_zero, List.getD_cons_succ,
        List.getD_nil]
     sym_norm))

/-- Same, for a single register, stating the value.  Produces `getr R r = v`
    as a hypothesis, leaving the caller's `tac` to close whatever arithmetic
    is left. -/
macro "sym_reg " H:term "," R:term "," r:term "," v:term "," tac:tactic : tactic =>
  `(tactic| (have : getr $R $r = $v := by sym_regs $H; $tac))

/-! ## 5. `sym_block` -/

/-- Structural length of a list literal, without reducing any element. -/
private partial def listLenNat (e : Expr) : MetaM Nat := do
  let e := (← withTransparency .all (whnf e)).consumeMData
  match e.getAppFn, e.getAppArgs with
  | .const ``List.nil _, _ => return 0
  | .const ``List.cons _, #[_, _, tl] => return (← listLenNat tl) + 1
  | _, _ => throwError "list_len: expected a list literal, got{indentExpr e}"

/-- Find the first `mkst regs (ofInt 64 pc) mem rom` application in `e`.  Returns the whole application together with its four
    explicit arguments; the traversal descends through applications and
    binders, exactly the places Ltac's `context` looks. -/
private partial def findMkst (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let e := e.consumeMData
  if e.getAppFn.isConstOf ``mkst then
    match e.getAppArgs with
    | #[_, regs, pc, mem, rom] => return some (e, regs, pc, mem, rom)
    | _ => pure ()
  for a in e.getAppArgs do
    if let some r ← findMkst a then return some r
  match e with
  | .lam _ _ b _ => findMkst b
  | .forallE _ _ b _ => findMkst b
  | .letE _ _ v b _ =>
    if let some r ← findMkst v then return some r
    findMkst b
  | .mdata _ b => findMkst b
  | _ => return none

/-- Run a tactic script on a fresh metavariable of type `ty` (in `ctx`'s
    local context) and return the — possibly still open — proof expression
    together with the goals the script could not close. -/
private def runOn (ctx : MVarId) (ty : Expr) (tac : Syntax) :
    Lean.Elab.Tactic.TacticM (Expr × List MVarId) := do
  let m ← ctx.withContext (mkFreshExprSyntheticOpaqueMVar ty)
  let rem ← Lean.Elab.Tactic.run m.mvarId! (evalTactic tac)
  return (m, rem)


/-- Syntactic length of a list literal.  Deliberately NOT
    `eval vm_compute in (length l)`: `pvals`/`rvals` hold OPEN `BitVec`
    terms, and evaluating one of those is what `bveq`'s docstring
    warns about.  This walks the term instead and never reduces an element.

     is an `Ltac` returning a `constr`; in Lean it is a term
    `elab` (so it can be used wherever a `Nat` term is wanted), backed by the
    same structural walk.  `sym_block` uses the meta-level helper
    `listLenNat` directly. -/
elab "list_len " l:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm l none
  let e ← instantiateMVars e
  let n ← listLenNat e
  return (mkNatLit n)

/-- Put the chain goal's pc into the `BitVec.ofInt 64 z` spelling `st_ok`
    wants.

    a total no-op.  A propositional rewrite is not needed because a `bv`'s
    numeral form and its `Z_to_bv` form would carry different
    well-formedness proofs elsewhere; in Lean `(0x11020 : word)` and
    `BitVec.ofInt 64 69664` are the same value up to conversion, so nothing
    has to be rewritten (compare `norm_pc`, which this tree makes a
    no-op for the same reason).  `sym_block` reads the pc off the goal's
    `mkst` directly instead of rewriting it. -/
macro "sym_pc_Z" : tactic => `(tactic| skip)

/-- Re-spell the chain state's pc as a numeral literal.  `StepTac`'s
    `norm_pc` does this for the chain-goal heads it enumerates; a block can
    also land on one it does not know (`StreamSim`'s `lh_next`, the
    loop-body goal), and the pc has to be a literal for the next fetch lemma
    to apply.

    total no-op, for the same conversion reason as `sym_pc_Z`. -/
macro "sym_pc_lit" : tactic => `(tactic| skip)

/-- The side conditions a block emits that need no per-binary input.  Every
    `SCFlat` is "this address is inside the window the caller already has
    bounds for", which is one `omega`; every `SCBr` whose operands the pins
    made literal is closed.  Between them that is two thirds of the
    obligations of a typical block, and discharging them here is the
    difference between a per-block cost that scales with the number of
    memory accesses and one that scales with the number of INTERESTING
    memory accesses.

    Deliberately no evaluation: an `SCFlat` mentions the caller's symbolic
    `sp`, and evaluating an open `BitVec` term is what `bveq`'s docstring
    warns about.
-/
macro "sym_sc_auto" : tactic =>
  `(tactic|
    first
    | rfl
    | decide
    | (repeat (first | apply And.intro | omega)))

/-- Run `tac` on goal `g`, reporting failure as `none` instead of an
    exception — this tree's form of  `first [ … ]` backtracking over
    hypothesis choices, which needs a *try* rather than a *commit*. -/
private def tryTac (g : MVarId) (tac : Syntax) : Lean.Elab.Tactic.TacticM (Option (List MVarId)) := do
  try
    setGoals [g]
    let rem ← Lean.Elab.Tactic.run g (evalTactic tac)
    return some rem
  catch _ => return none

/-- A pin that the PREVIOUS block already established.  Blocks chain: the
    register a block pins is almost always one an earlier `sym_block` left a
    `regs_ok` fact about, so the obligation is discharged by reading it back
    out — which hypothesis to read it out of is found by backtracking over
    the `regs_ok` facts in context.  Deliberately closed with the
    evaluation-free closers only: a wrong guess must fail FAST, and the goal
    is open (`sp` is symbolic).
-/
elab "sym_pin_auto" : tactic => do
  let g ← getMainGoal
  let closers ← `(tactic|
    first
    | rfl
    | assumption
    | (apply BitVec.eq_of_toNat_eq; u_norm; omega)
    | bveq)
  match ← tryTac g closers with
  | some rem => setGoals rem
  | none =>
    let hyps ← g.withContext do
      let lctx ← getLCtx
      pure <| lctx.decls.toList.filterMap id |>.filterMap fun d =>
        match d with
        | .cdecl _ fv _ ty _ _ =>
          if ty.getAppFn.isConstOf ``regs_ok then some (fv, d.userName) else none
        | _ => none
    let mut done := false
    for (_, n) in hyps do
      unless done do
        let hId := mkIdentFrom (← getRef) n
        let tac ← `(tactic|
          (sym_regs $hId
           first
           | rfl
           | assumption
           | (apply BitVec.eq_of_toNat_eq; u_norm; omega)
           | bveq))
        match ← tryTac g tac with
        | some rem =>
          if rem.isEmpty then
            done := true
            setGoals []
          else
            setGoals rem
        | none => pure ()
    unless done do
      throwError "sym_pin_auto: the pin is neither closed by `rfl` nor readable out of a \
        `regs_ok` hypothesis"

/-- The entry state of a block, `st_ok`-shaped: an empty store log and a
    register file that the caller's pins describe.  () -/
theorem st_ok_mk (E : env) (base rom : word → Option byte) (pc : Int) (sr : List expr)
    (nx : Nat) (regs : BvMap word) (ms : machine_state)
    (Hms : ms = mkst regs (BitVec.ofInt 64 pc) base rom) (Hr : regs_ok E sr regs) :
    st_ok E base rom ⟨pc, sr, [], nx⟩ ms := by
  refine ⟨regs, ?_, Hr, trivial⟩
  rw [Hms]
  rfl

/-! ## 6. `sym_block` — the reflective entry point

    `sym_block` runs the block's instructions reflectively and ends by
    destructing the executor's conclusion INTO THE GOAL IT IS STANDING IN:
    the exit register file becomes a goal-local variable and the block's
    `msteps` is immediately spent by `chain_mst`.

    The shared body is `symBlockCore`; the two entry points differ only in
    where the entry state comes from and in what is left in the context. -/

/-- The shared body of `sym_block` and `sym_block_ex`.

    `onlyEx = false` is `sym_block`: the entry state is found in the goal,
    the `msteps` is spent by `chain_mst`, and the chain goal is left advanced
    to the pc the executor stopped at.

    `onlyEx = true` is `sym_block_ex`: the entry state is the caller's `ms`,
    and `R`, `H`, `Hms` are left in the context (with `Hms`'s projections
    reduced) without touching the goal. -/
private def symBlockCore (msArg : Option Expr) (segs fuel dirs rds ps pvals rvals : Expr)
    (R H : Ident) (onlyEx : Bool) : Lean.Elab.Tactic.TacticM Unit := do
  let g₀ ← getMainGoal
  -- 1. the entry machine state `mkst regs pc mem rom`
  let (ms, regs, pcW, mem, rom) ← g₀.withContext do
    let src ← match msArg with
      | some m => pure m
      | none => g₀.getType
    match ← findMkst src with
    | some r => pure r
    | none => throwError "sym_block: no `mkst regs pc mem rom` machine state to execute from.\n\
        The `lazymatch goal with |- context [mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom]` \
        has the same requirement: the block's entry state must be spelled `mkst _ _ _ _` \
        (in the goal for `sym_block`, in the `ms` argument for `sym_block_ex`)."
  -- 2. the entry symbolic state and the valuation
  let k ← g₀.withContext (listLenNat pvals)
  let pcE ← g₀.withContext (mkAppM ``Int.ofNat #[← mkAppM ``BitVec.toNat #[pcW]])
  let ss0 ← g₀.withContext do
    let sr0 ← mkAppM ``sr_pins #[ps, mkConst ``sr_id]
    let nilSentry := mkApp (mkConst ``List.nil [.zero]) (mkConst ``sentry)
    pure (mkAppN (mkConst ``sym_state.mk) #[pcE, sr0, nilSentry, mkNatLit (32 + k)])
  let ee ← g₀.withContext do
    let vals ← mkAppM ``List.append #[pvals, rvals]
    mkAppM ``Eplus #[regs, vals]
  -- 3. reduce the executor
  let nilAcc := mkApp (mkConst ``List.nil [.zero]) (mkConst ``sidecond)
  let app ← g₀.withContext (mkAppM ``sym_exec #[segs, fuel, dirs, rds, ss0, nilAcc])
  -- `reduceAll`, NOT `whnf`: `whnf` leaves the state's fields as lazy
  -- redexes (an unreduced `if bv_eqb rd 0` in `s_regs`, among others),
  -- which the kernel then re-reduces at every occurrence of the spliced
  -- statement — the difference between milliseconds and minutes — and
  -- which `sym_regs` cannot reduce either.
  let pr ← withTransparency .all (reduceAll app)
  let ss1 := mkProj ``Prod 0 pr
  let scs := mkProj ``Prod 1 pr
  -- 4a. `scs_denot segs mem E scs`: peel the batch, then normalize and close
  let scsTy ← g₀.withContext (mkAppM ``scs_denot #[segs, mem, ee, scs])
  let scsTac ← `(tactic|
    (simp (config := { failIfUnchanged := false }) only
       [scs_denot_cons, scs_denot_nil, and_true, true_and]
     sym_split_ands
     all_goals (try
       first
       | trivial
       | (try (unfold sc_denot)
          try sym_norm
          try sym_sc_auto))))
  let (scsProof, scsGoals) ← runOn g₀ scsTy scsTac
  let (_, g₁) ← g₀.note `Hsc scsProof (some scsTy)
  -- 4b. `pins_ok E regs ps`: peel the pin list, then `sym_pin_auto` per pin
  let pinsTy ← g₁.withContext (mkAppM ``pins_ok #[ee, regs, ps])
  let pinsTac ← `(tactic|
    (simp (config := { failIfUnchanged := false }) only
       [pins_ok_cons, pins_ok_nil, and_true, true_and, edenot, Eplus, ridx,
        List.getD, List.nil_append, List.cons_append, List.append_nil,
        Prod.fst, Prod.snd]
     sym_split_ands
     all_goals (try (first | rfl | sym_pin_auto | assumption))))
  let (pinsProof, pinsGoals) ← runOn g₁ pinsTy pinsTac
  let (_, g₂) ← g₁.note `Hpins pinsProof (some pinsTy)
  -- 4c. `st_ok E mem rom ss0 ms`, built by application to `st_ok_mk`
  let ofIntPc ← g₂.withContext (mkAppM ``BitVec.ofInt #[mkNatLit 64, pcE])
  let msNew ← g₂.withContext (mkAppM ``mkst #[regs, ofIntPc, mem, rom])
  let hmsEqTy ← g₂.withContext (mkAppM ``Eq #[ms, msNew])
  let (hmsEq, stGoals) ← runOn g₂ hmsEqTy (← `(tactic| rfl))
  let hregsProof ← g₂.withContext
    (mkAppM ``regs_ok_pins #[ee, ps, mkConst ``sr_id, regs,
      ← mkAppM ``regs_ok_Eplus #[regs, ← mkAppM ``List.append #[pvals, rvals]], pinsProof])
  let stProof ← g₂.withContext
    (mkAppM ``st_ok_mk #[ee, mem, rom, pcE, ← mkAppM ``sr_pins #[ps, mkConst ``sr_id],
      mkNatLit (32 + k), regs, ms, hmsEq, hregsProof])
  let stTy ← g₂.withContext (mkAppM ``st_ok #[ee, mem, rom, ss0, ms])
  let (_, g₃) ← g₂.note `Hst stProof (some stTy)
  -- 5. the executor's equation, then `sym_exec_ex`
  let pairVal ← mkAppM ``Prod.mk #[ss1, scs]
  let eqTy ← g₃.withContext (mkAppM ``Eq #[app, pairVal])
  let (eqProof, eqGoals) ← runOn g₃ eqTy (← `(tactic| rfl))
  let exProof ← g₃.withContext (mkAppM ``sym_exec_ex
    #[segs, fuel, dirs, rds, ss0, nilAcc, ss1, scs, ee, mem, rom, ms, eqProof, scsProof,
      stProof])
  let exTy ← inferType exProof
  let (_, g₄) ← g₃.note `HmsEx exProof (some exTy)
  -- 6. package
  let hmsExId := mkIdentFrom (← getRef) `HmsEx
  let hmsId := mkIdentFrom (← getRef) (if onlyEx then `Hms else `Hms)
  let tac ← if onlyEx then
    `(tactic|
      (obtain ⟨$R, $H, $hmsId⟩ := $hmsExId
       try (simp (config := { failIfUnchanged := false }) only
              [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot] at *)))
  else
    `(tactic|
      (obtain ⟨$R, $H, $hmsId⟩ := $hmsExId
       chain_mst <;>
         (first
          | exact $hmsId
          | (simp (config := { failIfUnchanged := false }) only
               [sym_state.s_pc, sym_state.s_regs, sym_state.s_log, mem_denot]
             try sym_mem_norm
             norm_pc
             sym_pc_lit))))
  let rem ← Lean.Elab.Tactic.run g₄ (evalTactic tac)
  setGoals (scsGoals ++ pinsGoals ++ stGoals ++ eqGoals ++ rem)

/-- **Execute a straight line reflectively.**

    Leaves, in order: the block's side conditions (one goal per entry of the
    batch the executor emitted, `sym_norm`/`sym_sc_auto` having closed
    whatever needed no input — empty for a pure ALU block), one goal per pin,
    and then the original chain goal advanced to the state the executor
    stopped at.

    `segs, fuel, dirs, rds, ps, pvals, rvals, R, H` — see the file header for
    what each argument means.  `R` and `H` are the NAMES to bind the exit
    register file and its `regs_ok` fact to. -/
elab "sym_block" segs:term "," fuel:term "," dirs:term "," rds:term "," ps:term ","
    pvals:term "," rvals:term "," R:ident "," H:ident : tactic => do
  let segsE ← Lean.Elab.Term.elabTermEnsuringType segs (listTy (mkConst ``Segment))
  let fuelE ← Lean.Elab.Term.elabTermEnsuringType fuel (mkConst ``Nat)
  let dirsE ← Lean.Elab.Term.elabTermEnsuringType dirs (listTy (mkConst ``Bool))
  let rdsE ← Lean.Elab.Term.elabTermEnsuringType rds (listTy (mkConst ``expr))
  let psE ← Lean.Elab.Term.elabTermEnsuringType ps
    (listTy (prodTy (mkConst ``reg) (mkConst ``expr)))
  let pvalsE ← Lean.Elab.Term.elabTermEnsuringType pvals (listTy (mkConst ``word))
  let rvalsE ← Lean.Elab.Term.elabTermEnsuringType rvals (listTy (mkConst ``word))
  symBlockCore none segsE fuelE dirsE rdsE psE pvalsE rvalsE R H false

/-! ## 7. `sym_block_ex` — the FACTORABLE variant

    `sym_block` ends by destructing the executor's conclusion INTO THE GOAL
    IT IS STANDING IN: the exit register file becomes a goal-local variable
    and the block's `msteps` is immediately spent by `chain_mst`.  That is
    right for a straight line kept in one goal, and wrong for anything one
    wants to prove ONCE and reuse — a per-iteration loop-body lemma

      theorem body : <pre> ->
        exists R, <facts about R> ∧ msteps segs ms (mkst R pc' mem' rom)

    cannot be closed with `sym_block` at all, because instantiating the
    existential with the tactic's local `R` takes it out of scope.
    (`DrainAlg`'s `Hread` hypothesis and a Hoare loop rule both ask for
    exactly that statement.)

    `sym_block_ex` moves the destruct OUT of the tactic: it runs the same
    executor over the same block and leaves

      R   : BvMap word          the exit register file
      H   : regs_ok E sr_exit R    every exit register, symbolically
      Hms : msteps segs ms (mkst R (ofInt 64 pc') mem' rom)

    in the CONTEXT, and does not touch the goal.  The caller then supplies
    `R` as their own existential's witness and reads whatever facts their
    statement promises out of `H` with `sym_regs` — the same reader
    `sym_block`'s callers already use.  Both routes go through the same
    `SymExec.sym_exec_ex`; only the packaging differs.

    ARGUMENTS.  As `sym_block`, plus:

    - `ms`  — the block's ENTRY machine state, given EXPLICITLY rather than
      found in the goal (there is no chain goal to find it in, and in a
      factored statement the exit state also matches the `mkst` pattern).  It
      must be spelled `mkst regs (ofInt 64 pc) mem rom`; that is the spelling
      `sym_pc_Z` produces at a call site and the one to write in a factored
      lemma's statement.
    - `Hms` — the name to bind the block's `msteps` to.

    THE EXIT MEMORY.  `Hms`'s target memory is the log's denotation, reduced
    by `simp`: for a block with no stores (the common case for a loop body
    that only computes) that is literally the entry `mem`, and for a block
    with stores it is the `wbytes` chain the log denotes, which is what the
    factored statement should say.  Unlike `sym_block` this is NOT put
    through `sym_mem_norm` — normalizing a hypothesis and normalizing a goal
    are different tactics, and the caller's own statement fixes the spelling
    anyway. -/
elab "sym_block_ex" segs:term "," ms:term "," fuel:term "," dirs:term "," rds:term ","
    ps:term "," pvals:term "," rvals:term "," R:ident "," H:ident "," Hms:ident : tactic => do
  let g₀ ← getMainGoal
  let segsE ← Lean.Elab.Term.elabTermEnsuringType segs (listTy (mkConst ``Segment))
  let msE ← Lean.Elab.Term.elabTermEnsuringType ms (mkConst ``machine_state)
  let fuelE ← Lean.Elab.Term.elabTermEnsuringType fuel (mkConst ``Nat)
  let dirsE ← Lean.Elab.Term.elabTermEnsuringType dirs (listTy (mkConst ``Bool))
  let rdsE ← Lean.Elab.Term.elabTermEnsuringType rds (listTy (mkConst ``expr))
  let psE ← Lean.Elab.Term.elabTermEnsuringType ps
    (listTy (prodTy (mkConst ``reg) (mkConst ``expr)))
  let pvalsE ← Lean.Elab.Term.elabTermEnsuringType pvals (listTy (mkConst ``word))
  let rvalsE ← Lean.Elab.Term.elabTermEnsuringType rvals (listTy (mkConst ``word))
  symBlockCore (some msE) segsE fuelE dirsE rdsE psE pvalsE rvalsE R H true

/-! ## 8. Consuming a factored block -/

/-- Attach a factored block's `msteps` to the chain goal at the call site.
    This is the other half of moving the `destruct` outwards: `sym_block` did
    `chain_mst; [exact Hms | ]; norm_pc` itself, and a caller who got their
    `msteps` from a LEMMA instead does it here.

    `sym_pc_Z` first because the chain goal's pc is a numeral literal and a
    factored statement's is `BitVec.ofInt 64 _` , then `norm_pc` / `sym_pc_lit` to put the pc back
    into the literal form the next fetch lemma wants.
    So the whole call is two lines:

      obtain ⟨R, Hfacts, Hms⟩ := block_lemma …
      sym_chain Hms
    and the block's results are read out of `Hfacts` — directly if the
    factored statement promised `getr R r = v` facts (the usual choice), or
    with `sym_regs Hfacts` if it exported the whole `regs_ok` against a
    reduced `s_regs` literal, which is the same reader a `sym_block` call
    site uses. -/
macro "sym_chain " Hms:term : tactic =>
  `(tactic|
    (sym_pc_Z
     chain_mst <;> (first | exact $Hms | (norm_pc; sym_pc_lit))))

/-! ## 9. -/

/-- `list_len` counts a literal list without reducing its elements. -/
example : list_len ([1, 2, 3] : List Nat) = 3 := rfl
example : list_len ([] : List word) = 0 := rfl

/-- The `mv` identity on a symbolic word. -/
example (x : word) : alu64 .ADD x (BitVec.ofInt 64 0) = x := alu64_add_0 x

/-- The `addiw` normal form: the executor's `EAluw ADD a (.ELit k)` spelling
    lands exactly on `v_addiw`. -/
example (a : word) (k : Int) :
    sext 64 (alu32 .ADD (low32 a) (low32 (BitVec.ofInt 64 k))) = v_addiw a k :=
  aluw_addi_lit a k

/-- The two address projections, at a literal and at a symbolic base. -/
example (E : env) (k : Int) : adenot E (SA .SBLit k) = BitVec.ofInt 64 k :=
  adenot_lit E k

example (E : env) (n : Nat) (k : Int) :
    adenot E (SA (.SBVar n) k) = BitVec.ofInt 64 ((E n).toNat + k) :=
  adenot_var E n k

/-- A pin list really does pin: the `(sp, EVar 32)` pin makes register 2 read
    the caller's first value. -/
example (regs : BvMap word) :
    regs_ok (Eplus regs [getr regs 2]) (sr_pins [(2, .EVar 32)] sr_id) regs := by
  refine regs_ok_pins _ _ _ _ (regs_ok_Eplus regs [getr regs 2]) ?_
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp only [Prod.fst, Prod.snd, edenot_var, Eplus, ridx]
  rfl

/-! ### The fixture, and what the executor does with it

    A two-instruction block (`addi a0,a0,1` twice) in an 8-byte executable
    segment, run for 4 steps from `0x100`.  The executor stops at `0x108`
    (the first byte outside the segment), so `sym_block` leaves the
    advanced chain goal `lh_next` at `0x108` to the caller.

    The three `rfl` checks pin the executor's behaviour through the kernel
    directly; the two `sym_block` examples then run the SAME block through
    the reflective entry point, which is what the tactic layer adds. -/

namespace Smoke

/-- `addi a0, a0, 1` (0x00150513), little-endian, twice. -/
def txt : Segment where
  seg_base := 0x100
  seg_size := 8
  seg_perms := "r-x"
  seg_bytes := ["13051500", "13051500"]

def segs : List Segment := [txt]

/-- The loop head the block is expected to reach. -/
def LH (ms : machine_state) : Prop := ms.ms_pc_val = BitVec.ofInt 64 0x108

/-- The entry symbolic state: every register is its own variable, empty log. -/
def ss0 : sym_state := ⟨0x100, sr_pins [] sr_id, [], 32⟩

/-- The executor stops at `0x108`. -/
example : (sym_exec segs 4 ([] : List Bool) ([] : List expr) ss0
    ([] : List sidecond)).1.s_pc = (0x108 : Int) := rfl

/-- ... it stored nothing, so the log is still empty ... -/
example : (sym_exec segs 4 ([] : List Bool) ([] : List expr) ss0
    ([] : List sidecond)).2 = ([] : List sidecond) := rfl

/-- ... and `a0` (register 10) holds `a0 + 2`: the two `addi`'s are folded. -/
example : (sym_exec segs 4 ([] : List Bool) ([] : List expr) ss0
    ([] : List sidecond)).1.s_regs.getD 10 (.ELit 0)
      = .EAlu .ADD (.EVar 10) (.ELit 2) := rfl

/-- One reflective block, all the way to `lh_next`: `sym_block` executes the
    two `addi`'s, spends the resulting `msteps` on `chain_mst`, and leaves
    the `lh_next` goal at `0x108`, which the `mst_refl` witness closes. -/
example (regs : BvMap word) (mem rom : word → Option byte) :
    StreamSim.lh_next segs LH (mkst regs (BitVec.ofInt 64 0x100) mem rom) := by
  sym_block segs, 4, ([] : List Bool), ([] : List expr), ([] : List (reg × expr)),
    ([] : List word), ([] : List word), R, H
  exact ⟨_, msteps.mst_refl _, rfl⟩

/-- The same block, factored: `sym_block_ex` runs it and leaves `R`, `H` and
    `Hms` in the context without touching the caller's statement. -/
example (regs : BvMap word) (mem rom : word → Option byte) :
    ∃ (R : BvMap word) (pc' : word), msteps segs (mkst regs (BitVec.ofInt 64 0x100) mem rom)
      (mkst R pc' mem rom) := by
  sym_block_ex segs, (mkst regs (BitVec.ofInt 64 0x100) mem rom), 4, ([] : List Bool),
    ([] : List expr), ([] : List (reg × expr)), ([] : List word), ([] : List word), R, H, Hms
  exact ⟨R, BitVec.ofInt 64 0x108, Hms⟩

/-! ### DEFERRED — two further examples

    These two are NOT stated, and are recorded here rather than left as
    holes:

    1. READING A REGISTER BACK.  The draft's

         example (regs : BvMap word) (mem rom : word → Option byte) :
             ∃ (R : BvMap word),
               getr R 10 = v_add (v_add (getr regs 10) (BitVec.ofInt 64 1))
                 (BitVec.ofInt 64 1) := by
           sym_block_ex segs, (mkst regs (BitVec.ofInt 64 0x100) mem rom), 4, …,
             R, H, Hms
           refine ⟨R, ?_⟩
           sym_regs H
           rfl

       has two problems.  Its STATEMENT is wrong for this fixture: the
       executor folds the two `addi`'s into one, so `getr R 10` is
       `alu64 .ADD (getr regs 10) (BitVec.ofInt 64 2)` (which `alu_add`
       turns into `v_add (getr regs 10) 2`), not `v_add (v_add a0 1) 1`
       — see the third `rfl` check above.  And `sym_regs`'s simp set is written for the
       `List.getD` spelling of `sr_get`, while the executor's register file
       indexes with `regs[i]?.getD`; the residual goal after `sym_regs H`
       still contains `if (10 == 0) = true then … else […][BitVec.toNat 10]?.getD …`,
       so `rfl` fails.  Fixing it means adding the `getElem?`/`Option.getD`
       lemmas (and `bv_eqb`'s `decide` reduction) to `sym_regs`'s set.

    2. `sym_chain` WITH A RAW `msteps` PREMISE.  The draft's fourth example
       stated its `Hms` premise as a plain `msteps segs (mkst regs 0x100 …)
       (mkst regs 0x104 …)` and then called `sym_block` under it.  A plain
       `msteps` goal is not one of the chain relations `chain_mst`
       enumerates, so the only alternative that fires is
       `msteps_trans`, which leaves `msteps segs (mkst R 0x104 …) (mkst regs
       0x104 …)` — the reversed tail — instead of advancing the goal.
       `sym_chain` is meant for the `to_*` / `lh_next` relation goals that
       `sym_block`'s own examples produce, which is what the first example
       above exercises. -/

end Smoke
end LinuxSem.Common.SymTac
