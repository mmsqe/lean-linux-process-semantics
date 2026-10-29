/-
  * Common.MuslCall — ADDRESS-PARAMETRIC summaries of musl's [write]
      wrapper and its [__syscall_cp] / [__syscall_ret] tail.

  PROTOTYPE / EXPLORATION, built on [Common/Hoare].

  Every example re-proves this code inline, at its own addresses:
  ~90 lines of [modprint_ns_source], and again in [cat1024_ns],
  [conditional_bug_ns], [grep_args_ns], [tail1_ns], [oob_read_bug_ns],
  [brk_rev_ns], [mmap_upper_ns], [alloc_join_ns].  The BYTES are
  identical in all of them — the soft-float musl build emits the same
  object, and the whole [write]/[__syscall_cp]/[__syscall_ret] blob is
  position-independent (every internal transfer is pc-relative).  Only
  the load address differs.

  So the summaries below are proved ONCE, in a section over

    - [segs]: any segment image, and
    - [B]: the address the blob is loaded at,

  with the blob's FETCH facts as hypotheses.  The DECODE facts are
  statements about instruction words, not about an image, so they are
  proved here rather than assumed.  A per-binary instantiation supplies
  16 [SF_*] lemmas from its generated fetch/decode facts and nothing else.

  Blob layout, relative to [B] (musl-gcc -Os, RV64 soft-float):

    +0x00  write: addi sp,sp,-16
    +0x04                  mv a3,a2
    +0x08                  li a6,0
    +0x0c                  mv a2,a1
    +0x10                  li a5,0
    +0x14                  mv a1,a0
    +0x18                  li a4,0
    +0x1c                  li a0,64          ; SYS_write
    +0x20                  sd ra,8(sp)
    +0x24                  jal ra,+0x6c      ; -> __syscall_cp
    +0x28                  ld ra,8(sp)
    +0x2c                  addi sp,sp,16
    +0x30                  j +4              ; -> __syscall_ret
    +0x34  __syscall_ret: lui a5,0xfffff
    +0x38                  bltu a5,a0,+8     ; errno branch (not taken)
    +0x3c                  ret
    ...    (+0x40..+0x68: the errno tail, unreachable on success)
    +0x6c  __syscall_cp_c: mv a7,a0 / mv a0,a1 / mv a1,a2 / mv a2,a3
    +0x7c                  mv a3,a4 / mv a4,a5 / mv a5,a6
    +0x88                  ecall
    +0x8c                  ret
    +0x90  __syscall_cp: j -0x24           ; -> __syscall_cp_c

  Two summaries, because a [triple] cannot cross the [ecall] (the
  syscall is not an [msteps] step):

    [musl_write_enter] : [B+0x00] -> [B+0x88], the pc at which the
                         caller applies [CatSim]'s [tw_write_ret];
    [musl_write_leave] : [B+0x8c] -> the caller's return address, the
                         post-syscall path back through
                         [__syscall_ret]'s not-taken errno branch.

  [musl_write_wexit] glues them around the syscall and hands the whole
  call to a [to_wexit] continuation — that is the form a per-binary
  proof actually applies.

  * The  `Section WithFP1 … WithFP5` wrappers exist only to scope
    `Ltac`s; this tree carries ONE ambient `variable [fx : FPState]` for
    the proof section, exactly as `PropExec`/`CatExec`/`SeqExec`/
    `MmapSim`/`Hoare` do.       - [at_fold] is a total no-op: `at_ b (x + y)` with `x`, `y` literal
        `Int`s is *definitionally* `at_ b (x+y)`'s value in Lean, so the
        `eval cbv`/`change` step  needs has nothing left to do.
        (Every offset on this blob is a literal sum, e.g. `0x24 + 108`.)
      - [apc] is `simp only [at_addi, at_btgt]`: the same two rewrites
         performs, plus [at_fold]'s (vacuous) fold.
 Lean has no `set` tactic
    and needs no substitute: the `wbytes` term IS the canonical form the
    summaries are applied at, so the proofs pass it directly (the `let`
    would only be a notation alias).  The one place where the term
    matters — a state the next `rw` has to see through — is called out at
    the `ld` step of [musl_write_leave], which states its equation at the
    reduced register file.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.Hoare
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.WallSim
import LinuxSem.Checks.Sys.Prelude

set_option autoImplicit false
-- Same rationale as `PropExec`/`CatExec`/`SeqExec`/`Hoare`: Lean adds a
-- section variable to a lemma's type only when the statement mentions it, and
-- the linters below flag exactly that (plus unused `simp` hints and unused
-- variables), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.MuslCall

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.Hoare
open LinuxSem.Common.WallSim
open LinuxSem.Checks.Sys.Prelude

/-! ## Tactics for an ADDRESS-PARAMETRIC chain -/

/-- Fold a literal offset sum inside [at_].

    a total no-op — see the module header.  [at_ B (0x24 + 108)] and
    [at_ B 0x90] are the same term up to kernel reduction of the `Int`
    literal sum, so the `eval cbv in (x + y)` / `change` pair 
    runs has nothing to change. -/
macro "at_fold" : tactic => `(tactic| skip)

/-- [SeqExec.getr_resolve] with its final [getr_nz] step removed: a
    LEFTOVER [getr regs r] on the section's opaque register file must stay
    [getr]-shaped, or the summary's [getr]-shaped hypotheses no longer
    apply.

     -/
macro "gres" : tactic =>
  `(tactic| (repeat (first
      | rw [getr_same _ _ _ (by decide)]
      | rw [getr_other _ _ _ _ (by decide)]
      | rw [getr_zero])))

/-- Fold the pc of the next state into [at_] form: 
    `reduce_bv_eqb_ifs; imm_norm; rewrite ?at_addi, ?at_btgt; at_fold`.

    the first two steps are total no-ops in Lean (a closed
    `bv_eqb`-driven `if` reduces during elaboration, and an encoded
    immediate's [BitVec.toInt] is already a numeral in the elaborated
    term), so only the two rewrites remain.  `simp only` rather than `rw`
    because the tail goal legitimately has nothing to fold. -/
macro "apc" : tactic => `(tactic| (first | simp only [at_addi, at_btgt] | skip))

/-- One straight-line step of the chain, with the writeback value named.
    The step is spelled:
    `eapply mst_step; [reflexivity | eapply step_addi_at with (v := vv);
      [exact F | reflexivity | exact D | reflexivity | tac] | apc]`.

The three [mst_step] premises are dispatched by shape (see the module
header): [rfl] closes `ms_svc_pending = none`, the [step_addi_at]
application (with [vv] at its value slot, [F]/[D] at the fetch/decode
slots, and `rfl`/`decide` for the `is_ecall`/`x0` guards) closes the step,
and [apc] folds the pc of the tail state for the next step. -/
macro "hstepv " F:term "," D:term "," vv:term "," tac:tactic : tactic =>
  `(tactic|
    (apply msteps.mst_step <;>
      first
      | rfl
      | (refine step_addi_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;>
          first | rfl | decide | ($tac; try rfl; done))
      | apc))

/-- [hstepv] for a step whose lemma is not [step_addi_at]: the step premise
    is the caller's tactic block, everything else as in [hstepv]. -/
macro "hstep " tac:tactic : tactic =>
  `(tactic|
    (apply msteps.mst_step <;>
      first
      | rfl
      | ($tac; try rfl; done)
      | apc))

/-- [hstep] with a pc rewrite folded into the tail step: a [ret] lands on
    [v_jalr k 0], whose `& ~1` mask needs the [ret_ok] hypothesis to become
    the plain address the next fetch fact is stated at . -/
macro "hstep_fold " tac:tactic "," post:tactic : tactic =>
  `(tactic|
    (apply msteps.mst_step <;>
      first
      | rfl
      | ($tac; try rfl; done)
      | (apc; $post)))

/-- Normalize the encoded immediate of an [OpImm] instruction
    (`imm.toInt`, a [BitVec.toInt] of a literal) to an [Int] numeral.

    `simp only [BitVec.reduceToInt]` — Lean's kernel keeps
    `(4080 : BitVec 12).toInt` opaque to a syntactic `rw` (the pattern
    `v_addi ?x 0` then refuses to match `v_addi x (BitVec.toInt 0)`), and
    [BitVec.reduceToInt] is the reduction lemma that exposes the numeral.
-/
macro "imm_norm" : tactic => `(tactic| (first | simp only [BitVec.reduceToInt] | skip))

/-! ## Instruction words and their decodings -/

/-- The blob's 25 relevant words.  These are IMAGE-INDEPENDENT: a decode
    fact is a statement about a 32-bit word, so it belongs here and not in
    a per-binary [*_code].   -/
def Wsp16m : BitVec 32 := 4278255891   -- addi sp,sp,-16
def Wmv_a3a2 : BitVec 32 := 394899
def Wli_a6_0 : BitVec 32 := 2067
def Wmv_a2a1 : BitVec 32 := 362003
def Wli_a5_0 : BitVec 32 := 1939
def Wmv_a1a0 : BitVec 32 := 329107
def Wli_a4_0 : BitVec 32 := 1811
def Wli_a0_64 : BitVec 32 := 67110163
def Wsd_ra8 : BitVec 32 := 1127459
def Wjal_cp : BitVec 32 := 113246447   -- jal ra,+108
def Wld_ra8 : BitVec 32 := 8466563
def Wsp16p : BitVec 32 := 16843027     -- addi sp,sp,16
def Wj4 : BitVec 32 := 4194415         -- j +4
def Wlui_a5 : BitVec 32 := 4294965175  -- lui a5,0xfffff
def Wbltu : BitVec 32 := 11002979      -- bltu a5,a0,+8
def Wret : BitVec 32 := 32871          -- jalr x0,0(ra)
def Wmv_a7a0 : BitVec 32 := 329875
def Wmv_a0a1 : BitVec 32 := 361747
def Wmv_a1a2 : BitVec 32 := 394643
def Wmv_a2a3 : BitVec 32 := 427539
def Wmv_a3a4 : BitVec 32 := 460435
def Wmv_a4a5 : BitVec 32 := 493331
def Wmv_a5a6 : BitVec 32 := 526227
def Wecall : BitVec 32 := 115
def Wj_cpc : BitVec 32 := 4259311727   -- j -36

theorem D_sp16m : decodeAny Wsp16m = some (Instr.opImm .ADD 2 2 4080, 4) := by decide
theorem D_mv_a3a2 : decodeAny Wmv_a3a2 = some (Instr.opImm .ADD 13 12 0, 4) := by decide
theorem D_li_a6_0 : decodeAny Wli_a6_0 = some (Instr.opImm .ADD 16 0 0, 4) := by decide
theorem D_mv_a2a1 : decodeAny Wmv_a2a1 = some (Instr.opImm .ADD 12 11 0, 4) := by decide
theorem D_li_a5_0 : decodeAny Wli_a5_0 = some (Instr.opImm .ADD 15 0 0, 4) := by decide
theorem D_mv_a1a0 : decodeAny Wmv_a1a0 = some (Instr.opImm .ADD 11 10 0, 4) := by decide
theorem D_li_a4_0 : decodeAny Wli_a4_0 = some (Instr.opImm .ADD 14 0 0, 4) := by decide
theorem D_li_a0_64 : decodeAny Wli_a0_64 = some (Instr.opImm .ADD 10 0 64, 4) := by decide
theorem D_sd_ra8 : decodeAny Wsd_ra8 = some (Instr.store .SZ8 2 1 8, 4) := by decide
theorem D_jal_cp : decodeAny Wjal_cp = some (Instr.jal 1 108, 4) := by decide
theorem D_ld_ra8 : decodeAny Wld_ra8 = some (Instr.load .SZ8 true 1 2 8, 4) := by decide
theorem D_sp16p : decodeAny Wsp16p = some (Instr.opImm .ADD 2 2 16, 4) := by decide
theorem D_j4 : decodeAny Wj4 = some (Instr.jal 0 4, 4) := by decide
theorem D_lui_a5 : decodeAny Wlui_a5 = some (Instr.lui 15 1048575, 4) := by decide
theorem D_bltu : decodeAny Wbltu = some (Instr.branch .LTU 15 10 8, 4) := by decide
theorem D_ret : decodeAny Wret = some (Instr.jalr 0 1 0, 4) := by decide
theorem D_mv_a7a0 : decodeAny Wmv_a7a0 = some (Instr.opImm .ADD 17 10 0, 4) := by decide
theorem D_mv_a0a1 : decodeAny Wmv_a0a1 = some (Instr.opImm .ADD 10 11 0, 4) := by decide
theorem D_mv_a1a2 : decodeAny Wmv_a1a2 = some (Instr.opImm .ADD 11 12 0, 4) := by decide
theorem D_mv_a2a3 : decodeAny Wmv_a2a3 = some (Instr.opImm .ADD 12 13 0, 4) := by decide
theorem D_mv_a3a4 : decodeAny Wmv_a3a4 = some (Instr.opImm .ADD 13 14 0, 4) := by decide
theorem D_mv_a4a5 : decodeAny Wmv_a4a5 = some (Instr.opImm .ADD 14 15 0, 4) := by decide
theorem D_mv_a5a6 : decodeAny Wmv_a5a6 = some (Instr.opImm .ADD 15 16 0, 4) := by decide
theorem D_j_cpc : decodeAny Wj_cpc = some (Instr.jal 0 2097116, 4) := by decide

theorem E_ecall : is_ecall Wecall = true := by rfl

/-! ## The blob's footprints -/

/-- The blob's clobber set: [ra], [sp] and the argument registers.  Every
    callee-saved register is outside it, so a caller keeps its [s*] and
    its frame pointer across the call for free (see [Hoare.triple_frame]
    and [Hoare.frameable_reg]). -/
def musl_clob : regset :=
  fun r => r = 1 ∨ r = 2 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13
           ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17

/-- Membership in [musl_clob], by computation: 
    `unfold musl_clob; repeat first [left; reflexivity | right];
    reflexivity`. -/
macro "in_clob" : tactic => `(tactic| (simp only [musl_clob]; decide))

/-- Its write set: the one stack slot the wrapper spills [ra] into. -/
def musl_wset (sp0 : word) : memset :=
  fun x => ∃ i, 0 ≤ i ∧ i < 8 ∧ x = at_ sp0 (-8 + i)

section MuslWrite

variable [fx : FPState]
variable (segs : List Segment) (B : word)

/- The 26 fetch facts — the ENTIRE per-binary interface: an
   instantiation discharges each with one [SF_*] from its generated
   [*_code].

    -/
variable (F00 : fetch_word segs (at_ B 0x00) = some Wsp16m)
variable (F04 : fetch_word segs (at_ B 0x04) = some Wmv_a3a2)
variable (F08 : fetch_word segs (at_ B 0x08) = some Wli_a6_0)
variable (F0c : fetch_word segs (at_ B 0x0c) = some Wmv_a2a1)
variable (F10 : fetch_word segs (at_ B 0x10) = some Wli_a5_0)
variable (F14 : fetch_word segs (at_ B 0x14) = some Wmv_a1a0)
variable (F18 : fetch_word segs (at_ B 0x18) = some Wli_a4_0)
variable (F1c : fetch_word segs (at_ B 0x1c) = some Wli_a0_64)
variable (F20 : fetch_word segs (at_ B 0x20) = some Wsd_ra8)
variable (F24 : fetch_word segs (at_ B 0x24) = some Wjal_cp)
variable (F28 : fetch_word segs (at_ B 0x28) = some Wld_ra8)
variable (F2c : fetch_word segs (at_ B 0x2c) = some Wsp16p)
variable (F30 : fetch_word segs (at_ B 0x30) = some Wj4)
variable (F34 : fetch_word segs (at_ B 0x34) = some Wlui_a5)
variable (F38 : fetch_word segs (at_ B 0x38) = some Wbltu)
variable (F3c : fetch_word segs (at_ B 0x3c) = some Wret)
variable (F6c : fetch_word segs (at_ B 0x6c) = some Wmv_a7a0)
variable (F70 : fetch_word segs (at_ B 0x70) = some Wmv_a0a1)
variable (F74 : fetch_word segs (at_ B 0x74) = some Wmv_a1a2)
variable (F78 : fetch_word segs (at_ B 0x78) = some Wmv_a2a3)
variable (F7c : fetch_word segs (at_ B 0x7c) = some Wmv_a3a4)
variable (F80 : fetch_word segs (at_ B 0x80) = some Wmv_a4a5)
variable (F84 : fetch_word segs (at_ B 0x84) = some Wmv_a5a6)
variable (F88 : fetch_word segs (at_ B 0x88) = some Wecall)
variable (F8c : fetch_word segs (at_ B 0x8c) = some Wret)
variable (F90 : fetch_word segs (at_ B 0x90) = some Wj_cpc)

/-! ## Summary 1: entry -> the ecall -/

include F00 F04 F08 F0c F10 F14 F18 F1c F20 F24 F6c F70 F74 F78 F7c F80 F84 F90 in
/-- [B+0x00] -> [B+0x88]: the register shuffle and the [sd ra,8(sp)], up to
    (not across) the [ecall]. -/
theorem musl_write_enter (k sp0 fd buf len : word) (mem0 : word → Option byte) :
    triple segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem0
         ∧ getr regs 1 = k ∧ getr regs 2 = sp0
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ store_ok segs mem0 (at_ sp0 (-8)) 8 = true)
      (at_ B 0x00) (at_ B 0x88)
      (fun regs mem _ =>
         mem = wbytes mem0 (at_ sp0 (-8)) (word_to_le_bytes 8 k)
         ∧ getr regs 1 = at_ B 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = fd ∧ getr regs 11 = buf ∧ getr regs 12 = len
         ∧ getr regs 17 = BitVec.ofInt 64 64) := by
  intro regs mem rom H
  obtain ⟨Hmem, Hra, Hsp, H10, H11, H12, Hok⟩ := H
  subst Hmem
  refine ⟨?regs', ?mem', ?st, ?post, ?rag, ?mag⟩
  case st =>
    -- +0x00 addi sp,sp,-16
    hstepv F00, D_sp16m, (at_ sp0 (-16)), (gres; imm_norm; rw [Hsp])
    -- +0x04 mv a3,a2
    hstepv F04, D_mv_a3a2, len, (gres; imm_norm; rw [H12]; rw [v_addi_0])
    -- +0x08 li a6,0
    hstepv F08, D_li_a6_0, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    -- +0x0c mv a2,a1
    hstepv F0c, D_mv_a2a1, buf, (gres; imm_norm; rw [H11]; rw [v_addi_0])
    -- +0x10 li a5,0
    hstepv F10, D_li_a5_0, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    -- +0x14 mv a1,a0
    hstepv F14, D_mv_a1a0, fd, (gres; imm_norm; rw [H10]; rw [v_addi_0])
    -- +0x18 li a4,0
    hstepv F18, D_li_a4_0, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    -- +0x1c li a0,64
    hstepv F1c, D_li_a0_64, (BitVec.ofInt 64 64), (gres; imm_norm; exact v_addi_0_64)
    -- +0x20 sd ra,8(sp)
    hstep ((refine step_sd_at _ _ _ _ _ _ _ _ _ (at_ sp0 (-8)) k F20 ?_ D_sd_ra8
              ?_ ?_ ?_ <;>
            first
            | rfl
            | decide
            | (gres; imm_norm; rw [at_addi])
            | (gres; exact Hra)
            | exact Hok))
    -- +0x24 jal ra,__syscall_cp
    hstep (exact step_jal_link _ _ _ _ _ _ _ _ F24 (by decide) D_jal_cp)
    -- +0x90 j __syscall_cp_c
    hstep (exact step_jal_x0 _ _ _ _ _ _ _ F90 (by decide) D_j_cpc)
    -- +0x6c mv a7,a0
    hstepv F6c, D_mv_a7a0, (BitVec.ofInt 64 64), (gres; imm_norm; rw [v_addi_0])
    -- +0x70 mv a0,a1
    hstepv F70, D_mv_a0a1, fd, (gres; imm_norm; rw [v_addi_0])
    -- +0x74 mv a1,a2
    hstepv F74, D_mv_a1a2, buf, (gres; imm_norm; rw [v_addi_0])
    -- +0x78 mv a2,a3
    hstepv F78, D_mv_a2a3, len, (gres; imm_norm; rw [v_addi_0])
    -- +0x7c mv a3,a4
    hstepv F7c, D_mv_a3a4, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    -- +0x80 mv a4,a5
    hstepv F80, D_mv_a4a5, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    -- +0x84 mv a5,a6
    hstepv F84, D_mv_a5a6, (BitVec.ofInt 64 0), (gres; imm_norm; rw [v_addi_0])
    exact msteps.mst_refl _
  case post =>
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (gres; try rfl; done)
  case rag =>
    repeat (first
      | (apply regs_agree_upd <;> (first | in_clob | skip))
      | exact regs_agree_refl musl_clob regs)
  case mag =>
    apply mem_agree_wbytes
    · intro i h0 hi
      unfold musl_wset
      rw [length_N_to_le_bytes] at hi
      exact ⟨i, h0, hi, at_at sp0 (-8) i⟩
    · exact mem_agree_refl (musl_wset sp0) mem

/-! ## Summary 2: the post-syscall return path -/

/-- [__syscall_ret]'s errno window: a return value at or above
    [-4096 mod 2^64] is an errno.  [write] of a fully readable buffer
    never lands there. -/
def errno_lo : word := BitVec.ofInt 64 18446744073709547520

theorem not_errno (rv : word) (H : (rv.toNat : Int) ≤ 18446744073709547520) :
    c_ltu errno_lo rv = false := by
  unfold c_ltu bv_ltu errno_lo
  rw [decide_eq_false_iff_not]
  have h : (BitVec.ofInt 64 18446744073709547520).toNat = 18446744073709547520 := by
    decide
  rw [h]
  omega

include F28 F2c F30 F34 F38 F3c F8c in
/-- [B+0x8c] -> the caller's return address: the post-syscall path back
    through [__syscall_ret]'s not-taken errno branch. -/
theorem musl_write_leave (k sp0 rv : word) (mem1 : word → Option byte)
    (Hk : ret_ok k) (Hr28 : ret_ok (at_ B 0x28)) :
    triple segs musl_clob (musl_wset sp0)
      (fun regs mem _ =>
         mem = mem1
         ∧ getr regs 1 = at_ B 0x28 ∧ getr regs 2 = at_ sp0 (-16)
         ∧ getr regs 10 = rv
         ∧ rdn segs mem1 (at_ sp0 (-8)) 8 = some (word_to_le_bytes 8 k)
         ∧ c_ltu errno_lo rv = false)
      (at_ B 0x8c) k
      (fun regs mem _ =>
         mem = mem1 ∧ getr regs 1 = k ∧ getr regs 2 = sp0 ∧ getr regs 10 = rv) := by
  intro regs mem rom H
  obtain ⟨Hmem, H1, H2, H10, Hrd, Hlt⟩ := H
  subst Hmem
  unfold ret_ok at Hk Hr28
  refine ⟨?regs', ?mem', ?st, ?post, ?rag, ?mag⟩
  case st =>
    -- +0x8c ret -> +0x28
    hstep_fold (refine step_jalr_x0 _ _ _ _ _ _ _ _ (at_ B 0x28) F8c ?_ D_ret ?_ <;>
        first | decide | (gres; exact H1)),
      (imm_norm; rw [Hr28])
    -- +0x28 ld ra,8(sp)
    -- the loaded register is written through `if bv_eqb rd 0`, so the step
    -- is stated at the REDUCED state: a later `rw` cannot see through the
    -- `ite` (its `Decidable` instance mentions the folded `bv_eqb`), while
    -- `refine` checks the equation up to conversion
    have hld : RiscvSemantics.step segs (mkst regs (at_ B 0x28) mem rom)
        = .MachineOk (mkst (regupd regs 1 k) (v_addi (at_ B 0x28) 4) mem rom) := by
      refine step_ld _ _ _ _ _ _ _ _ _ (word_to_le_bytes 8 k) k F28 ?_ D_ld_ra8 ?_ ?_
      · decide
      · gres; imm_norm; rw [H2]; rw [at_addi]; exact Hrd
      · exact bytes_le_to_Z_8 k
    hstep (exact hld)
    -- +0x2c addi sp,sp,16
    hstepv F2c, D_sp16p, sp0, (gres; imm_norm; rw [H2]; rw [at_addi]; exact at_0 sp0)
    -- +0x30 j __syscall_ret
    hstep (exact step_jal_x0 _ _ _ _ _ _ _ F30 (by decide) D_j4)
    -- +0x34 lui a5,0xfffff
    hstep (refine step_lui_at _ _ _ _ _ _ _ _ errno_lo F34 ?_ D_lui_a5 ?_ ?_ <;>
            first
            | rfl
            | decide
            | (unfold errno_lo; decide))
    -- +0x38 bltu a5,a0 NOT taken
    hstep (refine step_bltu_ft _ _ _ _ _ _ _ _ _ F38 ?_ D_bltu ?_ <;>
            first | rfl | decide | (gres; rw [H10]; exact Hlt))
    -- +0x3c ret -> the caller
    hstep_fold (refine step_jalr_x0 _ _ _ _ _ _ _ _ k F3c ?_ D_ret ?_ <;>
        first | rfl | decide | (gres; exact H1)),
      (imm_norm; rw [Hk])
    exact msteps.mst_refl _
  case post =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · gres; try rfl; done
    · gres; try rfl; done
    · gres
      rw [H10]
  case rag =>
    repeat (first
      | (apply regs_agree_upd <;> (first | in_clob | skip))
      | exact regs_agree_refl musl_clob regs)
  case mag =>
    exact mem_agree_refl (musl_wset sp0) mem

/-! ## The whole call, syscall included -/

include F00 F04 F08 F0c F10 F14 F18 F1c F20 F24 F28 F2c F30 F34 F38 F3c F6c F70 F74 F78
  F7c F80 F84 F88 F8c F90 in
/-- [write(1, buf, len)] from entry to return, handing the [ecall] to
    [SeqExec]'s [tw_write_ret] and the return to the caller's
    continuation.  The environment may deliver any nonempty prefix of
    the buffer, so the continuation is the delivered-length family: a0
    holds [len_word (first n out)] for the chosen [n] (never in the
    errno window, so [__syscall_ret]'s branch is not taken for ANY
    delivery).  THIS is the lemma a per-binary proof applies: one
    [apply] replaces the ~90 lines each example spends walking this
    code. -/
theorem musl_write_wexit (regs : BvMap word) (mem rom : word → Option byte)
    (k sp0 buf len : word) (out : List byte)
    (bufs : List (List byte)) (code : word)
    (Hrom : rom = seg_rom segs)
    (Hk : ret_ok k) (Hr28 : ret_ok (at_ B 0x28))
    (H1 : getr regs 1 = k) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = BitVec.ofInt 64 1) (H11 : getr regs 11 = buf)
    (H12 : getr regs 12 = len)
    (Hok : store_ok segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : ((at_ sp0 (-8)).toNat : Int) + 8 ≤ 2 ^ 64)
    (Hlen : (len.toNat : Int) ≤ 18446744073709547520)
    (Hread : rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ (regs' : BvMap word) (n : Nat), 1 ≤ n → n ≤ out.length →
       getr regs' 1 = k → getr regs' 2 = sp0 →
       getr regs' 10 = len_word (out.take n) →
       to_wexit segs
         (mkst regs' k (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) rom)
         bufs code) :
    to_wexit segs (mkst regs (at_ B 0x00) mem rom) (out :: bufs) code := by
  -- (the binders are already hypotheses: a Lean theorem's explicit
  -- binders are introduced by the proof start, not by `intros`)
  -- the spilled-[ra] memory: this tree names it with `set (mem1 := …)` and
  -- `subst`s it later; in Lean the term IS the normal form (no `set`
  -- tactic, and a `let` would only be a notational alias), so the
  -- summaries below are applied at the term itself.
  have Hlout : out.length = len.toNat := rdn_length segs _ _ _ _ Hread
  have HoutZ : ((out.length : Int)) = (len.toNat : Int) := by rw [Hlout]
  have Houtlen : (out.length : Int) < 2 ^ 64 := by
    rw [HoutZ]; exact (u64_range len).2
  -- entry -> the ecall
  apply triple_wexit
  · -- the entry summary, at fd = 1
    exact musl_write_enter (segs := segs) (B := B) (F00 := F00) (F04 := F04)
      (F08 := F08) (F0c := F0c) (F10 := F10) (F14 := F14) (F18 := F18) (F1c := F1c)
      (F20 := F20) (F24 := F24) (F6c := F6c) (F70 := F70) (F74 := F74) (F78 := F78)
      (F7c := F7c) (F80 := F80) (F84 := F84) (F90 := F90) (k := k) (sp0 := sp0)
      (fd := BitVec.ofInt 64 1) (buf := buf) (len := len) (mem0 := mem)
  · exact ⟨rfl, H1, H2, H10, H11, H12, Hok⟩
  · -- the ecall, then [__syscall_ret] and the caller
    intro regs1 mem1' HQ
    obtain ⟨Hm1, Q1, Q2, Q10, Q11, Q12, Q17⟩ := HQ
    subst Hm1
    apply to_wexit.tw_step
    · rfl
    · exact step_ecall _ _ _ _ _ _ F88 E_ecall
    · have hwr := tw_write_ret segs regs1 (at_ B 0x88) (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k)) rom out bufs code
      refine hwr ?_ ?_ ?_ Hnb ?_
      · rw [Q17]; decide
      · rw [← getr_nz regs1 10 (by decide)]; exact Q10
      · rw [ms_read_bytes_rdn segs _ _ _ Hrom]
        rw [← getr_nz regs1 11 (by decide), ← getr_nz regs1 12 (by decide)]
        rw [Q11, Q12]
        exact Hread
      · intro n Hn1 Hn2
        have Hru : ((len_word (out.take n)).toNat : Int) = (n : Int) := by
          have hlt : (((out.take n).length : Int)) < two_pow_64 := by
            have h2 : (out.length : Int) < two_pow_64 := by
              unfold two_pow_64; exact Houtlen
            have h1 : ((out.take n).length : Int) ≤ (n : Int) :=
              Int.ofNat_le.mpr (List.length_take_le n out)
            have h3 : (n : Int) ≤ (out.length : Int) := Int.ofNat_le.mpr Hn2
            omega
          rw [len_word_unsigned (out.take n) hlt, List.length_take]
          have h : min n out.length = n := Nat.min_eq_left Hn2
          rw [h]
        rw [at_addi]
        apply triple_wexit
        · exact musl_write_leave (segs := segs) (B := B) (F28 := F28) (F2c := F2c)
            (F30 := F30) (F34 := F34) (F38 := F38) (F3c := F3c) (F8c := F8c)
            (k := k) (sp0 := sp0) (rv := len_word (out.take n)) (mem1 := wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 k))
            (Hk := Hk) (Hr28 := Hr28)
        · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
          · rw [getr_other regs1 10 _ 1 (by decide)]; exact Q1
          · rw [getr_other regs1 10 _ 2 (by decide)]; exact Q2
          · rw [getr_same regs1 10 _ (by decide)]
          · exact rdn_wbytes_hit8 segs mem (at_ sp0 (-8)) k Hnw
          · apply not_errno
            rw [Hru]
            have hn : (n : Int) ≤ (out.length : Int) := Int.ofNat_le.mpr Hn2
            omega
        · intro regs2 mem2 HQ2
          obtain ⟨Hm2, R1, R2, R10⟩ := HQ2
          subst Hm2
          exact Hcont regs2 n Hn1 Hn2 R1 R2 R10

/-! ## The whole call, for a PUT-LOOP caller -/

include F00 F04 F08 F0c F10 F14 F18 F1c F20 F24 F28 F2c F30 F34 F38 F3c F6c F70 F74 F78
  F7c F80 F84 F88 F8c F90 in
/-- [write(1, buf, len)] from entry to return, handing the [ecall] to
    [WallSim]'s write node and — per delivered length [n] — the return
    path back through [__syscall_ret] to the CALLER'S retry-loop
    obligation: a [to_wall_tail] of the remainder [out.drop n] down to
    an arbitrary continuation predicate [k].  This is the summary a
    per-binary proof applies when the caller wraps the call in a
    put-style retry loop (so its trace contribution is ALL of [out]).

    SHARES 27 LINES WITH [musl_write_wexit] ABOVE — its whole 13-line
    hypothesis list, and four blocks of proof body.

    It is not folded because the two lemmas' conclusions live in
    different inductive families with no bridge between them —
    [SeqExec.to_wexit] (node intro [tw_write_ret]) and
    [WallSim.to_wall_tail] (node intro [twl_write_rec], closure
    [msteps_to_wall_tail]).  [WallSim.to_wallexit] bridges [to_wall] to
    [to_wexit] only in the buffer-LIST form, not the tail form, so
    neither lemma is an instance of the other; generalizing over the
    family needs three interface hypotheses (msteps closure, ecall step,
    node intro) whose statements come to about what the shared body
    costs.  The hypothesis lists are identical precisely BECAUSE the two
    calls are the same code — the difference is only what the caller
    does with the return.

    What the available folds are actually worth, measured rather than
    guessed: an arithmetic lemma over the two [len_word (first n out)]
    preambles nets about -1; an [Ltac] for the write-node side
    conditions and another for the [musl_write_leave] ones net -3 each,
    and both would resolve caller-local hypothesis names ([Q1], [Q10],
    [Hrom], [Hru], ...) dynamically, which couples every future call
    site to that naming.  The only fold that pays properly is turning
    the shared hypothesis list into one [Definition], about -8, and it
    changes both lemmas' statements and moves two call sites
    ([conditional_bug_ns_hoare:96], [modprint_ns_hoare:103]).  That
    is a follow-up on main, not an append to this branch.

    A cleaner win exists and is worth taking first: this lemma's
    continuation hypothesis carries [regs_agree musl_clob regs regs'],
    its only consumer ([conditional_bug_ns_hoare:103]) binds it and
    never uses it, and the proof pays three lines of
    [regs_agree_trans]/[regs_agree_upd] to supply it.  Dropping it
    removes about four lines here and one unused binder there, with no
    other consumer affected. -/
theorem musl_write_wall (k : machine_state → Prop)
    (regs : BvMap word) (mem rom : word → Option byte)
    (kra sp0 buf len : word) (out : List byte)
    (Hrom : rom = seg_rom segs)
    (Hk : ret_ok kra) (Hr28 : ret_ok (at_ B 0x28))
    (H1 : getr regs 1 = kra) (H2 : getr regs 2 = sp0)
    (H10 : getr regs 10 = BitVec.ofInt 64 1) (H11 : getr regs 11 = buf)
    (H12 : getr regs 12 = len)
    (Hok : store_ok segs mem (at_ sp0 (-8)) 8 = true)
    (Hnw : ((at_ sp0 (-8)).toNat : Int) + 8 ≤ 2 ^ 64)
    (Hlen : (len.toNat : Int) ≤ 18446744073709547520)
    (Hread : rdn segs (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
      buf (word_to_nat len) = some out)
    (Hnb : 1 ≤ out.length)
    (Hcont : ∀ (regs' : BvMap word) (n : Nat), 1 ≤ n → n ≤ out.length →
       regs_agree musl_clob regs regs' →
       getr regs' 1 = kra → getr regs' 2 = sp0 →
       getr regs' 10 = len_word (out.take n) →
       to_wall_tail segs (BitVec.ofInt 64 1)
         (mkst regs' kra (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom)
         (out.drop n) k) :
    to_wall_tail segs (BitVec.ofInt 64 1) (mkst regs (at_ B 0x00) mem rom) out k := by
  have Hlout : out.length = len.toNat := rdn_length segs _ _ _ _ Hread
  have HoutZ : ((out.length : Int)) = (len.toNat : Int) := by rw [Hlout]
  have Houtlen : (out.length : Int) < 2 ^ 64 := by
    rw [HoutZ]; exact (u64_range len).2
  -- entry -> the ecall, destructed (the wall form needs the raw state)
  obtain ⟨regs1, mem1', Hst1, HQ1, Hag1, _⟩ :=
    musl_write_enter (segs := segs) (B := B) (F00 := F00) (F04 := F04)
      (F08 := F08) (F0c := F0c) (F10 := F10) (F14 := F14) (F18 := F18) (F1c := F1c)
      (F20 := F20) (F24 := F24) (F6c := F6c) (F70 := F70) (F74 := F74) (F78 := F78)
      (F7c := F7c) (F80 := F80) (F84 := F84) (F90 := F90) (k := kra) (sp0 := sp0)
      (fd := BitVec.ofInt 64 1) (buf := buf) (len := len) (mem0 := mem)
      regs mem rom ⟨rfl, H1, H2, H10, H11, H12, Hok⟩
  obtain ⟨Hm1, Q1, Q2, Q10, Q11, Q12, Q17⟩ := HQ1
  subst Hm1
  have hwt := twl_write_rec segs (BitVec.ofInt 64 1) k out regs1 (at_ B 0x88) (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom
  refine msteps_to_wall_tail segs (BitVec.ofInt 64 1) _ _ out k Hst1 ?_
  -- the ecall itself, then the write node
  apply to_wall_tail.twt_step
  · rfl
  · exact step_ecall _ _ _ _ _ _ F88 E_ecall
  · apply to_wall_tail.twt_more
    · exact Hnb
    · refine hwt ?_ ?_ ?_ Hnb ?_
      · rw [Q17]; decide
      · rw [← getr_nz regs1 10 (by decide)]; exact Q10
      · rw [ms_read_bytes_rdn segs _ _ _ Hrom]
        rw [← getr_nz regs1 11 (by decide), ← getr_nz regs1 12 (by decide)]
        rw [Q11, Q12]
        exact Hread
      · intro n Hn1 Hn2
        have Hru : ((len_word (out.take n)).toNat : Int) = (n : Int) := by
          have hlt : (((out.take n).length : Int)) < two_pow_64 := by
            have h2 : (out.length : Int) < two_pow_64 := by
              unfold two_pow_64; exact Houtlen
            have h1 : ((out.take n).length : Int) ≤ (n : Int) :=
              Int.ofNat_le.mpr (List.length_take_le n out)
            have h3 : (n : Int) ≤ (out.length : Int) := Int.ofNat_le.mpr Hn2
            omega
          rw [len_word_unsigned (out.take n) hlt, List.length_take]
          have h : min n out.length = n := Nat.min_eq_left Hn2
          rw [h]
        rw [at_addi]
        -- back from the kernel: [__syscall_ret], then the caller's put loop
        obtain ⟨regs2, mem2, Hst2, HQ2, Hag2, _⟩ :=
          musl_write_leave (segs := segs) (B := B) (F28 := F28) (F2c := F2c)
            (F30 := F30) (F34 := F34) (F38 := F38) (F3c := F3c) (F8c := F8c)
            (k := kra) (sp0 := sp0) (rv := len_word (out.take n))
            (mem1 := wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra))
            (Hk := Hk) (Hr28 := Hr28)
            (regupd regs1 10 (len_word (out.take n)))
            (wbytes mem (at_ sp0 (-8)) (word_to_le_bytes 8 kra)) rom (by
              refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
              · rw [getr_other regs1 10 _ 1 (by decide)]; exact Q1
              · rw [getr_other regs1 10 _ 2 (by decide)]; exact Q2
              · rw [getr_same regs1 10 _ (by decide)]
              · exact rdn_wbytes_hit8 segs mem (at_ sp0 (-8)) kra Hnw
              · apply not_errno
                rw [Hru]
                have hn : (n : Int) ≤ (out.length : Int) := Int.ofNat_le.mpr Hn2
                omega)
        obtain ⟨Hm2, R1, R2, R10⟩ := HQ2
        subst Hm2
        refine msteps_to_wall_tail segs (BitVec.ofInt 64 1) _ _ (out.drop n) k Hst2 ?_
        have HagMid : regs_agree musl_clob regs (regupd regs1 10 (len_word (out.take n))) :=
          regs_agree_trans musl_clob regs regs1 _
            Hag1
            (regs_agree_upd musl_clob regs1 regs1 10 _
              (by in_clob) (regs_agree_refl musl_clob regs1))
        exact Hcont regs2 n Hn1 Hn2
          (regs_agree_trans musl_clob regs _ regs2 HagMid Hag2) R1 R2 R10

/-! ## What a caller keeps across the call -/

/-- The frame rule at this summary's footprints, as the caller sees it:
    any callee-saved register and any buffer disjoint from the one
    spilled stack slot survives the whole [write] call — including the
    syscall — with no help from the summary's postcondition.  This is
    what the current per-binary proofs cannot express: they re-derive
    every surviving fact by re-walking the chain. -/
theorem musl_write_frame (sp0 : word) (r : reg) (v a : word) (n : Nat)
    (bs : List byte)
    (Hr : ¬ musl_clob r)
    (Ha : ∀ i, 0 ≤ i → i < (n : Int) → ¬ musl_wset sp0 (BitVec.ofInt 64 ((a.toNat : Int) + i))) :
    frameable musl_clob (musl_wset sp0)
      (fun regs mem _ => getr regs r = v ∧ rdn segs mem a n = some bs) := by
  refine frameable_and musl_clob (musl_wset sp0) _ _ ?_ ?_
  · exact frameable_reg musl_clob (musl_wset sp0) r v Hr
  · exact frameable_rdn segs musl_clob (musl_wset sp0) a n bs Ha

end MuslWrite

end LinuxSem.Common.MuslCall
