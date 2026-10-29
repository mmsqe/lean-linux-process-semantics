/-
  * Common.StreamExec — extra value facts and syscall post-state collapses
    needed by the streamcat binaries.

  PURELY ADDITIVE over [Common.PropExec] / [Common.CatExec] /
  [Common.SeqExec]. Image-INDEPENDENT.

  Notes:
  - [step_bgeu_ft]/[step_bgeu_tk] live in PropExec (instances of the
    generic branch pipeline; the taken variant has no [align4]
    hypothesis). This file does not restate them.
  - [c_ltu_small] also lives in PropExec, as the hypothesis-free
    definitional restatement [c_ltu x y = bv_ltu x y].
  - The [write_to_mem] frame/read-back lemmas below are thin corollaries
    of the CatExec/SeqExec [wbytes] theory (the interpreter's byte
    writer IS [wbytes], [CatExec.write_to_mem_wbytes]); the wrapping
    [bv] address walk gives them the CatExec-standard no-overflow
    hypotheses, trivially discharged downstream.

  NOTES.

  - `Section WithFP1`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec`,
    `CatExec`, `SeqExec` and `MmapSim` do; the section's `fp_regs`/`fp_csr`
    are `fx.fp_regs`/`fx.fp_csr`, and the `mkst`/`regupd`/`v_addi`
    abbreviations are PropExec's.
  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `length data` → `data.length`,
    `2^64` (in `Z`) → `((2 ^ 64 : Nat) : Int)` — the SAME shape
    `CatExec.wbytes_below`/`wbytes_above` state their no-overflow
    hypotheses in, so each lemma below is a direct application of the
    [wbytes] fact it is a corollary of.
  - The  `reflexivity` goals ([v_lui_4096], [c_lts_0_0]) are
    `rfl` / `by decide` here; the `lia` calls inside [rdn_wtm_out] are
    `omega`.  `destruct data as [|b rest]` in [adv_apply_delivered] is
    `cases data with`.
  - Every  declaration is present with the type, modulo
    the [Z]/[Int] and record/`structure` conventions above.  No
    was needed: the proof scripts of `CatExec`'s
    [wbytes] theory already supply everything the corollaries consume.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.ExitSim
import LinuxSem.LinuxProcessSem.Sys.Uaccess

set_option autoImplicit false
-- Same rationale as `PropExec`/`CatExec`/`SeqExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.StreamExec

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.ExitSim
open LinuxSem.Common.SeqExec
open LinuxSem.LinuxProcessSem.Sys.Uaccess

section WithFP1

variable [fx : FPState]

/- =================================================================
   New value/condition shapes
   ================================================================= -/

/- v_addiw, c_ltu, step_addiw, step_bgeu_ft/tk, and c_ltu_small all live
   in PropExec; see the header note. -/

/- =================================================================
   Value facts used by the streamcat loops
   ================================================================= -/

/-- `lui` of the constant 4096, in the value normal form the loops use. -/
theorem v_lui_4096 : v_lui 4096 = BitVec.ofInt 64 4096 := rfl

/-- [blez]/[bge x0,a0] outcomes on the read return value: both operands
    zero, so the signed comparison is false. -/
theorem c_lts_0_0 : c_lts (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) = false := by decide

/- [c_lts_0_pos] lives in PropExec.  Do not restate it here: a second
   lemma of that name would make [apply c_lts_0_pos] mean different
   things in different files, depending on Require order. -/

/- =================================================================
   Round-trip: bytes just written to memory read straight back.
   ================================================================= -/

/-- Below the written region, [write_to_mem] leaves memory unchanged.
    The no-overflow hypothesis [buf + length data <= 2^64] is needed
    because the write walk is a wrapping [bv] add — mirrors
    [CatExec.wbytes_below]. -/
theorem write_to_mem_below (data : List byte) (mem : word → Option byte) (buf a : word)
    (Hnw : (buf.toNat : Int) + (data.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Ha : (a.toNat : Int) < (buf.toNat : Int)) :
    write_to_mem mem buf data a = mem a := by
  rw [write_to_mem_wbytes data mem buf]
  exact wbytes_below data mem buf a Hnw Ha

/-- Outside [buf, buf + length data), [write_to_mem] leaves memory alone
    (above-side companion of [write_to_mem_below]; no extra no-overflow
    needed — [a < 2^64] already caps the walk). -/
theorem write_to_mem_above (data : List byte) (mem : word → Option byte) (buf a : word)
    (Ha : (buf.toNat : Int) + (data.length : Int) ≤ (a.toNat : Int)) :
    write_to_mem mem buf data a = mem a := by
  rw [write_to_mem_wbytes data mem buf]
  exact wbytes_above data mem buf a Ha

/-- [rdn] reads through a disjoint [write_to_mem].  The two no-overflow
    hypotheses are the standard [rdn_ext]/[wbytes_below] ones. -/
theorem rdn_wtm_out (segs : List Segment) (data : List byte) (m : word → Option byte)
    (buf a : word) (n : Nat)
    (Hna : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hnb : (buf.toNat : Int) + (data.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hd : (buf.toNat : Int) + (data.length : Int) ≤ (a.toNat : Int) ∨
      (a.toNat : Int) + (n : Int) ≤ (buf.toNat : Int)) :
    rdn segs (write_to_mem m buf data) a n = rdn segs m a n := by
  apply rdn_ext
  · exact Hna
  · intro x Hx
    rcases Hd with Hd | Hd
    · apply write_to_mem_above
      omega
    · apply write_to_mem_below <;> omega

/-- [rdn] reads back exactly the bytes just written by [write_to_mem]
    (no-overflow hypothesis, as in [SeqExec.rdn_wbytes_hit]). -/
theorem rdn_write_to_mem (segs : List Segment) (data : List byte) (mem : word → Option byte)
    (buf : word)
    (Hnw : (buf.toNat : Int) + (data.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (write_to_mem mem buf data) buf data.length = some data := by
  rw [write_to_mem_wbytes data mem buf]
  exact rdn_wbytes_hit segs data mem buf Hnw

/- =================================================================
   mkst-normal-form bridges for the syscall post-states.
   ================================================================= -/

/-- [advance_past_svc] of [apply_effect] with a single-buffer write effect
    (the read post-state): sets x10 to the return value, advances pc by 4,
    clears svc, and writes [data] into [ms_mem] at [buf].  The input
    record carries the (post-ecall) [ms_resv := none]. -/
theorem adv_apply_write (regs : BvMap word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (ret buf : word) (data : List byte) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }
      (mkEffect ret [(buf, data)] []))
    = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  have hne : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, apply_effect, mkEffect, set_reg, hne, Bool.false_eq_true,
    ite_false, reduceIte, ms_pc, apply_writes, apply_copies, apply_zeros, apply_unmaps,
    mkst, regupd, b_npc4]

/-- The same bridge for the canonical [delivered_writes] shape (see
    Specs): a zero-byte delivery carries no write entry, and
    [write_to_mem] of [] is the identity, so both shapes normalize to
    the same [mkst]. -/
theorem adv_apply_delivered (regs : BvMap word) (pc : word) (sv : Option word)
    (mem rom : word → Option byte) (ret buf : word) (data : List byte) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc, ms_svc_pending := sv,
        ms_resv := none, ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }
      (mkEffect ret (delivered_writes buf data) []))
    = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  cases data with
  | cons b rest => exact adv_apply_write regs pc sv mem rom ret buf (b :: rest)
  | nil =>
    have hne : bv_eqb (10 : reg) 0 = false := by decide
    simp only [delivered_writes, advance_past_svc, apply_effect, mkEffect, set_reg, hne,
      Bool.false_eq_true, ite_false, reduceIte, ms_pc, apply_writes, apply_copies,
      apply_zeros, apply_unmaps, write_to_mem, mkst, regupd, b_npc4]

end WithFP1

end LinuxSem.Common.StreamExec
