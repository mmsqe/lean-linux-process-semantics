/-
  * Examples.RwxFlagNs.RwxFlagNsTarget — the TARGET binary

  PROOF-SIDE FILE (not part of the trusted specification).

  Delivers the one `to_wexit` derivation of the target binary: no output,
  exit 5, on every input.  The target's code is an ordinary immutable r-x
  segment, so this side is the standard static-fetch machinery — six
  instructions: form the data address, store 5 into the writable global,
  load it back, exit with it.

  ON THE FETCH FACTS.  The `TF_`/`TD_` facts below are

    TF_<pc> : fetch_word <segs> 0x<pc> = Some <word>
  TD_<pc>: decodeAny (BitVec.ofInt 32 <word>) = Some (<AST>, 4)

  one pair per instruction word of the image.  Each is proved by
  `decide`, i.e. by kernel evaluation of the model's own fetch and
  decoder against the snapshot bytes.  Nothing here is assumed: if the
  payload or a word were wrong, these would not close.
-/
import LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs

/- `autoImplicit` is off: in a STATEMENT a bare identifier would otherwise
   become an implicitly bound variable, i.e. a weakened claim rather than a
   compile error. -/
set_option autoImplicit false

/- The generated fetch facts reduce the model's hex decoder over the 4 KiB
   segment images.  Resource knobs, not proof steps. -/
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/- `target_wexit` carries the ASLR-window hypotheses `Hsp_lo`/`Hsp_hi`
  for uniformity with the statements in `Proof.lean`, but this program
  never reads the entry stack, so the derivation does not use them: the
  proof holds for EVERY valid stack pointer, which is the stronger
  statement.  The binders stay (they are what the statements and
  the glue in `Proof.lean` are written against). -/
set_option linter.unusedVariables false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.MmapSim

namespace LinuxSem.Examples.RwxFlagNs

namespace RwxFlagNsTarget

/-- Same local instance as `RwxFlagNsDefs.lean`. -/
local instance rwx_fx : FPState := LinuxSem.Common.PropExec.fx0

/- =========================================================================
   Generated fetch facts: the target's `.text`, six words.

   `fetch_word` is the STATIC fetch (`code_read`: the `x /\ ~w` gate), which
   is what runs on this side — the code page is `r-x`, so the overlay is
   never consulted.
   ========================================================================= -/

theorem TF_1001190 : fetch_word target_segs (BitVec.ofInt 64 0x1001190) = some 0x01002537 := by
  decide

theorem TF_1001194 : fetch_word target_segs (BitVec.ofInt 64 0x1001194) = some 0x00500593 := by
  decide

theorem TF_1001198 : fetch_word target_segs (BitVec.ofInt 64 0x1001198) = some 0x1ab50423 := by
  decide

theorem TF_100119c : fetch_word target_segs (BitVec.ofInt 64 0x100119c) = some 0x1a854503 := by
  decide

theorem TF_10011a0 : fetch_word target_segs (BitVec.ofInt 64 0x10011a0) = some 0x05d00893 := by
  decide

theorem TF_10011a4 : fetch_word target_segs (BitVec.ofInt 64 0x10011a4) = some 0x00000073 := by
  decide

/- =========================================================================
  Generated decode facts, from this tree's own decoder.
   ========================================================================= -/

theorem TD_1001190 : decodeAny 0x01002537 = some (Instr.lui 0x0a#5 0x01002#20, 4) := by
  decide

theorem TD_1001194 :
    decodeAny 0x00500593 = some (Instr.opImm .ADD 0x0b#5 0x00#5 0x005#12, 4) := by
  decide

theorem TD_1001198 :
    decodeAny 0x1ab50423 = some (Instr.store .SZ1 0x0a#5 0x0b#5 0x1a8#12, 4) := by
  decide

theorem TD_100119c :
    decodeAny 0x1a854503 = some (Instr.load .SZ1 false 0x0a#5 0x0a#5 0x1a8#12, 4) := by
  decide

theorem TD_10011a0 :
    decodeAny 0x05d00893 = some (Instr.opImm .ADD 0x11#5 0x00#5 0x05d#12, 4) := by
  decide

theorem TD_10011a4 : decodeAny 0x00000073 = some (Instr.ecall, 4) := by
  decide

/- =========================================================================
   The derivation: six instructions, no output, exit 5.
   ========================================================================= -/

section TargetProof

/-- The window's lower bound as a plain decimal. -/
theorem asp_lo_num (asp : word) (Hsp_lo : (sp_window_lo ≤ (asp.toNat : Int))) :
    (0x7fff80000000 ≤ (asp.toNat : Int)) := Hsp_lo

/-- …and the upper. -/
theorem asp_hi_num (asp : word) (Hsp_hi : ((asp.toNat : Int) ≤ sp_window_hi)) :
    ((asp.toNat : Int) ≤ 0x800000000000) := Hsp_hi

/-- The target program (see `target/program.zig`).  Note what is NOT
    assumed: nothing about the stack pointer beyond the ASLR window
    (`Hsp_lo`/`Hsp_hi`), and nothing about the entry draw `arnd` — this
    program never reads the entry stack, so it holds for every one. -/
theorem target_wexit (av ev : List (List byte)) (asp : word) (arnd : EntryDraw)
    (Hsp_lo : (sp_window_lo ≤ (asp.toNat : Int)))
    (Hsp_hi : ((asp.toNat : Int) ≤ sp_window_hi))
    (uid : word) (hw : word) :
    to_wexit target_segs
      (init_machine_state target_segs 0x1001190 target_phdrs asp arnd av ev uid hw)
      [] (BitVec.ofInt 64 5) := by
  rw [init_mkst]
  -- 0x1001190 lui a0, 0x1002 — a0 := the .data page's 4 KiB base
  apply to_wexit.tw_step
  · rfl
  · exact step_lui target_segs _ _ _ _ _ _ _ TF_1001190 rfl TD_1001190
  · step_simpl
    -- 0x1001194 li a1, 5
    apply to_wexit.tw_step
    · rfl
    · exact step_addi_at target_segs _ _ _ _ _ _ _ _ _ TF_1001194 rfl TD_1001194
        (by decide) rfl
    · step_simpl
      -- 0x1001198 sb a1, 424(a0) — the writable global := 5
      apply to_wexit.tw_step
      · rfl
      · exact step_sb_at target_segs _ _ _ _ _ _ _ _
          (BitVec.ofInt 64 0x10021a8) (BitVec.ofInt 64 5) (BitVec.ofInt 8 5)
          TF_1001198 rfl TD_1001198 rfl rfl (by decide)
          (target_store_ok _ (BitVec.ofInt 64 0x10021a8) 1 (by decide) (by decide))
      · step_simpl
        -- 0x100119c lbu a0, 424(a0) — read it back, out of the overlay the
        -- store just wrote
        apply to_wexit.tw_step
        · rfl
        · exact step_lbu target_segs _ _ _ _ _ _ _ _ (BitVec.ofInt 8 5)
            TF_100119c rfl TD_100119c
            (rdn_wbytes_hit target_segs [BitVec.ofInt 8 5] _ _ (by decide))
        · step_simpl
          -- 0x10011a0 li a7, 93
          apply to_wexit.tw_step
          · rfl
          · exact step_addi_at target_segs _ _ _ _ _ _ _ _ _ TF_10011a0 rfl TD_10011a0
              (by decide) rfl
          · step_simpl
            -- 0x10011a4 ecall — exit(5)
            apply to_wexit.tw_step
            · rfl
            · exact step_ecall target_segs _ _ _ _ _ TF_10011a4 rfl
            · refine tw_exit_coden target_segs _ _ _ _ (BitVec.ofInt 64 5) ?_ ?_ ?_
              · rfl
              · rfl
              · decide

end TargetProof

end RwxFlagNsTarget

end LinuxSem.Examples.RwxFlagNs
