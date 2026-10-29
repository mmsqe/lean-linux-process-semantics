/-
  * Examples.RwxFlagNs.RwxFlagNsSource — the SOURCE binary

  PROOF-SIDE FILE (not part of the trusted specification).

  Delivers the one `to_wexit` derivation of the source binary (musl-gcc
  `-Os`, single RWX LOAD segment): no output, exit 5, on every valid input.

  Every fetch of this binary goes through the overlay-aware w+x path
  (`RiscvSemantics.fetch_word_ov`): the image is a single RWX LOAD
  segment, so the static `fetch_word` declines everywhere
  (`source_no_ro_exec`).  Each step closes its fetch from the generated
  static `fetch_word_wx` fact via `WxExec.wx_fetch_intro`, whose overlay
  side condition is the FRAME INVARIANT "the overlay misses.text = `[0x10078, 0x100e4)`" — established on the initial state
  (`wx_clear_init`: the initial overlay is the stack image, far above the
  loaded segment) and re-established across each store by
  `wx_clear_store` (both stores land at/above `0x100e4`, i.e. outside the
  code: this is precisely the no-self-modifying-code condition).  The
  `lbu` then reads the byte the `sb` just wrote out of the overlay
  (`rdn_wbytes_hit`) — through the very same memory view fetch uses.

  ON THE FETCH FACTS.  Because this image is w+x, the `SF_`/`SD_` facts
  below are stated over the STATIC projection `fetch_word_wx`, which is
  the one that can decline (`source_no_ro_exec`); each is proved by
  `decide` against the snapshot bytes, so a wrong payload or a wrong
  word would not close.

  ON `argcN`/`u_argcN`.  Both come from `Common.ArgvEnv` — `argcN` is
  `len_word av` and `u_argcN` states `(argcN av).toNat = av.length` —
  which is the spelling `read_argc` and every other stack-reader in the
  tree is stated over, so a local copy here would be a duplicate.

  ON `src_clear`.  The frame invariant is re-established from three
  facts named once (`wx_clear_init`, and `wx_clear_store` applied twice),
  and each step cites the one that describes its memory.  Lean has no
  goal-shape-driven recursion worth writing for two stores, so peeling
  `mem_clear_wbytes` off the current overlay until it reaches
  `mem_clear_wrap` — the same three facts in the same order — is spelled
  out instead.
-/
import LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs
import LinuxSem.Common.ArgvEnv

/- `autoImplicit` is off: in a STATEMENT a bare identifier would otherwise
   become an implicitly bound variable, i.e. a weakened claim rather than a
   compile error. -/
set_option autoImplicit false

/- The generated fetch facts reduce the model's hex decoder over the 4 KiB
   segment image.  Resource knobs, not proof steps. -/
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StreamSim
open LinuxSem.Common.StoreOk
open LinuxSem.Common.WxExec
open LinuxSem.Common.ArgvEnv
open LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs

namespace LinuxSem.Examples.RwxFlagNs

namespace RwxFlagNsSource

/-- Same local instance as `RwxFlagNsDefs.lean`. -/
local instance rwx_fx : FPState := LinuxSem.Common.PropExec.fx0

/- =========================================================================
   Generated fetch facts: the source's `.text`, eighteen words.

   `fetch_word_wx` — the STATIC projection of the overlay-aware fetch — is
   what the generator states these over for a w+x image: a pure function of
   the snapshot, so it is checkable by computation, and `wx_fetch_intro`
   converts it to the overlay-aware premise the step uses.
   ========================================================================= -/

theorem SF_10078 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10078) = some 0x00001197 := by
  decide

theorem SF_1007c : fetch_word_wx source_segs (BitVec.ofInt 64 0x1007c) = some 0x86d18193 := by
  decide

theorem SF_10080 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10080) = some 0x00013503 := by
  decide

theorem SF_10084 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10084) = some 0x00810593 := by
  decide

theorem SF_10088 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10088) = some 0x00351293 := by
  decide

theorem SF_1008c : fetch_word_wx source_segs (BitVec.ofInt 64 0x1008c) = some 0x00558633 := by
  decide

theorem SF_10090 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10090) = some 0x00860613 := by
  decide

theorem SF_10094 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10094) = some 0x00000317 := by
  decide

theorem SF_10098 : fetch_word_wx source_segs (BitVec.ofInt 64 0x10098) = some 0x05430313 := by
  decide

theorem SF_1009c : fetch_word_wx source_segs (BitVec.ofInt 64 0x1009c) = some 0x00c33023 := by
  decide

theorem SF_100a0 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100a0) = some 0x030000ef := by
  decide

theorem SF_100d0 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100d0) = some 0x000107b7 := by
  decide

theorem SF_100d4 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100d4) = some 0x00500713 := by
  decide

theorem SF_100d8 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100d8) = some 0x0ee78223 := by
  decide

theorem SF_100dc : fetch_word_wx source_segs (BitVec.ofInt 64 0x100dc) = some 0x0e47c503 := by
  decide

theorem SF_100e0 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100e0) = some 0x00008067 := by
  decide

theorem SF_100a4 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100a4) = some 0x05d00893 := by
  decide

theorem SF_100a8 : fetch_word_wx source_segs (BitVec.ofInt 64 0x100a8) = some 0x00000073 := by
  decide

/- =========================================================================
   Generated decode facts.
   ========================================================================= -/

theorem SD_10078 :
    decodeAny 0x00001197 = some (Instr.auipc 0x03#5 0x00001#20, 4) := by
  decide

theorem SD_1007c :
    decodeAny 0x86d18193 = some (Instr.opImm .ADD 0x03#5 0x03#5 0x86d#12, 4) := by
  decide

theorem SD_10080 :
    decodeAny 0x00013503 = some (Instr.load .SZ8 true 0x0a#5 0x02#5 0x000#12, 4) := by
  decide

theorem SD_10084 :
    decodeAny 0x00810593 = some (Instr.opImm .ADD 0x0b#5 0x02#5 0x008#12, 4) := by
  decide

theorem SD_10088 :
    decodeAny 0x00351293 = some (Instr.shiftImm .SLL 0x05#5 0x0a#5 0x03#6, 4) := by
  decide

theorem SD_1008c :
    decodeAny 0x00558633 = some (Instr.op .ADD 0x0c#5 0x0b#5 0x05#5, 4) := by
  decide

theorem SD_10090 :
    decodeAny 0x00860613 = some (Instr.opImm .ADD 0x0c#5 0x0c#5 0x008#12, 4) := by
  decide

theorem SD_10094 :
    decodeAny 0x00000317 = some (Instr.auipc 0x06#5 0x00000#20, 4) := by
  decide

theorem SD_10098 :
    decodeAny 0x05430313 = some (Instr.opImm .ADD 0x06#5 0x06#5 0x054#12, 4) := by
  decide

theorem SD_1009c :
    decodeAny 0x00c33023 = some (Instr.store .SZ8 0x06#5 0x0c#5 0x000#12, 4) := by
  decide

theorem SD_100a0 :
    decodeAny 0x030000ef = some (Instr.jal 0x01#5 0x000030#21, 4) := by
  decide

theorem SD_100d0 :
    decodeAny 0x000107b7 = some (Instr.lui 0x0f#5 0x00010#20, 4) := by
  decide

theorem SD_100d4 :
    decodeAny 0x00500713 = some (Instr.opImm .ADD 0x0e#5 0x00#5 0x005#12, 4) := by
  decide

theorem SD_100d8 :
    decodeAny 0x0ee78223 = some (Instr.store .SZ1 0x0f#5 0x0e#5 0x0e4#12, 4) := by
  decide

theorem SD_100dc :
    decodeAny 0x0e47c503 = some (Instr.load .SZ1 false 0x0a#5 0x0f#5 0x0e4#12, 4) := by
  decide

theorem SD_100e0 :
    decodeAny 0x00008067 = some (Instr.jalr 0#5 0x01#5 0x000#12, 4) := by
  decide

theorem SD_100a8 : decodeAny 0x00000073 = some (Instr.ecall, 4) := by
  decide

/- =========================================================================
   The inputs and the derived pointer

  These are stated with `av`, `ev`, `rsp`, `rrnd`, `uid` and `hw` as
  explicit parameters rather than section variables: Lean section
  variables used by a `def` become parameters anyway, so `envp_ptr`
  would silently turn into a function of `av` and `rsp`.
   ========================================================================= -/

/-- The window's lower bound as a plain decimal. -/
theorem rsp_lo_num (rsp : word) (Hsp_lo : (sp_window_lo ≤ (rsp.toNat : Int))) :
    (0x7fff80000000 ≤ (rsp.toNat : Int)) := Hsp_lo

/-- …and the upper. -/
theorem rsp_hi_num (rsp : word) (Hsp_hi : ((rsp.toNat : Int) ≤ sp_window_hi)) :
    ((rsp.toNat : Int) ≤ 0x800000000000) := Hsp_hi

/-- The pointer `_start` stores into musl's `__environ` slot at `0x100e8`:
    `sp + 8 + 8 * argc + 8`, the address of the first environment pointer. -/
def envp_ptr (av : List (List byte)) (rsp : word) : word :=
  BitVec.ofInt 64 ((rsp.toNat : Int) + 8 + 8 * (av.length : Int) + 8)

/-- No-overflow bound for the initial stack image (feeds the stack-read
    lemmas' side conditions). -/
theorem source_bsb_nw (av ev : List (List byte)) (Hva : valid_argv av) (Hve : valid_envp ev)
    (rsp : word) (rrnd : EntryDraw) (uid hw : word)
    (Hsp_hi : ((rsp.toNat : Int) ≤ sp_window_hi)) :
    ((rsp.toNat : Int)
      + ((build_stack_bytes source_phdrs rsp av ev uid hw rrnd).length : Int)
      < ((2 ^ 64 : Nat) : Int)) := by
  have h1 := bsb_bound source_phdrs rsp av ev uid hw rrnd Hva Hve
  have h2 := rsp_hi_num rsp Hsp_hi
  omega

/-- The value `_start` computes in a2 equals `envp_ptr`.

  The proof shape: `v_add_small` at the `a1 + t0` node, the
  `v_slli_3` bound on the shift, `u_Z2bv` for the two casts, and the
  final `f_equal` by `omega` on the `toNat` readings. -/
theorem envp_ptr_eq (av : List (List byte)) (Hva : valid_argv av) (rsp : word)
    (Hsp_hi : ((rsp.toNat : Int) ≤ sp_window_hi)) :
    v_addi (v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8)) (v_slli (argcN av) 3)) 8
      = envp_ptr av rsp := by
  have hhi := rsp_hi_num rsp Hsp_hi
  have hlen : (av.length : Int) ≤ 1024 := valid_argv_len av Hva
  have hu : ((argcN av).toNat : Int) = (av.length : Int) := u_argcN av Hva
  have h1 : ((BitVec.ofInt 64 ((rsp.toNat : Int) + 8)).toNat : Int)
      = (rsp.toNat : Int) + 8 := by
    rw [u_Z2bv] <;> omega
  have h2 : 8 * ((argcN av).toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [hu]; omega
  have h3 : ((v_slli (argcN av) 3).toNat : Int) = 8 * ((argcN av).toNat : Int) :=
    v_slli_3 (argcN av) h2
  have h4 : ((BitVec.ofInt 64 ((rsp.toNat : Int) + 8)).toNat : Int)
      + ((v_slli (argcN av) 3).toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [h1, h3, hu]; omega
  have h5 : ((v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8)) (v_slli (argcN av) 3)).toNat : Int)
      = ((BitVec.ofInt 64 ((rsp.toNat : Int) + 8)).toNat : Int)
        + ((v_slli (argcN av) 3).toNat : Int) := v_add_small _ _ h4
  have h6 : ((v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8))
      (v_slli (argcN av) 3)).toNat : Int) + 8 < ((2 ^ 64 : Nat) : Int) := by
    rw [h5, h1, h3, hu]; omega
  have h7 : ((v_addi (v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8))
      (v_slli (argcN av) 3)) 8).toNat : Int)
      = ((v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8))
          (v_slli (argcN av) 3)).toNat : Int) + 8 := v_addi_nneg _ 8 (by decide) h6
  have h8 : ((envp_ptr av rsp).toNat : Int)
      = (rsp.toNat : Int) + 8 + 8 * (av.length : Int) + 8 := by
    rw [envp_ptr, u_Z2bv] <;> omega
  have h9 : ((v_addi (v_add (BitVec.ofInt 64 ((rsp.toNat : Int) + 8))
      (v_slli (argcN av) 3)) 8).toNat : Int)
      = ((envp_ptr av rsp).toNat : Int) := by
    rw [h7, h5, h1, h3, hu, h8]
  apply BitVec.eq_of_toNat_eq
  exact_mod_cast h9

/- =========================================================================
   The frame invariant, once per memory the derivation visits
   ========================================================================= -/

/-- The initial overlay is the stack image plus its zero window, both in the
    `valid_sp` ASLR window — far above the loaded segment, hence above
    `.text`. -/
theorem wx_clear_init (av ev : List (List byte)) (rsp : word) (rrnd : EntryDraw)
    (uid hw : word) (Hsp_lo : (sp_window_lo ≤ (rsp.toNat : Int))) :
    mem_clear (wrap_mem source_phdrs rsp av ev uid hw rrnd) stext_lo stext_hi := by
  refine mem_clear_wrap source_phdrs rsp av ev stext_lo stext_hi uid hw rrnd ?_
  have h1 := rsp_lo_num rsp Hsp_lo
  have h2 : stack_max_size = 8388608 :=
    LinuxSem.Common.CatExec.stack_max_size_val
  have h3 : stext_hi = 0x100e4 := rfl
  have h4 : stext_lo = 0x10078 := rfl
  omega

/-- `0#12`'s reading is `0`, so the `addi x, x, 0` of the
    decoded immediate cancels.  Stated for the immediate's `toInt` shape
    because that is the form the decoder hands the step lemmas (a plain
    `v_addi x 0` does not match it syntactically). -/
theorem v_addi_zero12 (x : word) : v_addi x (0#12).toInt = x := by
  rw [show (0#12).toInt = (0 : Int) from rfl, v_addi_0]

/-- A store at or above `stext_hi` leaves the `.text` range clear — the
    no-self-modifying-code condition, in the one form the derivation
    needs. -/
theorem wx_clear_store (m : word → Option byte) (a : word) (bs : List byte)
    (Hcc : mem_clear m stext_lo stext_hi)
    (Ha : (stext_hi : Int) ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    mem_clear (wbytes m a bs) stext_lo stext_hi :=
  mem_clear_wbytes m a bs stext_lo stext_hi Hcc (Or.inl Ha) Hnw

/- =========================================================================
   The derivation: 18 instructions, no output, exit 5.
   ========================================================================= -/

theorem source_wexit (av ev : List (List byte)) (Hva : valid_argv av) (Hve : valid_envp ev)
    (rsp : word) (rrnd : EntryDraw)
    (Hsp_lo : (sp_window_lo ≤ (rsp.toNat : Int)))
    (Hsp_hi : ((rsp.toNat : Int) ≤ sp_window_hi))
    (uid hw : word) :
    to_wexit source_segs
      (init_machine_state source_segs 0x10078 source_phdrs rsp rrnd av ev uid hw)
      [] (BitVec.ofInt 64 5) := by
  have hclear0 := wx_clear_init av ev rsp rrnd uid hw Hsp_lo
  rw [init_mkst]
  -- 0x10078 auipc gp, 0x1
  apply to_wexit.tw_step
  · rfl
  · exact step_auipc_wx source_segs _ _ _ _ _ _ _
      (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
        (by decide) (by decide) (by decide) SF_10078) rfl SD_10078
  · step_simpl
    -- 0x1007c addi gp, gp, -1939 (gp is dead: never read below)
    apply to_wexit.tw_step
    · rfl
    · exact step_addi_wx source_segs _ _ _ _ _ _ _ _
        (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
          (by decide) (by decide) (by decide) SF_1007c) rfl SD_1007c
    · step_simpl
      -- 0x10080 ld a0, 0(sp) — argc out of the initial stack image
      apply to_wexit.tw_step
      · rfl
      · refine step_ld_wx source_segs _ _ _ _ _ _ _ _ (word_le8 (argcN av)) (argcN av)
          (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
            (by decide) (by decide) (by decide) SF_10080) rfl SD_10080 ?_
          (bytes_le_n_to_le_8 (argcN av))
        rw [v_addi_zero12]
        exact read_argc_w source_segs source_phdrs _ av ev uid hw rrnd Hva Hve Hsp_hi
      · step_simpl
        -- 0x10084 addi a1, sp, 8
        apply to_wexit.tw_step
        · rfl
        · refine step_addi_at_wx source_segs _ _ _ _ _ _ _ _
            (BitVec.ofInt 64 ((rsp.toNat : Int) + 8))
            (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
              (by decide) (by decide) (by decide) SF_10084) rfl SD_10084 (by decide) ?_
          rfl
        · step_simpl
          -- 0x10088 slli t0, a0, 3
          apply to_wexit.tw_step
          · rfl
          · exact step_slli_wx source_segs _ _ _ _ _ _ _ _
              (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                (by decide) (by decide) (by decide) SF_10088) rfl SD_10088
          · step_simpl
            -- 0x1008c add a2, a1, t0
            apply to_wexit.tw_step
            · rfl
            · exact step_add_wx source_segs _ _ _ _ _ _ _ _
                (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                  (by decide) (by decide) (by decide) SF_1008c) rfl SD_1008c
            · step_simpl
              -- 0x10090 addi a2, a2, 8 — a2 is now the envp pointer
              apply to_wexit.tw_step
              · rfl
              · refine step_addi_at_wx source_segs _ _ _ _ _ _ _ _ (envp_ptr av rsp)
                  (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                    (by decide) (by decide) (by decide) SF_10090) rfl SD_10090 (by decide) ?_
                exact envp_ptr_eq av Hva rsp Hsp_hi
              · step_simpl
                -- 0x10094 auipc t1, 0x0
                apply to_wexit.tw_step
                · rfl
                · exact step_auipc_wx source_segs _ _ _ _ _ _ _
                    (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                      (by decide) (by decide) (by decide) SF_10094) rfl SD_10094
                · step_simpl
                  -- 0x10098 addi t1, t1, 84 — t1 = &__environ = 0x100e8
                  apply to_wexit.tw_step
                  · rfl
                  · refine step_addi_at_wx source_segs _ _ _ _ _ _ _ _
                      (BitVec.ofInt 64 0x100e8)
                      (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                        (by decide) (by decide) (by decide) SF_10098) rfl SD_10098 (by decide) ?_
                    rfl
                  · step_simpl
                    -- 0x1009c sd a2, 0(t1) — the envp pointer into `__environ`
                    apply to_wexit.tw_step
                    · rfl
                    · refine step_sd_at_wx source_segs _ _ _ _ _ _ _ _
                        (BitVec.ofInt 64 0x100e8) (envp_ptr av rsp)
                        (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear0
                          (by decide) (by decide) (by decide) SF_1009c) rfl SD_1009c rfl
                          rfl ?_
                      exact source_store_ok _ _ 8 (by decide) (by decide)
                    · step_simpl
                      -- the overlay now carries the `__environ` write; the
                      -- frame invariant survives it (it lands above `.text`)
                      have hclear1 : mem_clear
                          (wbytes (wrap_mem source_phdrs rsp av ev uid hw rrnd)
                            (BitVec.ofInt 64 0x100e8) (word_to_le_bytes 8 (envp_ptr av rsp)))
                          stext_lo stext_hi :=
                        wx_clear_store _ _ _ hclear0 (by decide)
                          (by rw [length_N_to_le_bytes]; decide)
                      -- 0x100a0 jal ra, main (0x100d0)
                      apply to_wexit.tw_step
                      · rfl
                      · exact step_jal_link_wx source_segs _ _ _ _ _ _ _
                          (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear1
                            (by decide) (by decide) (by decide) SF_100a0) rfl SD_100a0
                      · step_simpl
                        -- 0x100d0 lui a5, 0x10
                        apply to_wexit.tw_step
                        · rfl
                        · exact step_lui_wx source_segs _ _ _ _ _ _ _
                            (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear1
                              (by decide) (by decide) (by decide) SF_100d0) rfl SD_100d0
                        · step_simpl
                          -- 0x100d4 li a4, 5
                          apply to_wexit.tw_step
                          · rfl
                          · refine step_addi_at_wx source_segs _ _ _ _ _ _ _ _
                              (BitVec.ofInt 64 5)
                              (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear1
                                (by decide) (by decide) (by decide) SF_100d4) rfl SD_100d4 (by decide) ?_
                            rfl
                          · step_simpl
                            -- 0x100d8 sb a4, 228(a5) — flag := 5, in the SAME
                            -- RWX segment the code runs from
                            apply to_wexit.tw_step
                            · rfl
                            · refine step_sb_at_wx source_segs _ _ _ _ _ _ _ _
                                (BitVec.ofInt 64 0x100e4) (BitVec.ofInt 64 5) (BitVec.ofInt 8 5)
                                (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear1
                                  (by decide) (by decide) (by decide) SF_100d8) rfl SD_100d8 rfl rfl
                                (by decide) ?_
                              exact source_store_ok _ _ 1 (by decide) (by decide)
                            · step_simpl
                              -- the second store, likewise above `.text`
                              have hclear2 : mem_clear
                                  (wbytes (wbytes (wrap_mem source_phdrs rsp av ev uid hw rrnd)
                                      (BitVec.ofInt 64 0x100e8) (word_to_le_bytes 8 (envp_ptr av rsp)))
                                    (BitVec.ofInt 64 0x100e4) [BitVec.ofInt 8 5])
                                  stext_lo stext_hi :=
                                wx_clear_store _ _ _ hclear1 (by decide) (by decide)
                              -- 0x100dc lbu a0, 228(a5) — read flag back OUT OF
                              -- THE OVERLAY the store just wrote
                              apply to_wexit.tw_step
                              · rfl
                              · refine step_lbu_wx source_segs _ _ _ _ _ _ _ _
                                  (BitVec.ofInt 8 5)
                                  (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear2
                                    (by decide) (by decide) (by decide) SF_100dc) rfl SD_100dc ?_
                                exact rdn_wbytes_hit source_segs [BitVec.ofInt 8 5] _ _ (by decide)
                              · step_simpl
                                -- 0x100e0 ret
                                apply to_wexit.tw_step
                                · rfl
                                · refine step_jalr_x0_wx source_segs _ _ _ _ _ _ _
                                    (BitVec.ofInt 64 0x100a4)
                                    (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear2
                                      (by decide) (by decide) (by decide) SF_100e0) rfl SD_100e0 ?_
                                  rfl
                                · step_simpl
                                  -- 0x100a4 li a7, 93
                                  apply to_wexit.tw_step
                                  · rfl
                                  · refine step_addi_at_wx source_segs _ _ _ _ _ _ _ _
                                      (BitVec.ofInt 64 93)
                                      (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear2
                                        (by decide) (by decide) (by decide) SF_100a4) rfl TD_10011a0 (by decide) ?_
                                    rfl
                                  · step_simpl
                                    -- 0x100a8 ecall — exit(5)
                                    apply to_wexit.tw_step
                                    · rfl
                                    · exact step_ecall_wx source_segs _ _ _ _ _
                                        (wx_fetch_intro source_segs _ _ _ stext_lo stext_hi source_no_ro_exec hclear2
                                          (by decide) (by decide) (by decide) SF_100a8) rfl
                                    · refine tw_exit_coden source_segs _ _ _ _ (BitVec.ofInt 64 5) ?_ ?_ ?_
                                      · rfl
                                      · rfl
                                      · decide

end RwxFlagNsSource

end LinuxSem.Examples.RwxFlagNs


