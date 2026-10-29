/-
  * Common.WxExec — step lemmas for code in a WRITABLE executable (w+x) segment

  PROOF-SIDE FILE (not part of the trusted specification).

  [RiscvSemantics.step] fetches an instruction from an immutable
  (x and not w) segment with the static [fetch_word], and from a
  WRITABLE executable (w+x) segment — the merged RWX layout GNU ld's
  default [-z noseparate-code] produces — with the overlay-aware
  [fetch_word_ov], which reads the writable overlay first and the
  segment image underneath.  The per-example generated
  fetch facts for a w+x image are stated over the STATIC projection
  [fetch_word_wx] (a pure function of the snapshot, closed by
  [decide]); this file supplies the bridge that turns them into
  [fetch_word_ov] facts, and the per-instruction step lemmas that
  consume them:

  - [mem_clear m lo hi] — the FRAME INVARIANT a w+x example's proof
    carries: the overlay misses the whole [.text] range [lo, hi).
    Established at [init_machine_state] ([mem_clear_wrap]: the
    initial overlay is the stack image, far above every loaded
    segment) and preserved by each store the program makes
    ([mem_clear_wbytes]: the store target is disjoint from the text
    range — data stores in the same RWX segment are fine, only a
    store OVER the code would break it, i.e. self-modifying code is
    exactly what the invariant excludes).
  - [fetch_word_ov_of_wx] — under the invariant, the overlay-aware
    fetch of an address inside the clear range rewrites to the static
    [fetch_word_wx], so the generated lemma closes the fetch.
  - [wx_fetch]/[wx_fetch_intro] — the two facts a step needs
    ([fetch_word] declines: nothing immutable-executable covers the
    pc; [fetch_word_ov] succeeds), packed as one premise so the
    per-instruction lemmas below stay one-premise-per-concern.
    [fetch_word_none_no_ro_exec] discharges the first over a whole
    image at once: an image with NO immutable executable segment
    (e.g. the single-RWX-segment layout) never satisfies the static
    fetch anywhere.
  - [step_*_wx] — mirrors of the [PropExec]/[SeqExec]/[MmapSim]
    per-instruction step lemmas with the fetch premise replaced by
    [wx_fetch]; conclusions are IDENTICAL, so everything downstream
    of a step (chain relations, register/memory normalization,
    [rdn] reads) is shared with the immutable-code examples.

  Only the instruction shapes the w+x example actually walks are
  mirrored; extend the family as new w+x examples need more.

  NOTES.

  - `Z` → `Int`, `bv_unsigned w` → `(w.toNat : Int)`,
    `bv_signed w` → `w.toInt`, `Z.shiftl z 12` → `zshiftl z 12`,
    `Z_to_bv n z` → `BitVec.ofInt n z`, `decode_any` → `decodeAny`,
    `N`/`nat` → `Nat`, `OpImm ALU_ADD` → `Instr.opImm .ADD`,
    `Load SZ1 false` → `Instr.load .SZ1 false`, `Store SZ8` →
    `Instr.store .SZ8`, `forallb` → `List.all`, `negb` → `!`.
  - `Section WithFP1`'s / `Section WithFP2`'s `Context {fx : FPState}`
    becomes the ambient `variable [fx : FPState]` (the same house rule
    `PropExec`/`SeqExec`/`MmapSim` follow).
  - `find_segment`'s range test is a `decide`-carrying `Bool`
    (`decide (base ≤ addr) && decide (addr + n ≤ top)`), so the two
    inversion lemmas unpack [Bool.and_eq_true]/[decide_eq_true_eq]
    rather than reading `Z.leb_le`.
 [mem_clear_wrap] also needs
    [CatExec.stack_max_size_val] (`stack_max_size = 8388608`) because
    `stack_max_size` is an opaque `Int` definition here.
  - `length_Z_to_le_bytes` is already a `BvBase` theorem; as
    `CatExec` does, it is restated here under this file's namespace so that
    proof scripts citing `WxExec.length_Z_to_le_bytes` work unchanged.   - The  `Ltac wx_step_pipeline` becomes the Lean `macro
    wx_step_pipeline` below (the same theorem list `PropExec`'s
    `step_pipeline` uses, with the two halves of [wx_fetch] replacing
    the single [fetch_word] fact); the load lemmas use
    `wx_load_start2`, the counterpart of `PropExec`'s
    `step_load_start2`.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.ExitSim

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.ExitSim

namespace LinuxSem.Common.WxExec

/-- The FP state at process entry, so that the `PropExec`/`CatExec` lemmas
    (whose proofs go through it) elaborate.  Same local instance
    `SpinAlg.lean` and `DrainAlg.lean` declare. -/
local instance wsexec_fx : FPState := PropExec.fx0

/- =========================================================================
   find_segment inversion
   ========================================================================= -/

theorem find_segment_in (segs : List Segment) (a n : Int) (seg : Segment)
    (H : find_segment segs a n = some seg) : seg ∈ segs := by
  induction segs generalizing seg with
  | nil => simp [find_segment] at H
  | cons s rest ih =>
    simp only [find_segment] at H
    split at H
    · simp only [Option.some.injEq] at H
      subst H
      simp
    · exact List.mem_cons_of_mem s (ih seg H)

theorem find_segment_range (segs : List Segment) (a n : Int) (seg : Segment)
    (H : find_segment segs a n = some seg) :
    (seg.seg_base : Int) ≤ a ∧ a + n ≤ (seg.seg_base : Int) + (seg.seg_size : Int) := by
  induction segs generalizing seg with
  | nil => simp [find_segment] at H
  | cons s rest ih =>
    simp only [find_segment] at H
    split at H
    · rename_i hb
      simp only [Option.some.injEq] at H
      subst H
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
    · exact ih seg H

/- =========================================================================
   The static fetch declines everywhere on an all-w+x image
   ========================================================================= -/

/-- No segment of the image is executable WITHOUT being writable — true
    of the single-RWX-segment layout, checked once per image by
    [decide].  Then the static [fetch_word] (gate [x /\ ~w])
    declines at EVERY address, which is the first half of [wx_fetch]
    at every step, discharged once instead of per pc. -/
def no_ro_exec (segs : List Segment) : Bool :=
  segs.all (fun s => !(seg_executable s && !seg_writable s))

theorem code_read_none_no_ro_exec (segs : List Segment) (a : word) (n : Nat)
    (Hro : no_ro_exec segs = true) : code_read segs a n = none := by
  unfold code_read
  cases hfs : find_segment segs (a.toNat : Int) (n : Int) with
  | none => rfl
  | some seg =>
    simp only []
    have hin : seg ∈ segs := find_segment_in segs (a.toNat : Int) (n : Int) seg hfs
    have hro := (List.all_eq_true.mp Hro) seg hin
    cases hg : (seg_executable seg && !seg_writable seg) with
    | false => simp [hg]
    | true => simp [hg] at hro

theorem fetch_word_none_no_ro_exec (segs : List Segment) (pc : word)
    (Hro : no_ro_exec segs = true) : fetch_word segs pc = none := by
  unfold fetch_word
  by_cases hodd : pc.toNat % 2 ≠ 0
  · rw [ite_eq_left hodd]
  · rw [ite_eq_right hodd, code_read_none_no_ro_exec segs pc 4 Hro]

/- =========================================================================
   The frame invariant: the overlay misses the text range
   ========================================================================= -/

def mem_clear (m : word → Option byte) (lo hi : Int) : Prop :=
  ∀ a : word, lo ≤ (a.toNat : Int) ∧ (a.toNat : Int) < hi → m a = none

/-- Established at [init_machine_state]: the initial overlay is the
    stack image plus its zero window, both inside the [valid_sp] ASLR
    window far above every loaded segment. -/
theorem mem_clear_wrap (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (lo hi : Int) (uid hw : word) (rnd : EntryDraw)
    (Hhi : hi ≤ (sp.toNat : Int) - stack_max_size) :
    mem_clear (wrap_mem ph sp argv envp uid hw rnd) lo hi := by
  intro a Ha
  have hsms := CatExec.stack_max_size_val
  unfold wrap_mem stack_to_mem
  have hsp : ¬ (sp.toNat ≤ a.toNat) := by omega
  have hgate : ¬ (((sp.toNat : Int) - stack_max_size ≤ (a.toNat : Int)) &&
      ((a.toNat : Int) < (sp.toNat : Int))) := by
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  simp only [ite_eq_right hsp, ite_eq_right hgate]

/-- Preserved by a store whose target range is disjoint from the clear
    range — every store an ordinary (non-self-modifying) w+x program
    makes.  The no-wrap bound keeps the write walk from wrapping into
    the range from above. -/
theorem mem_clear_wbytes (m : word → Option byte) (addr : word) (bs : List byte)
    (lo hi : Int) (Hcc : mem_clear m lo hi)
    (Hdisj : hi ≤ (addr.toNat : Int) ∨ (addr.toNat : Int) + (bs.length : Int) ≤ lo)
    (Hnw : (addr.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    mem_clear (wbytes m addr bs) lo hi := by
  intro a Ha
  rcases Hdisj with Habove | Hbelow
  · rw [wbytes_below bs m addr a Hnw (by omega)]
    exact Hcc a Ha
  · rw [wbytes_above bs m addr a (by omega)]
    exact Hcc a Ha

/-- [word_to_le_bytes n v] really is [n] bytes (feeds the length
    side conditions of [mem_clear_wbytes]). -/
theorem length_Z_to_le_bytes (n : Nat) (z : Int) : (Z_to_le_bytes n z).length = n :=
  LinuxSem.LinuxProcessSem.length_Z_to_le_bytes n z

theorem length_word_to_le_bytes (n : Nat) (v : word) :
    (word_to_le_bytes n v).length = n := by
  unfold word_to_le_bytes
  exact length_Z_to_le_bytes n (v.toNat : Int)

/- =========================================================================
   The fetch bridge: overlay-aware fetch = static fetch under clear
   ========================================================================= -/

/-- Under a clear overlay, the per-segment overlay-first read is the
    static image read. -/
theorem seg_ov_read_bytes_static (n : Nat) : ∀ (m : word → Option byte)
    (seg : Segment) (addr : word),
    (∀ a : word, (addr.toNat : Int) ≤ (a.toNat : Int) ∧
        (a.toNat : Int) < (addr.toNat : Int) + (n : Int) → m a = none) →
    (addr.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
    (seg.seg_base : Int) ≤ (addr.toNat : Int) →
    seg_ov_read_bytes m seg addr n
      = segment_read_bytes seg.seg_bytes (addr.toNat - seg.seg_base) n := by
  induction n with
  | zero => intro m seg addr Hclear Hnw Hbase; rfl
  | succ n ih =>
    intro m seg addr Hclear Hnw Hbase
    have hcur : m addr = none := Hclear addr ⟨by omega, by omega⟩
    simp only [seg_ov_read_bytes, hcur]
    cases hb : segment_byte_at seg.seg_bytes (addr.toNat - seg.seg_base) with
    | none => simp only [hb, segment_read_bytes]
    | some b =>
      simp only [hb, segment_read_bytes]
      cases n with
      | zero => rfl
      | succ n =>
        have hn1 : ((n + 1 + 1 : Nat) : Int) = (n : Int) + 1 + 1 := by simp
        have Hu1 : ((addr + 1).toNat : Int) = (addr.toNat : Int) + 1 := by
          refine u_add1 addr ?_
          omega
        have Hu1N : (addr + 1).toNat = addr.toNat + 1 := by
          have h : ((addr + 1).toNat : Int) = ((addr.toNat + 1 : Nat) : Int) := by
            rw [Hu1]
            omega
          exact Int.ofNat.inj h
        have HbaseN : seg.seg_base ≤ addr.toNat := Int.ofNat_le.mp Hbase
        rw [ih m seg (addr + 1) ?_ ?_ ?_]
        · rw [show (addr + 1).toNat - seg.seg_base
              = (addr.toNat - seg.seg_base) + 1 from by
            rw [Hu1N, Nat.add_comm addr.toNat 1, Nat.add_sub_assoc HbaseN,
              Nat.add_comm 1 (addr.toNat - seg.seg_base)]]
          cases segment_read_bytes seg.seg_bytes (addr.toNat - seg.seg_base + 1) (n + 1) <;> rfl
        · intro a Ha
          exact Hclear a ⟨by omega, by omega⟩
        · rw [Hu1]
          omega
        · rw [Hu1]
          omega

/-- The bridge: an address whose 4 fetched bytes lie inside the clear
    range fetches through the overlay exactly what the static w+x
    projection says — so a generated [fetch_word_wx] lemma closes the
    overlay-aware fetch at every step. -/
theorem fetch_word_ov_of_wx (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) (lo hi : Int)
    (Hcc : mem_clear m lo hi)
    (Hlo : lo ≤ (pc.toNat : Int))
    (Hhi : (pc.toNat : Int) + 4 ≤ hi)
    (Hceil : hi ≤ ((2 ^ 64 : Nat) : Int))
    (Hwx : fetch_word_wx segs pc = some w) :
    fetch_word_ov segs m pc = some w := by
  unfold fetch_word_wx at Hwx
  unfold fetch_word_ov
  by_cases hodd : pc.toNat % 2 ≠ 0
  · simp only [ite_eq_left hodd] at Hwx ⊢
    exact absurd Hwx (by simp)
  · rw [ite_eq_right hodd] at Hwx ⊢
    unfold code_read_wx at Hwx
    unfold code_read_ov
    generalize hfs : find_segment segs (pc.toNat : Int) 4 = fs at Hwx ⊢
    cases fs with
    | none =>
      simp only [] at Hwx ⊢
      exact Hwx
    | some seg =>
      simp only [] at Hwx ⊢
      have hg : (seg_executable seg && seg_writable seg) = true := by
        cases hgate : (seg_executable seg && seg_writable seg) with
        | false => simp [hgate] at Hwx
        | true => rfl
      rw [ite_eq_left hg] at Hwx ⊢
      have Hrange := find_segment_range segs (pc.toNat : Int) 4 seg hfs
      rw [seg_ov_read_bytes_static 4 m seg pc ?_ ?_ ?_]
      · exact Hwx
      · intro a Ha
        exact Hcc a ⟨by omega, by omega⟩
      · omega
      · exact Hrange.1

/- =========================================================================
   The packed fetch premise, and the step-to-decode reduction
   ========================================================================= -/

/-- What one w+x step needs of the fetch: the static (immutable-code)
    fetch declines and the overlay-aware fetch yields [w]. -/
def wx_fetch (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) : Prop :=
  fetch_word segs pc = none ∧ fetch_word_ov segs m pc = some w

/-- The one constructor a proof uses per step: image-level [no_ro_exec]
    (checked once), the carried [mem_clear] invariant, the pc-in-text
    bounds, and the generated static fetch fact. -/
theorem wx_fetch_intro (segs : List Segment) (m : word → Option byte)
    (pc : word) (w : BitVec 32) (lo hi : Int)
    (Hro : no_ro_exec segs = true)
    (Hcc : mem_clear m lo hi)
    (Hlo : lo ≤ (pc.toNat : Int))
    (Hhi : (pc.toNat : Int) + 4 ≤ hi)
    (Hceil : hi ≤ ((2 ^ 64 : Nat) : Int))
    (Hwx : fetch_word_wx segs pc = some w) :
    wx_fetch segs m pc w := by
  refine ⟨fetch_word_none_no_ro_exec segs pc Hro, ?_⟩
  exact fetch_word_ov_of_wx segs m pc w lo hi Hcc Hlo Hhi Hceil Hwx

/- =========================================================================
   Per-instruction step lemmas (w+x fetch)

   Statements and proofs mirror PropExec/SeqExec/MmapSim; only the
   fetch premise differs.  Conclusions are IDENTICAL.
   ========================================================================= -/

/- The  `Ltac wx_step_pipeline`: `PropExec`'s `step_pipeline`
    with the two halves of [wx_fetch] replacing the single [fetch_word]
    fact, so the fetch dispatch takes the SECOND branch.  Keep the two in
    sync. -/
open Lean Parser Tactic in
macro "wx_step_pipeline" hn:simpLemma "," hov:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, $hn, $hov, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, interp_eff_accesses, mkAccessReport,
      rset, rget, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet, bvmap_set,
      getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, w0, Bool.false_eq_true, reduceIte,
      ite_true, ite_false])

/- [wx_step_pipeline]'s load counterpart (`PropExec.step_load_start2`). -/
open Lean Parser Tactic in
macro "wx_load_start2" hn:simpLemma "," hov:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, $hn, $hov, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, load_val, interp_eff_accesses,
      mkAccessReport, rset, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet,
      bvmap_set, Bool.false_eq_true, reduceIte, ite_true, ite_false, width_bytes])

variable [fx : FPState]

theorem step_opimm_gen_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg)
    (imm : BitVec 12)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm op rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem step_addi_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .ADD rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_addi (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  rw [step_opimm_gen_wx segs regs pc mem rom w .ADD rd rs imm ⟨Hn, Hov⟩ Hecall Hdecode,
    alu_addi (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- [step_addi_wx] with the writeback value pre-normalized
    ([SeqExec.step_addi_at]'s twin). -/
theorem step_addi_at_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .ADD rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_addi (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  rw [step_addi_wx segs regs pc mem rom w rd rs imm ⟨Hn, Hov⟩ Hecall Hdecode]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

theorem step_shiftimm_gen_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg)
    (sh : BitVec 6)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh))) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem step_slli_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm .SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_slli (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  rw [step_shiftimm_gen_wx segs regs pc mem rom w .SLL rd rs sh ⟨Hn, Hov⟩ Hecall Hdecode,
    alu_slli (getr regs rs) sh]

theorem step_op_gen_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs1 rs2 : reg)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

theorem step_add_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_add (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  rw [step_op_gen_wx segs regs pc mem rom w .ADD rd rs1 rs2 ⟨Hn, Hov⟩ Hecall Hdecode,
    alu_add (getr regs rs1) (getr regs rs2)]

theorem step_lui_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.lui rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lui (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hb : sext 64 (imm ++ (0#12)) = v_lui (zshiftl imm.toInt 12) := b_lui imm
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

theorem step_auipc_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.auipc rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_auipc pc (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hb : pc + sext 64 (imm ++ (0#12)) = v_auipc pc (zshiftl imm.toInt 12) :=
    b_auipc pc imm
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

theorem step_jal_link_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 21)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (btgt pc imm.toInt) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, b_npc4]

theorem step_jalr_gen_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (jalr_tgt (getr regs rs1) imm.toInt) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hb : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide : 12 ≤ 64)
  have hj : (getr regs rs1 + sext 64 imm) &&& ~~~(1 : word)
      = jalr_tgt (getr regs rs1) imm.toInt := b_jalr _ imm
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  simp only [getr, bv_eqb0_is_x0, w1, reg_get, w0] at hb hj ⊢
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, w0, w1, Bool.false_eq_true,
    reg_get] at hb hj ⊢
  all_goals rw [hj]
  all_goals simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, Nat.zero_add]

/-- [ret] / tail jump, target named ([SeqExec.step_jalr_x0]'s twin). -/
theorem step_jalr_x0_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12)
    (tgt : word)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jalr 0 rs1 imm, 4))
    (Ht : getr regs rs1 = tgt) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_jalr tgt imm.toInt) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  rw [step_jalr_gen_wx segs regs pc mem rom w 0 rs1 imm ⟨Hn, Hov⟩ Hecall Hdecode, Ht]
  simp only [bv_eqb_refl, ite_true, v_jalr, jalr_tgt]

theorem step_ecall_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
                   ms_svc_pending := some (getr regs 17), ms_resv := none,
                   ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom } := by
  obtain ⟨Hn, Hov⟩ := Hwx
  simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, Hn, Hov,
    decode_exec_accesses, Hecall, drop_access_report, mkAccessReport, ms_reg, getr,
    bv_eqb0_is_x0, is_x0_0, ite_true, ite_false, w0]

theorem step_lbu_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (b : byte)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ1 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (BitVec.ofInt 64 (b.toNat : Int))) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = some [b] := by
    rw [hba, ov_rdn]; exact Hread
  wx_load_start2 Hn, Hov, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]
  simp only [bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, zext8_le_word]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem step_ld_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ8 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 8 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd v) (v_addi pc 4) mem rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 8 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : bits 0 64 (le_bytes_to_word bs) = v := by
    rw [le_word_v bs v Hv]
    apply BitVec.eq_of_toNat_eq
    simp only [bits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (by have := v.isLt; omega)
  wx_load_start2 Hn, Hov, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

theorem step_sd_val_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ8 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 8 (getr regs rs2))) rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 8 = true := by
    rw [hba]; exact Hok
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, word_to_le_bytes, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [step_sd_val_wx] with address and value pre-normalized
    ([SeqExec.step_sd_at]'s twin). -/
theorem step_sd_at_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ8 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hok : store_ok segs mem a 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  rw [step_sd_val_wx segs regs pc mem rom w rs1 rs2 imm Hwx Hecall Hdecode]
  · simp only [Ha, Hv]
  · rw [Ha]; exact Hok

theorem step_sb_val_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 1 (getr regs rs2))) rom) := by
  obtain ⟨Hn, Hov⟩ := Hwx
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 1 = true := by
    rw [hba]; exact Hok
  wx_step_pipeline Hn, Hov, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, store_bytes_low8, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [step_sb_val_wx] with address, value and stored byte pre-normalized
    ([MmapSim.step_sb_at]'s twin). -/
theorem step_sb_at_wx (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word) (b : byte)
    (Hwx : wx_fetch segs mem pc w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hb : BitVec.ofInt 8 (v.toNat : Int) = b)
    (Hok : store_ok segs mem a 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom) := by
  have hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true := by
    rw [Ha]; exact Hok
  rw [step_sb_val_wx segs regs pc mem rom w rs1 rs2 imm Hwx Hecall Hdecode hok]
  simp only [Ha, Hv, word_to_le_bytes, Z_to_le_bytes, Hb]
