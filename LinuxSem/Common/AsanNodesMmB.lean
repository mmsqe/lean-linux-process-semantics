/-
  * AsanNodesMmB — node obligations M4 (brk2), M5 (YBrk / YSetTid / YMunmap), M6 (exit)
    of AsanNodesIface, proved on the spec.
   module-level imports `AX2`, `AX2S`, `AP`, `APS` are the `open`s
  below; `AsanNodesMmLib` and `AsanNodesLibE` are the two libraries the nodes
  are built on.
 Nothing is
  deferred; the block that used to carry `node_brk2_sound`'s statement is now
  the closing "nothing deferred" note at the end of this file.
  DEVIATION in the small facts: the twenty helpers whose faithful owner is
  `AsanNodesMmLib` (`sum_sizes_app`, `zfill_in`, `in_ivs_cons`,
  `vm_backing_used_le`, `bv5_of_nat` + the seven `bv5_*`, `some_inj`,
  `CEIL_eq`, `KHI_eq`, `FLOOR_eq`, `Z_to_bv64_m1`, `in_allow_ext`,
  `seps_map_disjoint`, `covered_maps_subtract`) are NOT restated here any
  more — the local copies this file used to carry are deleted and the names
  resolve to `AsanNodesMmLib` through the `open` below, so the two copies
  cannot drift.
  declarations (8, each flagged at its declaration).  Two are the
  inversions  performs INLINE and which this tree names once so that no
  `check`-equation or `Int`-match is ever re-stated (the `whnf` cliff):
  `node_exit_some` and `zland_255`.  The other six
  are `node_brk2_sound`'s granted-grow abbreviations — `brk2_vm`,
  `brk2_model`, `brk2_req`, `brk2_R`, `brk2_FULL`, `brk2_mid` — which
   introduces with `set (h' := …)`, `set (model' := …)`,
  `set (req := …)`, `set (R' := …)`, `set (FULL' := …)` and `set (csB := …)`
  and then re-folds with `fold`; a Lean `have` is opaque and a `let` is opaque
  to `omega` (§5.7), so each is a six-line `def` instead, and the proofs read
  them back with `rfl`/`show`.  No statement changes because of them.
  DEVIATION (1, statement-level, inherited): `node_exit` returns `zland code
  255`, and this tree's `zland` has no `Int.land`; `zland_255` is the bridge.
  See `AsanNodesLibE`'s `bv_and_255` note and

  Word hygiene: this file contains no proof hole and no extra postulate.
-/

import LinuxSem.Common.AsanNodesMmLib
import LinuxSem.Common.AsanNodesLibE
import LinuxSem.Common.AsanNodesIface
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanNodesMmB

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamExec
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AgentNodes
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.BackingAlgebra
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.MmapSim
open LinuxSem.Common.AsanNodesMmLib
open LinuxSem.Common.AllocSim
open LinuxSem.Common.AsanCeil
open LinuxSem.Common.Nodes
open LinuxSem.Common.RefNodes
open LinuxSem.Common.AsanNodesIface
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The entry FP state. -/
local instance asannodesmmb_fx : PropExec.FPState := PropExec.fx0

/-! #########################################################################
    ## A. Checker-side read-backs and small facts
    ######################################################################### -/

/-- `lit_diff e f = some d`: `u e ≡ u f + d (mod 2^64)` with `0 ≤ d < 2^64`. -/
theorem lit_diff_sound (E : env) (e f : expr) (d : Int) (H : lit_diff e f = some d) :
    0 ≤ d ∧ d < two64 ∧ (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) % two64 = d := by
  unfold lit_diff at H
  generalize h : esub e f = g at H
  cases g with
  | ELit z =>
    simp only [Option.some.injEq] at H
    subst H
    have hden : edenot E (esub e f) = edenot E e - edenot E f := by
      rw [esub, mkAlu_denot, SymExec.alu64_sub_eq]
    have hz : bv_unsigned (edenot E (esub e f)) = z % two64 := by
      rw [h]; exact u_lit64 z
    have hz2 : bv_unsigned (edenot E e - edenot E f) = z % two64 := by
      rw [← hden]; exact hz
    have hmod : (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) % two64 = z % two64 := by
      rw [show (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) % two64
            = bv_unsigned (edenot E e - edenot E f) from by rw [u_sub64]; rfl]
      exact hz2
    rw [hmod]
    exact ⟨Int.emod_nonneg _ (by decide : two64 ≠ 0),
           Int.emod_lt_of_pos _ (by decide : (0:Int) < two64), rfl⟩
  | EVar n => simp at H
  | EAlu a b c => simp at H
  | EAluw a b c => simp at H
  | EMd a b c => simp at H
  | EMdw a b c => simp at H
  | EExt a b c d => simp at H
  | EBlob a b c d => simp at H

/-- An overlapping entry refutes `region_free`. -/
theorem region_free_false_of_overlap (lo n a sz : word) (L : List (word × word))
    (Hin : (a, sz) ∈ L) (Hov : iv_overlap lo n a sz = true) :
    region_free L lo n = false := by
  induction L with
  | nil => cases Hin
  | cons p L ih =>
    obtain ⟨a', sz'⟩ := p
    rcases List.mem_cons.mp Hin with h | Hin
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
      simp only [region_free, Hov, Bool.not_true, Bool.false_and]
    · simp only [region_free]
      rw [ih Hin]
      simp

/-- A free region misses every entry of the ledger it was checked against. -/
theorem region_free_intro (L : List (word × word)) (lo n : word)
    (H : ∀ a sz, (a, sz) ∈ L → iv_overlap lo n a sz = false) :
    region_free L lo n = true := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨a, sz⟩ := p
    simp only [region_free]
    rw [H a sz (List.mem_cons_self ..),
      ih (fun a' sz' h' => H a' sz' (List.mem_cons_of_mem _ h'))]
    rfl

/-- The `Some`-pair injectivity  spells `Some_pair_inj`. -/
theorem Some_pair_inj {T U : Type} (a c : T) (b d : U) (H : some (a, b) = some (c, d)) :
    a = c ∧ b = d := by
  simpa using H

/-- `regs_ok` survives writing back the value a register already holds. -/
theorem regs_ok_regupd_same (E : env) (sr : List expr) (R : BvMap word) (r : reg) (v : word)
    (HR : regs_ok E sr R) (Hv : getr R r = v) (Hr : r ≠ 0) : regs_ok E sr (regupd R r v) := by
  intro r'
  by_cases h : r' = r
  · rw [h]
    rw [getr_same R r v Hr, ← Hv]
    exact HR r
  · rw [getr_other R r v r' h]
    exact HR r'

/-- `seps` inversion at a cons. -/
theorem seps_cons_inv (p : word × word) (l : List (word × word)) (H : seps (p :: l)) :
    (∀ x ∈ l, iv_disjoint p x) ∧ seps l := by
  cases H with
  | cons p l hd tl => exact ⟨hd, tl⟩

/-- Distinct members of a separated ledger of nonempty intervals are disjoint. -/
theorem seps_In_disjoint (l : List (word × word)) (p q : word × word)
    (Hs : seps l) (Hpos : ∀ iv ∈ l, 0 < bv_unsigned iv.2) (Hp : p ∈ l) (Hq : q ∈ l)
    (Hne : p ≠ q) : iv_disjoint p q := by
  induction l with
  | nil => cases Hp
  | cons h t ih =>
    obtain ⟨Hf, Ht⟩ := seps_cons_inv h t Hs
    have Hpos' : ∀ iv ∈ t, 0 < bv_unsigned iv.2 :=
      fun iv hiv => Hpos iv (List.mem_cons_of_mem _ hiv)
    rcases List.mem_cons.mp Hp with h1 | Hp
    · rcases List.mem_cons.mp Hq with h2 | Hq
      · rw [h1, h2] at Hne; exact absurd rfl Hne
      · rw [h1]; exact Hf q Hq
    · rcases List.mem_cons.mp Hq with h2 | Hq
      · have D := Hf p Hp
        rw [h2] at *
        unfold iv_disjoint at *
        omega
      · exact ih Ht Hpos' Hp Hq

/-- A separated ledger of nonempty intervals has no duplicate. -/
theorem seps_NoDup (l : List (word × word)) (Hs : seps l)
    (Hpos : ∀ iv ∈ l, 0 < bv_unsigned iv.2) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons h t ih =>
    obtain ⟨Hf, Ht⟩ := seps_cons_inv h t Hs
    rw [List.nodup_cons]
    refine ⟨?_, ih Ht (fun iv hiv => Hpos iv (List.mem_cons_of_mem _ hiv))⟩
    intro hin
    have D := Hf h hin
    have hp := Hpos h (List.mem_cons_self ..)
    unfold iv_disjoint at D
    omega

/-- The eager meter, read through `BackingAlgebra.live_msa`. -/
theorem eager_used_sem_brk (m : Model) (W : ivs_wf (m_vmmaps m).vm_maps) :
    eager_used m
      = sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps := by
  have H := vm_backing_used_sem_maps m W
  rw [vm_backing_used_split] at H
  omega

/-- One more ledger entry costs at most its size. -/
theorem eager_used_cons_le (m : Model) (b n : word) (h' : VmMaps)
    (W : ivs_wf (m_vmmaps m).vm_maps) (Wb : iv_wf (b, n))
    (Hm : h'.vm_maps = (b, n) :: (m_vmmaps m).vm_maps)
    (Hn : h'.vm_noaccess = (m_vmmaps m).vm_noaccess) :
    eager_used (with_vmmaps h' m) ≤ eager_used m + bv_unsigned n := by
  have W' : ivs_wf (m_vmmaps (with_vmmaps h' m)).vm_maps := by
    rw [LinuxProcessSem.m_vmmaps_with_vmmaps, Hm]; exact ivs_wf_cons (b, n) _ Wb W
  rw [eager_used_sem_brk _ W', eager_used_sem_brk _ W]
  rw [LinuxProcessSem.m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hm, Hn]
  show iv_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x)) (b, n)
      + sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps
    ≤ sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps + bv_unsigned n
  have Hc : iv_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x)) (b, n)
      ≤ bv_unsigned n := by
    have h := zcount_le_len (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
      (B (b, n)) (S (b, n)).toNat
    have hs : ((S (b, n)).toNat : Int) = bv_unsigned n := by
      show (((n.toNat : Int)).toNat : Int) = (n.toNat : Int)
      rw [Int.toNat_of_nonneg (Int.natCast_nonneg n.toNat)]
    unfold iv_count
    omega
  omega

/-- The refuted direction of `RefNodes.brk_grow_ok_aligned_intro`: an
    overlapping ledger entry blocks the aligned grow. -/
theorem brk_grow_ok_aligned_refuted (m : Model) (d : Int) (a sz : word)
    (Hbal : ((m_vmmaps m).vm_brk.toNat : Int) % page_size = 0)
    (Hdal : d % page_size = 0) (Hd : 0 < d)
    (Hb0 : 0 < ((m_vmmaps m).vm_brk.toNat : Int))
    (Hnw : ((m_vmmaps m).vm_brk.toNat : Int) + d + page_size < 2 ^ 64)
    (Hin : (a, sz) ∈ ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps))
    (Hov1 : ((m_vmmaps m).vm_brk.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int))
    (Hov2 : (a.toNat : Int) < ((m_vmmaps m).vm_brk.toNat : Int) + d) :
    Sys.Mm.Mmap.brk_grow_ok m (BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d))
      (BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)) = false := by
  have hps : (0 : Int) < page_size := by unfold page_size; omega
  have hb0 : decide (0 < ((m_vmmaps m).vm_brk.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]; exact Hb0
  have Hr : ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) + d :=
    AgentLib.u64_lit _ ⟨by omega, by omega⟩
  have hlt : decide (((m_vmmaps m).vm_brk.toNat : Int)
      < ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    rw [Hr]; omega
  have hlo : page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) :=
    AllocSim.page_round_up_Z_aligned _ (by omega) Hbal
  have hhi0 : page_round_up_Z
      ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int)
      = ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int) :=
    AllocSim.page_round_up_Z_aligned _ (by rw [Hr]; omega)
      (by rw [Hr, Int.add_emod, Hbal, Hdal]; simp)
  have hhi : page_round_up_Z
      ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) + d := by rw [hhi0, Hr]
  have hltlo : page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)
      < page_round_up_Z ((BitVec.ofInt 64
          (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int) := by
    rw [hlo, hhi]; omega
  have hdp : d + page_size < 2 ^ 64 := by omega
  have hd0 : 0 < d + page_size := by unfold page_size at *; omega
  have hnat1 : ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat : Int)).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) := AgentLib.u64_lit _ ⟨by omega, by omega⟩
  have hnat2 : ((BitVec.ofInt 64 (d + page_size)).toNat : Int) = d + page_size :=
    AgentLib.u64_lit _ ⟨by omega, hdp⟩
  have hov : iv_overlap (m_vmmaps m).vm_brk (BitVec.ofInt 64 (d + page_size)) a sz = true := by
    rw [← show BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat : Int) = (m_vmmaps m).vm_brk from
      Z_to_bv_u_eq' _ _ rfl]
    unfold iv_overlap
    rw [hnat1, hnat2]
    have e1 : decide (((m_vmmaps m).vm_brk.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int))
        = true := by simp only [decide_eq_true_eq]; exact Hov1
    have e2 : decide ((a.toNat : Int) < ((m_vmmaps m).vm_brk.toNat : Int) + (d + page_size))
        = true := by simp only [decide_eq_true_eq]; omega
    rw [e1, e2]
    rfl
  have hrf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      (BitVec.ofInt 64 (page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)))
      (BitVec.ofInt 64 (page_round_up_Z
          ((BitVec.ofInt 64 (((m_vmmaps m).vm_brk.toNat : Int) + d)).toNat : Int)
        + page_size - page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int))) = false := by
    rw [hlo, hhi,
      show ((m_vmmaps m).vm_brk.toNat : Int) + d + page_size - ((m_vmmaps m).vm_brk.toNat : Int)
        = d + page_size from by omega,
      show BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat : Int) = (m_vmmaps m).vm_brk from
        Z_to_bv_u_eq' _ _ rfl]
    exact region_free_false_of_overlap _ _ a sz _ Hin hov
  unfold Sys.Mm.Mmap.brk_grow_ok
  simp only []
  rw [hb0, hlt, show (true && true) = true from rfl, ite_eq_left rfl, ite_eq_left hltlo, hrf]
  simp

/-! #########################################################################
    ## B. M6 exit, M5 set_tid_address / brk, M4 brk2

     opens `Section SoundB` here with the parameter block

      SEGS : List Segment, A : atable, nx0 : Nat, LIMIT : Int,
      SINV : env → (word → Option byte) → Prop, argH : env → word → Bool,
      FS0 : Fs.Fs,

    and the hypotheses `SEGS_in_hull`, `RES_hull`, `HULL_ok`, `SHADOW_ok`,
    `argH_high`, `argH_agree`, `SINV_frame`, `SINV_agree`, `PLACEMENT`.
    ######################################################################### -/

/-- `node_exit` inverted: the two admissible numbers and the exit code. -/
theorem node_exit_some (cs : acs) (code : Int) (H : node_exit cs = some code) :
    (reg_lit cs 17 = some 94 ∨ reg_lit cs 17 = some 93) ∧
      ∃ c0, reg_lit cs 10 = some c0 ∧ code = zland c0 255 := by
  unfold node_exit at H
  split at H
  · rename_i h17 h10
    exact ⟨Or.inl h17, _, h10, (Option.some.inj H).symm⟩
  · rename_i h17 h10
    exact ⟨Or.inr h17, _, h10, (Option.some.inj H).symm⟩
  · cases H

/-- `zland c 255` is the low byte . -/
theorem zland_255 (c : Int) : zland c 255 = c % 256 := by
  have h := AxSymExec3Sound.zland_ones c 8 (by decide)
  rw [show ((2 : Int) ^ 8 - 1) = 255 from by decide] at h
  rw [h, show ((2 : Int) ^ 8) = 256 from by decide]

/-- `---- M6: exit ----`. -/
theorem node_exit_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_hull : ∀ iv ∈ segments_reserved SEGS,
      A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ E E' (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ E E' M, env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    exit_stmt SEGS A nx0 LIMIT SINV argH FS0 := by
  intro cs code E R FULL model HC Hec Hn
  obtain ⟨Hpc0, Hpc4, w, HF, HE⟩ := AsanNodesLibE.is_ecall_at_sound SEGS cs Hec
  obtain ⟨Ha7, c0, H10, rfl⟩ := node_exit_some cs code Hn
  obtain ⟨G10, Hc0⟩ :=
    reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 c0 HC
      ⟨by omega, by omega⟩ H10
  have G17 : getr R (Z_to_bv 5 17) = Z_to_bv 64 94 ∨ getr R (Z_to_bv 5 17) = Z_to_bv 64 93 := by
    rcases Ha7 with h | h
    · left
      exact (reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 94 HC
        ⟨by omega, by omega⟩ h).1
    · right
      exact (reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 93 HC
        ⟨by omega, by omega⟩ h).1
  show srealizes SEGS (cfg_of SEGS R (pc cs) FULL model)
    (t_exit (BitVec.ofInt 64 (zland c0 255)) (m_fs model))
  rw [zland_255, ← AsanNodesLibE.bv_and_255 c0 Hc0]
  exact AsanNodesLibE.srz_exit_at_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
    (BitVec.ofInt 64 c0) HF HE HC.co_halt G17 G10

/-! ### B.1 The kept knowledge lies apart from a fresh region above the image,
    below `CEIL`, apart from every tracked entry -/

/-- `foot_safe`: the footprint lies on the stack side, in the
    image hull, or inside a tracked entry. -/
def foot_safe (A : atable) (E : env) (ms : List amap) (s l : Int) : Prop :=
  (CEIL ≤ s ∧ s + l ≤ 2 ^ 64) ∨
  (A.img_lo ≤ s ∧ s + l ≤ A.img_hi) ∨
  (∃ m, m ∈ ms ∧ bv_unsigned (edenot E m.am_base) ≤ s ∧
    s + l ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))

/-- `inside_maps` read back. -/
theorem inside_maps_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (ms : List amap) (b : expr) (off : Int) (len : expr)
    (HK : know_ok SEGS E M k) (H : inside_maps k ms b off len = true) :
    ∃ m, m ∈ ms ∧ bv_unsigned (edenot E m.am_base) ≤ estart E (SA b off) ∧
      estart E (SA b off) + elenZ E len ≤
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
  induction ms with
  | nil => simp [inside_maps] at H
  | cons m rest ih =>
    rw [show inside_maps k (m :: rest) b off len
        = ((!is_fog m && xinside k b off len m.am_base 0 m.am_len) ||
            inside_maps k rest b off len) from rfl] at H
    rw [Bool.or_eq_true] at H
    rcases H with H | H
    · rw [Bool.and_eq_true] at H
      obtain ⟨-, Hx⟩ := H
      obtain ⟨H1, H2⟩ := xinside_sound SEGS E M k b off len m.am_base 0 m.am_len HK Hx
      refine ⟨m, List.mem_cons_self .., ?_, ?_⟩
      · rw [estart, estart] at *
        simp only [SA, elenZ] at *
        omega
      · rw [estart, estart] at *
        simp only [SA, elenZ] at *
        omega
    · obtain ⟨m', hm', h1, h2⟩ := ih H
      exact ⟨m', List.mem_cons_of_mem _ hm', h1, h2⟩

/-- `safe_range` read back. -/
theorem safe_range_sound (SEGS : List Segment) (A : atable) (E : env)
    (M : word → Option byte) (k : List kentry) (ms : List amap) (b : expr) (off : Int)
    (len : expr) (HK : know_ok SEGS E M k) (H : safe_range A k ms b off len = true) :
    foot_safe A E ms (estart E (SA b off)) (elenZ E len) := by
  unfold safe_range at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · revert H
    cases hx : xhi k len with
    | none => intro H; simp [hx] at H
    | some lh =>
      cases hb : base_range k b with
      | none => intro H; simp [hx, hb] at H
      | some p =>
        obtain ⟨lo, hi⟩ := p
        intro H
        simp only [hx, hb] at H
        have L1 : bv_unsigned (edenot E len) ≤ lh := xhi_sound SEGS E M k len lh HK hx
        have Lbr := base_range_sound SEGS E M k b lo hi HK hb
        have L2 : lo ≤ bv_unsigned (edenot E b) := Lbr.1
        have L3 : bv_unsigned (edenot E b) ≤ hi := Lbr.2
        rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at H
        rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [decide_eq_true_eq] at h1 h2
          left
          unfold two64 at *
          unfold estart elenZ
          simp only [SA]
          omega
        · rw [decide_eq_true_eq] at h1 h2
          right; left
          unfold estart elenZ
          simp only [SA]
          omega
  · right; right
    exact inside_maps_sound SEGS E M k ms b off len HK H

/-! ### B.2 `vis_add`'s output, projected -/

/-- `vis_add`'s output, projected. -/
theorem vis_add_shape (A : atable) (LIMIT : Int) (cs : acs) (b n : expr)
    (k : List kentry) (cs2 : acs) (Hv : vis_add A LIMIT cs b n k = some cs2) :
    flat_x (kn cs) (split_lit b).1 (split_lit b).2 n = true ∧
      pc cs2 = pc cs ∧ cs2.a_ss.s_regs = cs.a_ss.s_regs ∧
      cs2.a_vis = (b, n) :: cs.a_vis ∧
      cs2.a_maps = cs.a_maps ∧ cs2.a_ghost = cs.a_ghost := by
  rw [vis_add_eq] at Hv
  unfold vis_add_ref at Hv
  simp only [] at Hv
  cases hx : xhi (kn cs) n with
  | none => rw [hx] at Hv; cases Hv
  | some nhi =>
    rw [hx] at Hv
    simp only [] at Hv
    split at Hv
    · rename_i hguard
      simp only [Bool.and_eq_true, and_assoc] at hguard
      obtain ⟨-, -, hflat, -⟩ := hguard
      simp only [Option.some.injEq] at Hv
      rw [← Hv]
      exact ⟨hflat, rfl, rfl, rfl, rfl, rfl⟩
    · simp at Hv

/-! #########################################################################
    ## C. M5 munmap — the small facts of the section
    ######################################################################### -/

theorem reserved_free_above (SEGS : List Segment) (A : atable) (model : Model)
    (lo n : word)
    (RES_hullH : AsanNodesMmLib.RES_hull_def SEGS A)
    (Hres : (m_vmmaps model).vm_reserved = segments_reserved SEGS)
    (Hlo : A.img_hi ≤ bv_unsigned lo) :
    region_free ((m_vmmaps model).vm_reserved) lo n = true := by
  rw [Hres]
  apply region_free_intro
  intro b s Hin
  obtain ⟨H1, H2⟩ := RES_hullH (b, s) Hin
  dsimp only at H1 H2
  unfold iv_overlap
  rw [show decide (bv_unsigned lo < bv_unsigned b + bv_unsigned s) = false from by
        simp only [decide_eq_false_iff_not]; omega]
  simp

/-- `len_eqb_sound`. -/
theorem len_eqb_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (n m : expr) (HK : know_ok SEGS E M k)
    (H : len_eqb k n m = true) : edenot E n = edenot E m := by
  unfold len_eqb at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · rw [expr_eqb_eq n m H]
  · rw [Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    have A1 := lin_ge0_sound SEGS E M k [(n, 0)] [(m, 0)] HK H1
    have B1 := lin_ge0_sound SEGS E M k [(m, 0)] [(n, 0)] HK H2
    simp only [xt_den] at A1 B1
    apply BitVec.eq_of_toNat_eq
    have h1 : bv_unsigned (edenot E n) = bv_unsigned (edenot E m) := by omega
    exact Int.ofNat.inj h1

/-- `existsb_filter_split`. -/
theorem existsb_filter_split {T : Type} (g h : T → Bool) (l : List T) :
    l.any h = ((l.filter g).any h || (l.filter (fun x => !(g x))).any h) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons, List.filter_cons]
    cases hg : g x <;> cases hx : h x <;> simp_all

/-- What survives the iterated `kn_unfill` over the gone ranges' shadows, as
    the checker spells the shadow interval. -/
def sh_iv (A : atable) (E : env) (k : List kentry) (p : expr × expr) : Int × Int :=
  let (sb, sk, sn) := shadow_of A k p.1 p.2
  (estart E (SA sb sk), elenZ E sn)

/-- `brk_req`: a positive page-multiple request `≤ 2^40`,
    congruent to `a0 - brk` mod `2^64`. -/
theorem brk_req_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model) (d : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) (H : brk_req cs = some d) :
    0 < d ∧ d % 4096 = 0 ∧ d ≤ 2 ^ 40 ∧
      (bv_unsigned (edenot E (reg cs 10)) -
        bv_unsigned (m_vmmaps model).vm_brk) % two64 = d := by
  unfold brk_req at H
  cases hld : lit_diff (reg cs 10) cs.a_brk with
  | none => rw [hld] at H; simp at H
  | some d0 =>
    rw [hld] at H
    simp only [] at H
    split at H
    · rename_i hc
      simp only [Option.some.injEq] at H
      subst H
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [decide_eq_true_eq] using h1
      · simpa only [beq_iff_eq] using h2
      · rw [decide_eq_true_eq] at h3
        rwa [show zpow 2 40 = (2 : Int) ^ 40 from by decide] at h3
      · obtain ⟨-, -, hm⟩ := lit_diff_sound E (reg cs 10) cs.a_brk d0 hld
        rw [HC.co_brk]
        exact hm
    · simp at H

/-- `brk_base_ok`: the break is page aligned, positive, above
    the image, and `brk + d ≤ KHI`. -/
theorem brk_base_ok_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model) (d : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (H : brk_base_ok A cs d = true) :
    bv_unsigned (m_vmmaps model).vm_brk % 4096 = 0 ∧
      0 < bv_unsigned (m_vmmaps model).vm_brk ∧
      A.img_hi ≤ bv_unsigned (m_vmmaps model).vm_brk ∧
      bv_unsigned (m_vmmaps model).vm_brk + d ≤ KHI := by
  unfold brk_base_ok at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨Hal, H⟩ := H
  cases hlo : xlo (kn cs) cs.a_brk with
  | none => rw [hlo] at H; simp at H
  | some lo =>
    cases hhi : xhi (kn cs) cs.a_brk with
    | none => rw [hlo, hhi] at H; simp at H
    | some hi =>
      rw [hlo, hhi] at H
      simp only [] at H
      simp only [Bool.and_eq_true] at H
      obtain ⟨⟨h0, hi1⟩, hk⟩ := H
      have HK := HC.co_know
      have L := xlo_sound SEGS E _ (kn cs) cs.a_brk lo HK hlo
      have Hh := xhi_sound SEGS E _ (kn cs) cs.a_brk hi HK hhi
      have P := page_aligned_sound SEGS E _ (kn cs) cs.a_brk HK Hal
      rw [← HC.co_brk] at L Hh P
      rw [decide_eq_true_eq] at h0 hi1 hk
      exact ⟨P, by omega, by omega, by omega⟩

/-- The common successor of the brk query and the blocked grow:
    `a0 := brk`, `pc += 4`, registers/memory/model otherwise unchanged. -/
theorem brk_keep_ok (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok SEGS A LIMIT SINV argH FS0 E
      (set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4))
      (regupd R 10 (m_vmmaps model).vm_brk) FULL model := by
  have hss : set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4)
      = with_ss cs (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 cs.a_brk)
          (cs.a_ss.s_know) (cs.a_ss.s_next)) := rfl
  rw [hss]
  refine cs_ok_frame SEGS A LIMIT SINV argH FS0 SINV_frame E cs R FULL model
    (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 cs.a_brk)
      (cs.a_ss.s_know) (cs.a_ss.s_next))
    (regupd R 10 (m_vmmaps model).vm_brk) FULL model HC
    (same_but_materialized_refl model) ?_ ?_ ?_ HC.co_know ?_
  · exact HC.co_minv
  · exact regs_ok_set_n E cs.a_ss.s_regs R 10 cs.a_brk ((m_vmmaps model).vm_brk)
      HC.co_regs ⟨by omega, by omega⟩ HC.co_brk.symm
  · rfl
  · intro a _
    rfl

/-! #########################################################################
    ## D. The deferred section-B / section-C lemmas, landed
    ######################################################################### -/

/-- The request register holds exactly `brk + d` (no wrap).
    The `nia` step  is the `b ≤ u` / `u < b` split below: in the first
    branch `u - b` is its own residue, in the second the residue is
    `u - b + 2^64`, which the guard-page room `brk + d ≤ KHI < 2^64` refutes. -/
theorem brk_req_val (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model) (d : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hr : brk_req cs = some d) (Hb : brk_base_ok A cs d = true) :
    getr R (Z_to_bv 5 10) = Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d) := by
  obtain ⟨D1, D2, D3, Dm⟩ :=
    brk_req_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model d HC Hr
  obtain ⟨B1, B2, B3, B4⟩ :=
    brk_base_ok_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model d HC Hb
  -- the `%`-shaped hypotheses only lose the linear solver; `Dm` carries the value
  clear D2 B1
  have hdlt : d < two64 := by
    rw [← Dm]
    exact Int.emod_lt_of_pos _ (by decide)
  have hd0 : 0 < d := D1
  -- one spelling per atom: `u64_range` states its bounds at `↑x.toNat`, the
  -- section's vocabulary uses `bv_unsigned x` (the same term, `abbrev`)
  have hU0 : 0 ≤ bv_unsigned (edenot E (reg cs 10)) := (u64_range _).1
  have hU1 : bv_unsigned (edenot E (reg cs 10)) < two64 := (u64_range _).2
  have hBr0 : 0 ≤ bv_unsigned (m_vmmaps model).vm_brk := (u64_range _).1
  have hBr1 : bv_unsigned (m_vmmaps model).vm_brk < two64 := (u64_range _).2
  have hKHI : KHI < two64 := by unfold KHI two64; decide
  have key : bv_unsigned (edenot E (reg cs 10))
      = bv_unsigned (m_vmmaps model).vm_brk + d := by
    by_cases hle : bv_unsigned (m_vmmaps model).vm_brk ≤ bv_unsigned (edenot E (reg cs 10))
    · have he : (bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (m_vmmaps model).vm_brk)
            % two64
          = bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (m_vmmaps model).vm_brk :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [he] at Dm
      omega
    · exfalso
      have hshift : (bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (m_vmmaps model).vm_brk)
            % two64
          = bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (m_vmmaps model).vm_brk
            + two64 := by
        have hlt1 : 0 ≤ bv_unsigned (edenot E (reg cs 10))
            - bv_unsigned (m_vmmaps model).vm_brk + two64 := by omega
        have hlt2 : bv_unsigned (edenot E (reg cs 10))
            - bv_unsigned (m_vmmaps model).vm_brk + two64 < two64 := by omega
        have he2 := Int.emod_eq_of_lt hlt1 hlt2
        have hsame : (bv_unsigned (edenot E (reg cs 10))
              - bv_unsigned (m_vmmaps model).vm_brk + two64) % two64
            = (bv_unsigned (edenot E (reg cs 10))
              - bv_unsigned (m_vmmaps model).vm_brk) % two64 := by
          rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
        omega
      rw [hshift] at Dm
      omega
  rw [show Z_to_bv 5 10 = Z_to_bv 5 ((10 : Nat) : Int) from rfl]
  rw [reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC ⟨by omega, by omega⟩]
  exact (Z_to_bv_u_eq' (edenot E (reg cs 10)) _ key.symm).symm

/-- A provably-zero range: flat, and zero under the knowledge's memory. -/
theorem kzero_x_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (allkn k : List kentry) (b : expr) (off : Int) (n : expr)
    (HA : know_ok SEGS E M allkn) (HK : know_ok SEGS E M k)
    (H : kzero_x allkn k b off n = true) :
    0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 ∧
      ∀ x : word, (estart E (SA b off) ≤ bv_unsigned x ∧
        bv_unsigned x < estart E (SA b off) + elenZ E n) → M x = some (Z_to_bv 8 0) := by
  -- the `KZero` arm: the `KZero`'s footprint covers the query range
  have CONT : ∀ (zb : expr) (zk : Int) (zn : expr),
      kentry_ok SEGS E M (.KZero (SA zb zk) zn) →
      estart E (SA zb zk) ≤ estart E (SA b off) →
      estart E (SA b off) + elenZ E n ≤ estart E (SA zb zk) + elenZ E zn →
      0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 ∧
        ∀ x : word, (estart E (SA b off) ≤ bv_unsigned x ∧
          bv_unsigned x < estart E (SA b off) + elenZ E n) → M x = some (Z_to_bv 8 0) := by
    intro zb zk zn Hk I1 I2
    obtain ⟨⟨F1, F2, F3, F4⟩, Hz⟩ := Hk
    refine ⟨by omega, by omega, ?_⟩
    intro x Hx
    have h1 : 0 ≤ bv_unsigned x - estart E (SA zb zk) := by omega
    have h2 : bv_unsigned x - estart E (SA zb zk) < elenZ E zn := by omega
    have key := Hz (bv_unsigned x - estart E (SA zb zk)) h1 h2
    rw [show estart E (SA zb zk) + (bv_unsigned x - estart E (SA zb zk)) = bv_unsigned x
        from by omega,
      show BitVec.ofInt 64 (bv_unsigned x) = x from Z_to_bv_u_eq' x _ rfl] at key
    exact key
  induction k with
  | nil => simp [kzero_x] at H
  | cons K rest ih =>
    have HKt : know_ok SEGS E M rest := fun K' h' => HK K' (List.mem_cons_of_mem _ h')
    cases K with
    | KZero a zn =>
      obtain ⟨zb, zk⟩ := a
      have HKK : kentry_ok SEGS E M (.KZero (SA zb zk) zn) := HK _ (List.mem_cons_self ..)
      -- the query range falls inside this entry (`xinside`), or the search goes on
      have TAIL : ((if xinside allkn b off n zb zk zn = true then true
                    else kzero_x allkn rest b off n) = true) →
          0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 ∧
            ∀ x : word, (estart E (SA b off) ≤ bv_unsigned x ∧
              bv_unsigned x < estart E (SA b off) + elenZ E n) → M x = some (Z_to_bv 8 0) := by
        intro Hx
        by_cases hi : xinside allkn b off n zb zk zn = true
        · rw [ite_eq_left hi] at Hx
          obtain ⟨I1, I2⟩ := xinside_sound SEGS E M allkn b off n zb zk zn HA hi
          exact CONT zb zk zn HKK I1 I2
        · rw [ite_eq_right hi] at Hx
          exact ih HKt Hx
      simp only [kzero_x] at H
      split at H
      · rename_i hcond0
        -- the guard `b = zb && zk ≤ off` of this entry
        have hba : (expr_eqb b zb) = true := by
          have h' := hcond0; simp only [Bool.and_eq_true] at h' ; exact h'.1
        have hzo : decide (zk ≤ off) = true := by
          have h' := hcond0; simp only [Bool.and_eq_true] at h' ; exact h'.2
        have hb' : b = zb := expr_eqb_eq b zb hba
        have hzo' : zk ≤ off := of_decide_eq_true hzo
        cases hn : xhi allkn n with
        | none =>
          rw [hn] at H
          dsimp only at H
          rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at H
          exact TAIL H
        | some nh =>
          cases hz : xlo allkn zn with
          | none =>
            rw [hn, hz] at H
            dsimp only at H
            rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at H
            exact TAIL H
          | some zl =>
            rw [hn, hz] at H
            dsimp only at H
            by_cases hle : decide (off + nh ≤ zk + zl) = true
            · rw [ite_eq_left hle] at H
              have hle' : off + nh ≤ zk + zl := of_decide_eq_true hle
              have H1 := xhi_sound SEGS E M allkn n nh HA hn
              have H2 := xlo_sound SEGS E M allkn zn zl HA hz
              have hden : bv_unsigned (edenot E zb) = bv_unsigned (edenot E b) := by rw [hb']
              refine CONT zb zk zn HKK ?_ ?_
              · dsimp only [estart]
                omega
              · dsimp only [estart, elenZ]
                omega
            · rw [ite_eq_right hle] at H
              exact TAIL H
      · rename_i _
        rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at H
        exact TAIL H
    | KWord a w v => exact ih HKt H
    | KBlob a nn kb => exact ih HKt H
    | KImg lo hi => exact ih HKt H
    | KAlign e m => exact ih HKt H
    | KRange e lo hi => exact ih HKt H
    | KWr a nn => exact ih HKt H
    | KDisj a1 n1 a2 n2 => exact ih HKt H
    | KFill a nn c => exact ih HKt H
    | KUnk a nn => exact ih HKt H

/-- Keeping a fact whose footprint bytes are unchanged. -/
theorem kentry_keep_foot (SEGS : List Segment) (E : env) (M M' : word → Option byte) (K : kentry)
    (HK : kentry_ok SEGS E M K)
    (Hin : ∀ x : word, (match kfoot E K with
                    | some (s, l) => s ≤ bv_unsigned x ∧ bv_unsigned x < s + l
                    | none => False) → M' x = M x)
    (Hnone : ∀ x : word, M x = none → M' x = none) :
    kentry_ok SEGS E M' K := by
  cases K with
  | KAlign e m => exact HK
  | KRange e lo hi => exact HK
  | KDisj a1 n1 a2 n2 => exact HK
  | KWord a w v =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hw, Hfl, Hrd⟩ := HK
    refine ⟨Hw, Hfl, ?_⟩
    rw [← Hrd]
    have hu : ((adenot E a).toNat : Int) = estart E a := flat_u E a _ Hfl
    refine rdn_ext SEGS w M' M (adenot E a) ?_ ?_
    · obtain ⟨F1, F2, F3, F4⟩ := Hfl
      rw [hu, show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from (by decide : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64)]
      omega
    · intro x hx
      apply Hin x
      rw [hu] at hx
      exact hx
  | KZero a n =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hfl, Hz⟩ := HK
    refine ⟨Hfl, ?_⟩
    intro i h1 h2
    obtain ⟨F1, F2, F3, F4⟩ := Hfl
    have hu : bv_unsigned (BitVec.ofInt 64 (estart E a + i)) = estart E a + i :=
      AgentLib.u64_lit _ ⟨by omega, by omega⟩
    rw [Hin _ ?_]
    · exact Hz i h1 h2
    · rw [hu]; exact ⟨by omega, by omega⟩
  | KBlob a n kb =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hfl, Hlen, Hz⟩ := HK
    refine ⟨Hfl, Hlen, ?_⟩
    intro i h1 h2
    obtain ⟨F1, F2, F3, F4⟩ := Hfl
    have hu : bv_unsigned (BitVec.ofInt 64 (estart E a + i)) = estart E a + i :=
      AgentLib.u64_lit _ ⟨by omega, by omega⟩
    rw [Hin _ ?_]
    · exact Hz i h1 h2
    · rw [hu]; exact ⟨by omega, by omega⟩
  | KFill a n c =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hfl, Hz⟩ := HK
    refine ⟨Hfl, ?_⟩
    intro i h1 h2
    obtain ⟨F1, F2, F3, F4⟩ := Hfl
    have hu : bv_unsigned (BitVec.ofInt 64 (estart E a + i)) = estart E a + i :=
      AgentLib.u64_lit _ ⟨by omega, by omega⟩
    rw [Hin _ ?_]
    · exact Hz i h1 h2
    · rw [hu]; exact ⟨by omega, by omega⟩
  | KUnk a n =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hfl, Hz⟩ := HK
    refine ⟨Hfl, ?_⟩
    intro i h1 h2
    obtain ⟨F1, F2, F3, F4⟩ := Hfl
    have hu : bv_unsigned (BitVec.ofInt 64 (estart E a + i)) = estart E a + i :=
      AgentLib.u64_lit _ ⟨by omega, by omega⟩
    rw [Hin _ ?_]
    · exact Hz i h1 h2
    · rw [hu]; exact ⟨by omega, by omega⟩
  | KImg lo hi =>
    dsimp only [kfoot] at Hin
    obtain ⟨H1, H2, Hz⟩ := HK
    refine ⟨H1, H2, ?_⟩
    intro i h1 h2
    have hu : bv_unsigned (BitVec.ofInt 64 i) = i := AgentLib.u64_lit _ ⟨by omega, by omega⟩
    rw [Hin _ ?_]
    · exact Hz i h1 h2
    · rw [hu]; exact ⟨by omega, by omega⟩
  | KWr a n =>
    dsimp only [kfoot] at Hin
    obtain ⟨Hfl, Hs⟩ := HK
    refine ⟨Hfl, ?_⟩
    intro d m hd0 hdm
    obtain ⟨F1, F2, F3, F4⟩ := Hfl
    cases m with
    | zero => rfl
    | succ m' =>
      have hu : ((BitVec.ofInt 64 (estart E a + d)).toNat : Int) = estart E a + d :=
        AgentLib.u64_lit _ ⟨by omega, by omega⟩
      have hpow : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := (by decide : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64)
      have hbound : ((BitVec.ofInt 64 (estart E a + d)).toNat : Int) + ((m' + 1 : Nat) : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hu, hpow]; omega
      apply StoreOk.store_ok_of_all
      · exact hbound
      · intro x hx1 hx2
        have h1 : estart E a + d ≤ bv_unsigned x := by
          have h' := hx1; rw [hu] at h'; exact h'
        have h2 : bv_unsigned x < estart E a + d + ((m' + 1 : Nat) : Int) := by
          have h' := hx2; rw [hu] at h'; exact h'
        have hM : M' x = M x := Hin x ⟨by omega, by omega⟩
        have hw : wview SEGS M' x = wview SEGS M x := by
          dsimp only [wview]
          rw [hM]
        rw [hw]
        exact StoreOk.store_ok_all SEGS M (m' + 1) (BitVec.ofInt 64 (estart E a + d)) hbound
          (Hs d (m' + 1) hd0 (by omega)) x hx1 hx2

/-- What survives the iterated `kn_unfill` over the gone ranges' shadows. -/
theorem fold_unfill_inv (SEGS : List Segment) (A : atable) (E : env) (M : word → Option byte)
    (k : List kentry) (gone : List (expr × expr)) (acc : List kentry) (K : kentry)
    (HK : know_ok SEGS E M k) (Hacc : ∀ K', K' ∈ acc → K' ∈ k)
    (Hin : K ∈ List.foldl (fun kk p =>
        let (sb, sk, sn) := shadow_of A k p.1 p.2
        kn_unfill kk sb sk sn) acc gone) :
    K ∈ acc ∧ (kimg_b K = true ∨
      ∀ p, p ∈ gone → kfoot_apart E K (sh_iv A E k p).1 (sh_iv A E k p).2) := by
  induction gone generalizing acc K with
  | nil =>
    rw [List.foldl_nil] at Hin
    exact ⟨Hin, Or.inr (fun q hq => absurd hq (by simp))⟩
  | cons p gone ih =>
    obtain ⟨pb, pn⟩ := p
    rw [List.foldl_cons] at Hin
    dsimp only at Hin
    generalize hsh : shadow_of A k pb pn = sh at Hin
    obtain ⟨sb, sk, sn⟩ := sh
    dsimp only at Hin
    have Hacc' : ∀ K', K' ∈ kn_unfill acc sb sk sn → K' ∈ k := by
      intro K' h'
      exact Hacc K' (List.mem_filter.mp (by simpa only [kn_unfill] using h')).1
    obtain ⟨Hin1, Hrest⟩ := ih (kn_unfill acc sb sk sn) K Hacc' Hin
    have Hkeep := (List.mem_filter.mp (by simpa only [kn_unfill] using Hin1)).2
    have Hin0 := (List.mem_filter.mp (by simpa only [kn_unfill] using Hin1)).1
    refine ⟨Hin0, ?_⟩
    rw [Bool.or_eq_true] at Hkeep
    rcases Hkeep with Himg | Hap
    · exact Or.inl Himg
    · rcases Hrest with Himg | Hrest
      · exact Or.inl Himg
      · refine Or.inr ?_
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · have Hap' : kentry_apart_b acc sb sk sn K = true := by
            simpa only [kentry_apart_bp_eq] using Hap
          have hsem := kentry_apart_b_sem SEGS E M acc K sb sk sn
            (fun K' h' => HK K' (Hacc K' h')) Hap'
          unfold sh_iv
          dsimp only
          rw [hsh]
          exact hsem
        · exact Hrest q hq

/-- Every fact kept by `grant_keep_b` / `kimg_clip` still holds after the
    granted range's bytes were zero-filled. -/
theorem kn_grant_filter_sound (SEGS : List Segment) (A : atable) (HULL_ok : hull_ok A)
    (E : env) (M M' : word → Option byte) (k : List kentry) (ms : List amap) (lo n : Int)
    (HK : know_ok SEGS E M k) (Hce : lo + n ≤ CEIL) (Hih : A.img_hi ≤ lo) (Hn : 0 ≤ n)
    (Hms : ∀ m, m ∈ ms → bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ lo ∨
      lo + n ≤ bv_unsigned (edenot E m.am_base))
    (Hout : ∀ x : word, bv_unsigned x < lo ∨ lo + n ≤ bv_unsigned x → M' x = M x) :
    know_ok SEGS E M' (kn_grant_filter A k ms) := by
  -- a footprint that is safe (`foot_safe`) lies below the granted range or above it
  have SAFE : ∀ s l, foot_safe A E ms s l → 0 ≤ l → s + l ≤ lo ∨ lo + n ≤ s := by
    intro s l F Hl
    rcases F with ⟨F1, F2⟩ | ⟨F1, F2⟩ | ⟨m, hm, F1, F2⟩
    · right; unfold CEIL at *; omega
    · left; omega
    · rcases Hms m hm with h | h
      · left; omega
      · right; omega
  intro K Hin
  unfold kn_grant_filter at Hin
  obtain ⟨Hin1, Hclip⟩ := List.mem_filter.mp Hin
  obtain ⟨Hin2, Hkeep⟩ := List.mem_filter.mp Hin1
  have HKK : kentry_ok SEGS E M K := HK K Hin2
  refine kentry_keep_sem SEGS E M M' K lo n HKK ?_ Hout
  cases K with
  | KAlign e m => dsimp only [kfoot_apart, kfoot]
  | KRange e lo' hi' => dsimp only [kfoot_apart, kfoot]
  | KDisj a1 n1 a2 n2 => dsimp only [kfoot_apart, kfoot]
  | KWord a w v =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    rw [Bool.and_eq_true] at Hkeep
    obtain ⟨Hw, Hs⟩ := Hkeep
    rw [decide_eq_true_eq] at Hw
    have F := safe_range_sound SEGS A E M k ms b o (.ELit (w : Int)) HK Hs
    have Hl : 0 ≤ elenZ E (.ELit (w : Int)) := by
      rw [elenZ_lit E _ ⟨by omega, by omega⟩]; omega
    have S := SAFE _ _ F Hl
    rw [elenZ_lit E _ ⟨by omega, by omega⟩] at S
    exact S
  | KZero a l =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    have F := safe_range_sound SEGS A E M k ms b o l HK Hkeep
    have Hl : 0 ≤ elenZ E l := (u64_range (edenot E l)).1
    exact SAFE _ _ F Hl
  | KBlob a l kb =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    have F := safe_range_sound SEGS A E M k ms b o l HK Hkeep
    have Hl : 0 ≤ elenZ E l := (u64_range (edenot E l)).1
    exact SAFE _ _ F Hl
  | KWr a l =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    have F := safe_range_sound SEGS A E M k ms b o l HK Hkeep
    have Hl : 0 ≤ elenZ E l := (u64_range (edenot E l)).1
    exact SAFE _ _ F Hl
  | KFill a l c =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    have F := safe_range_sound SEGS A E M k ms b o l HK Hkeep
    have Hl : 0 ≤ elenZ E l := (u64_range (edenot E l)).1
    exact SAFE _ _ F Hl
  | KUnk a l =>
    obtain ⟨b, o⟩ := a
    dsimp only [kfoot, grant_keep_b] at Hkeep ⊢
    have F := safe_range_sound SEGS A E M k ms b o l HK Hkeep
    have Hl : 0 ≤ elenZ E l := (u64_range (edenot E l)).1
    exact SAFE _ _ F Hl
  | KImg ilo ihi =>
    dsimp only [kfoot_apart, kfoot] at ⊢
    dsimp only at Hclip
    rw [Bool.and_eq_true, Bool.and_eq_true] at Hclip
    obtain ⟨⟨h1, h2⟩, h3⟩ := Hclip
    rw [decide_eq_true_eq] at h1 h2 h3
    left; omega

/-! ### D.1 `set_tid_address` — the M5 leaf -/

/-- `---- M5: set_tid_address ----`.  The node fixes the fresh variable at
    `nxt cs`, writes it into `a0`, records `1 ≤ v ≤ PID_MAX-1` in the
    knowledge and marks `a_tidset`; the syscall itself returns any tid in
    `(0, PID_MAX_ENVELOPE)`, so the continuation is applied at the extended
    valuation `ext1 E (nxt cs) tid` (`srz_set_tid_lazy`).  Every `cs_ok` field
    other than `co_regs` / `co_know` / `co_tid` survives because the successor
    keeps the ledger, the budgets and the model's mapping part verbatim
    (`with_tid` writes only `m_proc`). -/
theorem node_sys_sound_YSetTid (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_hull : ∀ iv ∈ segments_reserved SEGS,
      A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ E E' (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ E E' M, env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    sys_stmt SEGS A nx0 LIMIT SINV argH FS0 .YSetTid := by
  intro cs cs' E R FULL model T HC Hec Hn Hk
  obtain ⟨Hpc0, Hpc4, w, HF, HE⟩ := AsanNodesLibE.is_ecall_at_sound SEGS cs Hec
  have Hn0 : node_settid nx0 cs = some cs' := Hn
  unfold node_settid at Hn0
  split at Hn0
  · rename_i h17
    split at Hn0
    · rename_i hguard
      have hg := hguard
      rw [Bool.and_eq_true] at hg
      obtain ⟨hnt, hfr⟩ := hg
      have hts : cs.a_tidset = false := by simpa using hnt
      dsimp only at Hn0
      have hcs' : cs' = ACS (mk_ss (pc cs + 4)
            (sr_upd cs.a_ss.s_regs 10 (.EVar (nxt cs)))
            (.KRange (.EVar (nxt cs)) 1 (PID_MAX - 1) :: cs.a_ss.s_know) (nxt cs + 1))
          cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
          cs.a_brk cs.a_fd true := (Option.some.inj Hn0).symm
      subst hcs'
      obtain ⟨G17, -⟩ := reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model
        17 96 HC ⟨by omega, by omega⟩ h17
      obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hfr
      have Htid : m_tid model = none := HC.co_tid hts
      refine AsanNodesLibE.srz_set_tid_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model T w
        HF HE HC.co_halt ?_ Htid ?_
      · exact G17
      · intro tid Hb
        rw [v_addi_pc (pc cs) Hpc0 Hpc4]
        refine Hk (ext1 E (nxt cs) tid) (regupd R 10 tid) FULL (with_tid tid model)
          ⟨env_agree_le nx0 (nxt cs) E (ext1 E (nxt cs) tid) (ext1_agree E (nxt cs) tid) Fle, ext1_agree E (nxt cs) tid⟩ ?_ rfl
        have HC' := cs_ok_agree SEGS A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E
          (ext1 E (nxt cs) tid) cs R FULL model (ext1_agree E (nxt cs) tid) hfr HC
        have Hv : edenot (ext1 E (nxt cs) tid) (.EVar (nxt cs)) = tid := by
          show (ext1 E (nxt cs) tid).ev (nxt cs) = tid
          exact ext1_at E (nxt cs) tid
        refine
          { co_regs := regs_ok_set_n (ext1 E (nxt cs) tid) cs.a_ss.s_regs R 10
              (.EVar (nxt cs)) tid HC'.co_regs ⟨by omega, by omega⟩ Hv
            co_log := rfl
            co_know := ?_
            co_halt := HC'.co_halt
            co_fds := HC'.co_fds
            co_fs := HC'.co_fs
            co_tid := ?_
            co_res := HC'.co_res
            co_limit := HC'.co_limit
            co_maps := HC'.co_maps
            co_holes := HC'.co_holes
            co_seps := HC'.co_seps
            co_wf := HC'.co_wf
            co_bounds := HC'.co_bounds
            co_lazyb := HC'.co_lazyb
            co_nasub := HC'.co_nasub
            co_none := HC'.co_none
            co_kinds := HC'.co_kinds
            co_totsz := HC'.co_totsz
            co_split := HC'.co_split
            co_brk := HC'.co_brk
            co_sbrk := HC'.co_sbrk
            co_eager := HC'.co_eager
            co_abytes := HC'.co_abytes
            co_minv := ⟨HC'.co_minv.minv_nodup, HC'.co_minv.minv_aligned, HC'.co_minv.minv_allowed, HC'.co_minv.minv_lazy, HC'.co_minv.minv_budget⟩
            co_zero := HC'.co_zero
            co_sinv := HC'.co_sinv }
        · intro K HK
          rcases List.mem_cons.mp HK with rfl | HK
          · refine ⟨?_, ?_⟩
            · rw [Hv]
              show (1 : Int) ≤ (tid.toNat : Int)
              omega
            · rw [Hv]
              show (tid.toNat : Int) ≤ PID_MAX - 1
              have h2 := Hb.2
              have hpe : PID_MAX_ENVELOPE = (4194304 : Int) := by decide
              have hpm : PID_MAX = (4194304 : Int) := by decide
              rw [hpe] at h2
              rw [hpm]
              omega
          · exact HC'.co_know K HK
        · intro h; exact absurd h (by simp)
    · rename_i hguard
      simp at Hn0
  · rename_i h
    simp at Hn0

/-! ### D.2 brk: the query and the provably blocked grow -/

/-- `---- M5: brk query / blocked grow ----`.  Both accepted shapes end at the
    same successor (`brk_keep_ok`), so the continuation is applied at `E`
    itself: the syscall writes only `a0 := brk`.  The query is discharged by
    `srz_brk_query_lazy`; the blocked grow by `srz_brk_grow_blocked_lazy`,
    whose `brk_grow_ok model req req = false` is the tracked entry the guard
    produced, through `brk_grow_ok_aligned_refuted` (the guard's two
    `lin_ge0` facts are exactly its overlap premises). -/
theorem node_sys_sound_YBrk (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_hull : ∀ iv ∈ segments_reserved SEGS,
      A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ E E' (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ E E' M, env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    sys_stmt SEGS A nx0 LIMIT SINV argH FS0 .YBrk := by
  intro cs cs' E R FULL model T HC Hec Hn Hk
  obtain ⟨Hpc0, Hpc4, w, HF, HE⟩ := AsanNodesLibE.is_ecall_at_sound SEGS cs Hec
  have Hn0 : node_brk1 A cs = some cs' := Hn
  unfold node_brk1 at Hn0
  split at Hn0
  · rename_i h17
    obtain ⟨G17, -⟩ := reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model
      17 214 HC ⟨by omega, by omega⟩ h17
    dsimp only at Hn0
    split at Hn0
    · -- the query: `a0 = 0`
      rename_i h10
      have h2 : some (set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4)) = some cs' := by
        simpa using Hn0
      have hcs' : cs' = set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4) :=
        (Option.some.inj h2).symm
      subst hcs'
      have Hpost : srealizes SEGS (AsanAcct.mkCfg (mkst (regupd R 10 (m_vmmaps model).vm_brk)
          (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T := by
        rw [v_addi_pc (pc cs) Hpc0 Hpc4]
        exact Hk E (regupd R 10 (m_vmmaps model).vm_brk) FULL model
          ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩
          (brk_keep_ok SEGS A nx0 LIMIT SINV argH FS0 SINV_frame E cs R FULL model HC) rfl
      obtain ⟨G10, -⟩ := reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model
        10 0 HC ⟨by omega, by omega⟩ h10
      exact AsanNodesLibE.srz_brk_query_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)
        model w T HF HE HC.co_halt G17 G10 Hpost
    · -- a blocked grow
      rename_i h10
      split at Hn0
      · rename_i d hreq
        split at Hn0
        · rename_i hblk
          have h2 : some (set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4)) = some cs' := by
            simpa using Hn0
          have hcs' : cs' = set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4) :=
            (Option.some.inj h2).symm
          subst hcs'
          -- the successor is the checker's; build the continuation's `cs_ok` now
          have Hpost : srealizes SEGS (AsanAcct.mkCfg (mkst (regupd R 10 (m_vmmaps model).vm_brk)
              (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T := by
            rw [v_addi_pc (pc cs) Hpc0 Hpc4]
            exact Hk E (regupd R 10 (m_vmmaps model).vm_brk) FULL model
              ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩
              (brk_keep_ok SEGS A nx0 LIMIT SINV argH FS0 SINV_frame E cs R FULL model HC) rfl
          unfold brk_grow_blocked at hblk
          rw [Bool.and_eq_true] at hblk
          obtain ⟨Hbase, Hex⟩ := hblk
          obtain ⟨m, hm, Hm⟩ := List.any_eq_true.mp Hex
          rw [Bool.and_eq_true, Bool.and_eq_true] at Hm
          obtain ⟨⟨Hnf, Hm1⟩, Hm2⟩ := Hm
          have Hnf' : is_fog m = false := by simpa using Hnf
          obtain ⟨D1, D2, -, -⟩ :=
            brk_req_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model d HC hreq
          obtain ⟨B1, B2, -, B4⟩ :=
            brk_base_ok_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model d HC Hbase
          -- one spelling per atom, and the `%`-carrying facts are kept OUT of the
          -- arithmetic (they unfold into divisions and derail `omega`)
          have hbal : ((m_vmmaps model).vm_brk.toNat : Int) % page_size = 0 := by
            unfold page_size; exact B1
          have hdal : d % page_size = 0 := by unfold page_size; exact D2
          have hb0 : 0 < ((m_vmmaps model).vm_brk.toNat : Int) := B2
          have hB4 : bv_unsigned (m_vmmaps model).vm_brk + d ≤ KHI := B4
          clear B1 B2 B4 D2
          have hBr0 : 0 ≤ bv_unsigned (m_vmmaps model).vm_brk := (u64_range _).1
          have hsbrk : bv_unsigned (m_vmmaps model).vm_start_brk
              ≤ bv_unsigned (m_vmmaps model).vm_brk := HC.co_sbrk
          have G10 := brk_req_val SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model d HC hreq Hbase
          have L1 := lin_ge0_sound SEGS E _ (kn cs) [(m.am_base, -1), (m.am_len, 0)]
            [(cs.a_brk, 0)] HC.co_know Hm1
          have L2 := lin_ge0_sound SEGS E _ (kn cs) [(cs.a_brk, d - 1)]
            [(m.am_base, 0)] HC.co_know Hm2
          simp only [xt_den] at L1 L2
          rw [← HC.co_brk] at L1 L2
          simp only [bv_unsigned] at L1 L2
          have hub : bv_unsigned (m_vmmaps model).vm_brk + d < two64 := by
            clear hbal hdal
            simp only [bv_unsigned] at *
            have hK : KHI < two64 := by unfold KHI two64; decide
            unfold two64 at *
            omega
          have hnw : ((m_vmmaps model).vm_brk.toNat : Int) + d + page_size < 2 ^ 64 := by
            clear hbal hdal
            simp only [bv_unsigned] at *
            have hk : KHI + (4096 : Int) < (2 : Int) ^ 64 := by decide
            have hps : page_size = (4096 : Int) := rfl
            rw [hps]
            unfold KHI at *
            omega
          have hov1 : ((m_vmmaps model).vm_brk.toNat : Int)
              < ((edenot E m.am_base).toNat : Int) + ((edenot E m.am_len).toNat : Int) := by
            clear hbal hdal
            simp only [bv_unsigned] at *
            omega
          have hov2 : ((edenot E m.am_base).toNat : Int)
              < ((m_vmmaps model).vm_brk.toNat : Int) + d := by
            clear hbal hdal
            simp only [bv_unsigned] at *
            omega
          have Hin : (edenot E m.am_base, edenot E m.am_len)
              ∈ ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) := by
            rw [List.mem_append]
            exact Or.inr (maps_match_In E cs.a_maps (m_vmmaps model).vm_maps m HC.co_maps hm Hnf')
          have Hblk : Sys.Mm.Mmap.brk_grow_ok model
              (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d))
              (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d)) = false :=
            brk_grow_ok_aligned_refuted model d (edenot E m.am_base) (edenot E m.am_len)
              hbal hdal D1 hb0 hnw Hin hov1 hov2
          clear hbal hdal
          have hreqval : ((Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d)).toNat : Int)
              = bv_unsigned (m_vmmaps model).vm_brk + d := by
            refine AgentLib.u64_lit _ ⟨?_, hub⟩
            omega
          refine AsanNodesLibE.srz_brk_grow_blocked_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL
            (seg_rom SEGS) model w (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d)) T
            HF HE HC.co_halt G17 G10 ?_ ?_ ?_ Hblk Hpost
          · rw [hreqval]
            clear hB4 hub hnw hov1 hov2 Hblk L1 L2 hreqval hb0 Hbase Hex Hm1 Hm2
            omega
          · rw [hreqval]
            show bv_unsigned (m_vmmaps model).vm_start_brk
              ≤ bv_unsigned (m_vmmaps model).vm_brk + d
            clear hB4 hub hnw hov1 hov2 Hblk L1 L2 hreqval hb0 Hbase Hex Hm1 Hm2
            omega
          · rw [hreqval]
            show bv_unsigned (m_vmmaps model).vm_brk
              ≤ bv_unsigned (m_vmmaps model).vm_brk + d
            clear hB4 hub hnw hov1 hov2 Hblk L1 L2 hreqval hb0 Hbase Hex Hm1 Hm2
            omega
        · rename_i hblk
          try simp only [Bool.false_eq_true, ite_false] at Hn0
          cases Hn0
      · rename_i hnone
        try simp only [Bool.false_eq_true, ite_false] at Hn0
        cases Hn0
  · rename_i h
    simp at Hn0
/-! ## Section `C` — the munmap node

  The largest proof of the file.   Then `srz_munmap_lazy` carries it to the conclusion.
  PERF NOTE (this is the reason the visibility facts are *local* to `co_know`):
  `subst hcs'` inlines the eight-line `ACS …` successor term into every
  statement about `cs'`.  Two successor-sized `have`s in the *shared* context
  (VISLE/VISEQ — as much as they are needed by both `co_know` and `co_zero`)
  blow elaboration up from 6 s to 2 m 28 s and exhaust the heartbeat budget
  inside `co_zero`, which is otherwise fine.  Keeping them inside `co_know`
  (and stating them over the successor explicitly) keeps the file at ~7 s. -/

theorem node_munmap_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool)
    (RES_len : res_len_ok SEGS A) (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (FS0 : Fs.Fs) :
    ∀ cs cs' E R FULL model T,
      cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model → is_ecall_at SEGS cs = true →
      node_munmap A cs = some cs' →
      (∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' → m_fs model' = m_fs model →
        srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') T) →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
  intro cs cs' E R FULL model T HC Hec Hn HK
  obtain ⟨w, HF, HE, Hpc0, Hpc4⟩ := is_ecall_at_sound SEGS cs Hec
  have HKN := HC.co_know
  rw [node_munmap_eq] at Hn
  unfold node_munmap_ref at Hn
  split at Hn
  · rename_i x1 x2 ne nlo nhi heq17 h17
    dsimp only at Hn
    generalize hsp : split_lit (AsanPlanCore.reg cs 10) = sp at Hn
    obtain ⟨bb, bk⟩ := sp
    generalize hxhi : xhi (kn cs) (AsanPlanCore.reg cs 10) = xh at Hn
    cases xh with
    | none => simp at Hn
    | some ahi =>
      dsimp only at Hn
      generalize hgone : (List.filter (fun p : expr × expr =>
        !ranges_apart_x (kn cs) (split_lit p.1).1 (split_lit p.1).2 p.2 bb bk ne) cs.a_vis) = gone at Hn
      generalize hkept : (List.filter (fun p : expr × expr =>
        ranges_apart_x (kn cs) (split_lit p.1).1 (split_lit p.1).2 p.2 bb bk ne) cs.a_vis) = kept at Hn
      split at Hn
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨⟨Hhas, Hpal⟩, HFLAT⟩, Hhi64⟩, Hgone⟩ := hcond
        have hcs' := (some_inj _ _ Hn).symm
        subst hcs'
        obtain ⟨m, Hm, Hmatch⟩ := List.any_eq_true.mp Hhas
        unfold amap_match at Hmatch
        rw [Bool.and_eq_true, Bool.and_eq_true] at Hmatch
        obtain ⟨⟨Hnf, Hb⟩, Hlen_eq⟩ := Hmatch
        have Hnf' : is_fog m = false := by simpa using Hnf
        have hbase : AsanPlanCore.reg cs 10 = m.am_base := expr_eqb_eq _ _ Hb
        have Hne_eq : edenot E ne = edenot E m.am_len :=
          len_eqb_sound SEGS E _ (kn cs) ne m.am_len HKN Hlen_eq
        obtain ⟨HlenR, Hlen0, Hlen64, Hne, Hnlo0, Hnlole, Hnhi, HnZm, Hnen⟩ :=
          mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi HC h17

        generalize hlen : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) = len at *
        generalize hnZ : page_round_up_Z len = nZ at *
        generalize haddr : edenot E (AsanPlanCore.reg cs 10) = addr at *
        generalize hn : edenot E m.am_len = n at *
        have H17 : getr R 17 = BitVec.ofInt 64 215 := by
          have h := (reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 215 HC
            ⟨by omega, by omega⟩ heq17).1
          simpa using h
        have H10 : getr R 10 = addr := by
          have h := reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC
            ⟨by omega, by omega⟩
          rw [← haddr]
          simpa using h
        have H11 : getr R 11 = BitVec.ofInt 64 len := by simpa using HlenR
        have HIN : amap_den E m ∈ (m_vmmaps model).vm_maps :=
          maps_match_In E cs.a_maps _ m HC.co_maps Hm Hnf'
        obtain ⟨B1, B2, B3, B4, B5⟩ := HC.co_bounds (amap_den E m) HIN
        dsimp only [amap_den] at B1 B2 B3 B4 B5
        rw [← hbase, haddr] at B2 B4 B5
        rw [hn] at B1 B3 B5
        have BPOS : ∀ iv ∈ (m_vmmaps model).vm_maps, 0 < bv_unsigned iv.2 :=
          fun iv Hiv => (HC.co_bounds iv Hiv).1
        have hpage : page_size = 4096 := by decide
        have HnZpos : 0 < nZ := by
          have h := (page_round_up_Z_bounds len (by omega)).1
          rw [hnZ] at h
          omega
        have Hahi : 0 ≤ ahi := by
          have h := xhi_sound SEGS E _ (kn cs) (AsanPlanCore.reg cs 10) ahi HKN hxhi
          rw [haddr] at h
          have h2 : 0 ≤ bv_unsigned addr := (u64_range addr).1
          omega
        unfold two64 at Hhi64
        have HnZlt : nZ < 2 ^ 64 := by omega
        have Un : bv_unsigned n = nZ := by
          rw [← Hne_eq, Hne]
          exact u64_lit nZ ⟨by omega, by omega⟩
        have HnZw : Z_to_bv 64 nZ = n := by
          rw [← Un]
          exact Z_to_bv_u_eq' n (bv_unsigned n) rfl
        obtain ⟨Hest, Hest2, Hest3⟩ :=
          split_flat_estart SEGS E (Mr A argH E cs model FULL) (kn cs)
            (AsanPlanCore.reg cs 10) bb bk ne HKN hsp HFLAT
        rw [haddr] at Hest
        have HelenZ : elenZ E ne = nZ := by
          unfold elenZ
          rw [Hne]
          exact u64_lit nZ ⟨by omega, by omega⟩
        generalize hlo : bv_unsigned addr = lo at *
        generalize hhi : lo + nZ = hi at *
        have hlohi : A.img_hi ≤ lo ∧ hi ≤ CEIL ∧ lo < hi ∧ lo % 4096 = 0 ∧ hi % 4096 = 0 := by
          refine ⟨B4, ?_, ?_, B2, ?_⟩
          · rw [← hhi, ← Un]; exact B5
          · rw [← hhi]; omega
          · rw [← hhi, Int.add_emod, B2, HnZm]
            decide
        -- everything else in the ledger is elsewhere
        have DISJ' : ∀ m' ∈ cs.a_maps, is_fog m' = false → m ≠ m' →
            bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len) ≤ lo ∨
            hi ≤ bv_unsigned (edenot E m'.am_base) := by
          intro m' Hm' Hf' Hne'
          have D := maps_match_disjoint E cs.a_maps _ m m' HC.co_maps HC.co_seps Hm Hm' Hnf' Hf' Hne'
          unfold iv_disjoint at D
          dsimp only [amap_den] at D
          rw [← hbase] at D
          rw [haddr, hlo, hn, Un, hhi] at D
          rcases D with h | h
          · exact Or.inr h
          · exact Or.inl h
        have DISJl : ∀ iv ∈ (m_vmmaps model).vm_maps, iv ≠ amap_den E m →
            bv_unsigned iv.1 + bv_unsigned iv.2 ≤ lo ∨ hi ≤ bv_unsigned iv.1 := by
          intro iv Hiv Hne'
          have D := seps_In_disjoint _ iv (amap_den E m) HC.co_seps BPOS Hiv HIN Hne'
          unfold iv_disjoint at D
          dsimp only [amap_den] at D
          rw [← hbase] at D
          rw [haddr, hlo, hn, Un, hhi] at D
          rcases D with h | h
          · exact Or.inl h
          · exact Or.inr h
        have UNIQ : ∀ iv ∈ (m_vmmaps model).vm_maps, iv.1 = addr → iv = amap_den E m := by
          intro iv Hiv Hb0
          obtain ⟨ib, isz⟩ := iv
          dsimp only at Hb0 ⊢
          rw [Hb0] at Hiv ⊢
          cases Hs : bv_eqb isz n with
          | true =>
            have h1 : isz = n := (bv_eqb_eq isz n).mp Hs
            rw [h1]
            unfold amap_den
            rw [← hbase, haddr, hn]
          | false =>
            exfalso
            have Hne' : (addr, isz) ≠ amap_den E m := by
              intro Heq
              unfold amap_den at Heq
              rw [← hbase, haddr, hn] at Heq
              injection Heq with _ Heq2
              rw [Heq2, PropExec.bv_eqb_refl] at Hs
              cases Hs
            have D := DISJl (addr, isz) Hiv Hne'
            dsimp only at D
            have P := BPOS (addr, isz) Hiv
            dsimp only at P
            rcases D with h | h
            · omega
            · omega
        have MATCH : ∀ m' ∈ cs.a_maps,
            Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m')
              = Bool.not (amap_eqb m' m) := by
          intro m' Hm'
          by_cases Hmm : amap_eqb m' m = true
          · have h1 : m' = m := amap_eqb_eq Hmm
            rw [h1]
            have hA : amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m = true := by
              simp [amap_match, Hnf, Hb, Hlen_eq]
            rw [hA, amap_eqb_refl]
          · have Hmm' : amap_eqb m' m = false := by simpa using Hmm
            have Hne' : m ≠ m' := by
              intro h
              rw [h, amap_eqb_refl] at Hmm'
              cases Hmm'
            have hA : amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m' = false := by
              cases Hf' : is_fog m' with
              | true => simp [amap_match, Hf']
              | false =>
                cases Heq : expr_eqb (AsanPlanCore.reg cs 10) m'.am_base with
                | false => simp [amap_match, Hf', Heq]
                | true =>
                  have hbe : AsanPlanCore.reg cs 10 = m'.am_base := expr_eqb_eq _ _ Heq
                  have D := DISJ' m' Hm' Hf' Hne'
                  rw [← hbe, haddr, hlo] at D
                  have C1 := (HC.co_bounds (amap_den E m')
                    (maps_match_In E cs.a_maps _ m' HC.co_maps Hm' Hf')).1
                  dsimp only [amap_den] at C1
                  rcases D with h | h <;> omega
            rw [hA, Hmm']
        have MAPS' : maps_match E
            (List.filter (fun m' => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m')) cs.a_maps)
            (map_remove (m_vmmaps model).vm_maps addr) := by
          have hf : List.filter (fun m' => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m')) cs.a_maps
              = List.filter (fun m' => Bool.not (amap_eqb m' m)) cs.a_maps :=
            List.filter_congr (fun m' Hm' => MATCH m' Hm')
          rw [hf, ← haddr, hbase]
          exact maps_match_remove E cs.a_maps _ m HC.co_maps Hm Hnf'
            (seps_NoDup _ HC.co_seps BPOS)
            (fun iv Hiv Hfst => UNIQ iv Hiv (by rw [Hfst, ← hbase]; exact haddr))
        have INMAPS' : ∀ z, in_ivs z (map_remove (m_vmmaps model).vm_maps addr)
            = (in_ivs z (m_vmmaps model).vm_maps && Bool.not (in_rng lo hi z)) := by
          intro z
          change in_ivs z (List.filter (fun p => Bool.not (bv_eqb p.1 addr)) (m_vmmaps model).vm_maps)
            = (in_ivs z (m_vmmaps model).vm_maps && Bool.not (in_rng lo hi z))
          by_cases Hl : in_ivs z (List.filter (fun p => Bool.not (bv_eqb p.1 addr))
            (m_vmmaps model).vm_maps) = true
          · obtain ⟨iv, Hiv, Hziv⟩ := (in_ivs_true' z _).mp Hl
            obtain ⟨Hiv0, Hkeep⟩ := List.mem_filter.mp Hiv
            have Hkeep' : bv_eqb iv.1 addr = false := by simpa using Hkeep
            have Hne' : iv ≠ amap_den E m := by
              intro h
              rw [h] at Hkeep'
              unfold amap_den at Hkeep'
              rw [← hbase, haddr] at Hkeep'
              rw [PropExec.bv_eqb_refl] at Hkeep'
              cases Hkeep'
            have D := DISJl iv Hiv0 Hne'
            rw [Hl]
            have hR : (in_ivs z (m_vmmaps model).vm_maps && Bool.not (in_rng lo hi z)) = true := by
              rw [Bool.and_eq_true]
              refine ⟨(in_ivs_true' z _).mpr ⟨iv, Hiv0, Hziv⟩, ?_⟩
              show Bool.not (in_rng lo hi z) = true
              have hin : in_rng lo hi z = false := by
                unfold in_rng
                clear hlohi B2 B3 HnZm
                rcases D with h | h
                · rw [show decide (lo ≤ z) = false from by rw [decide_eq_false_iff_not]; omega]
                  rfl
                · rw [show decide (lo ≤ z) = true from by rw [decide_eq_true_iff]; omega]
                  rw [show decide (z < hi) = false from by rw [decide_eq_false_iff_not]; omega]
                  rfl
              rw [hin]
              rfl
            rw [hR]
          · have Hlf : in_ivs z (List.filter (fun p => Bool.not (bv_eqb p.1 addr))
                (m_vmmaps model).vm_maps) = false := by simpa using Hl
            have Hgoal : (in_ivs z (m_vmmaps model).vm_maps && Bool.not (in_rng lo hi z)) = false := by
              rw [Bool.and_eq_false_iff]
              by_cases Hin : in_ivs z (m_vmmaps model).vm_maps = true
              · right
                obtain ⟨iv, Hiv, Hziv⟩ := (in_ivs_true' z _).mp Hin
                show Bool.not (in_rng lo hi z) = false
                by_cases Hfa : bv_eqb iv.1 addr = true
                · have h1 : iv = amap_den E m := UNIQ iv Hiv ((bv_eqb_eq iv.1 addr).mp Hfa)
                  rw [h1] at Hziv
                  unfold amap_den at Hziv
                  rw [← hbase, haddr, hlo, hn] at Hziv
                  dsimp only at Hziv
                  have hin : in_rng lo hi z = true := by
                    unfold in_rng
                    rw [Bool.and_eq_true]
                    exact ⟨decide_eq_true Hziv.1, decide_eq_true (by omega)⟩
                  rw [hin]
                  rfl
                · exfalso
                  have Hfa' : bv_eqb iv.1 addr = false := by simpa using Hfa
                  have X : in_ivs z (List.filter (fun p => Bool.not (bv_eqb p.1 addr))
                      (m_vmmaps model).vm_maps) = true :=
                    (in_ivs_true' z _).mpr ⟨iv, List.mem_filter.mpr ⟨Hiv, by simpa using Hfa'⟩, Hziv⟩
                  rw [Hlf] at X
                  cases X
              · left
                have h : in_ivs z (m_vmmaps model).vm_maps = false := by simpa using Hin
                rw [h]
            rw [Hlf, Hgoal]
        -- the gone ranges: inside the entry; their shadows read zero
        have GONE : ∀ p ∈ gone,
            (∀ z, (decide (AsanPlanSound.uE E p.1 ≤ z)
                && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2)) = true → lo ≤ z ∧ z < hi) ∧
            (0 ≤ (sh_iv A E (kn cs) p).1) ∧
            (∀ x : word, (sh_iv A E (kn cs) p).1 ≤ bv_unsigned x ∧
              bv_unsigned x < (sh_iv A E (kn cs) p).1 + (sh_iv A E (kn cs) p).2 →
              Mr A argH E cs model FULL x = some (Z_to_bv 8 0)) ∧
            (∀ z, (decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p)) = true →
              (sh_iv A E (kn cs) p).1 ≤ z ∧ z < (sh_iv A E (kn cs) p).1 + (sh_iv A E (kn cs) p).2) := by
          intro p Hp
          have Hpv : p ∈ cs.a_vis := by
            rw [← hgone] at Hp
            exact (List.mem_filter.mp Hp).1
          have Gg := (List.all_eq_true.mp Hgone) p Hp
          generalize hps : split_lit p.1 = ps at *
          obtain ⟨pb, pk⟩ := ps
          generalize hsl : split_lit (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)) = sl at *
          obtain ⟨sb, sk⟩ := sl
          generalize hsn : mkSrl (kn cs) p.2 3 = sn at *
          have hsh : shadow_of A (kn cs) p.1 p.2 = (sb, sk, sn) := by
            simp only [shadow_of, hsl, hsn]
          rw [hsh] at Gg
          dsimp only at Gg
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at Gg
          obtain ⟨⟨⟨Gab, Gan⟩, Gin⟩, Gz⟩ := Gg
          rw [decide_eq_true_eq] at Gab Gan
          obtain ⟨Z1, Z2, Z3⟩ := kzero_x_sound SEGS E _ (kn cs) (kn cs) sb sk sn HKN HKN Gz
          obtain ⟨I1, I2⟩ := xinside_sound SEGS E _ (kn cs) pb pk p.2 bb bk ne HKN Gin
          rw [Hest] at I1 I2
          rw [show elenZ E ne = nZ from HelenZ] at I2
          simp only [elenZ] at I2
          have Hest2' : lo + nZ ≤ 2 ^ 64 := by
            have h : lo + elenZ E ne ≤ 2 ^ 64 := by rw [← Hest]; exact Hest2
            rwa [HelenZ] at h
          refine ⟨?_, ?_, ?_, ?_⟩
          · -- (1) the gone range is inside the entry
            intro z Hz
            rw [Bool.and_eq_true] at Hz
            obtain ⟨Hz1, Hz2⟩ := Hz
            have Hz1' : AsanPlanSound.uE E p.1 ≤ z := of_decide_eq_true Hz1
            have Hz2' : z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2 := of_decide_eq_true Hz2
            simp only [AsanPlanSound.uE, elenZ] at Hz1' Hz2'
            by_cases hA : estart E (SA pb pk) < 2 ^ 64
            · have h0 : (0 : Int) ≤ estart E (SA pb pk) := by
                refine Int.le_trans ?_ I1
                rw [← hlo]
                exact (u64_range addr).1
              have hU : bv_unsigned (edenot E p.1) = estart E (SA pb pk) :=
                u_of_split E p.1 pb pk hps ⟨h0, hA⟩
              constructor
              · refine Int.le_trans I1 ?_
                rw [← hU]
                exact Hz1'
              · rw [← hhi]
                refine Int.lt_of_lt_of_le ?_ I2
                rw [← hU]
                exact Hz2'
            · exfalso
              have hge : 2 ^ 64 ≤ estart E (SA pb pk) := by omega
              have hB : bv_unsigned (edenot E p.2) = 0 := by
                clear hlohi B2 B3 HnZm HnZpos HnZlt
                omega
              have hUpb : estart E (SA pb pk) = bv_unsigned (edenot E pb) + pk := rfl
              have hD := split_lit_denot E p.1 pb pk hps
              have h2 := congrArg bv_unsigned hD
              have hwrap : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E pb) + pk))
                  = (bv_unsigned (edenot E pb) + pk) % 2 ^ 64 := by
                have hh := u_lit64 (bv_unsigned (edenot E pb) + pk)
                have h2e : two64 = 2 ^ 64 := rfl
                rw [h2e] at hh
                exact hh
              rw [hwrap] at h2
              have hmod : (bv_unsigned (edenot E pb) + pk) % 2 ^ 64 = 0 := by
                rw [hUpb] at hge
                have h3 : bv_unsigned (edenot E pb) + pk = 2 ^ 64 := by omega
                rw [h3]
                exact Int.emod_self
              rw [hmod] at h2
              rw [h2] at Hz1'
              rw [h2, hB] at Hz2'
              exact absurd Hz2' (Int.not_lt.mpr Hz1')
          · -- (2) the shadow start is nonnegative
            simp only [sh_iv, hsh]
            exact Z1
          · -- (3) the shadow bytes read zero
            intro x hx
            simp only [sh_iv, hsh] at hx ⊢
            exact Z3 x hx
          · -- (4) the shadow interval as the checker spells it
            intro z Hz
            simp only [sh_iv, hsh]
            rw [Bool.and_eq_true] at Hz
            obtain ⟨Hz1, Hz2⟩ := Hz
            have Hz1' : sh_lo A E p ≤ z := of_decide_eq_true Hz1
            have Hz2' : z < sh_hi A E p := of_decide_eq_true Hz2
            have hSrl : bv_unsigned (edenot E (mkSrl (kn cs) p.2 3))
                = AsanPlanSound.uE E p.2 / 8 := by
              have h3 : bv_unsigned (Z_to_bv 64 3) = 3 := u64_lit 3 ⟨by decide, by decide⟩
              rw [mkSrl_denot SEGS E _ (kn cs) p.2 3 (Z_to_bv 64 3) HKN (by rw [h3]; decide)]
              rw [u_srl64, h3]
              show bv_unsigned (edenot E p.2) / (2 : Int) ^ ((3 : Int) % 64).toNat
                = bv_unsigned (edenot E p.2) / 8
              have h2e : (2 : Int) ^ ((3 : Int) % 64).toNat = 8 := by decide
              rw [h2e]
            have hSrl1 : bv_unsigned (edenot E (mkSrl (kn cs) p.1 3))
                = AsanPlanSound.uE E p.1 / 8 := by
              have h3 : bv_unsigned (Z_to_bv 64 3) = 3 := u64_lit 3 ⟨by decide, by decide⟩
              rw [mkSrl_denot SEGS E _ (kn cs) p.1 3 (Z_to_bv 64 3) HKN (by rw [h3]; decide)]
              rw [u_srl64, h3]
              show bv_unsigned (edenot E p.1) / (2 : Int) ^ ((3 : Int) % 64).toNat
                = bv_unsigned (edenot E p.1) / 8
              have h2e : (2 : Int) ^ ((3 : Int) % 64).toNat = 8 := by decide
              rw [h2e]
            have AL8 : ∀ e, 3 ≤ ealign (kn cs) e → AsanPlanSound.uE E e % 8 = 0 := by
              intro e Hee
              unfold AsanPlanSound.uE
              have hdvd : (8 : Int) ∣ bv_unsigned (edenot E e) := by
                have h8 : (8 : Int) = zpow 2 3 := by decide
                rw [h8]
                exact Int.dvd_trans (pow2_divide_le 3 (ealign (kn cs) e) ⟨by omega, Hee⟩)
                  (ealign_sound SEGS E _ (kn cs) e HKN).2
              exact Int.emod_eq_zero_of_dvd hdvd
            have A8b := AL8 p.1 Gab
            have A8n := AL8 p.2 Gan
            have hdiv : (AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2) / 8
                = AsanPlanSound.uE E p.1 / 8 + AsanPlanSound.uE E p.2 / 8 := by
              have h1 : (8 : Int) ∣ AsanPlanSound.uE E p.1 := Int.dvd_of_emod_eq_zero A8b
              have h2 : (8 : Int) ∣ AsanPlanSound.uE E p.2 := Int.dvd_of_emod_eq_zero A8n
              rw [Int.ediv_eq_of_eq_mul_left (by decide : (8 : Int) ≠ 0)]
              rw [Int.add_mul, Int.ediv_mul_cancel h1, Int.ediv_mul_cancel h2]
            have hhi2 : sh_hi A E p = sh_lo A E p + elenZ E sn := by
              have hsn' : elenZ E sn = AsanPlanSound.uE E p.2 / 8 := by
                rw [← hsn]; exact hSrl
              unfold sh_hi sh_lo
              rw [hdiv, hsn']
              omega
            have hS : 0 < elenZ E sn := by
              rw [hhi2] at Hz2'
              clear hlohi B2 B3 HnZm HnZpos HnZlt
              omega
            have hLt : bv_unsigned (edenot E sb) + sk < 2 ^ 64 := by
              have h := Z2
              rw [show estart E (SA sb sk) = bv_unsigned (edenot E sb) + sk from rfl] at h
              clear hlohi B2 B3 HnZm HnZpos HnZlt
              omega
            have hD := split_lit_denot E (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)) sb sk hsl
            have hval : bv_unsigned (edenot E (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)))
                = A.shadow_off + AsanPlanSound.uE E p.1 / 8 := by
              rw [eadd, mkAlu_denot, SymExec.alu64_add_eq, u_add64]
              rw [show bv_unsigned (edenot E (mkSrl (kn cs) p.1 3))
                  = AsanPlanSound.uE E p.1 / 8 from hSrl1]
              rw [show bv_unsigned (edenot E (expr.ELit A.shadow_off)) = A.shadow_off from by
                rw [show edenot E (expr.ELit A.shadow_off) = Z_to_bv 64 A.shadow_off from rfl]
                rw [u_lit64]
                rw [show two64 = 2 ^ 64 from rfl]
                exact Int.emod_eq_of_lt SHADOW_ok.1 (by have := SHADOW_ok.2; omega)]
              have hu : bv_unsigned (edenot E p.1) < 2 ^ 64 := (u64_range (edenot E p.1)).2
              have hnn : 0 ≤ bv_unsigned (edenot E p.1) := (u64_range (edenot E p.1)).1
              have h2 : A.shadow_off ≤ 2 ^ 47 := SHADOW_ok.2
              have hle : bv_unsigned (edenot E p.1) / 8 ≤ bv_unsigned (edenot E p.1) :=
                Int.ediv_le_self 8 hnn
              have hs : AsanPlanSound.uE E p.1 / 8 + A.shadow_off < 2 ^ 64 := by
                unfold AsanPlanSound.uE
                clear hlohi B2 B3 HnZm HnZpos HnZlt Z1 Z2 A8b A8n
                omega
              have hs0 : 0 ≤ AsanPlanSound.uE E p.1 / 8 + A.shadow_off := by
                have h1 : 0 ≤ bv_unsigned (edenot E p.1) / 8 := Int.ediv_nonneg hnn (by decide)
                have h3 : 0 ≤ A.shadow_off := SHADOW_ok.1
                unfold AsanPlanSound.uE
                clear hlohi B2 B3 HnZm HnZpos HnZlt Z1 Z2 A8b A8n
                omega
              rw [Int.emod_eq_of_lt hs0 hs]
              rw [Int.add_comm]
            have hLmod : (bv_unsigned (edenot E sb) + sk) % 2 ^ 64 = sh_lo A E p := by
              have h2 := congrArg bv_unsigned hD
              rw [hval] at h2
              rw [show bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E sb) + sk))
                  = (bv_unsigned (edenot E sb) + sk) % 2 ^ 64 from by
                have hh := u_lit64 (bv_unsigned (edenot E sb) + sk)
                have h2e : two64 = 2 ^ 64 := rfl
                rw [h2e] at hh
                exact hh] at h2
              exact h2.symm
            have hL : bv_unsigned (edenot E sb) + sk = sh_lo A E p := by
              rw [← hLmod]
              have hZ1 : 0 ≤ bv_unsigned (edenot E sb) + sk := by
                rw [show estart E (SA sb sk) = bv_unsigned (edenot E sb) + sk from rfl] at Z1
                exact Z1
              exact (Int.emod_eq_of_lt hZ1 hLt).symm
            constructor
            · show estart E (SA sb sk) ≤ z
              rw [show estart E (SA sb sk) = bv_unsigned (edenot E sb) + sk from rfl, hL]
              exact Hz1'
            · show z < estart E (SA sb sk) + elenZ E sn
              rw [show estart E (SA sb sk) = bv_unsigned (edenot E sb) + sk from rfl, hL, ← hhi2]
              exact Hz2'
        -- the model projections
        have hbvn : ((BitVec.ofInt 64 nZ).toNat : Int) = nZ := by
          rw [← show Z_to_bv 64 nZ = BitVec.ofInt 64 nZ from rfl]
          rw [HnZw]
          exact Un
        have PM : (m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_maps
            = map_remove (m_vmmaps model).vm_maps addr := rfl
        have PN : (m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_noaccess
            = maps_subtract (m_vmmaps model).vm_noaccess lo hi := by
          show maps_subtract (m_vmmaps model).vm_noaccess (addr.toNat : Int)
            ((addr.toNat : Int) + ((BitVec.ofInt 64 nZ).toNat : Int))
            = maps_subtract (m_vmmaps model).vm_noaccess lo hi
          rw [show (addr.toNat : Int) = lo from hlo, hbvn, ← hhi]
        have PL : m_vm_lazy (munmap_model addr (BitVec.ofInt 64 nZ) model)
            = maps_subtract (m_vm_lazy model) lo hi := by
          show maps_subtract (m_vm_lazy model) (addr.toNat : Int)
            ((addr.toNat : Int) + ((BitVec.ofInt 64 nZ).toNat : Int)) = maps_subtract (m_vm_lazy model) lo hi
          rw [show (addr.toNat : Int) = lo from hlo, hbvn, ← hhi]
        have PT : m_vm_materialized (munmap_model addr (BitVec.ofInt 64 nZ) model)
            = List.filter (page_outside_range lo hi) (m_vm_materialized model) := by
          show List.filter (page_outside_range (addr.toNat : Int)
            ((addr.toNat : Int) + ((BitVec.ofInt 64 nZ).toNat : Int))) (m_vm_materialized model)
            = List.filter (page_outside_range lo hi) (m_vm_materialized model)
          rw [show (addr.toNat : Int) = lo from hlo, hbvn, ← hhi]
        have PISP : (m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_init_sp
            = (m_vmmaps model).vm_init_sp := rfl
        have W1 := HC.co_wf.1
        have W2 := HC.co_wf.2.1
        have W3 := HC.co_wf.2.2.1
        have Wsp := HC.co_wf.2.2.2
        -- the successor's visibility facts
        have NOACC : ∀ z, in_ivs z (m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_noaccess
            = (in_ivs z (m_vmmaps model).vm_noaccess && Bool.not (in_rng lo hi z)) := by
          intro z
          rw [PN, in_ivs_covered, in_ivs_covered]
          exact covered_maps_subtract (m_vmmaps model).vm_noaccess lo hi W2 (by omega) z
        have LAZYOUT : ∀ x : word, bv_unsigned x < lo ∨ hi ≤ bv_unsigned x →
            page_in_ranges (page_base x) (m_vm_lazy (munmap_model addr (BitVec.ofInt 64 nZ) model))
              = page_in_ranges (page_base x) (m_vm_lazy model) := by
          intro x Hx
          rw [PL]
          exact page_in_ranges_subtract_out (page_base x) (m_vm_lazy model) lo hi W3 (by omega)
            (page_of_byte_out_aligned x lo hi hlohi.2.2.2.1 hlohi.2.2.2.2 Hx)
        have Hwf' : model_ivs_wf (munmap_model addr (BitVec.ofInt 64 nZ) model) := by
          unfold model_ivs_wf
          rw [PM, PN, PL]
          refine ⟨?_, ?_, ?_, ?_⟩
          · unfold map_remove
            exact ivs_wf_filter _ _ W1
          · exact maps_subtract_wf _ _ _ W2 (by omega)
          · exact maps_subtract_wf _ _ _ W3 (by omega)
          · unfold init_sp_ok
            rw [PISP]
            exact Wsp
        have HALLOW_bytes : A_bytes (allowA A E (ACS
              (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                    (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                  (kn_unfill (kn cs) bb bk ne) gone)
                cs.a_ss.s_next)
              (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
              cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
              cs.a_fd cs.a_tidset))
            = A_bytes (allowA A E cs) := by
          show A_bytes (List.flatMap (allow1 A E) (kept ++ (gone ++ cs.a_ghost)))
            = A_bytes (List.flatMap (allow1 A E) (cs.a_vis ++ cs.a_ghost))
          rw [← hkept, ← hgone]
          exact A_bytes_flat_map_split (allow1 A E)
            (fun p : expr × expr => ranges_apart_x (kn cs) (split_lit p.1).1 (split_lit p.1).2 p.2 bb bk ne)
            cs.a_vis (cs.a_ghost)
        have HALLOW_in : ∀ iv, iv ∈ allowA A E (ACS
              (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                    (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                  (kn_unfill (kn cs) bb bk ne) gone)
                cs.a_ss.s_next)
              (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
              cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
              cs.a_fd cs.a_tidset)
            ↔ iv ∈ allowA A E cs := by
          intro iv
          show iv ∈ List.flatMap (allow1 A E) (kept ++ (gone ++ cs.a_ghost))
            ↔ iv ∈ List.flatMap (allow1 A E) (cs.a_vis ++ cs.a_ghost)
          rw [← hkept, ← hgone]
          exact in_flat_map_split (allow1 A E)
            (fun p : expr × expr => ranges_apart_x (kn cs) (split_lit p.1).1 (split_lit p.1).2 p.2 bb bk ne)
            cs.a_vis (cs.a_ghost) iv
        have HEAGER : eager_used (munmap_model addr (BitVec.ofInt 64 nZ) model) ≤ eager_used model := by
          rw [eager_used_sem _ Hwf', eager_used_sem _ HC.co_wf, PM]
          unfold map_remove
          refine sum_count_filter_le
            (fun x => Bool.not (covered ((m_vmmaps model).vm_noaccess ++ m_vm_lazy model) x))
            (fun x => Bool.not (covered ((m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_noaccess
              ++ m_vm_lazy (munmap_model addr (BitVec.ofInt 64 nZ) model)) x))
            (fun p => Bool.not (bv_eqb p.1 addr)) (m_vmmaps model).vm_maps ?_
          intro q Hq Hkeep x hb1 hb2
          dsimp only [B, S, bv_unsigned] at hb1 hb2
          have Hke' : bv_eqb q.1 addr = false := by simpa using Hkeep
          have Hne' : q ≠ amap_den E m := by
            intro h
            rw [h] at Hke'
            unfold amap_den at Hke'
            rw [← hbase, haddr] at Hke'
            rw [PropExec.bv_eqb_refl] at Hke'
            cases Hke'
          have D := DISJl q Hq Hne'
          have Hxo : x < lo ∨ hi ≤ x := by
            rcases D with h | h
            · exact Or.inl (Int.lt_of_lt_of_le hb2 h)
            · exact Or.inr (Int.le_trans h hb1)
          have hinr : in_rng lo hi x = false := by
            rcases Hxo with h | h
            · exact in_rng_eq_false_of_lt h
            · exact in_rng_eq_false_of_le h
          show Bool.not (covered ((m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_noaccess
              ++ m_vm_lazy (munmap_model addr (BitVec.ofInt 64 nZ) model)) x)
            = Bool.not (covered ((m_vmmaps model).vm_noaccess ++ m_vm_lazy model) x)
          rw [PN, PL, covered_app, covered_app,
            covered_maps_subtract (m_vmmaps model).vm_noaccess lo hi W2 (by omega) x,
            covered_maps_subtract (m_vm_lazy model) lo hi W3 (by omega) x, hinr]
          simp only [Bool.not_false, Bool.and_true]
        have ALW : ∀ z, in_allow A E cs z = (in_allow A E (ACS
              (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                    (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                  (kn_unfill (kn cs) bb bk ne) gone)
                cs.a_ss.s_next)
              (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
              cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
              cs.a_fd cs.a_tidset) z
            || gone.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ z)
                && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2))
            || gone.any (fun p => decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p))) := by
          intro z
          show (in_vis E cs z || in_sh A E cs z)
            = (in_vis E (ACS _ _ _ _ _ _ _ _ _ _ _) z || in_sh A E (ACS _ _ _ _ _ _ _ _ _ _ _) z
              || gone.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ z)
                  && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2))
              || gone.any (fun p => decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p)))
          unfold in_vis in_sh
          show (cs.a_vis.any _ || cs.a_vis.any _)
            = (kept.any _ || kept.any _ || gone.any _ || gone.any _)
          rw [show cs.a_vis.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ z)
                && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2))
              = (kept.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ z)
                && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2))
                || gone.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ z)
                && decide (z < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2))) from by
              rw [← hkept, ← hgone]
              exact existsb_filter_split _ _ cs.a_vis,
            show cs.a_vis.any (fun p => decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p))
              = (kept.any (fun p => decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p))
                || gone.any (fun p => decide (sh_lo A E p ≤ z) && decide (z < sh_hi A E p))) from by
              rw [← hkept, ← hgone]
              exact existsb_filter_split _ _ cs.a_vis]
          simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
        have DISJF : ∀ m' ∈ List.filter (fun m0 => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m0)) cs.a_maps,
            m' ∈ cs.a_maps ∧ m ≠ m' ∧ (is_fog m' = false →
              bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len) ≤ lo ∨
              hi ≤ bv_unsigned (edenot E m'.am_base)) := by
          intro m' Hm'
          obtain ⟨Hm0, Hnm⟩ := List.mem_filter.mp Hm'
          have Hne' : m ≠ m' := by
            intro h
            rw [← h] at Hnm
            simp only [amap_match, Hnf, Hb, Hlen_eq, Bool.not_true, Bool.and_true,
              Bool.true_and] at Hnm
            cases Hnm
          exact ⟨Hm0, Hne', fun Hnf' => DISJ' m' Hm0 Hnf' Hne'⟩
        have KNF : ∀ m', m'.am_kind = .KNONE ∨ m'.am_kind = .KNONELAZY ∨ m'.am_kind = .KRWLAZY →
            is_fog m' = false := by
          intro m' Hk
          rcases Hk with h | h | h <;> simp [is_fog, is_tok_kind, h]
        -- the spec step
        have Hnw : (addr.toNat : Int) + page_round_up_Z len ≤ TASK_SIZE := by
          rw [show (addr.toNat : Int) = lo from hlo, hnZ, hhi]
          refine Int.le_trans hlohi.2.1 ?_
          decide
        have Hhas' : map_has (m_vmmaps model).vm_maps addr
            (BitVec.ofInt 64 (page_round_up_Z len)) = true := by
          have hn2 : edenot E m.am_len = BitVec.ofInt 64 (page_round_up_Z len) := by
            rw [hn, ← HnZw, ← hnZ]
          have hpair : amap_den E m = (addr, BitVec.ofInt 64 (page_round_up_Z len)) := by
            show (edenot E m.am_base, edenot E m.am_len) = _
            rw [← hbase, haddr, hn2]
          rw [hpair] at HIN
          exact map_has_intro _ _ _ HIN
        have Hal : ((addr.toNat : Int)) % page_size = 0 := by
          rw [show (addr.toNat : Int) = lo from hlo]
          have hp : page_size = 4096 := by decide
          rw [hp]
          exact B2
        have Hc : srealizes SEGS (AsanAcct.mkCfg (mkst (regupd R 10 (BitVec.ofInt 64 0))
            (v_addi (Z_to_bv 64 (pc cs)) 4) (unfill addr (BitVec.ofInt 64 nZ) FULL) (seg_rom SEGS))
            (munmap_model addr (BitVec.ofInt 64 nZ) model)) T := by
          rw [v_addi_pc (pc cs) Hpc0 Hpc4]
          refine HK E (regupd R 10 (BitVec.ofInt 64 0)) (unfill addr (BitVec.ofInt 64 nZ) FULL)
            (munmap_model addr (BitVec.ofInt 64 nZ) model)
            ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ ?_ rfl
          exact
            { co_regs := regs_ok_set_n E cs.a_ss.s_regs R 10 (.ELit 0) (BitVec.ofInt 64 0)
                HC.co_regs ⟨by omega, by omega⟩ rfl
              co_log := rfl

              co_know := by
                have HUNF : ∀ x : word, (bv_unsigned x < lo ∨ hi ≤ bv_unsigned x) →
                    unfill addr (BitVec.ofInt 64 nZ) FULL x = FULL x := by
                  intro x Hx
                  refine unfill_out addr (BitVec.ofInt 64 nZ) FULL x ?_
                  rcases Hx with h | h
                  · left
                    rw [show (addr.toNat : Int) = lo from hlo]
                    exact h
                  · right
                    rw [show (addr.toNat : Int) = lo from hlo,
                      show ((BitVec.ofInt 64 nZ).toNat : Int) = nZ from hbvn, hhi]
                    exact h
                have HOUT : ∀ x : word, ¬(lo ≤ bv_unsigned x ∧ bv_unsigned x < hi) →
                    bv_unsigned x < lo ∨ hi ≤ bv_unsigned x := by
                  intro x hz
                  by_cases h1 : lo ≤ bv_unsigned x
                  · right
                    exact Int.not_lt.mp (fun h2 => hz ⟨h1, h2⟩)
                  · left
                    exact Int.not_le.mp h1
                -- the pure Boolean core of `VISLE`: peeling `&& true` and weakening
                -- the last disjunct (`p` becomes `p || q1 || q2`)
                have BOOL : ∀ u c a b l p q1 q2 : Bool,
                    (u || c || (a && Bool.not b && (Bool.not l || p))) = true →
                    (u || c || (a && Bool.not b && (Bool.not l || (p || q1 || q2)))) = true := by
                  intro u c a b l p q1 q2 h
                  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
                  rcases h with h | h
                  · exact Or.inl h
                  · refine Or.inr ⟨h.1, ?_⟩
                    rcases h.2 with h2 | h2
                    · exact Or.inl h2
                    · exact Or.inr (Or.inl (Or.inl h2))
                have VISLE : ∀ x : word, vis A E (ACS
                      (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                        (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                            (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                          (kn_unfill (kn cs) bb bk ne) gone)
                        cs.a_ss.s_next)
                      (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                      cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                      cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model) x = true →
                    vis A E cs model x = true ∧ ¬(lo ≤ bv_unsigned x ∧ bv_unsigned x < hi) := by
                  intro x Hv
                  by_cases Hr : in_rng lo hi (bv_unsigned x) = true
                  · exfalso
                    have hz : lo ≤ bv_unsigned x ∧ bv_unsigned x < hi := (in_rng_true_iff lo hi _).mp Hr
                    unfold vis at Hv
                    dsimp only at Hv
                    rw [PM, INMAPS'] at Hv
                    have h1 : in_hull A (bv_unsigned x) = false := by
                      unfold in_hull
                      rw [Bool.and_eq_false_iff]
                      right
                      rw [decide_eq_false_iff_not]
                      omega
                    have h2 : decide (CEIL ≤ bv_unsigned x) = false := by
                      rw [decide_eq_false_iff_not]
                      omega
                    rw [h1, h2, Hr] at Hv
                    simp at Hv
                  · have Hrf : in_rng lo hi (bv_unsigned x) = false := by simpa using Hr
                    have hz : ¬(lo ≤ bv_unsigned x ∧ bv_unsigned x < hi) := (in_rng_false_iff lo hi _).mp Hrf
                    have Hx : bv_unsigned x < lo ∨ hi ≤ bv_unsigned x := by
                      by_cases h1 : lo ≤ bv_unsigned x
                      · right
                        exact Int.not_lt.mp (fun h2 => hz ⟨h1, h2⟩)
                      · left
                        exact Int.not_le.mp h1
                    refine ⟨?_, hz⟩
                    -- the successor's visibility, normalised to the old atoms
                    have hnr : Bool.not (in_rng lo hi (bv_unsigned x)) = true := by
                      rw [Hrf]; rfl
                    unfold vis at Hv
                    dsimp only at Hv
                    rw [PM, INMAPS', NOACC, LAZYOUT x Hx] at Hv
                    simp only [hnr, Bool.and_true] at Hv
                    -- the goal, with the old `in_allow` decomposed
                    unfold vis
                    dsimp only
                    rw [ALW (bv_unsigned x)]
                    exact BOOL _ _ _ _ _ _ _ _ Hv
                have VISEQ : ∀ x : word, (bv_unsigned x < lo ∨ hi ≤ bv_unsigned x) →
                    (∀ p, p ∈ gone → ¬((sh_iv A E (kn cs) p).1 ≤ bv_unsigned x ∧
                      bv_unsigned x < (sh_iv A E (kn cs) p).1 + (sh_iv A E (kn cs) p).2)) →
                    vis A E (ACS
                      (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                        (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                            (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                          (kn_unfill (kn cs) bb bk ne) gone)
                        cs.a_ss.s_next)
                      (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                      cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                      cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model) x
                      = vis A E cs model x := by
                  intro x Hx Hnsh
                  unfold vis
                  dsimp only
                  rw [PM, INMAPS', NOACC, LAZYOUT x Hx]
                  have Hrf : in_rng lo hi (bv_unsigned x) = false := by
                    rcases Hx with h | h
                    · exact in_rng_eq_false_of_lt h
                    · exact in_rng_eq_false_of_le h
                  rw [ALW (bv_unsigned x), Hrf]
                  have Hany1 : gone.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ bv_unsigned x)
                      && decide (bv_unsigned x < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2)) = false := by
                    refine existsb_false_forall _ _ ?_
                    intro p Hp
                    by_cases Hc1 : (decide (AsanPlanSound.uE E p.1 ≤ bv_unsigned x)
                        && decide (bv_unsigned x < AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2)) = true
                    · exfalso
                      have hz := (GONE p Hp).1 (bv_unsigned x) Hc1
                      rcases Hx with h | h <;> omega
                    · simpa using Hc1
                  have Hany2 : gone.any (fun p => decide (sh_lo A E p ≤ bv_unsigned x)
                      && decide (bv_unsigned x < sh_hi A E p)) = false := by
                    refine existsb_false_forall _ _ ?_
                    intro p Hp
                    by_cases Hc1 : (decide (sh_lo A E p ≤ bv_unsigned x)
                        && decide (bv_unsigned x < sh_hi A E p)) = true
                    · exfalso
                      exact Hnsh p Hp ((GONE p Hp).2.2.2 (bv_unsigned x) Hc1)
                    · simpa using Hc1
                  rw [Hany1, Hany2]
                  simp only [Bool.or_false, Bool.and_true, Bool.not_false]
                have MRNONE : ∀ x : word, Mr A argH E cs model FULL x = none →
                    Mr A argH E (ACS
                      (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                        (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                            (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                          (kn_unfill (kn cs) bb bk ne) gone)
                        cs.a_ss.s_next)
                      (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                      cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                      cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model)
                      (unfill addr (BitVec.ofInt 64 nZ) FULL) x = none := by
                  intro x Hx
                  by_cases harg : argH E x = true
                  · unfold Mr mrestrict hid
                    simp [harg]
                  · have harg' : argH E x = false := by simpa using harg
                    by_cases Hv' : vis A E (ACS
                        (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                          (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                              (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                            (kn_unfill (kn cs) bb bk ne) gone)
                          cs.a_ss.s_next)
                        (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                        cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                        cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model) x = true
                    · obtain ⟨Hv, hz⟩ := VISLE x Hv'
                      have hunf : unfill addr (BitVec.ofInt 64 nZ) FULL x = FULL x := HUNF x (HOUT x hz)
                      unfold Mr mrestrict hid at Hx ⊢
                      simp only [harg', Bool.false_or, Hv', Hv, hunf, Bool.not_true,
                        Bool.not_false] at Hx ⊢
                      exact Hx
                    · have Hv'f : vis A E (ACS
                          (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                            (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                                (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                              (kn_unfill (kn cs) bb bk ne) gone)
                            cs.a_ss.s_next)
                          (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                          cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                          cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model) x = false := by
                        simpa using Hv'
                      unfold Mr mrestrict hid
                      simp only [harg', Bool.false_or, Hv'f, Bool.not_false, ite_true]
                have MRKEEP : ∀ x : word, (bv_unsigned x < lo ∨ hi ≤ bv_unsigned x) →
                    (∀ p, p ∈ gone → ¬((sh_iv A E (kn cs) p).1 ≤ bv_unsigned x ∧
                      bv_unsigned x < (sh_iv A E (kn cs) p).1 + (sh_iv A E (kn cs) p).2)) →
                    Mr A argH E (ACS
                      (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                        (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                            (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                          (kn_unfill (kn cs) bb bk ne) gone)
                        cs.a_ss.s_next)
                      (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                      cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                      cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model)
                      (unfill addr (BitVec.ofInt 64 nZ) FULL) x = Mr A argH E cs model FULL x := by
                  intro x Hx Hnsh
                  have hvis := VISEQ x Hx Hnsh
                  have hunf := HUNF x Hx
                  unfold Mr mrestrict hid
                  dsimp only
                  simp only [hvis, hunf]
                unfold know_ok
                intro K HinK
                have hU : kn_unfill (kn cs) bb bk ne
                    = (kn cs).filter (fun K => kimg_b K
                        || kentry_apart_bp (kn cs) (mk_sprep (kn cs) bb bk ne) bb bk ne K) := rfl
                have Hacc : ∀ K', K' ∈ kn_unfill (kn cs) bb bk ne → K' ∈ kn cs := by
                  intro K' HK'
                  rw [hU] at HK'
                  exact (List.mem_filter.mp HK').1
                obtain ⟨Hin0, Hsh⟩ := fold_unfill_inv SEGS A E (Mr A argH E cs model FULL) (kn cs) gone
                  (kn_unfill (kn cs) bb bk ne) K HKN Hacc HinK
                rw [hU] at Hin0
                obtain ⟨Hin0', Hkeep0⟩ := List.mem_filter.mp Hin0
                have HKK := HKN K Hin0'
                by_cases Himg : kimg_b K = true
                · cases K with
                  | KImg klo khi =>
                    obtain ⟨HA, HB, HCC⟩ := HKK
                    exact ⟨HA, HB, fun i h1 h2 => MRNONE i (HCC i h1 h2)⟩
                  | KWord a w v => simp [kimg_b] at Himg
                  | KZero a n => simp [kimg_b] at Himg
                  | KBlob a n k => simp [kimg_b] at Himg
                  | KAlign e m => simp [kimg_b] at Himg
                  | KRange e l h => simp [kimg_b] at Himg
                  | KWr a n => simp [kimg_b] at Himg
                  | KDisj a1 n1 a2 n2 => simp [kimg_b] at Himg
                  | KFill a n c => simp [kimg_b] at Himg
                  | KUnk a n => simp [kimg_b] at Himg
                · have Hapart : kentry_apart_bp (kn cs) (mk_sprep (kn cs) bb bk ne) bb bk ne K = true := by
                    rw [Bool.or_eq_true] at Hkeep0
                    rcases Hkeep0 with h | h
                    · exact absurd h Himg
                    · exact h
                  rw [kentry_apart_bp_eq] at Hapart
                  have Hap0 := kentry_apart_b_sem SEGS E _ (kn cs) K bb bk ne HKN Hapart
                  rw [Hest, HelenZ] at Hap0
                  rcases Hsh with Himg2 | Hsh2
                  · exact absurd Himg2 Himg
                  · refine kentry_keep_foot SEGS E (Mr A argH E cs model FULL)
                      (Mr A argH E (ACS
                        (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                          (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                              (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                            (kn_unfill (kn cs) bb bk ne) gone)
                          cs.a_ss.s_next)
                        (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                        cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                        cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model)
                        (unfill addr (BitVec.ofInt 64 nZ) FULL)) K HKK ?_ MRNONE
                    intro x Hfx
                    apply MRKEEP
                    · unfold kfoot_apart at Hap0
                      cases hkf : kfoot E K with
                      | none =>
                        rw [hkf] at Hfx
                        exact Hfx.elim
                      | some sl =>
                        obtain ⟨fs, fl⟩ := sl
                        rw [hkf] at Hfx Hap0
                        dsimp only at Hfx Hap0
                        obtain ⟨g1, g2⟩ := Hfx
                        omega
                    · intro p Hp Hin
                      have HH := Hsh2 p Hp
                      unfold kfoot_apart at HH
                      cases hkf : kfoot E K with
                      | none =>
                        rw [hkf] at Hfx
                        exact Hfx.elim
                      | some sl =>
                        obtain ⟨fs, fl⟩ := sl
                        rw [hkf] at Hfx HH
                        dsimp only at Hfx HH
                        obtain ⟨g1, g2⟩ := Hfx
                        omega

              co_halt := HC.co_halt
              co_fds := HC.co_fds
              co_fs := HC.co_fs
              co_tid := HC.co_tid
              co_res := HC.co_res
              co_limit := HC.co_limit
              co_maps := by
                rw [PM]
                exact MAPS'
              co_holes := by
                rw [PM]
                intro m' Hm' Hh
                obtain ⟨Hm0, -, -⟩ := DISJF m' Hm'
                have hh := HC.co_holes m' Hm0 Hh
                refine ⟨?_, hh.2⟩
                intro iv Hiv
                apply hh.1
                rcases List.mem_append.mp Hiv with h | h
                · exact List.mem_append.mpr (Or.inl h)
                · exact List.mem_append.mpr (Or.inr (List.mem_filter.mp h).1)
              co_seps := by
                rw [PM]
                unfold map_remove
                exact AsanNodesMmLib.seps_filter _ _ HC.co_seps
              co_wf := Hwf'
              co_bounds := by
                rw [PM]
                unfold map_remove
                intro iv Hiv
                exact HC.co_bounds iv (List.mem_filter.mp Hiv).1
              co_lazyb := by
                rw [PL]
                intro iv Hiv
                obtain ⟨r, Hr, R1, R2, -⟩ := maps_subtract_pieces _ lo hi iv W3 Hiv
                obtain ⟨Y1, Y2⟩ := HC.co_lazyb r Hr
                exact ⟨Int.le_trans Y1 R1, Int.le_trans R2 Y2⟩
              co_nasub := by
                intro z Hz
                rw [NOACC, Bool.and_eq_true] at Hz
                rw [PM, INMAPS', HC.co_nasub z Hz.1, Hz.2]
                rfl
              co_none := by
                rw [PN]
                intro m' Hm' Hk'
                obtain ⟨Hm0, Hne', D⟩ := DISJF m' Hm'
                have Hnf' : is_fog m' = false := by
                  rcases Hk' with h | h
                  · exact KNF m' (Or.inl h)
                  · exact KNF m' (Or.inr (Or.inl h))
                have hD := D Hnf'
                have X := HC.co_none m' Hm0 Hk'
                have C1 := (HC.co_bounds (amap_den E m')
                  (maps_match_In E cs.a_maps _ m' HC.co_maps Hm0 Hnf')).1
                dsimp only [amap_den] at C1
                exact maps_subtract_keeps _ _ _ _ _ (by omega) C1 X hD
              co_kinds := by
                intro m' Hm' Hk' x hx
                obtain ⟨Hm0, Hne', D⟩ := DISJF m' Hm'
                have Hnf' : is_fog m' = false := KNF m' (Or.inr (Or.inr Hk'))
                have hD := D Hnf'
                obtain ⟨K1, K2⟩ := HC.co_kinds m' Hm0 Hk' x hx
                have Hxo : bv_unsigned x < lo ∨ hi ≤ bv_unsigned x := by
                  clear hlohi B2 B3 HnZm HnZpos HnZlt
                  omega
                rw [NOACC, LAZYOUT x Hxo, K1, K2]
                constructor <;> rfl
              co_totsz := by
                have SF := sum_sizes_filter_le (fun p => Bool.not (bv_eqb p.1 addr))
                  (m_vmmaps model).vm_maps
                have H := HC.co_totsz
                rw [sum_sizes_app] at H
                rw [PM, sum_sizes_app]
                show sum_sizes (m_vmmaps model).vm_reserved
                  + sum_sizes (List.filter (fun p => Bool.not (bv_eqb p.1 addr)) (m_vmmaps model).vm_maps)
                  ≤ cs.a_totsz
                omega
              co_split := by
                obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := HC.co_split
                refine ⟨Y, HY1, HY2, HY3, ?_⟩
                rw [PM]
                unfold map_remove
                obtain ⟨S1, S2⟩ := ledger_split_app_inv _ _ _ _ HY4
                exact ledger_split_app _ _ _ _ S1 (ledger_split_filter _ _ _ _ S2)
              co_brk := HC.co_brk
              co_sbrk := HC.co_sbrk
              co_eager := Int.le_trans HEAGER HC.co_eager
              co_abytes := by
                rw [HALLOW_bytes]
                exact HC.co_abytes
              co_minv := by
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · rw [PT]
                  exact HC.co_minv.minv_nodup.filter _
                · rw [PT]
                  intro q Hq
                  exact HC.co_minv.minv_aligned q (List.mem_filter.mp Hq).1
                · rw [PT]
                  intro q Hq
                  have hq := (List.mem_filter.mp Hq).1
                  have P3 := HC.co_minv.minv_allowed q hq
                  unfold page_allowedb at P3 ⊢
                  rw [List.any_eq_true] at P3 ⊢
                  obtain ⟨iv, Hiv, Hbb⟩ := P3
                  exact ⟨iv, (HALLOW_in iv).mpr Hiv, Hbb⟩
                · rw [PT]
                  intro q Hq
                  obtain ⟨hq, hout⟩ := List.mem_filter.mp Hq
                  have P4 := HC.co_minv.minv_lazy q hq
                  have hal : bv_unsigned q % 4096 = 0 := by
                    have Qa : (q.toNat : Int) % page_size = 0 := HC.co_minv.minv_aligned q hq
                    have hp : page_size = 4096 := by decide
                    rwa [hp] at Qa
                  have hpb : page_base q = q := page_base_aligned' q hal
                  have hout2 : ¬(lo ≤ bv_unsigned q ∧ bv_unsigned q < hi) := by
                    intro h
                    unfold page_outside_range at hout
                    have h2 : (decide (lo ≤ (q.toNat : Int)) && decide ((q.toNat : Int) < hi)) = true := by
                      rw [Bool.and_eq_true]
                      exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩
                    rw [h2] at hout
                    cases hout
                  have hprem : bv_unsigned q + page_size ≤ lo ∨ hi ≤ bv_unsigned q := by
                    have hxo : bv_unsigned q < lo ∨ hi ≤ bv_unsigned q := by
                      by_cases h1 : lo ≤ bv_unsigned q
                      · right
                        exact Int.not_lt.mp (fun h2 => hout2 ⟨h1, h2⟩)
                      · left
                        exact Int.not_le.mp h1
                    rcases hxo with h | h
                    · left
                      have h1 := page_of_byte_out_aligned q lo hi hlohi.2.2.2.1 hlohi.2.2.2.2 (Or.inl h)
                      rw [hpb] at h1
                      have hp : page_size = 4096 := by decide
                      rcases h1 with h1 | h1
                      · rwa [hp]
                      · omega
                    · exact Or.inr h
                  rw [PL, page_in_ranges_subtract_out q (m_vm_lazy model) lo hi W3 (by omega) hprem]
                  exact P4
                · rw [HALLOW_bytes]
                  rw [show (m_vmmaps (munmap_model addr (BitVec.ofInt 64 nZ) model)).vm_limit
                      = (m_vmmaps model).vm_limit from rfl]
                  rw [show eager_used (munmap_model addr (BitVec.ofInt 64 nZ) model)
                      = eager_used (munmap_model addr (BitVec.ofInt 64 nZ) model) from rfl]
                  exact Int.le_trans (Int.add_le_add_right HEAGER _) HC.co_minv.minv_budget
              co_zero := by
                intro x Hh Hmx Hna Hlz Hgh
                have Hgh0 : in_ghost E cs (bv_unsigned x) = false := by
                  unfold in_ghost at Hgh ⊢
                  rw [List.any_append, Bool.or_eq_false_iff] at Hgh
                  exact Hgh.2
                rw [PM, INMAPS', Bool.and_eq_true] at Hmx
                obtain ⟨Hmx0, Hxo'⟩ := Hmx
                have Hxo'f : in_rng lo hi (bv_unsigned x) = false := by simpa using Hxo'
                have Hxo : bv_unsigned x < lo ∨ hi ≤ bv_unsigned x := by
                  by_cases h1 : lo ≤ bv_unsigned x
                  · right
                    exact Int.not_lt.mp (fun h2 => (in_rng_false_iff lo hi _).mp Hxo'f ⟨h1, h2⟩)
                  · left
                    exact Int.not_le.mp h1
                have hunf : unfill addr (BitVec.ofInt 64 nZ) FULL x = FULL x := by
                  refine unfill_out addr (BitVec.ofInt 64 nZ) FULL x ?_
                  rcases Hxo with h | h
                  · left
                    rw [show (addr.toNat : Int) = lo from hlo]
                    exact h
                  · right
                    rw [show (addr.toNat : Int) = lo from hlo,
                      show ((BitVec.ofInt 64 nZ).toNat : Int) = nZ from hbvn, hhi]
                    exact h
                rw [hunf]
                rw [NOACC, Bool.and_eq_false_iff] at Hna
                rw [LAZYOUT x Hxo] at Hlz
                by_cases Hold : hid A argH E cs model x = true
                · refine HC.co_zero x Hold Hmx0 ?_ Hlz Hgh0
                  rcases Hna with h | h
                  · exact h
                  · exfalso
                    have h2 : in_rng lo hi (bv_unsigned x) = true := by simpa using h
                    rw [h2] at Hxo'f
                    cases Hxo'f
                · have Hold' : hid A argH E cs model x = false := by simpa using Hold
                  have harg : argH E x = false := by
                    unfold hid at Hold'
                    rw [Bool.or_eq_false_iff] at Hold'
                    exact Hold'.1
                  have hnotvis : vis A E cs model x = true := by
                    unfold hid at Hold'
                    rw [Bool.or_eq_false_iff] at Hold'
                    simpa using Hold'.2
                  have SHX : ∃ p, p ∈ gone ∧ (sh_iv A E (kn cs) p).1 ≤ bv_unsigned x ∧
                      bv_unsigned x < (sh_iv A E (kn cs) p).1 + (sh_iv A E (kn cs) p).2 := by
                    by_cases Hex : gone.any (fun p => decide (sh_lo A E p ≤ bv_unsigned x)
                        && decide (bv_unsigned x < sh_hi A E p)) = true
                    · obtain ⟨p, Hp, Hpx⟩ := List.any_eq_true.mp Hex
                      rw [Bool.and_eq_true] at Hpx
                      exact ⟨p, Hp, (GONE p Hp).2.2.2 (bv_unsigned x) (by
                        rw [Bool.and_eq_true]; exact Hpx)⟩
                    · exfalso
                      have Hexf : gone.any (fun p => decide (sh_lo A E p ≤ bv_unsigned x)
                          && decide (bv_unsigned x < sh_hi A E p)) = false := by simpa using Hex
                      have Hany1 : gone.any (fun p => decide (AsanPlanSound.uE E p.1 ≤ bv_unsigned x)
                          && decide (bv_unsigned x < AsanPlanSound.uE E p.1
                            + AsanPlanSound.uE E p.2)) = false := by
                        refine existsb_false_forall _ _ ?_
                        intro p Hp
                        by_cases Hc1 : (decide (AsanPlanSound.uE E p.1 ≤ bv_unsigned x)
                            && decide (bv_unsigned x < AsanPlanSound.uE E p.1
                              + AsanPlanSound.uE E p.2)) = true
                        · exfalso
                          have hz := (GONE p Hp).1 (bv_unsigned x) Hc1
                          rcases Hxo with h | h <;> omega
                        · simpa using Hc1
                      unfold vis at hnotvis
                      dsimp only at hnotvis
                      rw [ALW (bv_unsigned x), Hexf, Hany1, Bool.or_false, Bool.or_false] at hnotvis
                      have hgoal : (in_hull A (bv_unsigned x) || decide (CEIL ≤ bv_unsigned x) ||
                          (in_ivs (bv_unsigned x) (m_vmmaps model).vm_maps
                            && !(in_ivs (bv_unsigned x) (m_vmmaps model).vm_noaccess)
                            && (!(page_in_ranges (page_base x) (m_vm_lazy model))
                              || in_allow A E (ACS
                          (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                            (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                                (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                              (kn_unfill (kn cs) bb bk ne) gone)
                            cs.a_ss.s_next)
                          (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                          cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                          cs.a_fd cs.a_tidset) (bv_unsigned x)))) = true := hnotvis
                      have Hc' : vis A E (ACS
                          (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (expr.ELit 0))
                            (List.foldl (fun kk p => kn_unfill kk (shadow_of A (kn cs) p.1 p.2).1
                                (shadow_of A (kn cs) p.1 p.2).2.1 (shadow_of A (kn cs) p.1 p.2).2.2)
                              (kn_unfill (kn cs) bb bk ne) gone)
                            cs.a_ss.s_next)
                          (List.filter (fun m => Bool.not (amap_match (kn cs) (AsanPlanCore.reg cs 10) ne m)) cs.a_maps)
                          cs.a_totsz cs.a_ylo cs.a_eager kept (gone ++ cs.a_ghost) cs.a_abytes cs.a_brk
                          cs.a_fd cs.a_tidset) (munmap_model addr (BitVec.ofInt 64 nZ) model) x = true := by
                        unfold vis
                        dsimp only
                        rw [PM, INMAPS', NOACC, LAZYOUT x Hxo]
                        simp only [Hxo'f, Bool.not_false, Bool.and_true, Bool.not_true,
                          Bool.false_or, Bool.and_false]
                        exact hnotvis
                      unfold hid at Hh
                      rw [harg, Bool.false_or] at Hh
                      rw [Hc'] at Hh
                      cases Hh
                  obtain ⟨p, Hp, Hpx⟩ := SHX
                  have Z0 := (GONE p Hp).2.2.1 x Hpx
                  unfold Mr mrestrict at Z0
                  simp only [Hold', Bool.false_eq_true, ite_false] at Z0
                  exact Z0
              co_sinv := by
                refine SINV_frame E FULL (unfill addr (BitVec.ofInt 64 nZ) FULL) ?_ HC.co_sinv
                intro x Hx
                have hCEIL : CEIL ≤ bv_unsigned x := argH_high E x Hx
                have hlo' : (addr.toNat : Int) = lo := hlo
                have hbvn' : ((BitVec.ofInt 64 nZ).toNat : Int) = nZ := hbvn
                refine unfill_out addr (BitVec.ofInt 64 nZ) FULL x ?_
                right
                rw [hlo', hbvn']
                rw [hhi]
                exact Int.le_trans hlohi.2.1 hCEIL }
        have Hc' : srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (BitVec.ofInt 64 0))
            (v_addi (Z_to_bv 64 (pc cs)) 4)
            (unfill addr (BitVec.ofInt 64 (page_round_up_Z len)) FULL) (seg_rom SEGS))
            (munmap_model addr (BitVec.ofInt 64 (page_round_up_Z len)) model)) T := by
          rw [hnZ]
          exact Hc
        exact AsanNodesLibE.srz_munmap_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
          addr len T HF HE HC.co_halt H17 H10 Hal H11 Hlen0 Hnw Hhas' Hc'
      · rename_i hcond
        simp at Hn
  · simp at Hn

/-! ## Section `D` — `OBL_sys` assembled (`node_sys_sound_YMunmap`, `node_sys_sound`) -/

/-- `node_sys_sound_YMunmap`: the `sys_stmt` packaging of
    `node_munmap_sound`.   is `eapply node_munmap_sound; eauto`; in Lean
    `node_sys A nx0 .YMunmap` reduces to `node_munmap A` definitionally, so the
    unpacked form is a direct application. -/
theorem node_sys_sound_YMunmap (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (RES_len : res_len_ok SEGS A) (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M') :
    sys_stmt SEGS A nx0 LIMIT SINV argH FS0 .YMunmap := by
  intro cs cs' E R FULL model T HC Hec Hn HK
  exact node_munmap_sound SEGS A nx0 LIMIT SINV argH RES_len HULL_ok SHADOW_ok
    argH_high SINV_frame FS0 cs cs' E R FULL model T HC Hec Hn HK

/-- `node_sys_sound`: every `snode`, i.e. `OBL_sys`.
    Every caller that can dispatch to `YBrk` / `YSetTid` already has them, so
    the assembled statement is equivalent in practice. -/
theorem node_sys_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_hull : ∀ iv ∈ segments_reserved SEGS,
      A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi)
    (RES_len : res_len_ok SEGS A) (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ E E' (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ E E' M, env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    ∀ y, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y := by
  intro y
  cases y with
  | YMunmap =>
    exact node_sys_sound_YMunmap SEGS A nx0 LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok
      argH_high SINV_frame
  | YBrk =>
    exact node_sys_sound_YBrk SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_hull
      HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree PLACEMENT
  | YSetTid =>
    exact node_sys_sound_YSetTid SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_hull
      HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree PLACEMENT


/-! #########################################################################
    ## B.3 The `brk2` node

    The six `brk2_*` definitions below are the granted grow's abbreviations,
    which  introduces with `set` and re-folds with `fold`.  They are
    (see the header): a Lean `have` is opaque, and a `let` is opaque
    to `omega` (§5.7), so each is a `def` instead and the proof reads it back
    with `rfl` / `show`.
    ######################################################################### -/

/-- The `VmMaps` the granted grow installs. -/
def brk2_vm (model : Model) (d : Int) : VmMaps :=
  VmMaps.mkVmMapsFull (m_vmmaps model).vm_reserved
    (((m_vmmaps model).vm_brk, Z_to_bv 64 d) :: (m_vmmaps model).vm_maps)
    (m_vmmaps model).vm_noaccess (m_vmmaps model).vm_start_brk
    (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d))
    (m_vmmaps model).vm_limit (m_vmmaps model).vm_mmap_base
    (m_vmmaps model).vm_init_sp

/-- The model after the granted grow. -/
def brk2_model (model : Model) (d : Int) : Model := with_vmmaps (brk2_vm model d) model

/-- The requested break as a `word`. -/
def brk2_req (model : Model) (d : Int) : word :=
  Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + d)

/-- The register file after the granted grow. -/
def brk2_R (R : BvMap word) (model : Model) (d : Int) : BvMap word :=
  regupd R 10 (brk2_req model d)

/-- The full memory after the granted grow. -/
def brk2_FULL (FULL : word → Option byte) (model : Model) (d : Int) : word → Option byte :=
  zfill (m_vmmaps model).vm_brk (Z_to_bv 64 d) FULL

/-- The intermediate checker state of the granted grow : the filtered knowledge, the new ledger entry,
    the raised totals and break. -/
def brk2_mid (A : atable) (cs : acs) (d : Int) : acs :=
  ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs (kn_grant_filter A (kn cs) cs.a_maps) cs.a_ss.s_next)
    (AM cs.a_brk (.ELit d) .KRW :: cs.a_maps) (cs.a_totsz + d) cs.a_ylo
    (cs.a_eager + d) cs.a_vis cs.a_ghost cs.a_abytes (reg cs 10) cs.a_fd cs.a_tidset

/-- `node_brk2_sound`: the M4 `brk2` node.  The
    blocked child keeps the old break; the granted child installs `[brk, brk+d)`
    as a `KRW` entry on the lazy path, widens the visibility to the new range,
    raises the break, and reads as zero on it — its checker state is
    `vis_add_sound` over the intermediate state's 27-field `cs_ok`, and the
    step itself is `srz_brk_grow_lazy`. -/
theorem node_brk2_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_hull : ∀ iv ∈ segments_reserved SEGS,
      A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ E (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ E E' (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ E M M', (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ E E' M, env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    brk2_stmt SEGS A nx0 LIMIT SINV argH FS0 := by
  intro cs csa csb E R FULL model TA TB HC Hec Hn HkA HkB
  obtain ⟨Hpc0, Hpc4, w, HF, HE⟩ := AsanNodesLibE.is_ecall_at_sound SEGS cs Hec
  unfold node_brk2 at Hn
  split at Hn
  · rename_i dv h17 hreq
    split at Hn
    · rename_i hguard
      dsimp only at Hn
      split at Hn
      · rename_i j csB' hva
        obtain ⟨bb, bk, hsp⟩ : ∃ bb bk, split_lit cs.a_brk = (bb, bk) := ⟨_, _, rfl⟩
        rw [hsp] at hva
        dsimp only at hva
        have EcsA : set_pc (set_reg cs 10 cs.a_brk) (pc cs + 4) = csa :=
          (Prod.mk.injEq ..).mp (Option.some.inj Hn) |>.1
        have EcsB : csB' = csb :=
          (Prod.mk.injEq ..).mp (Option.some.inj Hn) |>.2
        rw [EcsB] at hva
        unfold brk_grow_possible at hguard
        rw [hsp] at hguard
        dsimp only at hguard
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hguard
        obtain ⟨⟨⟨⟨Hbase, Hnf⟩, Hapart⟩, Hbudget⟩, -⟩ := hguard
        unfold budget_ok at Hbudget
        rw [decide_eq_true_eq] at Hbudget
        obtain ⟨G17, -⟩ := reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 214 HC
          ⟨by omega, by omega⟩ h17
        obtain ⟨D1, D2, -, -⟩ :=
          brk_req_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model dv HC hreq
        obtain ⟨B1, B2, B3, B4⟩ :=
          brk_base_ok_sound SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model dv HC Hbase
        have G10 := brk_req_val SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model dv HC hreq Hbase
        have Hmaps := (maps_match_exact E cs.a_maps (m_vmmaps model).vm_maps Hnf).mp HC.co_maps
        have hkhi : KHI < 2 ^ 64 := by unfold KHI; decide
        have hbkd : bv_unsigned (m_vmmaps model).vm_brk + dv < 2 ^ 64 := by omega
        have hdvlt : dv < 2 ^ 64 := by omega
        have Un : bv_unsigned (Z_to_bv 64 dv) = dv := by
          show ((BitVec.ofInt 64 dv).toNat : Int) = dv
          exact u64_lit dv ⟨by omega, hdvlt⟩
        have Ureql : bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + dv))
            = bv_unsigned (m_vmmaps model).vm_brk + dv := by
          show ((BitVec.ofInt 64 (bv_unsigned (m_vmmaps model).vm_brk + dv)).toNat : Int)
            = bv_unsigned (m_vmmaps model).vm_brk + dv
          exact u64_lit _ ⟨by omega, hbkd⟩
        have Hkle : KHI ≤ alloc_ceiling := by
          rw [alloc_ceiling_val]; unfold KHI; decide
        -- the shadow split's base really is the break
        have HKf : know_ok SEGS E (Mr A argH E cs model FULL) (kn (brk2_mid A cs dv)) := by
          show know_ok SEGS E (Mr A argH E cs model FULL)
            (kn_grant_filter A (kn cs) cs.a_maps)
          unfold kn_grant_filter kimg_clip
          exact know_ok_filter SEGS E _ _ _ (know_ok_filter SEGS E _ _ _ HC.co_know)
        obtain ⟨Hflat, HpcB, HregsB, HvisB, HmapsB, HghostB⟩ :=
          vis_add_shape A LIMIT (brk2_mid A cs dv) cs.a_brk (.ELit dv)
            (.KWr (SA bb bk) (.ELit dv) :: .KZero (SA bb bk) (.ELit dv) :: kn (brk2_mid A cs dv))
            csb hva
        rw [hsp] at Hflat
        dsimp only at Hflat
        obtain ⟨Fb1, Fb2, Fb3⟩ :=
          flat_x_sound SEGS E (Mr A argH E cs model FULL) (kn (brk2_mid A cs dv)) bb bk (.ELit dv)
            HKf Hflat
        have hlen : bv_unsigned (edenot E (.ELit dv)) = dv := by
          show elenZ E (.ELit dv) = dv
          exact AsanPlanSound.elenZ_lit E dv ⟨by omega, hdvlt⟩
        have HestR : 0 ≤ estart E (SA bb bk) ∧ estart E (SA bb bk) < 2 ^ 64 := by
          refine ⟨Fb1, ?_⟩
          have h := Fb2
          rw [hlen] at h
          omega
        have Hest : estart E (SA bb bk) = bv_unsigned (m_vmmaps model).vm_brk := by
          rw [← u_of_split E cs.a_brk bb bk hsp HestR, ← HC.co_brk]
        -- the ledger lies apart from the new range (plus the guard page)
        have APARTG : ∀ m, m ∈ cs.a_maps →
            bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
              ≤ bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + (dv + 4096)
              ≤ bv_unsigned (edenot E m.am_base) := by
          intro m hm
          have h := List.all_eq_true.mp Hapart m hm
          have hd := ranges_apart_x_sound SEGS E (Mr A argH E cs model FULL) (kn cs)
            bb bk (.ELit (dv + 4096)) m.am_base 0 m.am_len HC.co_know h
          rw [Hest, AsanPlanSound.elenZ_lit E (dv + 4096) ⟨by omega, by omega⟩] at hd
          dsimp only [estart, SA, elenZ] at hd
          omega
        have APART : ∀ m, m ∈ cs.a_maps →
            bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
              ≤ bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned (edenot E m.am_base) := by
          intro m hm
          rcases APARTG m hm with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        -- ## the new range is free
        have Hrfg : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
            (m_vmmaps model).vm_brk (Z_to_bv 64 (dv + page_size)) = true := by
          clear B1 D2
          refine region_free_intro _ _ _ ?_
          intro a sz Hin
          rcases List.mem_append.mp Hin with Hin | Hin
          · rw [HC.co_res] at Hin
            obtain ⟨R1, R2⟩ := RES_hull (a, sz) Hin
            dsimp only at R2
            unfold iv_overlap
            rw [Bool.and_eq_false_iff]
            left
            rw [decide_eq_false_iff_not]
            exact Int.not_lt.mpr (Int.le_trans R2 B3)
          · rw [Hmaps] at Hin
            obtain ⟨m, hm, hEq⟩ := List.mem_map.mp Hin
            dsimp only [amap_den] at hEq
            obtain ⟨rfl, rfl⟩ := hEq
            rcases APARTG m hm with h | h
            · unfold iv_overlap
              rw [Bool.and_eq_false_iff]
              left
              rw [decide_eq_false_iff_not]
              exact Int.not_lt.mpr h
            · have hps : page_size = (4096 : Int) := rfl
              have hz : bv_unsigned (Z_to_bv 64 (dv + page_size)) = dv + page_size := by
                show ((BitVec.ofInt 64 (dv + page_size)).toNat : Int) = dv + page_size
                refine u64_lit _ ⟨by rw [hps]; omega, ?_⟩
                rw [hps]
                have hk : KHI + 8192 < 2 ^ 64 := by unfold KHI; decide
                omega
              unfold iv_overlap
              rw [Bool.and_eq_false_iff]
              right
              rw [decide_eq_false_iff_not]
              show ¬ (bv_unsigned (edenot E m.am_base)
                < bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 (dv + page_size)))
              rw [hz]
              exact Int.not_lt.mpr h
        -- ## the backing budget
        have Hused : vm_backing_used model ≤ cs.a_eager + cs.a_abytes :=
          Int.le_trans
            (vm_backing_used_le (allowA A E cs) model HC.co_minv (A_wf_allowA A E cs))
            (Int.add_le_add HC.co_eager HC.co_abytes)
        have Hlive : vm_backing_used model + dv ≤ (m_vmmaps model).vm_limit := by
          rw [HC.co_limit]
          exact Int.le_trans (Int.add_le_add_right Hused dv) Hbudget
        have Hce : ((m_vmmaps model).vm_brk.toNat : Int) + dv ≤ alloc_ceiling :=
          Int.le_trans B4 Hkle
        have Hadm : Sys.Mm.Mmap.brk_grow_ok model
            (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + dv))
            (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + dv)) = true :=
          brk_grow_ok_aligned_intro model dv (by unfold page_size; exact B1)
            (by unfold page_size; exact D2) D1 B2 Hce HC.co_wf.2.2.2 Hrfg Hlive
        -- ## the blocked child
        have HA : srealizes SEGS (AsanAcct.mkCfg (mkst (regupd R 10 (m_vmmaps model).vm_brk)
            (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA := by
          rw [v_addi_pc (pc cs) Hpc0 Hpc4]
          have hpca : pc cs + 4 = pc csa := congrArg pc EcsA
          rw [hpca]
          exact HkA E (regupd R 10 (m_vmmaps model).vm_brk) FULL model
            ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩
            (by rw [← EcsA]
                exact brk_keep_ok SEGS A nx0 LIMIT SINV argH FS0 SINV_frame E cs R FULL model HC)
            rfl
        -- ## transports away from the new range
        have V1 : ∀ x : word, bv_unsigned x < bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned x →
            vis A E (brk2_mid A cs dv) (brk2_model model dv) x = vis A E cs model x := by
          intro x Hx
          have hm : (m_vmmaps (brk2_model model dv)).vm_maps
              = ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps := rfl
          have hl : m_vm_lazy (brk2_model model dv) = m_vm_lazy model := rfl
          have hn : (m_vmmaps (brk2_model model dv)).vm_noaccess
              = (m_vmmaps model).vm_noaccess := rfl
          have ha : in_allow A E (brk2_mid A cs dv) (bv_unsigned x)
              = in_allow A E cs (bv_unsigned x) := rfl
          unfold vis
          dsimp only
          rw [hm, hl, hn, ha, in_ivs_cons]
          dsimp only
          rw [Un]
          have hf : (decide (bv_unsigned (m_vmmaps model).vm_brk ≤ bv_unsigned x)
              && decide (bv_unsigned x < bv_unsigned (m_vmmaps model).vm_brk + dv)) = false := by
            clear B1 D2
            rw [Bool.and_eq_false_iff]
            rcases Hx with h | h
            · left; rw [decide_eq_false_iff_not]
              exact Int.not_le.mpr h
            · right; rw [decide_eq_false_iff_not]
              exact Int.not_lt.mpr h
          rw [hf]
          simp only [Bool.false_or]
        have H1 : ∀ x : word, bv_unsigned x < bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned x →
            hid A argH E (brk2_mid A cs dv) (brk2_model model dv) x
              = hid A argH E cs model x := by
          intro x Hx
          show (argH E x || !(vis A E (brk2_mid A cs dv) (brk2_model model dv) x))
              = (argH E x || !(vis A E cs model x))
          rw [V1 x Hx]
        have F1 : ∀ x : word, bv_unsigned x < bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned x →
            brk2_FULL FULL model dv x = FULL x := by
          intro x Hx
          show zfill (m_vmmaps model).vm_brk (Z_to_bv 64 dv) FULL x = FULL x
          refine zfill_out _ _ _ _ ?_
          rcases Hx with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ bv_unsigned x
            rw [Un]
            exact h
        have M1 : ∀ x : word, bv_unsigned x < bv_unsigned (m_vmmaps model).vm_brk ∨
            bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned x →
            Mr A argH E (brk2_mid A cs dv) (brk2_model model dv) (brk2_FULL FULL model dv) x
              = Mr A argH E cs model FULL x := by
          intro x Hx
          show (if hid A argH E (brk2_mid A cs dv) (brk2_model model dv) x then none
              else brk2_FULL FULL model dv x)
            = (if hid A argH E cs model x then none else FULL x)
          rw [H1 x Hx, F1 x Hx]
        -- ## the intermediate state is a checker state
        have HCB : cs_ok SEGS A LIMIT SINV argH FS0 E (brk2_mid A cs dv)
            (brk2_R R model dv) (brk2_FULL FULL model dv) (brk2_model model dv) := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- co_regs
            show regs_ok E cs.a_ss.s_regs (regupd R 10 (brk2_req model dv))
            refine regs_ok_regupd_same E cs.a_ss.s_regs R 10 (brk2_req model dv) HC.co_regs ?_ ?_
            · show getr R (Z_to_bv 5 10) = brk2_req model dv
              exact G10
            · intro h
              exact absurd (congrArg bv_unsigned h) (by decide)
          · -- co_log
            rfl
          · -- co_know
            refine kn_grant_filter_sound SEGS A HULL_ok E (Mr A argH E cs model FULL)
              (Mr A argH E (brk2_mid A cs dv) (brk2_model model dv) (brk2_FULL FULL model dv))
              (kn cs) cs.a_maps (bv_unsigned (m_vmmaps model).vm_brk) dv HC.co_know ?_ ?_ ?_ ?_ ?_
            · exact Int.le_trans B4 Hkle
            · exact B3
            · exact Int.le_of_lt D1
            · exact APART
            · exact M1
          · exact HC.co_halt
          · exact HC.co_fds
          · exact HC.co_fs
          · exact HC.co_tid
          · exact HC.co_res
          · exact HC.co_limit
          · -- co_maps
            show maps_match E (AM cs.a_brk (.ELit dv) .KRW :: cs.a_maps)
              (((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps)
            rw [maps_match]
            have hfog : is_fog (AM cs.a_brk (.ELit dv) .KRW) = false := by rfl
            rw [hfog]
            refine ⟨(m_vmmaps model).vm_maps, ?_, HC.co_maps⟩
            show ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps
              = amap_den E (AM cs.a_brk (.ELit dv) .KRW) :: (m_vmmaps model).vm_maps
            rw [show amap_den E (AM cs.a_brk (.ELit dv) .KRW)
              = (edenot E cs.a_brk, edenot E (.ELit dv)) from rfl]
            rw [← HC.co_brk]
            rfl
          · -- co_holes
            intro m hm
            rcases List.mem_cons.mp hm with h0 | hm
            · rw [h0]
              intro hk
              exact absurd hk (by
                rw [show is_hole (AM cs.a_brk (.ELit dv) .KRW) = false from rfl]
                exact Bool.false_ne_true)
            · intro hk
              obtain ⟨h1, h2⟩ := HC.co_holes m hm hk
              refine ⟨?_, h2⟩
              intro iv hiv
              rcases List.mem_append.mp hiv with hiv | hiv
              · exact h1 iv (List.mem_append_left _ hiv)
              · rcases List.mem_cons.mp hiv with hiv0 | hiv
                · rw [hiv0]
                  rcases APART m hm with h | h
                  · right
                    show bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
                      ≤ bv_unsigned (m_vmmaps model).vm_brk
                    exact h
                  · left
                    show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv)
                      ≤ bv_unsigned (edenot E m.am_base)
                    rw [Un]
                    exact h
                · exact h1 iv (List.mem_append_right _ hiv)
          · -- co_seps
            show seps (((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps)
            refine seps.cons _ _ ?_ HC.co_seps
            intro x hx
            rw [Hmaps] at hx
            obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hx
            rw [← hEq]
            dsimp only [amap_den, iv_disjoint]
            rcases APART m hm with h | h
            · right
              exact h
            · left
              rw [Un]
              exact h
          · -- co_wf
            refine model_ivs_wf_with_vmmaps (brk2_vm model dv) model HC.co_wf ?_ ?_ ?_
            · show ivs_wf (((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps)
              refine ivs_wf_cons _ _ ?_ HC.co_wf.1
              show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ 2 ^ 64
              rw [Un]
              omega
            · exact HC.co_wf.2.1
            · rfl
          · -- co_bounds
            intro iv hiv
            rcases List.mem_cons.mp hiv with h0 | hiv
            · rw [h0]
              refine ⟨?_, ?_, ?_, B3, ?_⟩
              · show 0 < bv_unsigned (Z_to_bv 64 dv)
                rw [Un]; exact D1
              · exact B1
              · show bv_unsigned (Z_to_bv 64 dv) % 4096 = 0
                rw [Un]; exact D2
              · show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ CEIL
                rw [Un]
                exact Int.le_trans B4 Hkle
            · exact HC.co_bounds iv hiv
          · -- co_lazyb
            exact HC.co_lazyb
          · -- co_nasub
            intro z hz
            have h := HC.co_nasub z hz
            show in_ivs z (((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps) = true
            rw [in_ivs_cons, h, Bool.or_true]
          · -- co_none
            intro m hm hk
            rcases List.mem_cons.mp hm with h0 | hm
            · rw [h0] at hk
              dsimp only at hk
              rcases hk with h | h <;> cases h
            · exact HC.co_none m hm hk
          · -- co_kinds
            intro m hm hk
            rcases List.mem_cons.mp hm with h0 | hm
            · rw [h0] at hk
              dsimp only at hk
              cases hk
            · exact HC.co_kinds m hm hk
          · -- co_totsz
            have h := HC.co_totsz
            show sum_sizes ((m_vmmaps model).vm_reserved
              ++ (((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps))
              ≤ cs.a_totsz + dv
            rw [sum_sizes_app] at h ⊢
            dsimp only [sum_sizes] at h ⊢
            show sum_sizes (m_vmmaps model).vm_reserved
              + (bv_unsigned (Z_to_bv 64 dv) + sum_sizes (m_vmmaps model).vm_maps)
              ≤ cs.a_totsz + dv
            rw [Un]
            omega
          · -- co_split
            obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := HC.co_split
            refine ⟨Y, HY1, HY2, ?_, ?_⟩
            · exact HY3
            · intro bb' ss' Hin
              rcases List.mem_append.mp Hin with Hin | Hin
              · exact HY4 bb' ss' (List.mem_append_left _ Hin)
              · rcases List.mem_cons.mp Hin with h0 | Hin
                · obtain ⟨rfl, rfl⟩ := h0
                  left
                  show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv)
                    ≤ kHighMemBeg
                  rw [KHI_eq, Un]
                  exact B4
                · exact HY4 bb' ss' (List.mem_append_right _ Hin)
          · -- co_brk
            show Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + dv)
              = edenot E (reg cs 10)
            rw [← reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC ⟨by omega, by omega⟩]
            exact G10.symm
          · -- co_sbrk
            show bv_unsigned (m_vmmaps model).vm_start_brk
              ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + dv))
            rw [Ureql]
            exact Int.le_trans HC.co_sbrk (Int.le_add_of_nonneg_right (Int.le_of_lt D1))
          · -- co_eager
            have Wb : iv_wf ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) := by
              show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ 2 ^ 64
              rw [Un]
              omega
            have He := eager_used_cons_le model (m_vmmaps model).vm_brk (Z_to_bv 64 dv)
              (brk2_vm model dv) HC.co_wf.1 Wb rfl rfl
            rw [Un] at He
            exact Int.le_trans He (Int.add_le_add_right HC.co_eager dv)
          · -- co_abytes
            exact HC.co_abytes
          · -- co_minv
            have Wb : iv_wf ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) := by
              show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ 2 ^ 64
              rw [Un]
              omega
            have He : eager_used (brk2_model model dv) ≤ eager_used model + dv := by
              have h := eager_used_cons_le model (m_vmmaps model).vm_brk (Z_to_bv 64 dv)
                (brk2_vm model dv) HC.co_wf.1 Wb rfl rfl
              rw [Un] at h
              exact h
            refine MInv_transport (allowA A E (brk2_mid A cs dv)) model
              (brk2_model model dv) HC.co_minv rfl rfl ?_
            have hlim : (m_vmmaps (brk2_model model dv)).vm_limit = LIMIT := HC.co_limit
            rw [hlim]
            have h1 : eager_used model ≤ cs.a_eager := HC.co_eager
            have h2 : A_bytes (allowA A E (brk2_mid A cs dv)) ≤ cs.a_abytes := HC.co_abytes
            have h3 : cs.a_eager + cs.a_abytes + dv ≤ LIMIT := Hbudget
            have h4 : eager_used (brk2_model model dv) ≤ eager_used model + dv := He
            clear B1 D2
            refine Int.le_trans (Int.add_le_add_right h4 _) ?_
            refine Int.le_trans (Int.add_le_add (Int.add_le_add h1 (Int.le_refl dv)) h2) ?_
            omega
          · -- co_zero
            intro a Ha Hm Hna Hlz Hgh
            have hm : (m_vmmaps (brk2_model model dv)).vm_maps
                = ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps := rfl
            have hl : m_vm_lazy (brk2_model model dv) = m_vm_lazy model := rfl
            rw [hm] at Hm
            rw [hl] at Hlz
            rw [in_ivs_cons] at Hm
            dsimp only at Hm
            rw [Un] at Hm
            rcases Int.lt_or_le (bv_unsigned a) (bv_unsigned (m_vmmaps model).vm_brk) with hlt | hge
            · have hout : bv_unsigned a < bv_unsigned (m_vmmaps model).vm_brk ∨
                  bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned a := Or.inl hlt
              rw [F1 a hout]
              refine HC.co_zero a ?_ ?_ Hna Hlz Hgh
              · rw [← H1 a hout]; exact Ha
              · rw [Bool.or_eq_true] at Hm
                rcases Hm with h | h
                · rw [Bool.and_eq_true] at h
                  exfalso
                  have h1 : bv_unsigned (m_vmmaps model).vm_brk ≤ bv_unsigned a :=
                    of_decide_eq_true h.1
                  omega
                · exact h
            · rcases Int.lt_or_le (bv_unsigned a)
                (bv_unsigned (m_vmmaps model).vm_brk + dv) with hlt2 | hge2
              · exact zfill_in _ _ _ _ ⟨hge, by rw [Un]; exact hlt2⟩
              · have hout : bv_unsigned a < bv_unsigned (m_vmmaps model).vm_brk ∨
                    bv_unsigned (m_vmmaps model).vm_brk + dv ≤ bv_unsigned a := Or.inr hge2
                rw [F1 a hout]
                refine HC.co_zero a ?_ ?_ Hna Hlz Hgh
                · rw [← H1 a hout]; exact Ha
                · rw [Bool.or_eq_true] at Hm
                  rcases Hm with h | h
                  · rw [Bool.and_eq_true] at h
                    exfalso
                    have h2 : bv_unsigned a < bv_unsigned (m_vmmaps model).vm_brk + dv :=
                      of_decide_eq_true h.2
                    omega
                  · exact h
          · -- co_sinv
            refine SINV_frame E FULL (brk2_FULL FULL model dv) ?_ HC.co_sinv
            intro a Ha
            show zfill (m_vmmaps model).vm_brk (Z_to_bv 64 dv) FULL a = FULL a
            refine zfill_out _ _ _ _ ?_
            refine Or.inr ?_
            show bv_unsigned (m_vmmaps model).vm_brk + bv_unsigned (Z_to_bv 64 dv) ≤ bv_unsigned a
            rw [Un]
            exact Int.le_trans B4 (Int.le_trans Hkle (argH_high E a Ha))
        -- ## the new knowledge at the granted grow, read through the new visibility
        have HKnow : know_ok SEGS E
            (Mr A argH E csb (brk2_model model dv) (brk2_FULL FULL model dv))
            (.KWr (SA bb bk) (.ELit dv) :: .KZero (SA bb bk) (.ELit dv)
              :: kn (brk2_mid A cs dv)) := by
          -- ## the flat footprint of the new range
          have Hfl : flat E (SA bb bk) (elenZ E (.ELit dv)) := by
            unfold flat
            exact ⟨HestR.1, HestR.2, by rw [show elenZ E (.ELit dv) = dv from hlen]; exact Int.le_of_lt D1, Fb2⟩
          have hlenZ : elenZ E (.ELit dv) = dv := hlen
          -- ## nothing in the new range is PROT_NONE
          have NA : ∀ z : Int, bv_unsigned (m_vmmaps model).vm_brk ≤ z →
              z < bv_unsigned (m_vmmaps model).vm_brk + dv →
              in_ivs z (m_vmmaps model).vm_noaccess = false := by
            intro z Hx1 Hx2
            cases h : in_ivs z (m_vmmaps model).vm_noaccess with
            | false => rfl
            | true =>
              exfalso
              have hsub := HC.co_nasub z h
              rw [Hmaps] at hsub
              obtain ⟨iv, hiv, hb⟩ := (in_ivs_true z _).mp hsub
              obtain ⟨m, hm, hEq⟩ := List.mem_map.mp hiv
              dsimp only [amap_den] at hEq
              obtain ⟨rfl, rfl⟩ := hEq
              dsimp only at hb
              rcases APART m hm with hh | hh
              · omega
              · omega
          -- ## the new range reads as zero
          have INB : ∀ i : Int, 0 ≤ i → i < dv →
              Mr A argH E csb (brk2_model model dv) (brk2_FULL FULL model dv)
                (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) = some (Z_to_bv 8 0) := by
            intro i Hi0 Hid
            have Ua : bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i))
                = bv_unsigned (m_vmmaps model).vm_brk + i := by
              show ((BitVec.ofInt 64 (bv_unsigned (m_vmmaps model).vm_brk + i)).toNat : Int)
                = bv_unsigned (m_vmmaps model).vm_brk + i
              refine u64_lit _ ⟨by omega, ?_⟩
              have hk : KHI + 8192 < 2 ^ 64 := by unfold KHI; decide
              omega
            have Hargh : argH E (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) = false := by
              cases hg : argH E (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) with
              | false => rfl
              | true =>
                exfalso
                have hh := argH_high E _ hg
                rw [Ua] at hh
                have hk : KHI < CEIL := by unfold KHI CEIL; decide
                omega
            have Hal : in_allow A E csb (bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)))
                = true := by
              have h1 : AsanPlanSound.uE E cs.a_brk = bv_unsigned (m_vmmaps model).vm_brk :=
                congrArg bv_unsigned HC.co_brk.symm
              have h2 : AsanPlanSound.uE E (.ELit dv) = dv := hlen
              show (AsanPlanSound.in_vis E csb
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)))
                || AsanPlanSound.in_sh A E csb
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)))) = true
              rw [Bool.or_eq_true]
              left
              unfold AsanPlanSound.in_vis
              rw [HvisB, List.any_cons]
              dsimp only
              rw [Ua, h1, h2]
              have h3 : decide (bv_unsigned (m_vmmaps model).vm_brk
                  ≤ bv_unsigned (m_vmmaps model).vm_brk + i) = true := by
                rw [decide_eq_true_eq]; omega
              have h4 : decide (bv_unsigned (m_vmmaps model).vm_brk + i
                  < bv_unsigned (m_vmmaps model).vm_brk + dv) = true := by
                rw [decide_eq_true_eq]; omega
              rw [h3, h4, Bool.true_and, Bool.true_or]
            have Hvis : vis A E csb (brk2_model model dv)
                (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) = true := by
              unfold vis
              dsimp only
              rw [show (m_vmmaps (brk2_model model dv)).vm_maps
                  = ((m_vmmaps model).vm_brk, Z_to_bv 64 dv) :: (m_vmmaps model).vm_maps from rfl]
              rw [show m_vm_lazy (brk2_model model dv) = m_vm_lazy model from rfl]
              rw [show (m_vmmaps (brk2_model model dv)).vm_noaccess
                  = (m_vmmaps model).vm_noaccess from rfl]
              rw [in_ivs_cons]
              dsimp only
              have Hal' : in_allow A E csb (bv_unsigned (m_vmmaps model).vm_brk + i) = true := by
                rw [← Ua]; exact Hal
              rw [Ua, Un, Hal']
              have h3 : decide (bv_unsigned (m_vmmaps model).vm_brk
                  ≤ bv_unsigned (m_vmmaps model).vm_brk + i) = true := by
                rw [decide_eq_true_eq]; omega
              have h4 : decide (bv_unsigned (m_vmmaps model).vm_brk + i
                  < bv_unsigned (m_vmmaps model).vm_brk + dv) = true := by
                rw [decide_eq_true_eq]; omega
              rw [h3, h4, Bool.true_and]
              rw [NA (bv_unsigned (m_vmmaps model).vm_brk + i) (by omega) (by omega)]
              simp only [Bool.not_false, Bool.true_and, Bool.and_true, Bool.true_or, Bool.or_true]
            have hhid : hid A argH E csb (brk2_model model dv)
                (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) = false := by
              show (argH E (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i))
                || !(vis A E csb (brk2_model model dv)
                  (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)))) = false
              rw [Hargh, Hvis]
              rfl
            show mrestrict (fun a => hid A argH E csb (brk2_model model dv) a)
              (brk2_FULL FULL model dv) (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i))
              = some (Z_to_bv 8 0)
            unfold mrestrict
            show (if hid A argH E csb (brk2_model model dv)
                (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)) then none
              else brk2_FULL FULL model dv (Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk + i)))
              = some (Z_to_bv 8 0)
            rw [hhid]
            exact zfill_in _ _ _ _ ⟨by rw [Ua]; omega, by rw [Un, Ua]; omega⟩
          -- ## the two new knowledge entries
          intro K HK
          rcases List.mem_cons.mp HK with rfl | HK
          · -- KWr
            unfold kentry_ok
            refine ⟨Hfl, ?_⟩
            intro off m' Hoff Hm'
            cases m' with
            | zero => rfl
            | succ k =>
              rw [hlenZ] at Hm'
              have hu : ((BitVec.ofInt 64 (estart E (SA bb bk) + off)).toNat : Int)
                  = estart E (SA bb bk) + off := by
                refine u64_lit _ ⟨by omega, ?_⟩
                rw [Hest]
                have hk : KHI + 8192 < 2 ^ 64 := by unfold KHI; decide
                omega
              refine StoreOk.store_ok_of_all SEGS _ (k + 1)
                (BitVec.ofInt 64 (estart E (SA bb bk) + off)) ?_ ?_
              · rw [hu, Hest]
                have h3 : bv_unsigned (m_vmmaps model).vm_brk + off + ↑(k + 1) ≤ (2 : Int) ^ 64 := by
                  omega
                calc bv_unsigned (m_vmmaps model).vm_brk + off + ↑(k + 1) ≤ (2 : Int) ^ 64 := h3
                  _ = ((2 ^ 64 : Nat) : Int) := by decide
              · intro x Hx1 Hx2
                rw [hu, Hest] at Hx1 Hx2
                have hx : x = Z_to_bv 64 (bv_unsigned (m_vmmaps model).vm_brk
                    + ((x.toNat : Int) - bv_unsigned (m_vmmaps model).vm_brk)) := by
                  apply BitVec.eq_of_toNat_eq
                  have hb : ((BitVec.ofInt 64 (bv_unsigned (m_vmmaps model).vm_brk
                      + ((x.toNat : Int) - bv_unsigned (m_vmmaps model).vm_brk))).toNat : Int)
                      = bv_unsigned (m_vmmaps model).vm_brk
                        + ((x.toNat : Int) - bv_unsigned (m_vmmaps model).vm_brk) := by
                    refine u64_lit _ ⟨by omega, ?_⟩
                    have hk : KHI + 8192 < 2 ^ 64 := by unfold KHI; decide
                    omega
                  show x.toNat = (BitVec.ofInt 64 (bv_unsigned (m_vmmaps model).vm_brk
                      + ((x.toNat : Int) - bv_unsigned (m_vmmaps model).vm_brk))).toNat
                  omega
                rw [hx]
                unfold wview
                rw [INB ((x.toNat : Int) - bv_unsigned (m_vmmaps model).vm_brk)
                  (by omega) (by omega)]
                simp
          · rcases List.mem_cons.mp HK with rfl | HK
            · -- KZero
              unfold kentry_ok
              refine ⟨Hfl, ?_⟩
              intro i Hi0 Hid
              rw [hlenZ] at Hid
              rw [Hest]
              exact INB i Hi0 Hid
            · -- the filtered old knowledge, seen at the larger visibility
              have HK1 : know_ok SEGS E
                  (mrestrict (hid A argH E csb (brk2_model model dv))
                    (brk2_FULL FULL model dv)) (kn (brk2_mid A cs dv)) := by
                refine know_ok_unhide SEGS A E
                  (hid A argH E (brk2_mid A cs dv) (brk2_model model dv))
                  (hid A argH E csb (brk2_model model dv))
                  (brk2_FULL FULL model dv) (kn (brk2_mid A cs dv)) ?_ ?_ ?_ ?_ ?_
                · exact H_off_segments_cs SEGS A argH E (brk2_mid A cs dv) (brk2_model model dv)
                    HULL_ok SEGS_in_hull argH_high
                · show kimg_in_hull A (kn_grant_filter A (kn cs) cs.a_maps)
                  unfold kn_grant_filter
                  exact kimg_clip_in_hull A _
                · -- the visibility only grows: `csb`'s list is the mid state's plus the new range
                  intro z Hz
                  have hmono : ∀ w : Int, in_allow A E (brk2_mid A cs dv) w = true →
                      in_allow A E csb w = true := by
                    intro w hw
                    have hvis : (brk2_mid A cs dv).a_vis = cs.a_vis := rfl
                    unfold in_allow at hw ⊢
                    rw [Bool.or_eq_true] at hw ⊢
                    rcases hw with h | h
                    · left
                      unfold in_vis at h ⊢
                      rw [hvis] at h
                      rw [HvisB, hvis, List.any_cons, h, Bool.or_true]
                    · right
                      unfold in_sh at h ⊢
                      rw [hvis] at h
                      rw [HvisB, hvis, List.any_cons, h, Bool.or_true]
                  show (argH E z || !(vis A E (brk2_mid A cs dv) (brk2_model model dv) z)) = true
                  unfold hid at Hz
                  rw [Bool.or_eq_true] at Hz ⊢
                  rcases Hz with h | h
                  · exact Or.inl h
                  · cases hv : vis A E (brk2_mid A cs dv) (brk2_model model dv) z with
                    | false => exact Or.inr rfl
                    | true =>
                      exfalso
                      have h2 : vis A E csb (brk2_model model dv) z = true :=
                        vis_mono A E (brk2_mid A cs dv) csb (brk2_model model dv) z hmono hv
                      rw [h2] at h
                      exact absurd h (by decide)
                · intro a Ha
                  exact hid_hull A argH E (brk2_mid A cs dv) (brk2_model model dv) HULL_ok argH_high a Ha
                · exact HCB.co_know
              exact HK1 K HK
        -- ## the checker state at the granted grow
        have HCsb : cs_ok SEGS A LIMIT SINV argH FS0 E csb
            (brk2_R R model dv) (brk2_FULL FULL model dv) (brk2_model model dv) :=
          vis_add_sound SEGS A LIMIT SINV argH FS0 E (brk2_mid A cs dv) cs.a_brk (.ELit dv)
            (.KWr (SA bb bk) (.ELit dv) :: .KZero (SA bb bk) (.ELit dv) :: kn (brk2_mid A cs dv))
            csb (brk2_R R model dv) (brk2_FULL FULL model dv) (brk2_model model dv)
            SHADOW_ok argH_high hva HCB HKnow
        -- ## the granted child
        have Hgrant : srealizes SEGS
            (AsanAcct.mkCfg (mkst (brk2_R R model dv) (v_addi (Z_to_bv 64 (pc cs)) 4)
              (brk2_FULL FULL model dv) (seg_rom SEGS)) (brk2_model model dv)) TB := by
          have hp : pc csb = pc cs + 4 := HpcB
          rw [v_addi_pc (pc cs) Hpc0 Hpc4, ← hp]
          exact HkB E (brk2_R R model dv) (brk2_FULL FULL model dv) (brk2_model model dv)
            ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ HCsb rfl
        -- ## the syscall step
        show srealizes SEGS (AsanAcct.mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) model)
          (t_alt2 TA TB)
        exact AsanNodesLibE.srz_brk_grow_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w dv TA TB
          HF HE HC.co_halt G17 B1 D2 D1 B2 hbkd
          (Int.le_trans HC.co_sbrk (Int.le_add_of_nonneg_right (Int.le_of_lt D1)))
          G10 Hadm HA Hgrant
      · simp at Hn
    · simp at Hn
  · simp at Hn

/-!
  Word hygiene: this file contains no proof hole and no extra postulate.
-/



