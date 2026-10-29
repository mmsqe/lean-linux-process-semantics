/-
  * Common.AsanStartLoops — machine-level lemmas for musl's two start-up scan
    loops (image-independent: the code is given by fetch/decode hypotheses at a
    symbolic pc `x`).

  - `env_loop`: the envp NULL-scan loop of `__init_libc`
      `x: ld a0,0(s1) ; x+4: addi s1,s1,8 ; x+8: bne a0,zero,x ; x+12: exit`
  - `pn_loop`: the program-name scan over argv[0]
      `x-8: sd a1,0(a0) ; x-4: addi a1,a1,1 ; x: lbu a3,-1(a1) ;`
      `x+4: beq a3,a2,x-8 ; x+8: bne a3,zero,x-4 ; x+12: exit`

  Both are stated as MODEL-FREE `msteps` contracts: the loops are given by
  `fetch_word`/`decodeAny` hypotheses at a symbolic pc `x`, the machine states
  are `mkst regs pc mem rom`, and the conclusions are `msteps` chains plus a
  register/postcondition and (for `pn_loop`) an invariant on the overlay.
 The Lean `section`s below are only this tree's
    grouping device.
  * The two  `Ltac`s.  `rif` (reduce a closed `if bv_eqb <lit> <lit>`
    by `vm_compute`) has no Lean counterpart: this tree's step lemmas deliver
    the `if bv_eqb rd 0` already reduced at the literal register numbers
    (`show bv_eqb (10 : reg) 0 = false from by decide` followed by
    `Bool.false_eq_true, ite_false`).   * `u_lit` is `StepTac.u_Z2bv` (same statement, `Z_to_bv 64` unfolding to
    `BitVec.ofInt 64`).   * `Rk`'s `bv_unsigned (ptr k) <> 0` is stated as `(ptr k).toNat ≠ 0`, the
    spelling this tree's `c_eq_0_false` consumes.
  * glue: `c_eq_0_false_ofInt` (`PropExec.c_eq_0_false` at the
    `Z_to_bv 64 0` spelling `PropExec.getr_zero` produces, which is
    `BitVec.ofInt 64 0` rather than the `BitVec.ofNat` zero).  It states no
    fact of this file — only the `Bool` comparison the step lemmas need.
 `lake env
  lean LinuxSem/Common/AsanStartLoops.lean` is silent.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.Hoare
import LinuxSem.Common.SymExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.AgentLib
import LinuxSem.Common.AxSymExec3

namespace LinuxSem.Common.AsanStartLoops

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StoreOk
open LinuxSem.Common.Hoare (regs_agree)
open LinuxSem.Common.SymExec
open LinuxSem.Common.AxSymExec3 (Z_to_bv bv_unsigned bv_signed)

/-- `Local Instance asanreflect_fx : PropExec.FPState :=
    PropExec.fx0`. -/
local instance asanstartloops_fx : FPState := fx0

/-! -/
set_option linter.unusedVariables false

/-! =================================================================
    ## Small word arithmetic
    ================================================================= -/

/-- `bv_unsigned (Z_to_bv 64 z) = z` for an in-range `z`.
    (Same statement as `StepTac.u_Z2bv`.) -/
theorem u_lit (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z :=
  StepTac.u_Z2bv z Hz.1 Hz.2

/-- `v_addi` of a literal. -/
theorem v_addi_lit (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) :
    v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k) :=
  SymExec.v_addi_lit a k

/-- Branch target of a literal pc. -/
theorem btgt_lit (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) :
    btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k) :=
  SymExec.btgt_lit a k

/-- `c_eq` of two literal words is `Z.eqb` of the `Z`s (this tree's
    `decide (a = b)`). -/
theorem c_eq_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = decide (a = b) :=
  AgentLib.c_eq_lit a b Ha Hb

/-- Distinct small `Z`s are distinct 5-bit register indices. -/
theorem reg_neq (a b : Int) (Ha : 0 ≤ a ∧ a < 32) (Hb : 0 ≤ b ∧ b < 32) (Hne : a ≠ b) :
    (Z_to_bv 5 a : reg) ≠ Z_to_bv 5 b := by
  intro Heq
  have h := congrArg BitVec.toNat Heq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt] at h
  have h3 : a % ((2 ^ 5 : Nat) : Int) = b % ((2 ^ 5 : Nat) : Int) := by
    have h4 := congrArg (fun n : Nat => (n : Int)) h
    rwa [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))] at h4
  rw [Int.emod_eq_of_lt Ha.1 (by omega), Int.emod_eq_of_lt Hb.1 (by omega)] at h3
  exact Hne h3

/-! ## The two  `Ltac`s

    `rif` collapses `if bv_eqb <lit> <lit> then _ else _` by `vm_compute`;
    `pc_is v` respells the pc of the current `msteps` source state by `lia`.
    Neither is needed in this tree (see the header note): the step lemmas are
    applied at literal register numbers and every pc stays in the literal
    `Z_to_bv 64 (x + k)` form. -/

/-! ## The decoded immediates

    `bv_signed` of the six immediates the two loops decode
    (`PropExec.bv_signed` is `BitVec.toInt`). -/

theorem signed12_0 : bv_signed (0 : BitVec 12) = 0 := by decide
theorem signed12_1 : bv_signed (1 : BitVec 12) = 1 := by decide
theorem signed12_8 : bv_signed (8 : BitVec 12) = 8 := by decide
theorem signed12_m1 : bv_signed (4095 : BitVec 12) = -1 := by decide
theorem signed13_m8 : bv_signed (8184 : BitVec 13) = -8 := by decide
theorem signed13_m12 : bv_signed (8180 : BitVec 13) = -12 := by decide

/-! =================================================================
    ## The envp NULL-scan loop
    ================================================================= -/

section EnvLoop

/-- glue: `c_eq_0_false` at the `Z_to_bv 64 0` spelling that
    `getr_zero` produces (`BitVec.ofInt 64 0`, not the `BitVec.ofNat` zero). -/
theorem c_eq_0_false_ofInt (x : word) (Hnz : x.toNat ≠ 0) :
    c_eq x (Z_to_bv 64 0) = false := by
  have h0 : (Z_to_bv 64 0 : word) = 0 := by decide
  rw [h0]
  exact c_eq_0_false x Hnz

/-- The postcondition of the envp scan: `s1` points one word past the NULL
    terminator, `a0` holds the NULL, and no other register was touched. -/
def env_post (e : Int) (envc : Nat) (regs regs' : BvMap word) : Prop :=
  getr regs' 9 = Z_to_bv 64 (e + 8 * (envc : Int) + 8)
  ∧ getr regs' 10 = Z_to_bv 64 0
  ∧ regs_agree (fun r => r = 9 ∨ r = 10) regs regs'

/-- The envp NULL-scan loop: from `s1 = e + 8k` with `k + n = envc` entries
    left, `n` iterations run from `x` to the exit at `x+12`, reading the
    `envc` non-NULL entries and terminating on the NULL at `e + 8*envc`. -/
theorem env_loop (segs : List Segment) (x : Int) (w1 w2 w3 : BitVec 32)
    (Hx : 0 ≤ x ∧ x + 12 < 2 ^ 64)
    (F1 : fetch_word segs (Z_to_bv 64 x) = some w1)
    (F2 : fetch_word segs (Z_to_bv 64 (x + 4)) = some w2)
    (F3 : fetch_word segs (Z_to_bv 64 (x + 8)) = some w3)
    (E1 : is_ecall w1 = false) (E2 : is_ecall w2 = false) (E3 : is_ecall w3 = false)
    (D1 : decodeAny w1 = some (Instr.load .SZ8 true 10 9 0, 4))
    (D2 : decodeAny w2 = some (Instr.opImm .ADD 9 9 8, 4))
    (D3 : decodeAny w3 = some (Instr.branch .NE 10 0 8184, 4))
    (M rom : word → Option byte) (e : Int) (envc : Nat) (ptr : Nat → word)
    (He : 0 ≤ e ∧ e + 8 * (envc : Int) + 16 < 2 ^ 64)
    (Rk : ∀ k, k < envc →
      rdn segs M (Z_to_bv 64 (e + 8 * (k : Int))) 8 = some (word_to_le_bytes 8 (ptr k))
      ∧ (ptr k).toNat ≠ 0)
    (Rn : rdn segs M (Z_to_bv 64 (e + 8 * (envc : Int))) 8
      = some (word_to_le_bytes 8 (Z_to_bv 64 0))) :
    ∀ (n k : Nat) (regs : BvMap word), k + n = envc →
      getr regs 9 = Z_to_bv 64 (e + 8 * (k : Int)) →
      ∃ regs',
        msteps segs (mkst regs (Z_to_bv 64 x) M rom)
          (mkst regs' (Z_to_bv 64 (x + 12)) M rom)
        ∧ env_post e envc regs regs' := by
  intro n
  induction n with
  | zero =>
    intro k regs Hkn H9
    -- last iteration: reads the NULL
    have hk : k = envc := by omega
    subst k
    have hR : rdn segs M (v_addi (getr regs 9) ((0 : BitVec 12)).toInt) 8
        = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
      rw [show ((0 : BitVec 12)).toInt = (0 : Int) from by decide, H9,
        SymExec.v_addi_lit, Int.add_zero]
      exact Rn
    -- `ld a0,0(s1)`
    let r1 : BvMap word := regupd regs 10 (Z_to_bv 64 0)
    have h1 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 x) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 4)) M rom) := by
      rw [PropExec.step_ld segs regs (Z_to_bv 64 x) M rom w1 10 9 0
        (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) F1 E1 D1 hR
        (SeqExec.bytes_le_to_Z_8 (Z_to_bv 64 0))]
      simp only [show bv_eqb (10 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r1, SymExec.v_addi_lit]
    -- `addi s1,s1,8`
    let r2 : BvMap word := regupd r1 9 (Z_to_bv 64 (e + 8 * (envc : Int) + 8))
    have hv2 : v_addi (getr r1 9) ((8 : BitVec 12)).toInt
        = Z_to_bv 64 (e + 8 * (envc : Int) + 8) := by
      simp only [r1, show ((8 : BitVec 12)).toInt = (8 : Int) from by decide,
        getr_other _ _ _ _ (by decide : (9 : reg) ≠ 10), H9, SymExec.v_addi_lit]
    have h2 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 4)) M rom)
        = .MachineOk (mkst r2 (Z_to_bv 64 (x + 8)) M rom) := by
      rw [PropExec.step_addi segs r1 (Z_to_bv 64 (x + 4)) M rom w2 9 9 8 F2 E2 D2]
      simp only [show bv_eqb (9 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r2, hv2, SymExec.v_addi_lit, show x + 4 + 4 = x + 8 by omega]
    -- `bne a0,zero,x` falls through (a0 is the NULL just loaded)
    have hce : c_eq (getr r2 10) (getr r2 0) = true := by
      simp only [r2, r1, getr_same _ _ _ (by decide : (10 : reg) ≠ 0),
        getr_other _ _ _ _ (by decide : (10 : reg) ≠ 9), getr_zero]
      decide
    have h3 : RiscvSemantics.step segs (mkst r2 (Z_to_bv 64 (x + 8)) M rom)
        = .MachineOk (mkst r2 (Z_to_bv 64 (x + 12)) M rom) := by
      rw [PropExec.step_bne_ft segs r2 (Z_to_bv 64 (x + 8)) M rom w3 10 0 8184 F3 E3 D3 hce]
      simp only [SymExec.v_addi_lit, show x + 8 + 4 = x + 12 by omega]
    refine ⟨r2, ?_, ?_, ?_, ?_⟩
    · exact msteps.mst_step _ _ _ (by rfl) h1
        (msteps.mst_step _ _ _ (by rfl) h2
          (msteps.mst_step _ _ _ (by rfl) h3 (msteps.mst_refl _)))
    · -- `getr regs' 9`
      simp only [r2, r1, getr_same _ _ _ (by decide : (9 : reg) ≠ 0)]
    · -- `getr regs' 10`
      simp only [r2, r1, getr_same _ _ _ (by decide : (10 : reg) ≠ 0),
        getr_other _ _ _ _ (by decide : (10 : reg) ≠ 9)]
    · -- nothing else changed
      intro r hr
      simp only [r2, r1]
      rw [getr_other _ _ _ _ (by intro h; exact hr (Or.inl h)),
        getr_other _ _ _ _ (by intro h; exact hr (Or.inr h))]
  | succ n ih =>
    intro k regs Hkn H9
    have hk : k < envc := by omega
    obtain ⟨Rd, Hnz⟩ := Rk k hk
    -- the non-NULL entry at `e + 8k`
    have hR : rdn segs M (v_addi (getr regs 9) ((0 : BitVec 12)).toInt) 8
        = some (word_to_le_bytes 8 (ptr k)) := by
      rw [show ((0 : BitVec 12)).toInt = (0 : Int) from by decide, H9,
        SymExec.v_addi_lit, Int.add_zero]
      exact Rd
    -- `ld a0,0(s1)` — the entry
    let r1 : BvMap word := regupd regs 10 (ptr k)
    have h1 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 x) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 4)) M rom) := by
      rw [PropExec.step_ld segs regs (Z_to_bv 64 x) M rom w1 10 9 0
        (word_to_le_bytes 8 (ptr k)) (ptr k) F1 E1 D1 hR
        (SeqExec.bytes_le_to_Z_8 (ptr k))]
      simp only [show bv_eqb (10 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r1, SymExec.v_addi_lit]
    -- `addi s1,s1,8`
    let r2 : BvMap word := regupd r1 9 (Z_to_bv 64 (e + 8 * ((k + 1 : Nat) : Int)))
    have hv2 : v_addi (getr r1 9) ((8 : BitVec 12)).toInt
        = Z_to_bv 64 (e + 8 * ((k + 1 : Nat) : Int)) := by
      simp only [r1, show ((8 : BitVec 12)).toInt = (8 : Int) from by decide,
        getr_other _ _ _ _ (by decide : (9 : reg) ≠ 10), H9, SymExec.v_addi_lit,
        show e + 8 * (k : Int) + 8 = e + 8 * ((k + 1 : Nat) : Int) by omega]
    have h2 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 4)) M rom)
        = .MachineOk (mkst r2 (Z_to_bv 64 (x + 8)) M rom) := by
      rw [PropExec.step_addi segs r1 (Z_to_bv 64 (x + 4)) M rom w2 9 9 8 F2 E2 D2]
      simp only [show bv_eqb (9 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r2, hv2, SymExec.v_addi_lit, show x + 4 + 4 = x + 8 by omega]
    -- `bne a0,zero,x` is taken: the entry is non-NULL
    have hce : c_eq (getr r2 10) (getr r2 0) = false := by
      simp only [r2, r1, getr_same _ _ _ (by decide : (10 : reg) ≠ 0),
        getr_other _ _ _ _ (by decide : (10 : reg) ≠ 9), getr_zero]
      exact c_eq_0_false_ofInt (ptr k) Hnz
    have h3 : RiscvSemantics.step segs (mkst r2 (Z_to_bv 64 (x + 8)) M rom)
        = .MachineOk (mkst r2 (Z_to_bv 64 x) M rom) := by
      rw [PropExec.step_bne_tk segs r2 (Z_to_bv 64 (x + 8)) M rom w3 10 0 8184 F3 E3 D3 hce]
      simp only [show ((8184 : BitVec 13)).toInt = (-8 : Int) from by decide,
        SymExec.btgt_lit]
      rw [show x + 8 + -8 = x by omega]
    -- the remaining `n` iterations from `s1 = e + 8(k+1)`
    obtain ⟨regs', Hms, Hpost⟩ :=
      ih (k + 1) r2 (by omega) (by
        simp only [r2, r1, getr_same _ _ _ (by decide : (9 : reg) ≠ 0)])
    obtain ⟨P9, P10, Pag⟩ := Hpost
    refine ⟨regs', ?_, ?_, P10, ?_⟩
    · exact msteps.mst_step _ _ _ (by rfl) h1
        (msteps.mst_step _ _ _ (by rfl) h2
          (msteps.mst_step _ _ _ (by rfl) h3 Hms))
    · rw [P9]
    · intro r hr
      rw [Pag r hr]
      simp only [r2, r1]
      rw [getr_other _ _ _ _ (by intro h; exact hr (Or.inl h)),
        getr_other _ _ _ _ (by intro h; exact hr (Or.inr h))]

end EnvLoop

/-! =================================================================
    ## The program-name scan loop
    ================================================================= -/

section PnLoop

/-- Memories reachable from `M0` by stores into the cell `[p, p+8)`: every
    byte outside the cell is unchanged, and the overlay only grew. -/
def cellrel (M0 : word → Option byte) (p : Int) (M : word → Option byte) : Prop :=
  (∀ a : word, (a.toNat : Int) < p ∨ p + 8 ≤ (a.toNat : Int) → M a = M0 a)
  ∧ mem_grows M0 M

theorem cellrel_refl (M0 : word → Option byte) (p : Int) : cellrel M0 p M0 :=
  ⟨fun _ _ => rfl, mem_grows_refl M0⟩

/-- A store of the whole cell keeps the invariant. -/
theorem cellrel_wbytes (M0 : word → Option byte) (p : Int) (Hp : 0 ≤ p ∧ p + 8 ≤ 2 ^ 64)
    (M : word → Option byte) (v : word) (HM : cellrel M0 p M) :
    cellrel M0 p (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 v)) := by
  obtain ⟨H1, H2⟩ := HM
  have hp : ((Z_to_bv 64 p).toNat : Int) = p := u_lit p ⟨Hp.1, by omega⟩
  have hlen : (word_to_le_bytes 8 v).length = 8 := CatExec.length_Z_to_le_bytes 8 (v.toNat : Int)
  refine ⟨?_, mem_grows_trans H2 (wbytes_grows (word_to_le_bytes 8 v) M (Z_to_bv 64 p))⟩
  intro a Ha
  rw [← H1 a Ha]
  rcases Ha with Ha | Ha
  · exact wbytes_below (word_to_le_bytes 8 v) M (Z_to_bv 64 p) a
      (by rw [hlen, hp]; omega) (by rw [hp]; exact Ha)
  · exact wbytes_above (word_to_le_bytes 8 v) M (Z_to_bv 64 p) a
      (by rw [hlen, hp]; omega)

/-- Reads of the string are untouched by stores into the cell: the cell and
    the string are apart. -/
theorem cellrel_rd (segs : List Segment) (M0 : word → Option byte) (p pn : Int) (s : List byte)
    (Hpn : 0 ≤ pn ∧ pn + (s.length : Int) + 2 < 2 ^ 64)
    (Hapart : p + 8 ≤ pn ∨ pn + (s.length : Int) + 1 ≤ p)
    (Hrd : ∀ j, j ≤ s.length →
      rdn segs M0 (Z_to_bv 64 (pn + (j : Int))) 1 = some [byte_at s j])
    (M : word → Option byte) (j : Nat) (HM : cellrel M0 p M) (Hj : j ≤ s.length) :
    rdn segs M (Z_to_bv 64 (pn + (j : Int))) 1 = some [byte_at s j] := by
  rw [← Hrd j Hj]
  have ha : ((Z_to_bv 64 (pn + (j : Int))).toNat : Int) = pn + (j : Int) :=
    u_lit _ ⟨by omega, by omega⟩
  refine rdn_ext segs 1 M M0 (Z_to_bv 64 (pn + (j : Int))) ?_ ?_
  · rw [ha]; omega
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [ha] at hx1 hx2
    exact HM.1 x (by
      rcases Hapart with H | H
      · right; omega
      · left; omega)

/-- The store into the cell is still permitted after a growth of the
    overlay. -/
theorem cellrel_st (segs : List Segment) (M0 : word → Option byte) (p : Int)
    (Hst : store_ok segs M0 (Z_to_bv 64 p) 8 = true)
    (M : word → Option byte) (HM : cellrel M0 p M) :
    store_ok segs M (Z_to_bv 64 p) 8 = true := by
  obtain ⟨_, H2⟩ := HM
  exact store_ok_mono segs 8 M0 M (Z_to_bv 64 p) H2 Hst

/-- The postcondition of the program-name scan: `a1` is one past the last
    byte, `a3` is the NUL, and no other register was touched. -/
def pn_post (pn : Int) (s : List byte) (regs regs' : BvMap word) : Prop :=
  getr regs' 11 = Z_to_bv 64 (pn + (s.length : Int) + 1)
  ∧ getr regs' 13 = Z_to_bv 64 0
  ∧ regs_agree (fun r => r = 11 ∨ r = 13) regs regs'

/-- A byte's unsigned value is in `[0, 256)`. -/
theorem byte_u (b : byte) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < 256 :=
  u8_range b

/-- The program-name scan loop: scanning the bytes `s` of the program name at
    `pn`, recording the position after each `/` into the cell at `p`.  `l2` is
    the unscanned suffix of `s`, `j` how many bytes have been scanned. -/
theorem pn_loop (segs : List Segment) (x : Int) (w0 w1 w2 w3 w4 : BitVec 32)
    (Hx : 8 ≤ x ∧ x + 12 < 2 ^ 64)
    (F0 : fetch_word segs (Z_to_bv 64 (x - 8)) = some w0)
    (F1 : fetch_word segs (Z_to_bv 64 (x - 4)) = some w1)
    (F2 : fetch_word segs (Z_to_bv 64 x) = some w2)
    (F3 : fetch_word segs (Z_to_bv 64 (x + 4)) = some w3)
    (F4 : fetch_word segs (Z_to_bv 64 (x + 8)) = some w4)
    (E0 : is_ecall w0 = false) (E1 : is_ecall w1 = false) (E2 : is_ecall w2 = false)
    (E3 : is_ecall w3 = false) (E4 : is_ecall w4 = false)
    (D0 : decodeAny w0 = some (Instr.store .SZ8 10 11 0, 4))
    (D1 : decodeAny w1 = some (Instr.opImm .ADD 11 11 1, 4))
    (D2 : decodeAny w2 = some (Instr.load .SZ1 false 13 11 4095, 4))
    (D3 : decodeAny w3 = some (Instr.branch .EQ 13 12 8180, 4))
    (D4 : decodeAny w4 = some (Instr.branch .NE 13 0 8180, 4))
    (M0 rom : word → Option byte) (p pn : Int) (s : List byte)
    (Hp : 0 ≤ p ∧ p + 8 ≤ 2 ^ 64)
    (Hpn : 0 ≤ pn ∧ pn + (s.length : Int) + 2 < 2 ^ 64)
    (Hapart : p + 8 ≤ pn ∨ pn + (s.length : Int) + 1 ≤ p)
    (Hnz : Z_to_bv 8 0 ∉ s)
    (Hrd : ∀ j, j ≤ s.length →
      rdn segs M0 (Z_to_bv 64 (pn + (j : Int))) 1 = some [byte_at s j])
    (Hst : store_ok segs M0 (Z_to_bv 64 p) 8 = true) :
    ∀ (l2 : List byte) (j : Nat) (regs : BvMap word) (M : word → Option byte),
      List.drop j s = l2 → j ≤ s.length →
      getr regs 10 = Z_to_bv 64 p →
      getr regs 11 = Z_to_bv 64 (pn + (j : Int) + 1) →
      getr regs 12 = Z_to_bv 64 47 →
      cellrel M0 p M →
      ∃ regs' M',
        msteps segs (mkst regs (Z_to_bv 64 x) M rom)
          (mkst regs' (Z_to_bv 64 (x + 12)) M' rom)
        ∧ pn_post pn s regs regs' ∧ cellrel M0 p M' := by
  intro l2
  induction l2 with
  | nil =>
    intro j regs M Hskip Hj H10 H11 H12 HM
    -- end of string: the NUL
    have hjl : j = s.length := by
      have h := congrArg List.length Hskip
      rw [List.length_drop] at h
      simp only [List.length_nil] at h
      omega
    subst j
    have hzero : ((Z_to_bv 8 0).toNat : Int) = 0 := by decide
    -- the read of the NUL byte one position back
    have hR : rdn segs M (v_addi (getr regs 11) ((4095 : BitVec 12)).toInt) 1
        = some [byte_at s s.length] := by
      rw [show ((4095 : BitVec 12)).toInt = (-1 : Int) from by decide, H11,
        SymExec.v_addi_lit, show pn + (s.length : Int) + 1 + -1 = pn + (s.length : Int) by omega]
      exact cellrel_rd segs M0 p pn s Hpn Hapart Hrd M s.length HM Hj
    -- `lbu a3,-1(a1)`
    let r1 : BvMap word := regupd regs 13 (Z_to_bv 64 0)
    have h1 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 x) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 4)) M rom) := by
      rw [PropExec.step_lbu segs regs (Z_to_bv 64 x) M rom w2 13 11 4095
        (byte_at s s.length) F2 E2 D2 hR]
      simp only [show bv_eqb (13 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r1, byte_at_len, hzero, SymExec.v_addi_lit]
    -- `beq a3,a2,x-8` falls through (`a3` is 0, not 47)
    have hce : c_eq (getr r1 13) (getr r1 12) = false := by
      simp only [r1, getr_same _ _ _ (by decide : (13 : reg) ≠ 0),
        getr_other _ _ _ _ (by decide : (12 : reg) ≠ 13), H12]
      rw [c_eq_lit 0 47 (by omega) (by omega)]
      decide
    have h2 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 4)) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 8)) M rom) := by
      rw [PropExec.step_beq_ft segs r1 (Z_to_bv 64 (x + 4)) M rom w3 13 12 8180 F3 E3 D3 hce]
      simp only [SymExec.v_addi_lit, show x + 4 + 4 = x + 8 by omega]
    -- `bne a3,zero,x-4` falls through (`a3` is 0)
    have hce2 : c_eq (getr r1 13) (getr r1 0) = true := by
      simp only [r1, getr_same _ _ _ (by decide : (13 : reg) ≠ 0),
        getr_other _ _ _ _ (by decide : (0 : reg) ≠ 13), getr_zero]
      decide
    have h3 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 8)) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 12)) M rom) := by
      rw [PropExec.step_bne_ft segs r1 (Z_to_bv 64 (x + 8)) M rom w4 13 0 8180 F4 E4 D4 hce2]
      simp only [SymExec.v_addi_lit, show x + 8 + 4 = x + 12 by omega]
    refine ⟨r1, M, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact msteps.mst_step _ _ _ (by rfl) h1
        (msteps.mst_step _ _ _ (by rfl) h2
          (msteps.mst_step _ _ _ (by rfl) h3 (msteps.mst_refl _)))
    · simp only [r1, getr_other _ _ _ _ (by decide : (11 : reg) ≠ 13)]
      exact H11
    · simp only [r1, getr_same _ _ _ (by decide : (13 : reg) ≠ 0)]
    · intro r hr
      simp only [r1]
      rw [getr_other _ _ _ _ (by intro h; exact hr (Or.inr h))]
    · exact HM
  | cons b l2 ih =>
    intro j regs M Hskip Hj H10 H11 H12 HM
    -- the current byte, and the suffix
    have Hjlt : j < s.length := by
      have h := congrArg List.length Hskip
      rw [List.length_drop] at h
      simp only [List.length_cons] at h
      omega
    have hdrop := List.drop_eq_getElem_cons (l := s) Hjlt
    have hcons : s[j] :: List.drop (j + 1) s = b :: l2 := by rw [← hdrop, Hskip]
    have Hb : byte_at s j = b := by
      rw [nth_lt_byte_at s j Hjlt]
      exact (List.cons.inj hcons).1
    have Hskip' : List.drop (j + 1) s = l2 := (List.cons.inj hcons).2
    have Hbu := u8_range b
    have Hbnz : (b.toNat : Int) ≠ 0 := by
      have hb0 : b ≠ Z_to_bv 8 0 := by
        rw [← Hb]
        exact byte_at_nz s j Hnz Hjlt
      exact StepTac.byte_nz_u b hb0
    -- the read of byte `j` one position back
    have hR : rdn segs M (v_addi (getr regs 11) ((4095 : BitVec 12)).toInt) 1 = some [b] := by
      rw [show ((4095 : BitVec 12)).toInt = (-1 : Int) from by decide, H11,
        SymExec.v_addi_lit, show pn + (j : Int) + 1 + -1 = pn + (j : Int) by omega, ← Hb]
      exact cellrel_rd segs M0 p pn s Hpn Hapart Hrd M j HM Hj
    -- `lbu a3,-1(a1)`
    let r1 : BvMap word := regupd regs 13 (Z_to_bv 64 (b.toNat : Int))
    have h1 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 x) M rom)
        = .MachineOk (mkst r1 (Z_to_bv 64 (x + 4)) M rom) := by
      rw [PropExec.step_lbu segs regs (Z_to_bv 64 x) M rom w2 13 11 4095 b F2 E2 D2 hR]
      simp only [show bv_eqb (13 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
        r1, SymExec.v_addi_lit]
    have G13 : getr r1 13 = Z_to_bv 64 (b.toNat : Int) := by
      simp only [r1, getr_same _ _ _ (by decide : (13 : reg) ≠ 0)]
    have G10 : getr r1 10 = Z_to_bv 64 p := by
      simp only [r1, getr_other _ _ _ _ (by decide : (10 : reg) ≠ 13)]
      exact H10
    have G11 : getr r1 11 = Z_to_bv 64 (pn + (j : Int) + 1) := by
      simp only [r1, getr_other _ _ _ _ (by decide : (11 : reg) ≠ 13)]
      exact H11
    have G12 : getr r1 12 = Z_to_bv 64 47 := by
      simp only [r1, getr_other _ _ _ _ (by decide : (12 : reg) ≠ 13)]
      exact H12
    -- the `beq a3,a2,x-8` test, as a `decide` (=  `Z.eqb`)
    have hceq : c_eq (getr r1 13) (getr r1 12) = decide ((b.toNat : Int) = 47) := by
      rw [G13, G12]
      exact c_eq_lit (b.toNat : Int) 47 ⟨by omega, by omega⟩ (by omega)
    -- the register file the next iteration starts from (branch-independent)
    let r2 : BvMap word := regupd r1 11 (Z_to_bv 64 (pn + ((j + 1 : Nat) : Int) + 1))
    have I10 : getr r2 10 = Z_to_bv 64 p := by
      simp only [r2, getr_other _ _ _ _ (by decide : (10 : reg) ≠ 11)]
      exact G10
    have I11 : getr r2 11 = Z_to_bv 64 (pn + ((j + 1 : Nat) : Int) + 1) := by
      simp only [r2, getr_same _ _ _ (by decide : (11 : reg) ≠ 0)]
    have I12 : getr r2 12 = Z_to_bv 64 47 := by
      simp only [r2, getr_other _ _ _ _ (by decide : (12 : reg) ≠ 11)]
      exact G12
    have hv4 : v_addi (getr r1 11) ((1 : BitVec 12)).toInt
        = Z_to_bv 64 (pn + ((j + 1 : Nat) : Int) + 1) := by
      rw [show ((1 : BitVec 12)).toInt = (1 : Int) from by decide, G11,
        SymExec.v_addi_lit, show pn + (j : Int) + 1 + 1 = pn + ((j + 1 : Nat) : Int) + 1 by omega]
    by_cases hb47 : (b.toNat : Int) = 47
    · -- a '/': record the position after it
      let M1 : word → Option byte :=
        wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + (j : Int) + 1)))
      have HM1 : cellrel M0 p M1 := by
        simp only [M1]
        exact cellrel_wbytes M0 p Hp M _ HM
      have hce : c_eq (getr r1 13) (getr r1 12) = true := by
        rw [hceq, decide_eq_true hb47]
      -- `beq a3,a2,x-8` is taken
      have h2 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 4)) M rom)
          = .MachineOk (mkst r1 (Z_to_bv 64 (x - 8)) M rom) := by
        rw [PropExec.step_beq_tk segs r1 (Z_to_bv 64 (x + 4)) M rom w3 13 12 8180 F3 E3 D3 hce]
        simp only [show ((8180 : BitVec 13)).toInt = (-12 : Int) from by decide,
          SymExec.btgt_lit]
        rw [show x + 4 + -12 = x - 8 by omega]
      -- `sd a1,0(a0)`: write the position of the `/` into the cell
      have Ha : v_addi (getr r1 10) ((0 : BitVec 12)).toInt = Z_to_bv 64 p := by
        rw [show ((0 : BitVec 12)).toInt = (0 : Int) from by decide, G10,
          SymExec.v_addi_lit, Int.add_zero]
      have hst : store_ok segs M (Z_to_bv 64 p) 8 = true := cellrel_st segs M0 p Hst M HM
      have h3 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x - 8)) M rom)
          = .MachineOk (mkst r1 (Z_to_bv 64 (x - 4)) M1 rom) := by
        rw [SeqExec.step_sd_at segs r1 (Z_to_bv 64 (x - 8)) M rom w0 10 11 0
          (Z_to_bv 64 p) (Z_to_bv 64 (pn + (j : Int) + 1)) F0 E0 D0 Ha G11 hst]
        simp only [M1, SymExec.v_addi_lit, show x - 8 + 4 = x - 4 by omega]
      -- `addi a1,a1,1`
      have h4 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x - 4)) M1 rom)
          = .MachineOk (mkst r2 (Z_to_bv 64 x) M1 rom) := by
        rw [PropExec.step_addi segs r1 (Z_to_bv 64 (x - 4)) M1 rom w1 11 11 1 F1 E1 D1]
        simp only [show bv_eqb (11 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
          r2, hv4, SymExec.v_addi_lit, show x - 4 + 4 = x by omega]
      obtain ⟨regs', M', Hms, Hpost, HM'⟩ :=
        ih (j + 1) r2 M1 Hskip' (by omega) I10 I11 I12 HM1
      obtain ⟨P11, P13, Pag⟩ := Hpost
      refine ⟨regs', M', ?_, ⟨P11, P13, ?_⟩, HM'⟩
      · exact msteps.mst_step _ _ _ (by rfl) h1
          (msteps.mst_step _ _ _ (by rfl) h2
            (msteps.mst_step _ _ _ (by rfl) h3
              (msteps.mst_step _ _ _ (by rfl) h4 Hms)))
      · intro r hr
        rw [Pag r hr]
        simp only [r2, r1]
        rw [getr_other _ _ _ _ (by intro h; exact hr (Or.inl h)),
          getr_other _ _ _ _ (by intro h; exact hr (Or.inr h))]
    · -- not a '/', not NUL: next byte
      have hce : c_eq (getr r1 13) (getr r1 12) = false := by
        rw [hceq, decide_eq_false hb47]
      -- `beq a3,a2,x-8` falls through
      have h2 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 4)) M rom)
          = .MachineOk (mkst r1 (Z_to_bv 64 (x + 8)) M rom) := by
        rw [PropExec.step_beq_ft segs r1 (Z_to_bv 64 (x + 4)) M rom w3 13 12 8180 F3 E3 D3 hce]
        simp only [SymExec.v_addi_lit, show x + 4 + 4 = x + 8 by omega]
      -- `bne a3,zero,x-4` is taken: the byte is not the NUL
      have hcne : c_eq (getr r1 13) (getr r1 0) = false := by
        have hb0 : (Z_to_bv 64 (b.toNat : Int)).toNat ≠ 0 := by
          have h1 : ((Z_to_bv 64 (b.toNat : Int)).toNat : Int) = (b.toNat : Int) :=
            StepTac.u_Z2bv _ (by omega) (by omega)
          intro h0
          exact Hbnz (by rw [← h1, h0]; rfl)
        rw [G13]
        simp only [r1, getr_other _ _ _ _ (by decide : (0 : reg) ≠ 13), getr_zero]
        exact c_eq_0_false_ofInt _ hb0
      have h3 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x + 8)) M rom)
          = .MachineOk (mkst r1 (Z_to_bv 64 (x - 4)) M rom) := by
        rw [PropExec.step_bne_tk segs r1 (Z_to_bv 64 (x + 8)) M rom w4 13 0 8180 F4 E4 D4 hcne]
        simp only [show ((8180 : BitVec 13)).toInt = (-12 : Int) from by decide,
          SymExec.btgt_lit]
        rw [show x + 8 + -12 = x - 4 by omega]
      -- `addi a1,a1,1`
      have h4 : RiscvSemantics.step segs (mkst r1 (Z_to_bv 64 (x - 4)) M rom)
          = .MachineOk (mkst r2 (Z_to_bv 64 x) M rom) := by
        rw [PropExec.step_addi segs r1 (Z_to_bv 64 (x - 4)) M rom w1 11 11 1 F1 E1 D1]
        simp only [show bv_eqb (11 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
          r2, hv4, SymExec.v_addi_lit, show x - 4 + 4 = x by omega]
      obtain ⟨regs', M', Hms, Hpost, HM'⟩ :=
        ih (j + 1) r2 M Hskip' (by omega) I10 I11 I12 HM
      obtain ⟨P11, P13, Pag⟩ := Hpost
      refine ⟨regs', M', ?_, ⟨P11, P13, ?_⟩, HM'⟩
      · exact msteps.mst_step _ _ _ (by rfl) h1
          (msteps.mst_step _ _ _ (by rfl) h2
            (msteps.mst_step _ _ _ (by rfl) h3
              (msteps.mst_step _ _ _ (by rfl) h4 Hms)))
      · intro r hr
        rw [Pag r hr]
        simp only [r2, r1]
        rw [getr_other _ _ _ _ (by intro h; exact hr (Or.inl h)),
          getr_other _ _ _ _ (by intro h; exact hr (Or.inr h))]

end PnLoop

end LinuxSem.Common.AsanStartLoops
