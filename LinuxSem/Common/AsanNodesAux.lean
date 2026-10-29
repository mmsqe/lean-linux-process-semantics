/-

  * AsanNodesAux — small generic lemmas/tactics the node-soundness files use.
  the same name.  `lake env lean
  LinuxSem/Common/AsanNodesAux.lean` is silent.
  WHAT THE FILE IS FOR.  Its content splits in two:
  - a checker-vocabulary layer (`§1`): literal word arithmetic
    (`u_lit`…`reg_neq`), the two decoded immediates (`signed12_0/1`), the
    `len_eqb` / `kwritable` / `kimg_cut` soundness lemmas — the three ways a
    node turns a checker-side test on the KNOWLEDGE into a fact about the
    memory (`edenot` equality, `store_ok` + bounds, and monotonicity of the
    `KImg` cut) — the register file's two-register post-state
    (`reg_lit5`, `regs_ok_post2`), `edenot_ev_agree` (`nb_lt`-bounded
    expressions read the same in any two valuations agreeing below the
    bound), `fetch_lit` (a code fact transported to the literal pc
    spelling), and `with_ss`'s two definitional identities;
  - the `Section NodesD` layer (`§2`): the restriction `Hv = negb ∘ vis`,
    its `hid`/`hull`/ceiling facts, the two `lazy_cover` restatements
    (`lazy_cover_vis` for `Hv`, `lazy_cover_hid` for `hid`),
    `H_off_segments_vis`, and the two `mrestrict`/`Mr` frame lemmas.
           Variable A : atable.
      Variable nx0 : nat.                      Variable LIMIT : Z.
      Variable SINV : env -> (word -> option byte) -> Prop.
      Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
      Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
      Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
      Hypothesis HULL_ok : hull_ok A.
      Hypothesis argH_high : ...   Hypothesis argH_agree : ...
      Hypothesis SINV_frame : ...  Hypothesis SINV_agree : ...
  Lean inserts section variables only at DECLARATION sites, so — as in
  `AsanPlanSound` — the block is threaded EXPLICITLY, and only the part a
  declaration actually uses (`AsanPlanSound`'s rule): `lazy_cover_vis` /
  `lazy_cover_hid` take `segs A LIMIT SINV argH FS0` plus `HULL_ok` and the
  `cs_ok` state (`E cs R FULL model`); `H_off_segments_vis` takes `segs A`
  and `SEGS_in_hull`; `argH_high`, `argH_agree`, `SINV_frame`,
  `SINV_agree` and `SEGS_wx` are used by no lemma in this file, so they are
  not parameters anywhere.
  NOTES.
  - `Z` is `Int`, `nat` is `Nat`, `word` is `BitVec 64`, `byte` is
    `BitVec 8`, `bv n` is `BitVec n`, `reg` is `BitVec 5`, `Z_to_bv n z` is
    `BitVec.ofInt n z`, `bv_unsigned w` is `(w.toNat : Int)`,
    `Z.to_nat n` is `n.toNat`, `Z.of_nat n` is `(n : Int)`.
  - `List.Forall P l` does not exist in this core: every occurrence is
    `∀ x ∈ l, P x` (so `kwritable_sound`/`kimg_cut_sound` induct over the
    knowledge list instead of over a `Forall`), and `know_ok` is that form.
    Consequently `kentry_ok` conjoins as `a ∧ b ∧ c` and the projections are
    anonymous-constructor patterns.
 `u_lit` is `StepTac.u_Z2bv`.
  - DEFERRED (with reasons): the two `Ltac`s `rif` and `pc_is`.  Both are 
    `Ltac`s, i.e. proof-script helpers that no statement mentions: `rif`
    collapses `if bv_eqb <lit> <lit>` by `vm_compute`, which in Lean is
    `decide`/`simp` on closed `BitVec`s, and `pc_is v` respells the pc of the
    current `msteps` source state, which in Lean is `omega` on the
    `Z_to_bv 64 (x + k)` spelling.  Nothing in this tree needs either (the
    same situation `AsanStartLoops` records for its two `Ltac`s), and a Lean
    file cannot call them.
`vis w = true`, and the visible set's
    three disjuncts are discharged against the lazy interval, the hull and
    the allowed set — the last by `AsanPlanSound.in_allow_page`).
  - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.AgentLib
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StepTac
import LinuxSem.Common.AsanAcctShape
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanNodesAux

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.BackingAlgebra
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.StoreOk

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asannodesaux_fx : PropExec.FPState := PropExec.fx0

/-! ### Small word arithmetic -/

/-- `bv_unsigned (Z_to_bv 64 z) = z` for an in-range `z`. -/
theorem u_lit (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z :=
  StepTac.u_Z2bv z Hz.1 Hz.2

/-- `v_addi` of a literal. -/
theorem v_addi_lit (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) :
    v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k) :=
  SymExec.v_addi_lit a k

/-- Branch target of a literal. -/
theorem btgt_lit (a k : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) :
    btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k) :=
  SymExec.btgt_lit a k

/-- `c_eq` of two literal words. -/
theorem c_eq_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = decide (a = b) :=
  AgentLib.c_eq_lit a b Ha Hb

/-! ### The two  `Ltac`s

    `rif` collapses `if bv_eqb <lit> <lit> then _ else _` by `vm_compute`;
    `pc_is v` respells the pc of the current `msteps` source state by `lia`.
    Neither is a declaration: they are proof-script helpers that no statement
    mentions, and in Lean the same steps are `decide`/`simp` (the checker's
    `bv_eqb` on closed literals reduces definitionally) and `congr 1`/`omega`
    on the pc's `Z_to_bv` spelling.  They are therefore not restated here.
-/

/-- The decoded immediate `0`. -/
theorem signed12_0 : bv_signed (0 : BitVec 12) = 0 := by decide

/-- The decoded immediate `1`. -/
theorem signed12_1 : bv_signed (1 : BitVec 12) = 1 := by decide

/-! ## 1. Generic lemmas about the checker vocabulary -/

/-! ### `len_eqb`, `kwritable`, `kimg_cut` -/

/-- `len_eqb`: provable equality of two expressions. -/
theorem len_eqb_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (n m : expr) (HK : know_ok segs E M k)
    (H : len_eqb k n m = true) : edenot E n = edenot E m := by
  unfold len_eqb at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · rw [expr_eqb_eq n m H]
  · rw [Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    have A1 := lin_ge0_sound segs E M k _ _ HK H1
    have A2 := lin_ge0_sound segs E M k _ _ HK H2
    simp only [xt_den] at A1 A2
    apply BitVec.eq_of_toNat_eq
    simp only [bv_unsigned] at A1 A2 ⊢
    omega

/-- `kwritable` (literal length). -/
theorem kwritable_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn k : List kentry) (b : expr) (off n : Int) :
    know_ok segs E M allkn →
    know_ok segs E M k → kwritable allkn k b off n = true → 0 ≤ n →
    store_ok segs M (Z_to_bv 64 (estart E (SA b off))) n.toNat = true ∧
      0 ≤ estart E (SA b off) ∧ estart E (SA b off) + n ≤ 2 ^ 64 := by
  intro Hall HK H Hn
  induction k with
  | nil => simp [kwritable] at H
  | cons K rest ih =>
    have HKK : kentry_ok segs E M K := HK K List.mem_cons_self
    have Hrest : know_ok segs E M rest := fun x hx => HK x (List.mem_cons_of_mem _ hx)
    have HIH := ih Hrest
    cases K with
    | KWr a wn =>
      obtain ⟨wb, wk⟩ := a
      simp only [kentry_ok] at HKK
      obtain ⟨Hfl, Hs⟩ := HKK
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      simp only [estart, SA] at F1 F2 F4 Hs ⊢
      -- the entry's own extent is writable, so any sub-range of it is
      have CORE : bv_unsigned (edenot E wb) + wk ≤ bv_unsigned (edenot E b) + off →
          bv_unsigned (edenot E b) + off + n ≤ bv_unsigned (edenot E wb) + wk + elenZ E wn →
          store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) n.toNat = true ∧
            0 ≤ bv_unsigned (edenot E b) + off ∧
            bv_unsigned (edenot E b) + off + n ≤ 2 ^ 64 := by
        intro A B
        have hd : 0 ≤ bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk) := by
          omega
        have hn' : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg Hn
        have hm : bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk) +
            (n.toNat : Int) ≤ elenZ E wn := by omega
        have hst := Hs _ _ hd hm
        refine ⟨?_, by omega, by omega⟩
        rw [show bv_unsigned (edenot E b) + off = bv_unsigned (edenot E wb) + wk +
            (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk)) from by omega]
        exact hst
      -- the second checker test: the range lies inside the entry by `xinside`
      have SEC : ((0 ≤ n ∧ n < two64) ∧
          xinside allkn b off (expr.ELit n) wb wk wn = true) →
          store_ok segs M (Z_to_bv 64 (estart E (SA b off))) n.toNat = true ∧
            0 ≤ estart E (SA b off) ∧ estart E (SA b off) + n ≤ 2 ^ 64 := by
        rintro ⟨⟨Hn0, Hn1⟩, Hxi⟩
        obtain ⟨I1, I2⟩ :=
          xinside_sound segs E M allkn b off (expr.ELit n) wb wk wn Hall Hxi
        have hel : elenZ E (expr.ELit n) = n := by
          rw [elenZ, edenot_lit]
          exact u64_lit n ⟨Hn0, Hn1⟩
        rw [hel] at I2
        simp only [estart, SA] at I1 I2 ⊢
        exact CORE (by omega) (by omega)
      simp only [kwritable] at H
      split at H
      · -- the range is inside the `KWr` entry's own window
        rename_i hc
        rw [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨H0, H1⟩ := hc
        have H0' : b = wb := expr_eqb_eq b wb H0
        subst wb
        cases hx : xlo allkn wn with
        | none =>
          rw [hx] at H
          simp at H
          rcases H with hc2 | hk
          · exact SEC hc2
          · exact HIH hk
        | some wl =>
          rw [hx] at H
          by_cases hle : off + n ≤ wk + wl
          · rw [ite_eq_left (by simp [hle])] at H
            have Hwl := xlo_sound segs E M allkn wn wl Hall hx
            refine CORE (by omega) ?_
            simp only [elenZ] at Hwl ⊢
            omega
          · rw [ite_eq_right (by simp [hle])] at H
            split at H
            · rename_i hc2
              rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
                decide_eq_true_eq] at hc2
              exact SEC hc2
            · rename_i hc2; exact HIH H
      · -- the first test failed: fall through to `xinside`
        simp at H
        rcases H with hc2 | hk
        · exact SEC hc2
        · exact HIH hk
    | KWord a w v => exact HIH H
    | KZero a n' => exact HIH H
    | KBlob a n' k' => exact HIH H
    | KImg lo hi => exact HIH H
    | KAlign e m => exact HIH H
    | KRange e lo hi => exact HIH H
    | KDisj a1 n1 a2 n2 => exact HIH H
    | KFill a n' c => exact HIH H
    | KUnk a n' => exact HIH H

/-! ### Registers after a routine that set two registers -/

/-- A register index below 32, as a literal. -/
theorem reg_lit5 (n : Nat) (Hn : n < 32) :
    bv_unsigned (Z_to_bv 5 (n : Int)) = (n : Int) := by
  show (BitVec.ofInt 5 (n : Int)).toNat = (n : Int)
  rw [BitVec.toNat_ofInt, show ((2 ^ 5 : Nat) : Int) = 32 from by decide,
    Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega), Int.toNat_natCast]

/-- Registers after a routine that set two registers and kept the rest. -/
theorem regs_ok_post2 (E : env) (sr : List expr) (R R' : BvMap word)
    (n1 : Nat) (r1 : reg) (e1 : expr) (n2 : Nat) (r2 : reg) (e2 : expr)
    (HR : regs_ok E sr R) (Hn1 : 0 < n1 ∧ n1 < 32) (Hn2 : 0 < n2 ∧ n2 < 32)
    (Hne : n1 ≠ n2) (U1 : bv_unsigned r1 = (n1 : Int)) (U2 : bv_unsigned r2 = (n2 : Int))
    (G1 : getr R' r1 = edenot E e1) (G2 : getr R' r2 = edenot E e2)
    (Gr : ∀ r, r ≠ r1 → r ≠ r2 → getr R' r = getr R r) :
    regs_ok E (sr_upd (sr_upd sr n1 e1) n2 e2) R' := by
  have E1 : r1 = Z_to_bv 5 (n1 : Int) := by
    apply BitVec.toNat_inj.mp
    show BitVec.toNat r1 = (BitVec.ofInt 5 (n1 : Int)).toNat
    rw [BitVec.toNat_ofInt, show ((2 ^ 5 : Nat) : Int) = 32 from by decide,
      Int.emod_eq_of_lt (Int.natCast_nonneg n1) (by omega), Int.toNat_natCast]
    simp only [bv_unsigned] at U1
    omega
  have E2 : r2 = Z_to_bv 5 (n2 : Int) := by
    apply BitVec.toNat_inj.mp
    show BitVec.toNat r2 = (BitVec.ofInt 5 (n2 : Int)).toNat
    rw [BitVec.toNat_ofInt, show ((2 ^ 5 : Nat) : Int) = 32 from by decide,
      Int.emod_eq_of_lt (Int.natCast_nonneg n2) (by omega), Int.toNat_natCast]
    simp only [bv_unsigned] at U2
    omega
  have Z1 : r1 ≠ 0 := by
    intro h
    rw [h] at U1
    have h0 : bv_unsigned (0 : reg) = 0 := rfl
    rw [h0] at U1
    omega
  have Z2 : r2 ≠ 0 := by
    intro h
    rw [h] at U2
    have h0 : bv_unsigned (0 : reg) = 0 := rfl
    rw [h0] at U2
    omega
  have K := regs_ok_set_n E (sr_upd sr n1 e1)
    (regupd R (Z_to_bv 5 (n1 : Int)) (edenot E e1)) n2 e2 (edenot E e2)
    (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 rfl) Hn2 rfl
  rw [← E1, ← E2] at K
  intro r
  rw [← K r]
  by_cases h2 : r = r2
  · subst h2
    rw [getr_same _ _ _ Z2]
    exact G2
  · rw [getr_other _ r2 _ r h2]
    by_cases h1 : r = r1
    · subst h1
      rw [getr_same _ _ _ Z1]
      exact G1
    · rw [getr_other _ r1 _ r h1]
      exact Gr r h1 h2

/-! ### `nb_lt`, `edenot_ev_agree` -/

/-- `edenot` of a blob-free expression only reads `ev` below a bound. -/
def nb_lt (b : Nat) : expr → Bool
  | .ELit _ => true
  | .EVar n => n < b
  | .EAlu _ a c => nb_lt b a && nb_lt b c
  | .EAluw _ a c => nb_lt b a && nb_lt b c
  | .EMd _ a c => nb_lt b a && nb_lt b c
  | .EMdw _ a c => nb_lt b a && nb_lt b c
  | .EExt _ _ _ a => nb_lt b a
  | .EBlob _ _ _ _ => false

/-- Two valuations that agree below `b` denote `nb_lt b` expressions alike. -/
theorem edenot_ev_agree (b : Nat) (E E' : env) (e : expr)
    (H : nb_lt b e = true) (Hag : ∀ n, n < b → E.ev n = E'.ev n) :
    edenot E e = edenot E' e := by
  induction e with
  | ELit z => rfl
  | EVar n =>
    exact Hag n (by simpa [nb_lt] using H)
  | EAlu op a c iha ihc =>
    simp only [nb_lt, Bool.and_eq_true] at H
    rw [show edenot E (.EAlu op a c) = alu64 op (edenot E a) (edenot E c) from rfl,
      show edenot E' (.EAlu op a c) = alu64 op (edenot E' a) (edenot E' c) from rfl,
      iha H.1, ihc H.2]
  | EAluw op a c iha ihc =>
    simp only [nb_lt, Bool.and_eq_true] at H
    rw [show edenot E (.EAluw op a c) = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E c))) from rfl,
      show edenot E' (.EAluw op a c) = sext 64 (alu32 op (low32 (edenot E' a)) (low32 (edenot E' c))) from rfl,
      iha H.1, ihc H.2]
  | EMd op a c iha ihc =>
    simp only [nb_lt, Bool.and_eq_true] at H
    rw [show edenot E (.EMd op a c) = mul_div op (edenot E a) (edenot E c) from rfl,
      show edenot E' (.EMd op a c) = mul_div op (edenot E' a) (edenot E' c) from rfl,
      iha H.1, ihc H.2]
  | EMdw op a c iha ihc =>
    simp only [nb_lt, Bool.and_eq_true] at H
    rw [show edenot E (.EMdw op a c) = sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E c))) from rfl,
      show edenot E' (.EMdw op a c) = sext 64 (mul_div op (low32 (edenot E' a)) (low32 (edenot E' c))) from rfl,
      iha H.1, ihc H.2]
  | EExt sx lo n a ih =>
    simp only [nb_lt] at H
    rw [show edenot E (.EExt sx lo n a) = ext_val sx lo n (edenot E a) from rfl,
      show edenot E' (.EExt sx lo n a) = ext_val sx lo n (edenot E' a) from rfl,
      ih H]
  | EBlob sx k i n => simp [nb_lt] at H

/-! ### Code facts at the `Z_to_bv` spelling of a pc -/

/-- Code facts at the `Z_to_bv` spelling of a pc. -/
theorem fetch_lit (segs : List Segment) (z : Int) (w : word) (x : BitVec 32)
    (Hw : bv_unsigned w = z) (Hf : fetch_word segs w = some x) :
    fetch_word segs (Z_to_bv 64 z) = some x := by
  have h : Z_to_bv 64 z = w := by
    rw [← Hw]
    exact ofInt_toNat w
  rw [h]
  exact Hf

/-! ### Checker-state surgery -/

theorem with_ss_idem (cs : acs) (s1 s2 : sym_state) :
    with_ss (with_ss cs s1) s2 = with_ss cs s2 := rfl

theorem a_ss_with_ss (cs : acs) (s : sym_state) : (with_ss cs s).a_ss = s := rfl

/-! ### Page arithmetic (local copies of the APS lemmas) -/

/-- Page arithmetic: the base of a word's page is at or below it, the word is
    inside its page, and the base is aligned.   -/
theorem page_base_le' (a : word) : bv_unsigned (page_base a) ≤ bv_unsigned a ∧
    bv_unsigned a < bv_unsigned (page_base a) + 4096 ∧
    bv_unsigned (page_base a) % 4096 = 0 :=
  AsanPlanSound.page_base_le a

/-- A page wholly inside an interval that starts at or above an aligned bound
    `lo` cannot hold a byte below `lo`; dually for the upper bound.   -/
theorem page_in_ranges_bounds' (a : word) (l : List (word × word)) (lo hi : Int)
    (Hl : ∀ iv ∈ l, lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ hi)
    (Hp : page_in_ranges (page_base a) l = true) :
    lo ≤ bv_unsigned a ∧ bv_unsigned a + 1 ≤ hi + 4095 :=
  AsanPlanSound.page_in_ranges_bounds a l lo hi Hl Hp

/-- The allowed set is page-aligned at both ends by construction.   -/
theorem A_wf_allowA' (A : atable) (E : env) (cs : acs) : A_wf (allowA A E cs) :=
  AsanPlanSound.A_wf_allowA A E cs

/-! ## 2. The restriction `negb ∘ vis` -/

/-- The complement of the visible set. -/
def Hv (A : atable) (E : env) (cs : acs) (model : Model) : word → Bool :=
  fun a => !(vis A E cs model a)

/-- A `Hv`-hidden byte is `hid`-hidden. -/
theorem Hv_hid (A : atable) (argH : env → word → Bool) (E : env) (cs : acs)
    (model : Model) (a : word) (H : Hv A E cs model a = true) :
    hid A argH E cs model a = true := by
  unfold hid
  unfold Hv at H
  rw [H]
  simp

/-- Nothing at or above the ceiling is `Hv`-hidden. -/
theorem Hv_high (A : atable) (E : env) (cs : acs) (model : Model) (a : word)
    (Ha : CEIL ≤ bv_unsigned a) : Hv A E cs model a = false := by
  unfold Hv vis
  simp only
  rw [show (decide (CEIL ≤ bv_unsigned a)) = true from by simp [Ha]]
  simp

/-- Nothing inside the image hull is `Hv`-hidden. -/
theorem Hv_hull (A : atable) (E : env) (cs : acs) (model : Model) (a : word)
    (Ha : in_hull A (bv_unsigned a) = true) : Hv A E cs model a = false := by
  unfold Hv vis
  simp only
  rw [Ha]
  simp

/-- The lazy pages of a `cs_ok` state are covered by the allowed set, through
    the VISIBLE predicate. -/
theorem lazy_cover_vis (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HULL_ok : hull_ok A) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    lazy_cover (Hv A E cs model) (m_vm_lazy model) (allowA A E cs) := by
  intro w Hlz Hh
  have Hlz' : page_in_ranges (page_base w) (m_vm_lazy model) = true := Hlz
  -- `Hv` false means `vis` true
  have hvis : vis A E cs model w = true := by
    have h := Hh
    unfold Hv at h
    simpa using h
  rw [page_in_ranges, List.any_eq_true] at Hlz
  obtain ⟨iv, Hin, Hb⟩ := Hlz
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hb
  obtain ⟨L1, L2⟩ := HC.co_lazyb iv Hin
  obtain ⟨P1, P2, P3⟩ := page_base_le' w
  simp only [page_size] at Hb
  have hlo : A.img_hi ≤ bv_unsigned w := Int.le_trans L1 (Int.le_trans Hb.1 P1)
  have hhi : bv_unsigned w < CEIL :=
    Int.lt_of_lt_of_le P2 (Int.le_trans Hb.2 L2)
  simp only [vis] at hvis
  rw [Bool.or_eq_true] at hvis
  rcases hvis with h | h
  · rw [Bool.or_eq_true] at h
    rcases h with hhull | hceil
    · exfalso
      simp only [in_hull, Bool.and_eq_true, decide_eq_true_eq] at hhull
      exact (Int.not_lt.mpr hlo) hhull.2
    · exfalso
      simp only [decide_eq_true_eq] at hceil
      exact (Int.not_lt.mpr hceil) hhi
  · rw [Bool.and_eq_true] at h
    obtain ⟨-, h2⟩ := h
    rw [Hlz'] at h2
    simp only [Bool.not_true, Bool.false_or] at h2
    exact in_allow_page A E cs w h2

/-- The same for `hid` . -/
theorem lazy_cover_hid (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HULL_ok : hull_ok A) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    lazy_cover (hid A argH E cs model) (m_vm_lazy model) (allowA A E cs) :=
  lazy_cover_cs segs A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC

/-- No `Hv`-hidden address lies inside a loaded segment. -/
theorem H_off_segments_vis (segs : List Segment) (A : atable)
    (HSEGS : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (E : env) (cs : acs) (model : Model) :
    H_off_segments segs (Hv A E cs model) := by
  intro a Hh
  have h1 : vis A E cs model a = false := by
    have h := Hh
    unfold Hv at h
    simpa using h
  have h2 : in_hull A (bv_unsigned a) = false := by
    rw [vis] at h1
    simp only [Bool.or_eq_false_iff] at h1
    exact h1.1.1
  exact HSEGS a h2

/-- The restricted memory agrees with `FULL` above the ceiling. -/
theorem mrestrict_Hv_high (A : atable) (E : env) (cs : acs) (model : Model)
    (FULL : word → Option byte) (a : word) (Ha : CEIL ≤ bv_unsigned a) :
    mrestrict (Hv A E cs model) FULL a = FULL a := by
  unfold mrestrict
  rw [Hv_high A E cs model a Ha]
  rfl

/-- `Mr` is below `mrestrict Hv` in the definedness order. -/
theorem Mr_grows_Hv (A : atable) (argH : env → word → Bool) (E : env) (cs : acs)
    (model : Model) (FULL : word → Option byte) :
    mem_grows (Mr A argH E cs model FULL) (mrestrict (Hv A E cs model) FULL) := by
  intro a h
  unfold Mr mrestrict hid Hv at *
  cases hb : argH E a <;> cases hv : vis A E cs model a <;> simp_all

/-- Un-restricting the restricted memory gives the memory back. -/
theorem munrestrict_mrestrict (H : word → Bool) (FULL : word → Option byte) :
    munrestrict H FULL (mrestrict H FULL) = FULL :=
  AsanAcct.munrestrict_mrestrict H FULL

end LinuxSem.Common.AsanNodesAux


