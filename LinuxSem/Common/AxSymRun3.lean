/-
  * Common.AxSymRun3 — using `AxSymExec3`: entry/exit packaging, valuation
    extension, side-condition discharge tactics.
  `AxSymRun3` (`Import AX2. Import AX2S.`).

  Image-INDEPENDENT.  The workflow for one straight-line block:

  1. Have `HR : regs_ok E sr regs` and `HK : know_ok segs E base kn` for the
     block's entry state `mkst regs (Z_to_bv 64 pc) base rom`
     (for the program entry state use `regs_ok_init`).
  2. `sym_run_tac SEGS fuel stops scr nx HR HK as R' HR' Hlf Hms`:
     computes `sym_exec` by `vm_compute`, applies `run_sound`, and leaves
       - `Hms : msteps SEGS (mkst regs pc base rom) (mkst R' pc' (mem_denot E base log') rom)`
       - `HR' : regs_ok E sr' R'`,  `Hlf : log_flat E log'`
       - one goal per side condition that `sc_auto` could not discharge.
  3. Read results off `HR'` (`reg_val HR' r`) and continue (syscall node,
     next block).  For the next block's knowledge use `carry_after`.

     The valuation `E` maps variable indices to words through a LIST
     (`⟨vals_ev vals, blobs⟩`); appending to the list preserves every
     denotation that only mentions earlier indices (`*_agree` lemmas,
     checked syntactically by `*_vars_lt`).

  ---------------------------------------------------------------------
  — THREE THEOREMS ARE OUT OF REACH HERE, NOT OMITTED
  ---------------------------------------------------------------------

  `AxSymExec3Sound` is green but its coverage is: it is complete
  through  line ~2477 plus every definition, and its own header
  lists what remains ("…pruning/carry, XSound/CarrySound, and the
  `sym_step_sound*` / `sym_exec_*` drivers").
  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------
  * `Z` → `Int`, `N`/`nat` → `Nat`, `option` → `Option`, `list` → `List`,
    `Z_of_nat` → `(· : Int)`, records → structures, `bv_unsigned w` →
    `(w.toNat : Int)` (spelled `bv_unsigned`, an abbrev, everywhere).
  * `Env (vals_ev vals) ebs` → `⟨vals_ev vals, ebs⟩`: this tree's `env` is a
    structure with fields `ev`/`eb`, not a two-argument constructor.
  * `nth n vals (Z_to_bv 64 0)` → `vals.getD n (Z_to_bv 64 0)`
    (`List.getD` is `nth` with the default as a value).
  * The two `Bool`-valued recursion subjects (`expr_vars_lt`, `sr_vars_lt`,
    `kn_vars_lt`, `log_vars_lt`) are `def`s by structural recursion, so
    `simp only [f]` uses their equational lemmas — no `cbn [f]` needed.
 This tree
    replaces that with ONE `by decide` fact about the concrete list
    (`sr_init_getD_lt`, evaluated over `List.range 32`), which is the same
    syntactic check this tree uses for every other decidable definition.
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
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.SymExec
import LinuxSem.Common.SymStepR
import LinuxSem.Common.StepTac
import LinuxSem.Common.RocqSpelling
import LinuxSem.Common.AxSymExec3
import LinuxSem.Common.AxSymExec3Sound

namespace LinuxSem.Common.AxSymRun3

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StoreOk
open LinuxSem.Common.SymStepR
open LinuxSem.Common.StepTac
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3Sound

/-- `Local Instance asanreflect_fx : PropExec.FPState :=
    PropExec.fx0`, which every example file re-declares. -/
local instance axsymrun3_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! #########################################################################
    ## 1. List-backed valuations and agreement
    ######################################################################### -/

/-- The valuation whose word variables are the entries of a LIST (index 0 is
    `sp` in `regs_ok_init` below); out-of-range reads are 0. -/
def vals_ev (vals : List word) : Nat → word :=
  fun n => vals.getD n (Z_to_bv 64 0)

/-- **Variable bound, syntactically.**  Every variable index occurring in `e`
    is below `b`.  Deciding this on the syntax is what lets the `*_agree`
    lemmas below lift a `env_agree` hypothesis through an arbitrary
    expression without ever evaluating it. -/
def expr_vars_lt (b : Nat) : expr → Bool
  | .ELit _ => true
  | .EVar n => decide (n < b)
  | .EAlu _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EAluw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EMd _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | .EExt _ _ _ x => expr_vars_lt b x
  | .EBlob _ _ _ _ => true

/-- The same for an address: only the base expression carries variables. -/
def saddr_vars_lt (b : Nat) (a : saddr) : Bool :=
  expr_vars_lt b a.a_base

/-- Every entry of a register file is below `b`. -/
def sr_vars_lt (b : Nat) : List expr → Bool
  | [] => true
  | e :: r => expr_vars_lt b e && sr_vars_lt b r

/-- Every expression a knowledge entry mentions is below `b`.
    `KFill` is treated exactly like `KZero` (its byte is a literal). -/
def kentry_vars_lt (b : Nat) : kentry → Bool
  | .KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | .KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | .KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | .KImg _ _ => true
  | .KAlign e _ => expr_vars_lt b e
  | .KRange e _ _ => expr_vars_lt b e
  | .KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | .KDisj a1 n1 a2 n2 =>
      saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | .KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | .KUnk a n => saddr_vars_lt b a && expr_vars_lt b n

/-- Every expression a knowledge LIST mentions is below `b`. -/
def kn_vars_lt (b : Nat) : List kentry → Bool
  | [] => true
  | K :: r => kentry_vars_lt b K && kn_vars_lt b r

/-- Every expression a store LOG mentions is below `b`. -/
def log_vars_lt (b : Nat) : List sentry → Bool
  | [] => true
  | ⟨a, _, v⟩ :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r

/-! -/

example : expr_vars_lt 4 (.EVar 3) = true := by decide
example : expr_vars_lt 4 (.EVar 4) = false := by decide
example : expr_vars_lt 4 (.EAlu .ADD (.EVar 3) (.EVar 5)) = false := by decide
example : expr_vars_lt 4 (.EAlu .ADD (.EVar 3) (.EVar 1)) = true := by decide
example : expr_vars_lt 4 (.EExt false 0 4 (.EVar 3)) = true := by decide
example : saddr_vars_lt 4 (SA (.EVar 2) (- 8)) = true := by decide
example : sr_vars_lt 4 [.EVar 0, .EVar 1] = true := by decide
example : sr_vars_lt 4 [.EVar 0, .EVar 9] = false := by decide
example : kentry_vars_lt 4 (.KWord (SA (.EVar 0) 8) 8 (.EVar 3)) = true := by decide
example : kn_vars_lt 4 [.KZero (SA (.EVar 1) 0) (.ELit 8)] = true := by decide
example : kn_vars_lt 4 [.KImg 0 4096] = true := by decide
example : vals_ev [11, 22] 1 = 22 := by decide
example : vals_ev [11, 22] 5 = 0 := by decide

/-- **Agreement below a bound.**  Two valuations agree on every variable with
    index `< b`, and on the byte strings (which are never extended). -/
def env_agree (b : Nat) (E E' : env) : Prop :=
  (∀ n, n < b → E.ev n = E'.ev n) ∧ E.eb = E'.eb

/-- An expression whose variables are all below `b` denotes the same word
    under any two valuations agreeing below `b`. -/
theorem edenot_agree (b : Nat) (E E' : env) (Ha : env_agree b E E') :
    ∀ e : expr, expr_vars_lt b e = true → edenot E e = edenot E' e := by
  obtain ⟨Hv, Hb⟩ := Ha
  intro e
  induction e with
  | ELit z => intro _; rfl
  | EVar n =>
      intro H
      exact Hv n (of_decide_eq_true H)
  | EAlu op x y ihx ihy =>
      intro H
      simp only [expr_vars_lt, Bool.and_eq_true] at H
      show alu64 op (edenot E x) (edenot E y) = alu64 op (edenot E' x) (edenot E' y)
      rw [ihx H.1, ihy H.2]
  | EAluw op x y ihx ihy =>
      intro H
      simp only [expr_vars_lt, Bool.and_eq_true] at H
      show sext 64 (alu32 op (low32 (edenot E x)) (low32 (edenot E y)))
          = sext 64 (alu32 op (low32 (edenot E' x)) (low32 (edenot E' y)))
      rw [ihx H.1, ihy H.2]
  | EMd op x y ihx ihy =>
      intro H
      simp only [expr_vars_lt, Bool.and_eq_true] at H
      show mul_div op (edenot E x) (edenot E y) = mul_div op (edenot E' x) (edenot E' y)
      rw [ihx H.1, ihy H.2]
  | EMdw op x y ihx ihy =>
      intro H
      simp only [expr_vars_lt, Bool.and_eq_true] at H
      show sext 64 (mul_div op (low32 (edenot E x)) (low32 (edenot E y)))
          = sext 64 (mul_div op (low32 (edenot E' x)) (low32 (edenot E' y)))
      rw [ihx H.1, ihy H.2]
  | EExt sx lo n x ih =>
      intro H
      show ext_val sx lo n (edenot E x) = ext_val sx lo n (edenot E' x)
      rw [ih H]
  | EBlob sx k i n =>
      intro _
      show blob_val sx (E.eb k) i n = blob_val sx (E'.eb k) i n
      rw [Hb]

/-- An address whose base is below `b` denotes the same word. -/
theorem adenot_agree (b : Nat) (E E' : env) (a : saddr) (Ha : env_agree b E E')
    (H : saddr_vars_lt b a = true) : adenot E a = adenot E' a := by
  show v_addi (edenot E a.a_base) a.a_off = v_addi (edenot E' a.a_base) a.a_off
  rw [edenot_agree b E E' Ha a.a_base H]

/-- A register file whose every entry is below `b` denotes the same concrete
    register file under any two valuations agreeing below `b`. -/
theorem regs_ok_agree (b : Nat) (E E' : env) (sr : List expr) (regs : BvMap word)
    (Ha : env_agree b E E') (Hsr : sr_vars_lt b sr = true) (HR : regs_ok E sr regs) :
    regs_ok E' sr regs := by
  -- every in-range entry of `sr` satisfies the bound
  have Hnth : ∀ sr : List expr, sr_vars_lt b sr = true →
      ∀ i, expr_vars_lt b (sr.getD i (.ELit 0)) = true := by
    intro sr
    induction sr with
    | nil => intro _ i; rfl
    | cons e t ih =>
        intro Hs i
        simp only [sr_vars_lt, Bool.and_eq_true] at Hs
        obtain ⟨He, Ht⟩ := Hs
        cases i with
        | zero => simpa using He
        | succ i => simpa using ih Ht i
  intro r
  rw [HR r]
  show edenot E (sr_get sr r) = edenot E' (sr_get sr r)
  unfold sr_get
  by_cases h0 : bv_eqb r 0 = true
  · rw [ite_eq_left h0]
    rfl
  · rw [ite_eq_right h0]
    exact edenot_agree b E E' Ha _ (Hnth sr Hsr (ridx r))

/-- The store log denotes the same memory under any two valuations agreeing
    below `b`. -/
theorem mem_denot_agree (b : Nat) (E E' : env) (base : word → Option byte) :
    env_agree b E E' → ∀ log : List sentry, log_vars_lt b log = true →
      mem_denot E base log = mem_denot E' base log := by
  intro Ha log
  induction log with
  | nil => intro _; rfl
  | cons hd rest ih =>
      obtain ⟨a, w, v⟩ := hd
      intro H
      simp only [log_vars_lt, Bool.and_eq_true] at H
      obtain ⟨H1, H3⟩ := H
      obtain ⟨H1, H2⟩ := H1
      show wbytes (mem_denot E base rest) (adenot E a)
            (word_to_le_bytes w (edenot E v))
          = wbytes (mem_denot E' base rest) (adenot E' a)
            (word_to_le_bytes w (edenot E' v))
      rw [ih H3, adenot_agree b E E' a Ha H1, edenot_agree b E E' Ha v H2]

/-- Flatness is valuation-independent when the base is below `b`. -/
theorem flat_agree (b : Nat) (E E' : env) (a : saddr) (n : Int) (Ha : env_agree b E E')
    (H : saddr_vars_lt b a = true) : (flat E a n ↔ flat E' a n) := by
  unfold flat estart
  simp only [edenot_agree b E E' Ha a.a_base H]

/-- `log_flat` transfers across agreeing valuations. -/
theorem log_flat_agree (b : Nat) (E E' : env) (log : List sentry) (Ha : env_agree b E E')
    (H : log_vars_lt b log = true) (Hl : log_flat E log) : log_flat E' log := by
  induction log with
  | nil => exact trivial
  | cons hd rest ih =>
      obtain ⟨a, w, v⟩ := hd
      simp only [log_vars_lt, Bool.and_eq_true] at H
      obtain ⟨H1, H3⟩ := H
      obtain ⟨H1, H2⟩ := H1
      obtain ⟨Hw, Hf, Hr⟩ := Hl
      refine ⟨Hw, ?_, ih H3 Hr⟩
      exact (flat_agree b E E' a (w : Int) Ha H1).mp Hf

/-- One knowledge entry's denotation transfers across agreeing valuations.
     -/
theorem kentry_ok_agree (segs : List Segment) (b : Nat) (E E' : env)
    (base : word → Option byte) (Ha : env_agree b E E') (K : kentry)
    (HK : kentry_vars_lt b K = true) (Hk : kentry_ok segs E base K) :
    kentry_ok segs E' base K := by
  obtain ⟨Hv, Hb⟩ := Ha
  have Ha' : env_agree b E E' := ⟨Hv, Hb⟩
  -- `estart`/`elenZ` are the only routes from `E` into `kentry_ok`, so every
  -- case is the same rewrite: put the goal in `E`'s spelling, then use `Hk`.
  have est : ∀ (a : saddr), saddr_vars_lt b a = true → estart E' a = estart E a := by
    intro a h
    show bv_unsigned (edenot E' a.a_base) + a.a_off = bv_unsigned (edenot E a.a_base) + a.a_off
    rw [edenot_agree b E E' Ha' a.a_base h]
  have eln : ∀ (n : expr), expr_vars_lt b n = true → elenZ E' n = elenZ E n := by
    intro n h
    show bv_unsigned (edenot E' n) = bv_unsigned (edenot E n)
    rw [edenot_agree b E E' Ha' n h]
  cases K with
  | KWord a w v =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hV⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨Hk.1, ?_, ?_⟩
      · rw [est a hA]; exact Hk.2.1
      · rw [← adenot_agree b E E' a Ha' hA, ← edenot_agree b E E' Ha' v hV]
        exact Hk.2.2
  | KZero a n =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hN⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨?_, ?_⟩
      · rw [est a hA, eln n hN]; exact Hk.1
      · intro i h0 hi
        rw [eln n hN] at hi
        rw [est a hA]
        exact Hk.2 i h0 hi
  | KBlob a n k =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hN⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [est a hA, eln n hN]; exact Hk.1
      · rw [← Hb, eln n hN]; exact Hk.2.1
      · intro i h0 hi
        rw [eln n hN] at hi
        rw [← Hb, est a hA]
        exact Hk.2.2 i h0 hi
  | KImg lo hi =>
      simp only [kentry_ok] at Hk ⊢
      exact Hk
  | KAlign e m =>
      simp only [kentry_vars_lt] at HK
      simp only [kentry_ok] at Hk ⊢
      rw [← edenot_agree b E E' Ha' e HK]
      exact Hk
  | KRange e lo hi =>
      simp only [kentry_vars_lt] at HK
      simp only [kentry_ok] at Hk ⊢
      rw [← edenot_agree b E E' Ha' e HK]
      exact Hk
  | KWr a n =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hN⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨?_, ?_⟩
      · rw [est a hA, eln n hN]; exact Hk.1
      · intro d m h0 hm
        rw [eln n hN] at hm
        rw [est a hA]
        exact Hk.2 d m h0 hm
  | KDisj a1 n1 a2 n2 =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨⟨⟨hA1, hN1⟩, hA2⟩, hN2⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      rw [est a1 hA1, eln n1 hN1, est a2 hA2, eln n2 hN2]
      exact Hk
  | KFill a n c =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hN⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨?_, ?_⟩
      · rw [est a hA, eln n hN]; exact Hk.1
      · intro i h0 hi
        rw [eln n hN] at hi
        rw [est a hA]
        exact Hk.2 i h0 hi
  | KUnk a n =>
      simp only [kentry_vars_lt, Bool.and_eq_true] at HK
      obtain ⟨hA, hN⟩ := HK
      simp only [kentry_ok] at Hk ⊢
      unfold flat at Hk ⊢
      refine ⟨?_, ?_⟩
      · rw [est a hA, eln n hN]; exact Hk.1
      · intro i h0 hi
        rw [eln n hN] at hi
        rw [est a hA]
        exact Hk.2 i h0 hi

/-- A whole knowledge list transfers across agreeing valuations. -/
theorem know_ok_agree (segs : List Segment) (b : Nat) (E E' : env)
    (base : word → Option byte) (Ha : env_agree b E E') :
    ∀ kn : List kentry, kn_vars_lt b kn = true → know_ok segs E base kn →
      know_ok segs E' base kn := by
  intro kn
  induction kn with
  | nil =>
      intro _ _ K hK
      exact (List.not_mem_nil hK).elim
  | cons K r ih =>
      intro H Hk K' hK'
      simp only [kn_vars_lt, Bool.and_eq_true] at H
      obtain ⟨HK, Hr⟩ := H
      rcases List.mem_cons.mp hK' with hEq | hK'
      · rw [hEq]
        exact kentry_ok_agree segs b E E' base Ha K HK (Hk K (List.mem_cons_self ..))
      · exact ih Hr (fun M hM => Hk M (List.mem_cons_of_mem _ hM)) K' hK'

/-- **Appending to the value list agrees below its old length.**  This is the
    only reason `env_agree` measures the bound in VARIABLE INDICES: a block
    that allocates fresh variables appends to `vals` and every earlier
    denotation is untouched. -/
theorem vals_app_agree (vals extra : List word) (ebs : Nat → List byte) :
    env_agree vals.length ⟨vals_ev vals, ebs⟩ ⟨vals_ev (vals ++ extra), ebs⟩ := by
  have key : ∀ vals : List word, ∀ n, n < vals.length →
      vals_ev vals n = vals_ev (vals ++ extra) n := by
    intro vals
    induction vals with
    | nil => intro n hn; exact absurd hn (by simp)
    | cons v vs ih =>
        intro n hn
        cases n with
        | zero => rfl
        | succ n =>
            simp only [vals_ev, List.getD_cons_succ, List.cons_append] at ⊢
            exact ih n (by simpa using hn)
  refine ⟨?_, rfl⟩
  intro n hn
  exact key vals n hn

/-! #########################################################################
    ## 2. Running a block
    ######################################################################### -/

section Run

/- `segs`  is a section variable of `Section Run`; this tree makes it
    an explicit parameter of every lemma, exactly as `SymExec.sc_denot` does. -/

/-- **Entry packaging.**  Registers plus knowledge about the entry memory give
    `st_ok` for a state with an EMPTY store log. -/
theorem st_ok_entry (segs : List Segment) (E : env) (base rom : word → Option byte)
    (pc : Int) (sr : List expr) (kn : List kentry) (nx : Nat) (regs : BvMap word)
    (HR : regs_ok E sr regs) (HK : know_ok segs E base kn) :
    st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom) :=
  ⟨regs, rfl, HR, trivial, HK⟩

/-- **`run_sound`** — a symbolic run of a block simulates a machine run.

    This is `AX2S.sym_exec_ex` applied to `st_ok_entry`: the entry state
    satisfies the abstract `st_ok` invariant, so the executor's soundness
    theorem turns the concrete `sym_exec` result into a `msteps` chain whose
    final machine state is denoted by the symbolic post-state. -/
theorem run_sound (segs : List Segment) (fuel : Nat) (stops : List Int) (scr : scripts)
    (pc : Int) (sr : List expr) (kn : List kentry) (nx : Nat) (ss' : sym_state)
    (scs : List sidecond) (scr' : scripts) (E : env) (base rom : word → Option byte)
    (regs : BvMap word)
    (H : sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr'))
    (HR : regs_ok E sr regs) (HK : know_ok segs E base kn)
    (Hsc : scs_denot segs base E scs) :
    ∃ R, regs_ok E ss'.s_regs R ∧ log_flat E ss'.s_log ∧
      msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
        (mkst R (Z_to_bv 64 ss'.s_pc) (mem_denot E base ss'.s_log) rom) :=
  sym_exec_ex segs E base rom fuel true stops scr (SS pc sr [] kn nx) [] ss' scs scr'
    (mkst regs (Z_to_bv 64 pc) base rom) H Hsc
    (st_ok_entry segs E base rom pc sr kn nx regs HR HK)

/-- **`AX2S.eagree` and `env_agree` are the same relation** (the two files
    define it separately, with the same body). -/
theorem eagree_env_agree (b : Nat) (E E' : env) : eagree b E E' ↔ env_agree b E E' :=
  Iff.rfl

/-- A block-boundary state whose registers and knowledge mention only
    variables below its counter `nx` relates to the machine under EVERY
    valuation agreeing with `E` below `nx` — the premise of
    `AX2S.sym_execTX_ex` (and so of `runTX_sound`). -/
theorem st_okX_entry (segs : List Segment) (E : env) (base rom : word → Option byte)
    (pc : Int) (sr : List expr) (kn : List kentry) (nx : Nat) (regs : BvMap word)
    (HR : regs_ok E sr regs) (HK : know_ok segs E base kn)
    (Hsr : sr_vars_lt nx sr = true) (Hkn : kn_vars_lt nx kn = true) :
    ∀ E' : env, eagree nx E E' →
      st_ok segs E' base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom) := by
  intro E' Ha
  have Ha' : env_agree nx E E' := (eagree_env_agree nx E E').mp Ha
  exact st_ok_entry segs E' base rom pc sr kn nx regs
    (regs_ok_agree nx E E' sr regs Ha' Hsr HR)
    (know_ok_agree segs nx E E' base Ha' kn Hkn HK)

/-- **`runTX_sound`** — a symbolic run of a whole table simulates a machine run,
    with the environment transported along the way.

    `AX2S.sym_execTX_ex` applied to `st_okX_entry`: the entry state satisfies
    the extension-mode invariant for every environment agreeing with `E` below
    `nx`, so the executor's soundness theorem produces the transported
    environment `E'`, the register file `R`, the `msteps` chain, and the
    final-state obligation at every further extension of `E'`. -/
theorem runTX_sound (segs : List Segment) (t : itab) (K fuel : Nat) (stops : List Int)
    (pc : Int) (sr : List expr) (kn : List kentry) (nx : Nat)
    (E : env) (base rom : word → Option byte) (regs : BvMap word)
    (Ht : itab_sound segs t) (HR : regs_ok E sr regs) (HK : know_ok segs E base kn)
    (Hsr : sr_vars_lt nx sr = true) (Hkn : kn_vars_lt nx kn = true) :
    ∃ E' R, env_agree nx E E' ∧
      nx ≤ (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_next ∧
      regs_ok E' (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_regs R ∧
      log_flat E' (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_log ∧
      know_ok segs E' base (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_know ∧
      msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
        (mkst R (Z_to_bv 64 (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_pc)
          (mem_denot E' base (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_log) rom) ∧
      (∀ E'', env_agree (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_next E' E'' →
        st_ok segs E'' base rom (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx))
          (mkst R (Z_to_bv 64 (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_pc)
            (mem_denot E' base (sym_execTX segs t K fuel true stops (SS pc sr [] kn nx)).s_log) rom)) := by
  obtain ⟨E', R, Hag, Hnext, Hregs, Hlf, Hkn', Hms, Hfin⟩ :=
    sym_execTX_ex segs E base rom t K fuel true stops (SS pc sr [] kn nx)
      (mkst regs (Z_to_bv 64 pc) base rom) Ht
      (st_okX_entry segs E base rom pc sr kn nx regs HR HK Hsr Hkn)
  exact ⟨E', R, (eagree_env_agree nx E E').mp Hag, Hnext, Hregs, Hlf, Hkn', Hms,
    fun E'' H => Hfin E'' ((eagree_env_agree _ E' E'').mpr H)⟩

/-- **`carry_after`** — the knowledge resulting from a carry is still sound,
    against the memory that the store log describes.

    A one-line corollary of `AX2S.carry_sound`, instantiated at
    `anybase := base`.  It is what makes the *inter-block* part of the
    analysis work: after a block's stores have been carried into the
    knowledge, the entries that survive describe the memory the stores
    actually produced. -/
theorem carry_after (segs : List Segment) (E : env) (base : word → Option byte)
    (log : List sentry) (kn : List kentry) (hints : List Bool)
    (kn' : List kentry) (scs : List sidecond) (hs' : List Bool)
    (Hc : carry log kn hints = (kn', scs, hs'))
    (Hlf : log_flat E log) (Hkn : know_ok segs E base kn)
    (Hscs : scs_denot segs base E scs) :
    know_ok segs E (mem_denot E base log) kn' :=
  carry_sound segs E base base log kn hints kn' scs hs' Hc Hlf Hkn Hscs

/-- **Registers: read one back.**  The whole point of carrying `regs_ok` out
    of a run: `reg_val HR' r` IS the value the block left in `r`. -/
theorem reg_val (E : env) (sr : List expr) (R : BvMap word) (r : reg)
    (HR : regs_ok E sr R) : getr R r = edenot E (sr_get sr r) :=
  HR r

/-- **Re-seed the symbolic register file** after the caller changed one
    register concretely (e.g. a syscall's return value in a0). -/
theorem regs_ok_set (E : env) (sr : List expr) (R : BvMap word) (rd : reg)
    (v : word) (e : expr) (HR : regs_ok E sr R) (Hrd : rd ≠ 0) (He : edenot E e = v) :
    regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v) := by
  have H := regs_ok_upd E sr R rd v e HR He
  have Hb : bv_eqb rd 0 = false := bv_eqb_neq rd 0 Hrd
  rw [Hb] at H
  simpa using H

end Run

/-! #########################################################################
    ## 3. Initial program state
    ######################################################################### -/

/-- The entry register file of `init_machine_state`: x2 = sp, everything else
    0 (x10 is explicitly 0). -/
def sr_init : List expr :=
  [.ELit 0, .ELit 0, .EVar 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0,
   .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0,
   .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0,
   .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0, .ELit 0]

/-- The length of the entry register file (a `by decide` sanity check). -/
theorem sr_init_length : sr_init.length = 32 := by decide

/-- **Only x2 is non-zero in `sr_init`.**   proves this by destructing
    `ridx r` into 32 cases; this tree decides the whole concrete list at once
    over `List.range 32` — the same syntactic check, in one `by decide`. -/
theorem sr_init_getD_lt (i : Nat) (hi : i < 32) :
    sr_init.getD i (.ELit 0) = if i = 2 then .EVar 0 else .ELit 0 := by
  have hall : (List.range 32).all (fun j =>
      (sr_init.getD j (.ELit 0) == (if j = 2 then .EVar 0 else .ELit 0))) = true := by
    decide
  have hmem : i ∈ List.range 32 := List.mem_range.mpr hi
  have h := List.all_eq_true.mp hall i hmem
  exact beq_iff_eq.mp h

/-- `sr_init` at index 2. -/
theorem sr_init_getD_two : sr_init.getD 2 (.ELit 0) = .EVar 0 := by decide

/-- `sr_init` away from index 2. -/
theorem sr_init_getD_other (i : Nat) (hi : i < 32) (h2 : i ≠ 2) :
    sr_init.getD i (.ELit 0) = .ELit 0 := by
  rw [sr_init_getD_lt i hi, ite_eq_right h2]

/-- **The program entry state satisfies `regs_ok`.**  `sp` is the first entry
    of the value list, so `EVar 0` is `sp`. -/
theorem regs_ok_init (sp : word) (rest : List word) (ebs : Nat → List byte) :
    regs_ok ⟨vals_ev (sp :: rest), ebs⟩ sr_init
      (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) := by
  intro r
  show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) r
      = edenot ⟨vals_ev (sp :: rest), ebs⟩ (sr_get sr_init r)
  unfold sr_get
  by_cases hr0 : bv_eqb r 0 = true
  · -- x0 reads 0 on both sides
    rw [ite_eq_left hr0]
    have hr : r = 0 := beq_iff_eq.mp hr0
    subst hr
    show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (BitVec.ofInt 64 0)) 2 sp) 0
        = BitVec.ofInt 64 0
    rw [show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (BitVec.ofInt 64 0)) 2 sp) 0
          = 0 from by simp [getr, bv_eqb_refl]]
    decide
  · rw [ite_eq_right hr0]
    have hlt : ridx r < 32 := ridx_range r
    have hrt : Z_to_bv 5 (ridx r : Int) = r := ridx_roundtrip r
    have hne0 : r ≠ 0 := by
      intro h; apply hr0; rw [h]; rfl
    by_cases h2 : ridx r = 2
    · -- the stack pointer: `sr_init.getD 2 = EVar 0`, and x2 holds `sp`
      have hr2 : r = (2 : reg) := by rw [← hrt, h2]; decide
      rw [sr_init_getD_lt (ridx r) hlt, ite_eq_left h2]
      show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) r
          = (sp :: rest).getD 0 (BitVec.ofInt 64 0)
      rw [hr2, getr_same _ 2 sp (by decide)]
      rfl
    · -- every other register reads 0, and both `regupd`s miss it
      have hr2 : r ≠ (2 : reg) := by
        intro h
        apply h2
        have hc := congrArg ridx h
        simpa [ridx] using hc
      rw [sr_init_getD_lt (ridx r) hlt, ite_eq_right h2]
      show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) r
          = BitVec.ofInt 64 0
      rw [getr_other _ 2 sp r hr2]
      by_cases h10 : r = (10 : reg)
      · rw [h10, getr_same _ 10 (Z_to_bv 64 0) (by decide)]
      · rw [getr_other _ 10 (Z_to_bv 64 0) r h10, getr_nz _ r hne0]
        show reg_get (bvmap_empty : BvMap word) r = BitVec.ofInt 64 0
        rw [show reg_get (bvmap_empty : BvMap word) r = 0 from by
          simp [reg_get, bvmapGet, bvmap_get, bvmap_empty, w0]]
        decide

/-! #########################################################################
    ## 4. Writable windows (stack) and `store_ok` discharge
    ######################################################################### -/

/-- **"Every range inside `sp - K, sp` is writable in `mem`".**  This is the
    stack-window form of the machine store bound
    (`RiscvSemantics.store_ok`): one hypothesis covers every stack store a
    block performs, and `sc_store` discharges each `store_ok` goal from it. -/
def stk_ok (segs : List Segment) (mem : word → Option byte) (sp : word) (K : Int) : Prop :=
  ∀ (a : word) (n : Nat),
    bv_unsigned sp - K ≤ bv_unsigned a →
    bv_unsigned a + (n : Int) ≤ bv_unsigned sp →
    store_ok segs mem a n = true

/-- A store at `sp + off` with `off` inside `[-K, 0]`. -/
theorem stk_ok_vaddi (segs : List Segment) (mem : word → Option byte) (sp : word)
    (K off : Int) (n : Nat) (Hs : stk_ok segs mem sp K) (HK : K ≤ bv_unsigned sp)
    (H1 : -K ≤ off) (H2 : off + (n : Int) ≤ 0) :
    store_ok segs mem (v_addi sp off) n = true := by
  have hsp : bv_unsigned sp < 2 ^ 64 := (u64_range sp).2
  have hlo : 0 ≤ bv_unsigned sp + off := by omega
  have hhi : bv_unsigned sp + off < 2 ^ 64 := by omega
  have harg : bv_unsigned (v_addi sp off) = bv_unsigned sp + off := by
    show ((BitVec.ofInt 64 ((sp.toNat : Int) + off)).toNat : Int) = bv_unsigned sp + off
    rw [BitVec.toNat_ofInt,
      show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl,
      Int.emod_eq_of_lt hlo hhi, Int.toNat_of_nonneg hlo]
  exact Hs _ n (by rw [harg]; omega) (by rw [harg]; omega)

/-- A store at a literal address inside the window. -/
theorem stk_ok_lit (segs : List Segment) (mem : word → Option byte) (sp : word)
    (K z : Int) (n : Nat) (Hs : stk_ok segs mem sp K)
    (H1 : bv_unsigned sp - K ≤ z) (H2 : z + (n : Int) ≤ bv_unsigned sp) (H3 : 0 ≤ z) :
    store_ok segs mem (Z_to_bv 64 z) n = true := by
  have hsp : bv_unsigned sp < 2 ^ 64 := (u64_range sp).2
  have harg : bv_unsigned (Z_to_bv 64 z) = z := u_small ⟨H3, by omega⟩
  exact Hs _ n (by rw [harg]; omega) (by rw [harg]; omega)

/-- The window survives any memory growth (the overlay only adds bytes). -/
theorem stk_ok_grows (segs : List Segment) (mem mem' : word → Option byte) (sp : word)
    (K : Int) (Hs : stk_ok segs mem sp K) (Hg : mem_grows mem mem') :
    stk_ok segs mem' sp K := by
  intro a n H1 H2
  exact store_ok_mono segs n mem mem' a Hg (Hs a n H1 H2)

/-- The window survives the block's own store log. -/
theorem stk_ok_mem_denot (segs : List Segment) (E : env) (mem : word → Option byte)
    (log : List sentry) (sp : word) (K : Int) (Hs : stk_ok segs mem sp K) :
    stk_ok segs (mem_denot E mem log) sp K :=
  stk_ok_grows segs mem (mem_denot E mem log) sp K Hs (mem_denot_grows E mem log)

/-- **The initial memory: the whole 8 MiB window below sp is writable.** -/
theorem stk_ok_init (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rdraw : EntryDraw) :
    stk_ok segs (wrap_mem ph sp argv envp uid hw rdraw) sp stack_max_size := by
  intro a n H1 H2
  exact store_ok_wrap_window segs ph sp argv envp a n uid hw rdraw H1 H2

/-- **`KWr` from a stack window**: "the whole window is writable" IS the
    `KWr` knowledge entry, at `SA e (-K)` with length `ELit K`. -/
theorem kwr_of_stk_ok (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (sp : word) (K : Int) (He : edenot E e = sp)
    (Hs : stk_ok segs mem sp K) (HK : 0 ≤ K ∧ K ≤ bv_unsigned sp) :
    kentry_ok segs E mem (.KWr (SA e (- K)) (.ELit K)) := by
  obtain ⟨HK0, HK1⟩ := HK
  have hsp : bv_unsigned sp < 2 ^ 64 := (u64_range sp).2
  have hKsmall : bv_unsigned (Z_to_bv 64 K) = K := u_small ⟨HK0, by omega⟩
  have hest : estart E (SA e (- K)) = bv_unsigned sp - K := by
    show bv_unsigned (edenot E e) + (- K) = bv_unsigned sp - K
    rw [He]; omega
  have hlen : elenZ E (.ELit K) = K := hKsmall
  simp only [kentry_ok]
  unfold flat
  refine ⟨?_, ?_⟩
  · rw [hest, hlen]; omega
  · intro d m Hd Hm
    rw [hlen] at Hm
    rw [hest]
    have harg : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - K + d)) = bv_unsigned sp - K + d :=
      u_small ⟨by omega, by omega⟩
    exact Hs _ m (by rw [harg]; omega) (by rw [harg]; omega)

/-! ### Introduction lemmas for the knowledge kinds -/

/-- `KWord`: a read of `w` bytes at `e + off` returns `v`'s bytes. -/
theorem kword_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (a : word) (off : Int) (w : Nat) (v : expr) (x : word)
    (He : edenot E e = a) (Hv : edenot E v = x) (Hw1 : 1 ≤ w) (Hw : w ≤ 8)
    (H1 : 0 ≤ bv_unsigned a + off) (H2 : bv_unsigned a + off + (w : Int) ≤ 2 ^ 64)
    (Hr : rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = some (word_to_le_bytes w x)) :
    kentry_ok segs E mem (.KWord (SA e off) w v) := by
  have hest : estart E (SA e off) = bv_unsigned a + off := by
    show bv_unsigned (edenot E e) + off = bv_unsigned a + off
    rw [He]
  simp only [kentry_ok]
  unfold flat
  refine ⟨Hw, ?_, ?_⟩
  · rw [hest]; omega
  · have had : adenot E (SA e off) = Z_to_bv 64 (bv_unsigned a + off) := by
      show v_addi (edenot E e) off = BitVec.ofInt 64 (bv_unsigned a + off)
      rw [He]
      rfl
    show rdn segs mem (adenot E (SA e off)) w = some (word_to_le_bytes w (edenot E v))
    rw [had, Hv]
    exact Hr

/-- `KRange`: interval knowledge about an expression. -/
theorem krange_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (lo hi : Int)
    (H : lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi) :
    kentry_ok segs E mem (.KRange e lo hi) :=
  H

/-- `KAlign`: divisibility knowledge about an expression. -/
theorem kalign_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (m : Int) (H1 : 0 < m) (H2 : bv_unsigned (edenot E e) % m = 0) :
    kentry_ok segs E mem (.KAlign e m) :=
  ⟨H1, H2⟩

/-- `KImg`: the base overlay is undefined on `lo, hi`, so reads see the
    image. -/
theorem kimg_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (lo hi : Int) (H1 : 0 ≤ lo) (H2 : hi ≤ 2 ^ 64)
    (H3 : ∀ i, lo ≤ i → i < hi → mem (Z_to_bv 64 i) = none) :
    kentry_ok segs E mem (.KImg lo hi) :=
  ⟨H1, H2, H3⟩

/-- `KZero`: `len` zero bytes at `e + off`. -/
theorem kzero_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (a : word) (off : Int) (n : expr) (len : Int)
    (He : edenot E e = a) (Hn : bv_unsigned (edenot E n) = len)
    (H1 : 0 ≤ bv_unsigned a + off) (H2 : 0 < len)
    (H3 : bv_unsigned a + off + len ≤ 2 ^ 64)
    (Hz : ∀ i, 0 ≤ i → i < len →
      mem (Z_to_bv 64 (bv_unsigned a + off + i)) = some (Z_to_bv 8 0)) :
    kentry_ok segs E mem (.KZero (SA e off) n) := by
  have hest : estart E (SA e off) = bv_unsigned a + off := by
    show bv_unsigned (edenot E e) + off = bv_unsigned a + off
    rw [He]
  have hlen : elenZ E n = len := Hn
  simp only [kentry_ok]
  unfold flat
  refine ⟨?_, ?_⟩
  · rw [hest, hlen]; omega
  · intro i h0 hi
    rw [hlen] at hi
    rw [hest]
    exact Hz i h0 hi

/-- `KBlob`: the bytes of the byte string `E.eb k` at `e + off`. -/
theorem kblob_intro (segs : List Segment) (E : env) (mem : word → Option byte)
    (e : expr) (a : word) (off : Int) (n : expr) (k : Nat) (bs : List byte)
    (He : edenot E e = a) (Hb : E.eb k = bs)
    (Hn : bv_unsigned (edenot E n) = (bs.length : Int))
    (H1 : 0 ≤ bv_unsigned a + off) (H1' : bv_unsigned a + off < 2 ^ 64)
    (H2 : bv_unsigned a + off + (bs.length : Int) ≤ 2 ^ 64)
    (Hz : ∀ i, 0 ≤ i → i < (bs.length : Int) →
      mem (Z_to_bv 64 (bv_unsigned a + off + i)) = some (bs.getD i.toNat (Z_to_bv 8 0))) :
    kentry_ok segs E mem (.KBlob (SA e off) n k) := by
  have hest : estart E (SA e off) = bv_unsigned a + off := by
    show bv_unsigned (edenot E e) + off = bv_unsigned a + off
    rw [He]
  have hlen : elenZ E n = (bs.length : Int) := Hn
  simp only [kentry_ok]
  unfold flat
  refine ⟨?_, ?_, ?_⟩
  · rw [hest, hlen]; omega
  · show ((E.eb k).length : Int) = elenZ E n
    rw [Hb, hlen]
  · intro i h0 hi
    rw [hlen] at hi
    rw [hest]
    show mem (Z_to_bv 64 (bv_unsigned a + off + i))
        = some ((E.eb k).getD i.toNat (Z_to_bv 8 0))
    rw [Hb]
    exact Hz i h0 hi

/-- **The initial memory (`wrap_mem`) is `none` away from the stack block**,
    in particular on the whole image: use for `KImg`. -/
theorem wrap_mem_none_low (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid hw : word) (rdraw : EntryDraw) (i : Int)
    (H0 : 0 ≤ i) (Hi : i < bv_unsigned sp - stack_max_size) :
    wrap_mem ph sp argv envp uid hw rdraw (Z_to_bv 64 i) = none := by
  have hsp : bv_unsigned sp < 2 ^ 64 := (u64_range sp).2
  have hspos : (0 : Int) < stack_max_size := by decide
  have Hu : bv_unsigned (Z_to_bv 64 i) = i := u_small ⟨H0, by omega⟩
  have hlt : (Z_to_bv 64 i).toNat < sp.toNat := by
    have h2 : ((Z_to_bv 64 i).toNat : Int) = i := Hu
    have h3 : i < (sp.toNat : Int) - stack_max_size := Hi
    omega
  have hsm : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw) (Z_to_bv 64 i)
      = none := by
    simp only [stack_to_mem, ite_eq_right (by omega : ¬ (sp.toNat ≤ (Z_to_bv 64 i).toNat))]
  unfold wrap_mem
  simp only [hsm]
  rw [ite_eq_right (by
    intro h
    rw [Bool.and_eq_true] at h
    have h1 : (sp.toNat : Int) - stack_max_size ≤ ((Z_to_bv 64 i).toNat : Int) :=
      of_decide_eq_true h.1
    have h2 : ((Z_to_bv 64 i).toNat : Int) = i := Hu
    have h3 : i < (sp.toNat : Int) - stack_max_size := Hi
    omega)]

/-! ### Narrow loads of small values are the identity -/

/-- A zero-extended narrow load of a small value is the value. -/
theorem ext_val_zx_id (n : Nat) (v : word) (Hv : bv_unsigned v < 2 ^ (8 * n)) :
    ext_val false 0 n v = v := by
  have h0 : 0 ≤ bv_unsigned v := Int.natCast_nonneg v.toNat
  -- `ext_Z false 0 n _` is the remainder, `lo = 0` making the shift a `/ 1`
  have key : ext_Z false 0 n (bv_unsigned v) = bv_unsigned v := by
    unfold ext_Z
    simp only [Bool.false_eq_true, ite_false]
    show bv_unsigned v / 1 % 2 ^ (8 * n) = bv_unsigned v
    rw [Int.ediv_one, Int.emod_eq_of_lt h0 Hv]
  unfold ext_val
  rw [key, Z_to_bv_unsigned]

/-- A sign-extended narrow load of a small value is the value.  (`1 ≤ n`
    keeps `8 * n - 1` away from the `Nat`-subtraction degenerate case; every
    load width is at least 1.) -/
theorem ext_val_sx_id (n : Nat) (v : word) (Hn : 1 ≤ n)
    (Hv : bv_unsigned v < 2 ^ (8 * n - 1)) : ext_val true 0 n v = v := by
  have h0 : 0 ≤ bv_unsigned v := Int.natCast_nonneg v.toNat
  have hm : 1 ≤ 8 * n := by omega
  have hsucc : (8 * n - 1).succ = 8 * n := by omega
  have hpow : (2 : Int) ^ (8 * n) = 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
    rw [← hsucc, Int.pow_succ]
    have : (2 : Int) ^ (8 * n - 1) * 2 = 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by omega
    exact this
  have hpos : (0 : Int) < 2 ^ (8 * n - 1) := Int.pow_pos (by decide)
  have hlt : bv_unsigned v < 2 ^ (8 * n) := by omega
  have key : ext_Z true 0 n (bv_unsigned v)
      = bv_swrap (8 * n) (bv_unsigned v % 2 ^ (8 * n)) := by
    unfold ext_Z
    simp only [ite_true]
    show bv_swrap (8 * n) (bv_unsigned v / 1 % 2 ^ (8 * n))
        = bv_swrap (8 * n) (bv_unsigned v % 2 ^ (8 * n))
    rw [Int.ediv_one]
  unfold ext_val
  rw [key, Int.emod_eq_of_lt h0 hlt,
    bv_swrap_small (8 * n) hm _ ⟨h0, Hv⟩, Z_to_bv_unsigned]

/-! ### Literal branch conditions

    Each lemma is a `bv_*` fact about a literal operand (`bv_eqb_lit`,
    `bv_ltu_lit_r`, `bv_ltu_lit_l` — local glue), lifted to
    `branch_taken` by `unfold branch_taken`, which reduces the six-way
    dispatch to that one comparison. -/

/-- `beq` against a literal address. -/
theorem bv_eqb_lit (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_eqb v (Z_to_bv 64 z) = (bv_unsigned v == z) := by
  unfold bv_eqb
  show decide (v = Z_to_bv 64 z) = decide (bv_unsigned v = z)
  rw [decide_eq_decide]
  constructor
  · intro h
    calc bv_unsigned v = bv_unsigned (Z_to_bv 64 z) := by rw [h]
      _ = z := u_small Hz
  · intro h
    calc v = Z_to_bv 64 (bv_unsigned v) := (Z_to_bv_unsigned v).symm
      _ = Z_to_bv 64 z := by rw [h]

/-- `bltu` against a literal RIGHT operand. -/
theorem bv_ltu_lit_r (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_ltu v (Z_to_bv 64 z) = decide (bv_unsigned v < z) := by
  have htoNat : (Z_to_bv 64 z).toNat = z.toNat := by
    show (BitVec.ofInt 64 z).toNat = z.toNat
    rw [BitVec.toNat_ofInt,
      show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl,
      Int.emod_eq_of_lt Hz.1 Hz.2]
  have hint : ((Z_to_bv 64 z).toNat : Int) = z := by
    rw [htoNat, Int.toNat_of_nonneg Hz.1]
  show decide (v.toNat < (Z_to_bv 64 z).toNat) = decide ((v.toNat : Int) < z)
  rw [decide_eq_decide]
  omega

/-- `bltu` against a literal LEFT operand. -/
theorem bv_ltu_lit_l (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_ltu (Z_to_bv 64 z) v = decide (z < bv_unsigned v) := by
  have htoNat : (Z_to_bv 64 z).toNat = z.toNat := by
    show (BitVec.ofInt 64 z).toNat = z.toNat
    rw [BitVec.toNat_ofInt,
      show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl,
      Int.emod_eq_of_lt Hz.1 Hz.2]
  have hint : ((Z_to_bv 64 z).toNat : Int) = z := by
    rw [htoNat, Int.toNat_of_nonneg Hz.1]
  show decide ((Z_to_bv 64 z).toNat < v.toNat) = decide (z < (v.toNat : Int))
  rw [decide_eq_decide]
  omega

/-- `beq` against a literal address. -/
theorem branch_eq_lit (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .EQ v (Z_to_bv 64 z) = (bv_unsigned v == z) := by
  unfold branch_taken
  exact bv_eqb_lit v z Hz

/-- `bne` against a literal address. -/
theorem branch_ne_lit (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .NE v (Z_to_bv 64 z) = !(bv_unsigned v == z) := by
  unfold branch_taken
  rw [bv_eqb_lit v z Hz]

/-- `bltu` against a literal right operand. -/
theorem branch_ltu_lit_r (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .LTU v (Z_to_bv 64 z) = decide (bv_unsigned v < z) := by
  unfold branch_taken
  exact bv_ltu_lit_r v z Hz

/-- `bltu` against a literal left operand. -/
theorem branch_ltu_lit_l (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .LTU (Z_to_bv 64 z) v = decide (z < bv_unsigned v) := by
  unfold branch_taken
  exact bv_ltu_lit_l v z Hz

/-- `bgeu` against a literal right operand. -/
theorem branch_geu_lit_r (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .GEU v (Z_to_bv 64 z) = !(decide (bv_unsigned v < z)) := by
  unfold branch_taken
  rw [bv_ltu_lit_r v z Hz]

/-- `bgeu` against a literal left operand. -/
theorem branch_geu_lit_l (v : word) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    branch_taken .GEU (Z_to_bv 64 z) v = !(decide (z < bv_unsigned v)) := by
  unfold branch_taken
  rw [bv_ltu_lit_l v z Hz]

/-! #########################################################################
    ## 5.  Three mechanical notes:
    * `split_scs` splits `scs_denot` — this tree's `scs_denot` is the
      membership predicate, not a `Forall`, so the splitter is
      `scs_denot_cons` plus the empty case, not `constructor`.
    * `ground_mod` has no direct Lean counterpart: core Lean has no
      `Int.reduceMod` and the repository has no `norm_num`, so a CLOSED
      `a % b` is not a `simp` normal form (and `omega` treats it as an
      atom).     * `lit_u` is `StepTac.u_norm`, this tree's existing normalizer for the
      `(BitVec.ofInt 64 z).toNat` projections `sc_unfold` leaves behind.
    `sym_run_tac` is NOT provided (see the file header): it applies
    `run_sound`, which is blocked on `AX2S.sym_exec_ex`.  Of the macros
    below, `split_scs` and `sc_store` carry smoke tests at the end of the
    file (a macro that is only defined is not a macro that works);
    `sc_unfold` / `ground_mod` / `lit_u` / `sc_auto` have no call site until
    `sym_run_tac` can be written and are exercised only by elaboration. -/

/-- The empty batch (local: `Forall_nil`). -/
theorem scs_denot_nil (segs : List Segment) (base : word → Option byte) (env : env) :
    scs_denot segs base env [] := by
  intro s hs
  exact (List.not_mem_nil hs).elim

/-- Split `scs_denot segs base E [s1; …; sn]` into n goals `sc_denot … si`.
-/
macro "split_scs" : tactic =>
  `(tactic|
    (simp only [scs_denot_cons, scs_denot_nil, and_true, true_and]
     try (repeat' apply And.intro)))

/-- Reduce closed `Int` remainders (see the section note). -/
macro "ground_mod" : tactic => `(tactic| (try decide))

/-- Unfold one side condition to plain arithmetic where possible. -/
macro "sc_unfold" : tactic =>
  `(tactic|
    (simp only [sc_denot, flat, estart, elenZ, adenot, v_addi, edenot, vals_ev,
        saddr.a_base, saddr.a_off, Z_to_bv_unsigned, bv_wrap64_mod]
     ground_mod))

/-- Expose `bv_unsigned (Z_to_bv 64 k)` of small literals as `Int` numerals
    (this tree's `StepTac.u_norm`). -/
macro "lit_u" : tactic => `(tactic| u_norm)

/-- `store_ok` goals: try every `stk_ok` hypothesis in context. -/
macro "sc_store" : tactic =>
  `(tactic|
    (first
     | (apply stk_ok_vaddi _ _ _ _ _ _ <;> (first | assumption | omega))
     | (apply stk_ok_lit _ _ _ _ _ _ <;> (first | assumption | omega))))

/-- Default discharger: arithmetic facts by `omega` after exposing
    `bv_unsigned (Z_to_bv 64 k)` of small literals; the caller supplies a
    tactic for `store_ok` / read-base goals (or `skip`). -/
macro "sc_auto" extra:tacticSeq : tactic =>
  `(tactic|
    (sc_unfold
     first
     | omega
     | sc_store
     | ($extra)
     | ((repeat' apply And.intro) <;> (first | omega | sc_store | ($extra)))
     | skip))

/-! ### Smoke tests for the splitter

    The rest of the tactic layer has no call site until `sym_run_tac` can be
    written, but `split_scs` does not depend on the blocked drivers and is
    checked here. -/

/-- A call site of `sc_store` in the shape the side conditions arrive: the
    window hypothesis is in context, the arithmetic is `omega`'s. -/
example (segs : List Segment) (mem : word → Option byte) (sp : word) (K off : Int)
    (n : Nat) (Hs : stk_ok segs mem sp K) (HK : K ≤ bv_unsigned sp)
    (H1 : -K ≤ off) (H2 : off + (n : Int) ≤ 0) :
    store_ok segs mem (v_addi sp off) n = true := by
  sc_store

example (segs : List Segment) (mem : word → Option byte) (E : env) :
    scs_denot segs mem E [] := by
  split_scs

example (segs : List Segment) (mem : word → Option byte) (E : env)
    (H : sc_denot segs mem E (.SCEq (.ELit 0) (.ELit 0))) :
    scs_denot segs mem E [.SCEq (.ELit 0) (.ELit 0), .SCEq (.ELit 0) (.ELit 0)] := by
  split_scs <;> exact H
