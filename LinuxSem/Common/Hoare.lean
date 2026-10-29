/-
  * Common.Hoare — a Hoare/WP-style program logic over [msteps].

  PROTOTYPE / EXPLORATION.  Image-INDEPENDENT: nothing here knows about
  any particular binary.

  The existing library models a callee as its own [msteps] lemma
  parameterized by the return address ([Common/SeqExec]).  That works,
  but every such lemma is restated per binary, at that binary's
  addresses, and it carries no discipline about WHAT the callee may
  touch — so a caller cannot reuse any fact it held about its own
  registers or memory across the call without re-deriving it.

  This file packages the same reachability content as a triple with two
  explicit FOOTPRINTS:

    [triple segs C W P a b Q]

  "from any state satisfying [P] with pc = [a], execution reaches pc =
  [b] in a state satisfying [Q], clobbering no register outside [C] and
  no memory byte outside [W]".

  The triple is DEFINED semantically over [CatSim.msteps], so it is
  sound by construction; every rule below is a lemma about that
  definition.  The footprints are what make the frame rule
  ([triple_frame]) available: a callee summary states what it touches,
  and the caller keeps everything else for free instead of the callee's
  postcondition having to re-enumerate the caller's memory.

  Partial correctness only: [triple] says nothing about executions that
  never reach [b].  That is exactly the strength the equivalence proofs
  need — they build a [to_wexit] witness, i.e. an existential run — and
  [triple_wexit] / [triple_msteps] are the two hand-offs back to the
  shape files.

  ADDRESS PARAMETRICITY.  A triple mentions the code only through the
  fetch/decode facts used to prove it.  Since the [SD_*] decode facts of
  a per-binary [*_code] are statements about the instruction WORD, and
  are therefore already binary-independent, a summary of a fixed byte
  sequence (a musl function, say) needs only the [SF_*] fetch facts as
  hypotheses, at [at_ base off].  [Common/MuslCall] carries the worked
  example.  The [at_] helpers at the bottom of this file are the address
  arithmetic that makes such a section go through with no wrap-around
  side conditions.

  NOTES.

  - `Section WithFP1`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec`,
    `CatExec`, `SeqExec` and `MmapSim` do.
  - `bvmap 5 word` (the register file) is this tree's `BvMap word`;
    `reg = bv 5`, `word = bv 64`, `byte = bv 8` are the `Riscv.Prelude`
    abbreviations.
  - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_unsigned w` is
    `(w.toNat : Int)`, `Z.of_nat n` is `(n : Int)`, `length` is
    `List.length`, `lia` is `omega`, `vm_compute; reflexivity` is
    `decide`.
  - `mst_refl`/`mst_step` are the constructors `msteps.mst_refl`/
    `msteps.mst_step`; `MachineOk` is `machine_result.MachineOk`
    (spelled `.MachineOk`); `wbytes` is `CatExec.wbytes`, `rdn` is
    `PropExec.rdn`; `getr`/`regupd` are `PropExec.getr`/`regupd`.
  - `Z.land z (-2)` (the [jalr] target's clear-bit-0 mask) is
    [PropExec.zland_m2] in this tree — `z - z % 2`, the exact
    two's-complement identity, so [land_m2_even] is stated over
    `zland_m2` and its proof is the `z % 2 = 0` case of the definition
    rather than a chain of bitwise library lemmas.
  - The nested interval `(0 <= i < Z.of_nat n)%Z` is curried as
    `0 ≤ i → i < (n : Int) →...`, the shape this tree's `rdn` lemmas
    use (see `Common/MemsetLib`).
  - This is the module that supplies the `triple` / `frameable` / `ret_ok`
    vocabulary the not-yet-written `Common/MuslCall` defers its five
    `musl_*` lemmas to (`musl_write_enter`/`_leave`/`_wexit`/`_wall`/
    `_frame`): `proc` + `triple_call` is the call rule, `triple_frame` plus
    the `frameable_*` combinators the frame rule, and `at_`/`at_addi`/
    `at_at` the address arithmetic a musl summary is stated at.
-/
import LinuxSem.Common.SeqExec

set_option autoImplicit false
-- Same rationale as `PropExec`/`CatExec`/`SeqExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.Hoare

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec

section WithFP1

variable [fx : FPState]

/-! ## `ofInt` / `toNat` bridges (local helpers) -/

/-- The `toNat` of an `ofInt` at width 64, as the `Int` remainder: 
    inline `Z_to_bv_unsigned`. -/
theorem toNat64_ofInt (z : Int) :
    ((BitVec.ofInt 64 z).toNat : Int) = z % ((2 ^ 64 : Nat) : Int) := by
  rw [BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

/-- `ofInt` of a word's own unsigned value is that word: inline
    `Z_to_bv_unsigned` + `bv_wrap_small` pair. -/
theorem ofInt64_toNat (a : word) : BitVec.ofInt 64 ((a.toNat : Int)) = a := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq a

/-- The `Int` reading of `(a + 1).toNat`: inline
    `bv_add_unsigned` plus `bv_unsigned (1 : word) = 1`. -/
theorem toNat64_add_one (a : word) :
    (((a + 1).toNat : Nat) : Int) = ((a.toNat : Int) + 1) % ((2 ^ 64 : Nat) : Int) := by
  rw [BitVec.toNat_add, Int.natCast_emod]
  rfl

/- =========================================================================
   Address arithmetic for address-parametric summaries
   ========================================================================= -/

/-- [at_ base d] is [base + d], the address of the instruction at byte
    offset [d] of a relocatable code blob loaded at [base].  All the
    lemmas below are wrap-around-free BY CONSTRUCTION (the underlying
    [Z_to_bv] wraps), so an address-parametric summary needs NO bound on
    [base]. -/
def at_ (base : word) (d : Int) : word := BitVec.ofInt 64 ((base.toNat : Int) + d)

theorem at_0 (base : word) : at_ base 0 = base := by
  unfold at_
  rw [Int.add_zero]
  exact ofInt64_toNat base

/-- The workhorse: stepping the pc by any (possibly negative) displacement
    stays inside the [at_] normal form.  Covers [v_addi pc 4] from every
    straight-line step lemma and [btgt pc imm] from every jump/branch. -/
theorem at_addi (base : word) (d e : Int) : v_addi (at_ base d) e = at_ base (d + e) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 64 ((BitVec.ofInt 64 ((base.toNat : Int) + d)).toNat + e)).toNat
      = (BitVec.ofInt 64 ((base.toNat : Int) + (d + e))).toNat
  rw [toNat64_ofInt, BitVec.toNat_ofInt, BitVec.toNat_ofInt, Int.emod_add_emod,
    Int.add_assoc]

theorem at_btgt (base : word) (d e : Int) : btgt (at_ base d) e = at_ base (d + e) :=
  at_addi base d e

/-- [at_] of a literal base collapses to a literal address — this is the
    one-line bridge a per-binary instantiation uses to feed its [SF_*]
    fetch lemmas to an address-parametric summary. -/
theorem at_lit (base : word) (d : Int) (a : word)
    (H : BitVec.ofInt 64 ((base.toNat : Int) + d) = a) : at_ base d = a := H

/-- [at_] composes: an offset from an already-offset address.  ([v_addi]
    and [at_] are the same function, so this IS [at_addi].) -/
theorem at_at (base : word) (d e : Int) : at_ (at_ base d) e = at_ base (d + e) :=
  at_addi base d e

/-- Byte-walk helpers: [wbytes]/[rdn] recurse on [a + 1], so every proof
    about a byte RANGE has to re-normalize [bv_unsigned (a + 1) + i]. -/
theorem u_succ_shift (a : word) (i : Int) :
    BitVec.ofInt 64 (((a + 1).toNat : Int) + i)
      = BitVec.ofInt 64 ((a.toNat : Int) + (1 + i)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, toNat64_add_one, Int.emod_add_emod]
  congr 2
  omega

theorem at_self (a : word) : BitVec.ofInt 64 ((a.toNat : Int) + 0) = a :=
  at_0 a

/- =========================================================================
   Assertions and footprints
   ========================================================================= -/

/-- An assertion talks about the register file, the writable memory
    overlay and the read-only image.  It deliberately does NOT talk about
    the pc: the pc is the triple's index, exactly as in a Hoare logic for
    machine code. -/
abbrev assn := BvMap word → (word → Option byte) → (word → Option byte) → Prop

/-- Footprints: which registers a fragment may clobber, and which memory
    bytes it may write.  Both are plain predicates, so [fun _ => True] is
    "anything" and set union is [\/]. -/
abbrev regset := reg → Prop
abbrev memset := word → Prop

def regs_agree (C : regset) (regs regs' : BvMap word) : Prop :=
  ∀ r, ¬ C r → getr regs' r = getr regs r

def mem_agree (W : memset) (m m' : word → Option byte) : Prop :=
  ∀ x, ¬ W x → m' x = m x

theorem regs_agree_refl (C : regset) (regs : BvMap word) : regs_agree C regs regs :=
  fun _ _ => rfl

theorem mem_agree_refl (W : memset) (m : word → Option byte) : mem_agree W m m :=
  fun _ _ => rfl

theorem regs_agree_trans (C : regset) (regs1 regs2 regs3 : BvMap word)
    (H1 : regs_agree C regs1 regs2) (H2 : regs_agree C regs2 regs3) :
    regs_agree C regs1 regs3 := by
  intro r Hr
  rw [H2 r Hr]
  exact H1 r Hr

theorem mem_agree_trans (W : memset) (m1 m2 m3 : word → Option byte)
    (H1 : mem_agree W m1 m2) (H2 : mem_agree W m2 m3) : mem_agree W m1 m3 := by
  intro x Hx
  rw [H2 x Hx]
  exact H1 x Hx

theorem regs_agree_mono (C C' : regset) (regs regs' : BvMap word)
    (Hsub : ∀ r, C r → C' r) (H : regs_agree C regs regs') : regs_agree C' regs regs' :=
  fun r Hr => H r (fun h => Hr (Hsub r h))

theorem mem_agree_mono (W W' : memset) (m m' : word → Option byte)
    (Hsub : ∀ x, W x → W' x) (H : mem_agree W m m') : mem_agree W' m m' :=
  fun x Hx => H x (fun h => Hx (Hsub x h))

/-- The two shapes an actual step chain produces.  A register writeback is
    a [regupd]; a store is a [wbytes].  These turn "the final state is this
    concrete chain of updates" into the agreement facts a triple owes. -/
theorem regs_agree_upd (C : regset) (regs regs' : BvMap word) (r : reg) (v : word)
    (Hin : C r) (H : regs_agree C regs regs') :
    regs_agree C regs (regupd regs' r v) := by
  intro s Hs
  have hne : s ≠ r := fun h => Hs (h ▸ Hin)
  rw [getr_other regs' r v s hne]
  exact H s Hs

theorem mem_agree_wbytes (W : memset) (m m' : word → Option byte) (a : word)
    (bs : List byte)
    (Hin : ∀ i, 0 ≤ i → i < (bs.length : Int) →
      W (BitVec.ofInt 64 ((a.toNat : Int) + i)))
    (H : mem_agree W m m') : mem_agree W m (wbytes m' a bs) := by
  have main : ∀ (bs : List byte) (a : word) (m' : word → Option byte),
      (∀ i, 0 ≤ i → i < (bs.length : Int) →
        W (BitVec.ofInt 64 ((a.toNat : Int) + i))) →
      mem_agree W m m' → mem_agree W m (wbytes m' a bs) := by
    intro bs
    induction bs with
    | nil => intro a m' Hin H; exact H
    | cons b bs ih =>
      intro a m' Hin H
      have Ha : W a := by
        have h0 := Hin 0 (by omega) (by simp)
        rwa [at_self] at h0
      refine ih (a + 1) (fun a' => if bv_eqb a' a then some b else m' a') ?_ ?_
      · intro i h0 h1
        rw [u_succ_shift]
        exact Hin (1 + i) (by omega) (by simp [List.length_cons]; omega)
      · intro x hx
        simp only []
        by_cases hb : bv_eqb x a = true
        · rw [ite_eq_left hb]
          exfalso
          have hxa : x = a := by simpa [bv_eqb] using hb
          exact hx (by rw [hxa]; exact Ha)
        · rw [ite_eq_right hb]
          exact H x hx
  exact main bs a m' Hin H

/- =========================================================================
   The triple
   ========================================================================= -/

/-- [triple segs C W P a b Q]: from every [P]-state at pc [a] there is an
    [msteps] run to pc [b] landing in [Q], touching only [C] and [W].

    The read-only image [rom] is quantified inside and threaded unchanged:
    [msteps] never writes it, so it is an assertion PARAMETER rather than
    part of the mutable state. -/
def triple (segs : List Segment) (C : regset) (W : memset) (P : assn)
    (a b : word) (Q : assn) : Prop :=
  ∀ regs mem rom, P regs mem rom →
    ∃ regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      ∧ Q regs' mem' rom
      ∧ regs_agree C regs regs'
      ∧ mem_agree W mem mem'

/-- Introduction: this is the definition, but naming it keeps the
    per-summary proof scripts readable (and stable if [triple] gains a
    field). -/
theorem triple_intro (segs : List Segment) (C : regset) (W : memset) (P : assn)
    (a b : word) (Q : assn)
    (H : ∀ regs mem rom, P regs mem rom →
      ∃ regs' mem',
        msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
        ∧ Q regs' mem' rom
        ∧ regs_agree C regs regs'
        ∧ mem_agree W mem mem') :
    triple segs C W P a b Q := H

/- ------------------------------------------------------------------
   Structural rules
   ------------------------------------------------------------------ -/

/-- SKIP. -/
theorem triple_skip (segs : List Segment) (C : regset) (W : memset) (P : assn)
    (a : word) : triple segs C W P a a P := by
  intro regs mem rom HP
  exact ⟨regs, mem, msteps.mst_refl _, HP, regs_agree_refl C regs, mem_agree_refl W mem⟩

/-- SEQUENCING.  The footprints add up; use [triple_seq_same] when they
    are already the same set. -/
theorem triple_seq (segs : List Segment) (C1 : regset) (W1 : memset) (C2 : regset)
    (W2 : memset) (P Q R : assn) (a b c : word)
    (H1 : triple segs C1 W1 P a b Q) (H2 : triple segs C2 W2 Q b c R) :
    triple segs (fun r => C1 r ∨ C2 r) (fun x => W1 x ∨ W2 x) P a c R := by
  intro regs mem rom HP
  obtain ⟨regs1, mem1, Hst1, HQ, Hr1, Hm1⟩ := H1 regs mem rom HP
  obtain ⟨regs2, mem2, Hst2, HR, Hr2, Hm2⟩ := H2 regs1 mem1 rom HQ
  refine ⟨regs2, mem2, msteps_trans segs _ _ _ Hst1 Hst2, HR, ?_, ?_⟩
  · exact regs_agree_trans _ _ _ _
      (regs_agree_mono C1 (fun r => C1 r ∨ C2 r) regs regs1 (fun r h => Or.inl h) Hr1)
      (regs_agree_mono C2 (fun r => C1 r ∨ C2 r) regs1 regs2 (fun r h => Or.inr h) Hr2)
  · exact mem_agree_trans _ _ _ _
      (mem_agree_mono W1 (fun x => W1 x ∨ W2 x) mem mem1 (fun x h => Or.inl h) Hm1)
      (mem_agree_mono W2 (fun x => W1 x ∨ W2 x) mem1 mem2 (fun x h => Or.inr h) Hm2)

/-- CONSEQUENCE, both on the assertions and (weakening) on the
    footprints. -/
theorem triple_conseq (segs : List Segment) (C C' : regset) (W W' : memset)
    (P P' Q Q' : assn) (a b : word)
    (H : triple segs C W P a b Q)
    (HP : ∀ regs mem rom, P' regs mem rom → P regs mem rom)
    (HQ : ∀ regs mem rom, Q regs mem rom → Q' regs mem rom)
    (HC : ∀ r, C r → C' r)
    (HW : ∀ x, W x → W' x) :
    triple segs C' W' P' a b Q' := by
  intro regs mem rom HP'
  obtain ⟨regs', mem', Hst, HQ0, Hr, Hm⟩ := H regs mem rom (HP regs mem rom HP')
  exact ⟨regs', mem', Hst, HQ regs' mem' rom HQ0,
    regs_agree_mono C C' regs regs' HC Hr, mem_agree_mono W W' mem mem' HW Hm⟩

theorem triple_seq_same (segs : List Segment) (C : regset) (W : memset) (P Q R : assn)
    (a b c : word)
    (H1 : triple segs C W P a b Q) (H2 : triple segs C W Q b c R) :
    triple segs C W P a c R := by
  intro regs mem rom HP
  obtain ⟨regs1, mem1, Hst1, HQ, Hr1, Hm1⟩ := H1 regs mem rom HP
  obtain ⟨regs2, mem2, Hst2, HR, Hr2, Hm2⟩ := H2 regs1 mem1 rom HQ
  exact ⟨regs2, mem2, msteps_trans segs _ _ _ Hst1 Hst2, HR,
    regs_agree_trans C _ _ _ Hr1 Hr2, mem_agree_trans W _ _ _ Hm1 Hm2⟩

/- ------------------------------------------------------------------
   The frame rule
   ------------------------------------------------------------------ -/

/-- [R] is FRAMEABLE past a fragment with footprints [(C, W)] when it is
    stable under any change confined to those footprints.  This is the
    "separation-logic-lite" of the design: there is no [*] connective and
    no heap splitting, but the caller-side obligation is exactly the one
    [*] would generate — [R] must not look at what the callee writes. -/
def frameable (C : regset) (W : memset) (R : assn) : Prop :=
  ∀ regs mem rom regs' mem',
    regs_agree C regs regs' → mem_agree W mem mem' →
    R regs mem rom → R regs' mem' rom

/-- FRAME. -/
theorem triple_frame (segs : List Segment) (C : regset) (W : memset) (P Q R : assn)
    (a b : word)
    (H : triple segs C W P a b Q) (HR : frameable C W R) :
    triple segs C W (fun regs mem rom => P regs mem rom ∧ R regs mem rom) a b
                    (fun regs mem rom => Q regs mem rom ∧ R regs mem rom) := by
  intro regs mem rom HP
  obtain ⟨HP0, HRr⟩ := HP
  obtain ⟨regs', mem', Hst, HQ, Hr, Hm⟩ := H regs mem rom HP0
  exact ⟨regs', mem', Hst, ⟨HQ, HR regs mem rom regs' mem' Hr Hm HRr⟩, Hr, Hm⟩

/-- Frameability combinators.  These are what a caller actually uses: a
    register outside the clobber set keeps its value; a byte range outside
    the write set keeps its contents; and anything about [rom] alone is
    always frameable. -/
theorem frameable_and (C : regset) (W : memset) (R1 R2 : assn)
    (H1 : frameable C W R1) (H2 : frameable C W R2) :
    frameable C W (fun regs mem rom => R1 regs mem rom ∧ R2 regs mem rom) := by
  intro regs mem rom regs' mem' Hr Hm HR
  obtain ⟨A, B⟩ := HR
  exact ⟨H1 regs mem rom regs' mem' Hr Hm A, H2 regs mem rom regs' mem' Hr Hm B⟩

theorem frameable_reg (C : regset) (W : memset) (r : reg) (v : word)
    (Hnc : ¬ C r) : frameable C W (fun regs _ _ => getr regs r = v) := by
  intro regs mem rom regs' mem' Hr _ Hv
  rw [Hr r Hnc]
  exact Hv

/-- A byte-range read is frameable when the range misses the write set.
    Stated over [rdn], the library's memory read, so it composes with the
    existing read-back lemmas. -/
theorem frameable_rdn (segs : List Segment) (C : regset) (W : memset) (a : word)
    (n : Nat) (bs : List byte)
    (Hdisj : ∀ i, 0 ≤ i → i < (n : Int) → ¬ W (BitVec.ofInt 64 ((a.toNat : Int) + i))) :
    frameable C W (fun _ mem _ => rdn segs mem a n = some bs) := by
  intro regs mem rom regs' mem' _ Hm Hrd
  rw [← Hrd]
  clear Hrd bs
  have main : ∀ (n : Nat) (a : word),
      (∀ i, 0 ≤ i → i < (n : Int) → ¬ W (BitVec.ofInt 64 ((a.toNat : Int) + i))) →
      rdn segs mem' a n = rdn segs mem a n := by
    intro n
    induction n with
    | zero => intro a Hdisj; rfl
    | succ n ih =>
      intro a Hdisj
      have Ha : ¬ W a := by
        have h0 := Hdisj 0 (by omega) (by simp)
        rwa [at_self] at h0
      simp only [rdn]
      rw [Hm a Ha]
      rw [ih (a + 1) ?_]
      intro i h0 h1
      rw [u_succ_shift]
      exact Hdisj (1 + i) (by omega) (by omega)
  exact main n a Hdisj

/- ------------------------------------------------------------------
   The call rule
   ------------------------------------------------------------------ -/

/-- [ret_ok k]: [k] is a legal [ret] target, i.e. [jalr x0, 0(ra)] with
    [ra = k] lands on [k].  The ISA model masks bit 0, so this is
    "[k] is even" — always true of a real return address, and discharged
    by [bveq] whenever [k] is a literal. -/
def ret_ok (k : word) : Prop := v_jalr k 0 = k

theorem land_m2_even (z : Int) (Hz : z % 2 = 0) : zland_m2 z = z := by
  unfold zland_m2
  rw [Hz, Int.sub_zero]

theorem ret_ok_even (k : word) (Hk : (k.toNat : Int) % 2 = 0) : ret_ok k := by
  unfold ret_ok v_jalr jalr_tgtZ
  rw [Int.add_zero, land_m2_even _ Hk]
  exact ofInt64_toNat k

/-- A PROCEDURE summary: the address-parametric form.  [proc segs C W P
    entry Q] says the callee, entered at [entry] with a legal return
    address in [ra], returns to that address — whatever it is.  This is
    the shape a musl function is proved in once. -/
def proc (segs : List Segment) (C : regset) (W : memset) (P : assn) (entry : word)
    (Q : assn) : Prop :=
  ∀ k : word, ret_ok k →
    triple segs C W (fun regs mem rom => P regs mem rom ∧ getr regs 1 = k) entry k Q

/-- [P] does not look at [ra] — the caller's precondition cannot, since
    the [jal] overwrites it. -/
def ra_indep (P : assn) : Prop :=
  ∀ regs v mem rom, P regs mem rom → P (regupd regs 1 v) mem rom

/-- CALL.  [callsite] holds a [jal ra, entry] (any instruction that links
    [ret] into [ra] and jumps to [entry] without touching memory — the
    first hypothesis says exactly that, and is discharged by
    [SeqExec.step_jal_link] plus the binary's fetch/decode facts).  The
    resulting triple runs from the call site to the instruction after it,
    and clobbers [C] plus [ra].

    Note what the caller gets for free: every register outside [C] — sp
    and the callee-saved [s*] in a well-behaved callee — is preserved by
    the triple's own [regs_agree] component, with no help from [Q]. -/
theorem triple_call (segs : List Segment) (C : regset) (W : memset) (P Q : assn)
    (callsite entry ret : word)
    (Hjal : ∀ regs mem rom,
      RiscvSemantics.step segs (mkst regs callsite mem rom)
        = .MachineOk (mkst (regupd regs 1 ret) entry mem rom))
    (Hret : ret_ok ret)
    (HraP : ra_indep P)
    (Hproc : proc segs C W P entry Q) :
    triple segs (fun r => C r ∨ r = 1) W P callsite ret Q := by
  intro regs mem rom HP
  have Hpre : P (regupd regs 1 ret) mem rom ∧ getr (regupd regs 1 ret) 1 = ret := by
    refine ⟨HraP regs ret mem rom HP, ?_⟩
    exact getr_same regs 1 ret (by decide)
  obtain ⟨regs', mem', Hst, HQ, Hr, Hm⟩ := Hproc ret Hret (regupd regs 1 ret) mem rom Hpre
  refine ⟨regs', mem', ?_, HQ, ?_, Hm⟩
  · exact msteps.mst_step _ _ _ rfl (Hjal regs mem rom) Hst
  · intro r Hr0
    have HnC : ¬ C r := fun h => Hr0 (Or.inl h)
    have Hne : r ≠ 1 := fun h => Hr0 (Or.inr h)
    rw [Hr r HnC, getr_other regs 1 ret r Hne]

/- ------------------------------------------------------------------
   The loop rule
   ------------------------------------------------------------------ -/

/-- LOOP, in the measure-decreasing form the compiled loops actually have:
    the invariant is indexed by a [nat] measure, one body iteration
    returns to the loop head with the measure decreased by one, and the
    measure-zero case exits.

    This replaces the hand-rolled induction each looping example carries
    ([DrainSim]'s per-iteration lemma, [MuslStrlen]'s chunk walk,
    ...): the caller supplies the two hypotheses and gets the whole loop. -/
theorem triple_loop (segs : List Segment) (C : regset) (W : memset) (I : Nat → assn)
    (hd out : word) (Q : assn)
    (Hbody : ∀ i, triple segs C W (I (i + 1)) hd hd (I i))
    (Hexit : triple segs C W (I 0) hd out Q) :
    ∀ n, triple segs C W (I n) hd out Q := by
  intro n
  induction n with
  | zero => exact Hexit
  | succ n ih =>
    exact triple_seq_same segs C W (I (n + 1)) (I n) Q hd hd out (Hbody n) ih

/-- The same, with the measure read off the state instead of supplied by
    the caller: [Inv] holds now, and every state satisfying [Inv] has SOME
    measure. -/
theorem triple_loop_measure (segs : List Segment) (C : regset) (W : memset)
    (I : Nat → assn) (hd out : word) (Q P : assn)
    (Hbody : ∀ i, triple segs C W (I (i + 1)) hd hd (I i))
    (Hexit : triple segs C W (I 0) hd out Q)
    (Hmeas : ∀ regs mem rom, P regs mem rom → ∃ n, I n regs mem rom) :
    triple segs C W P hd out Q := by
  intro regs mem rom HP
  obtain ⟨n, HI⟩ := Hmeas regs mem rom HP
  exact triple_loop segs C W I hd out Q Hbody Hexit n regs mem rom HI

/- ------------------------------------------------------------------
   Hand-off to the behaviour-shape relations
   ------------------------------------------------------------------ -/

/-- Forget the footprints: a triple is an [msteps] lemma of the shape the
    existing example proofs consume. -/
theorem triple_msteps (segs : List Segment) (C : regset) (W : memset) (P : assn)
    (a b : word) (Q : assn) (regs : BvMap word) (mem rom : word → Option byte)
    (H : triple segs C W P a b Q) (HP : P regs mem rom) :
    ∃ regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom) ∧ Q regs' mem' rom := by
  obtain ⟨regs', mem', Hst, HQ, _, _⟩ := H regs mem rom HP
  exact ⟨regs', mem', Hst, HQ⟩

/-- Prepend a triple to a [to_wexit] derivation: this is how a summary
    whose tail is an [ecall] hands off to [CatSim]'s syscall constructors
    ([tw_write_ret], [tw_exit_coden]).  The continuation is given the
    postcondition and must produce the rest of the behaviour. -/
theorem triple_wexit (segs : List Segment) (C : regset) (W : memset) (P : assn)
    (a b : word) (Q : assn) (bufs : List (List byte)) (code : word)
    (regs : BvMap word) (mem rom : word → Option byte)
    (H : triple segs C W P a b Q) (HP : P regs mem rom)
    (Hcont : ∀ regs' mem', Q regs' mem' rom →
      to_wexit segs (mkst regs' b mem' rom) bufs code) :
    to_wexit segs (mkst regs a mem rom) bufs code := by
  obtain ⟨regs', mem', Hst, HQ, _, _⟩ := H regs mem rom HP
  exact msteps_to_wexit segs _ _ bufs code Hst (Hcont regs' mem' HQ)

/-! -/

example (segs : List Segment) (C : regset) (W : memset) (P : assn) (a : word) :
    triple segs C W P a a P :=
  triple_skip segs C W P a

example (base : word) (d : Int) (a : word)
    (h : BitVec.ofInt 64 ((base.toNat : Int) + d) = a) : at_ base d = a :=
  at_lit base d a h

example : at_ (16 : word) 8 = 24 := by decide

example : at_ (0 : word) (-8) = BitVec.ofInt 64 (-8) := by decide

example : at_ (BitVec.ofInt 64 (-1)) 1 = 0 := by decide

example : ret_ok (16 : word) := ret_ok_even 16 (by decide)

end WithFP1

end LinuxSem.Common.Hoare
