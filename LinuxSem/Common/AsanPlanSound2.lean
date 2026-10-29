/-

  * (node_join_sound, sys dispatcher, cs_ok_set_kn)

  * AsanPlanSound2 — more proved node obligations of
    [AsanPlanSound.APS.check_sound]: [node_join_sound : join_stmt] (PJoin).
  of the same name.

  WHAT THIS FILE IS.  `AsanPlanSound.check_sound` takes one hypothesis per
  plan-node shape (`AsanPlanSound.join_stmt`, `mm2_stmt`, … — the
  `AsanNodesIface.OBL_*` statements).  This file discharges TWO of them that
  need no image-specific reasoning because they only READ the knowledge:

  - `node_join_sound : join_stmt` — the `PJoin b off n` node (`AsanPlanCore
    §8`, `AsanPlanCore.node_join`): the `n <= 8` bytes at `b+off` are each
    read as a LITERAL through the knowledge stack (`kread_bytes`), and the
    joined little-endian word becomes ONE knowledge fact
    `KWord (SA b off) n (ELit (zbytes_le_to_Z zs))`.  The proof is the
    checker-state tuple: `node_join` is deterministic (a single successor),
    `cs_ok` re-establishes its `co_know` field from `kread_bytes_sound`, and
    the rest of `cs_ok` is `cs_ok_set_kn`.
  - the two byte lemmas the join needs (`bytes_le_to_Z_cons`,
    `Z_to_le_bytes_to_Z`) plus `kread_bytes_sound` (each 1-byte `kreadZ` is
    the overlay byte) and `rdn_of_bytes1` (n consecutive 1-byte reads
    compose to the n-byte read), which `node_join_sound` uses to build the
    `kentry_ok` of the new `KWord` entry.
      Variable SEGS : list Segment.            Variable A : atable.
      Variable nx0 : nat.                      Variable LIMIT : Z.
      Variable SINV : env -> (word -> option byte) -> Prop.
      Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
      #[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
 `A`, `nx0`, `LIMIT`,
  `SINV`, `argH`, `FS0` are unused by the two byte lemmas, so they are not
  parameters there — the same "skipping the ones it does not use" rule the
  `AsanPlanSound` header states.
  NOTES.
  - `Z` is `Int`, `nat` is `Nat`, `word` is `BitVec 64`, `byte` is
    `BitVec 8`, `bv_unsigned w` is `(w.toNat : Int)`, `Z_to_bv 64 z` is
    `BitVec.ofInt 64 z`, `length` is `List.length`, `map` is `List.map`,
    `nth j l d` is `l.getD j d`, `2 ^ 64` on `Int` is `two64`
    (`AxSymExec3.two64 = 2 ^ 64`).
 `bytes_le_to_Z_cons` and `Z_to_le_bytes_to_Z` are proved
    from that recursion alone — the same three `private` helpers
    (`bytes_le_to_Nat_cons`, `toNat_ofInt_8_nat`, `int_shiftRight_8_natCast`)
    `Sys/Uapi.lean` and `Common/LibWritev.lean` carry for the same reason.
  - `omega` cannot use `2 ^ 64` written as a `Nat` power (it drops the
    hypothesis); this tree keeps every `2 ^ 64` in `Int` form and states the
    one place a numeral is needed (`8 < two64`) as `by decide`.
  - HELPERS.     `word_to_le_bytes_zbytes` is the other helper (also `private`):
     closes the join's byte equation inline (`rewrite <- Mb,
    zbytes_map; … apply Z_to_le_bytes_to_Z`), and this tree factors that chain
    into one named lemma so the `Int`/`Nat` cast bookkeeping is stated once.
  - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanPlanSound2

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

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asanplansound2_fx : PropExec.FPState := PropExec.fx0

/-! ## Little-endian byte lemmas (`bytes_le_to_Z_cons`) -/

/-- A byte's unsigned value is below 256. -/
private theorem byte_lt_256 (b : byte) : b.toNat < 256 := by
  have := b.isLt
  rw [show (2 ^ 8 : Nat) = 256 by decide] at this
  exact this

/-- little-endian bytes: arithmetic form of the cons case -/
theorem bytes_le_to_Z_cons (b : byte) (bs : List byte) :
    bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256 := by
  unfold bytes_le_to_Z
  rw [bytes_le_to_Nat_cons]
  simp only [Int.natCast_add, Int.natCast_mul, bv_unsigned]
  omega

/-! ## `Z_to_le_bytes_to_Z` -/

/- The low byte of a `Nat` as `Z_to_le_bytes` encodes it, and its `>>> 8`
   shift, are the canonical `BvBase.toNat_ofInt_8_nat` and
   `BvBase.int_shiftRight_8_natCast`, imported and opened here. -/

/-- The byte `Z_to_le_bytes` emits first is the low byte. -/
private theorem low_byte_of_add_mul (b : byte) (N : Nat) :
    BitVec.ofInt 8 ((N * 256 + b.toNat : Nat) : Int) = b := by
  apply BitVec.toNat_inj.mp
  rw [toNat_ofInt_8_nat]
  rw [show (N * 256 + b.toNat) % 256 = b.toNat from by
    rw [Nat.mul_add_mod_self_right]
    exact Nat.mod_eq_of_lt (byte_lt_256 b)]

/-- The byte `Z_to_le_bytes` drops is the quotient by 256. -/
private theorem div256_add_mul (b : byte) (N : Nat) :
    (N * 256 + b.toNat) / 256 = N := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < 256),
    Nat.div_eq_of_lt (byte_lt_256 b), Nat.zero_add]

/-- The round trip at `Nat` (the `Int` statement follows definitionally). -/
private theorem Z_to_le_bytes_to_Z_nat (bs : List byte) :
    Z_to_le_bytes bs.length ((bytes_le_to_Nat bs : Nat) : Int) = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    rw [List.length_cons, bytes_le_to_Nat_cons]
    rw [Z_to_le_bytes]
    rw [int_shiftRight_8_natCast, div256_add_mul]
    rw [low_byte_of_add_mul]
    rw [ih]

/-- round trip: the n little-endian bytes of [bytes_le_to_Z bs] are [bs] -/
theorem Z_to_le_bytes_to_Z (bs : List byte) :
    Z_to_le_bytes bs.length (bytes_le_to_Z bs) = bs :=
  Z_to_le_bytes_to_Z_nat bs

/-! ## `kread_bytes_sound` -/

/-- each byte read through [kreadZ .. 1] is the overlay byte -/
theorem kread_bytes_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (n : Nat) :
    ∀ (b : expr) (off : Int) (zs : List Int),
      know_ok segs E M k →
      kread_bytes segs n k b off = some zs →
      0 ≤ estart E (SA b off) → estart E (SA b off) + (n : Int) ≤ 2 ^ 64 →
      ∃ (bs : List byte), bs.length = n ∧ bs.map bv_unsigned = zs ∧
        ∀ j, j < n → rdn segs M (Z_to_bv 64 (estart E (SA b off) + (j : Int))) 1 =
          some [bs.getD j (Z_to_bv 8 0)] := by
  induction n with
  | zero =>
    intro b off zs HK Hr Hlo Hhi
    have hzs : zs = [] := by
      have h : kread_bytes segs 0 k b off = some ([] : List Int) := rfl
      rw [h] at Hr
      exact (Option.some.inj Hr).symm
    subst hzs
    exact ⟨[], rfl, rfl, by intro j hj; omega⟩
  | succ n ih =>
    intro b off zs HK Hr Hlo Hhi
    -- split the fuel: the first byte and the rest of the run
    obtain ⟨z, rest, hz, hrest, hzs⟩ :
        ∃ (z : Int) (rest : List Int), kreadZ segs k b off 1 = some z ∧
          kread_bytes segs n k b (off + 1) = some rest ∧ z :: rest = zs := by
      simp only [kread_bytes] at Hr
      cases h1 : kreadZ segs k b off 1 with
      | none => rw [h1] at Hr; simp at Hr
      | some z =>
        cases h2 : kread_bytes segs n k b (off + 1) with
        | none => rw [h1, h2] at Hr; simp at Hr
        | some rest =>
          rw [h1, h2] at Hr
          simp only [Option.some.injEq] at Hr
          exact ⟨z, rest, rfl, rfl, Hr⟩
    subst hzs
    have hhi' : estart E (SA b off) + (n : Int) + 1 ≤ 2 ^ 64 := by
      simp only [Int.natCast_add, Int.natCast_one] at Hhi
      omega
    have hfl1 : flat E (SA b off) 1 := by
      unfold flat
      refine ⟨Hlo, by omega, by omega, by omega⟩
    -- the first byte, resolved through the knowledge
    have KL := know_lookup_sound segs E k M b off 1 false [] [] HK (by omega) (by omega)
    rw [kreadZ] at hz
    cases hlk : know_lookup segs k b off 1 false [] [] with
    | LHit v scs nx =>
      rw [hlk] at hz
      cases v with
      | ELit zl =>
        cases scs with
        | nil =>
          simp only [Option.some.injEq] at hz
          rw [hlk] at KL
          obtain ⟨bs1, R1, L1, V1⟩ := KL (by simp [scs_denot]) hfl1
          obtain ⟨b0, rfl⟩ : ∃ b0, bs1 = [b0] := by
            cases bs1 with
            | nil => simp at L1
            | cons b0 tl =>
              cases tl with
              | nil => exact ⟨b0, rfl⟩
              | cons _ _ => simp at L1
          simp only [List.length_cons, List.length_nil] at L1
          -- `V1`: the literal read back is the byte
          have hzext : extz false 1 (bytes_le_to_Z [b0]) = bv_unsigned b0 := by
            unfold extz
            simp only [Bool.false_eq_true, ite_false, bytes_le_to_Z_cons, bytes_le_to_Z,
              bytes_le_to_Nat, Nat.zero_shiftLeft, Nat.or_zero, Int.natCast_zero,
              Int.mul_zero, Int.add_zero, bv_unsigned]
          have hbnd : bv_unsigned b0 < two64 := by
            have h1 : bv_unsigned b0 < (256 : Int) := by
              have := byte_lt_256 b0
              simp only [bv_unsigned]
              omega
            have h2 : (256 : Int) ≤ two64 := by unfold two64; decide
            unfold two64 at *
            omega
          have hval : bv_unsigned b0 = z := by
            have hV := congrArg bv_unsigned V1
            rw [edenot_lit, u_lit64, u_lit64, hzext] at hV
            rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hbnd] at hV
            exact hV.trans hz
          -- the rest of the run
          obtain ⟨bs, Lb, Mb, Rb⟩ := ih b (off + 1) rest HK hrest (by
            simp only [estart, SA] at *
            omega) (by
            simp only [estart, SA] at *
            omega)
          refine ⟨b0 :: bs, by simp [Lb], ?_, ?_⟩
          · simp only [List.map_cons]
            rw [Mb, hval]
          · intro j hj
            cases j with
            | zero =>
              simp only [List.getD_cons_zero, Int.natCast_zero, Int.add_zero]
              exact R1
            | succ j =>
              simp only [List.getD_cons_succ]
              have harg : estart E (SA b off) + ((j + 1 : Nat) : Int) =
                  estart E (SA b (off + 1)) + (j : Int) := by
                simp only [estart, SA, Int.natCast_add, Int.natCast_one]
                omega
              rw [harg, ← Rb j (by omega)]
        | cons _ _ => simp at hz
      | EVar _ => simp at hz
      | EAlu _ _ _ => simp at hz
      | EAluw _ _ _ => simp at hz
      | EMd _ _ _ => simp at hz
      | EMdw _ _ _ => simp at hz
      | EExt _ _ _ _ => simp at hz
      | EBlob _ _ _ _ => simp at hz
    | LMiss _ _ => rw [hlk] at hz; simp at hz
    | LStuck => rw [hlk] at hz; simp at hz

/-! ## `rdn_of_bytes1` -/

/-- n consecutive 1-byte reads compose to the n-byte read -/
theorem rdn_of_bytes1 (segs : List Segment) (M : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte),
      bs.length = n → bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      (∀ j, j < n → rdn segs M (Z_to_bv 64 (bv_unsigned a + (j : Int))) 1 =
        some [bs.getD j (Z_to_bv 8 0)]) →
      rdn segs M a n = some bs := by
  induction n with
  | zero =>
    intro a bs Hlen Hnw Hpt
    cases bs with
    | nil => rfl
    | cons b bs' => simp at Hlen
  | succ n ih =>
    intro a bs Hlen Hnw Hpt
    cases bs with
    | nil => simp at Hlen
    | cons b bs' =>
      have Hlen' : bs'.length = n := by simp only [List.length_cons] at Hlen; omega
      have H0 := Hpt 0 (by omega)
      simp only [Int.natCast_zero, Int.add_zero, List.getD_cons_zero] at H0
      have H0' : rdn segs M a 1 = some [b] := by
        rw [← ofInt_toNat a]
        exact H0
      cases n with
      | zero =>
        cases bs' with
        | nil => exact H0'
        | cons _ _ => simp at Hlen'
      | succ n' =>
        refine rdn_cons1 (segs := segs) (mem := M) (a := a) (n := Nat.succ n') (b := b)
          (bs := bs') H0' ?_
        -- the fuel is at least 2, so `a + 1` does not wrap
        have hlt : bv_unsigned a + 1 < (2 : Int) ^ 64 := by
          have h2 := Hnw
          push_cast at h2
          have hn : (0 : Int) ≤ (n' : Int) := Int.natCast_nonneg n'
          omega
        have hsucc : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a hlt
        refine ih (a + 1) bs' Hlen' ?_ ?_
        · rw [hsucc]
          have h2 := Hnw
          push_cast at h2 ⊢
          omega
        · intro j hj
          have h := Hpt (j + 1) (by omega)
          rw [hsucc]
          have hcast : bv_unsigned a + 1 + (j : Int) =
              bv_unsigned a + ((j + 1 : Nat) : Int) := by
            push_cast
            omega
          rw [hcast]
          simpa [List.getD_cons_succ] using h

/-! ## `node_join_sound` -/

/-- `8 * len <= 64` at the byte bound `n <= 8`. -/
private theorem pow_le_two64 (bs : List byte) (n : Nat) (Hn : n ≤ 8)
    (Lb : bs.length = n) : (2 : Int) ^ (8 * bs.length) ≤ two64 := by
  have h1 : 2 ^ (8 * bs.length) ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : ((2 ^ (8 * bs.length) : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) :=
    Int.ofNat_le.mpr h1
  calc (2 : Int) ^ (8 * bs.length) = ((2 ^ (8 * bs.length) : Nat) : Int) := by
        rw [Int.natCast_pow]; rfl
    _ ≤ ((2 ^ 64 : Nat) : Int) := h2
    _ = two64 := rfl

/-- A byte list's `Int` value, read back as its 64-bit word's `Nat`. -/
private theorem toNat_Z_to_bv_bytes (bs : List byte) (Hsmall : bytes_le_to_Z bs < two64) :
    ((Z_to_bv 64 (bytes_le_to_Z bs)).toNat : Int) = bytes_le_to_Z bs := by
  rw [BitVec.toNat_ofInt, show ((2 ^ 64 : Nat) : Int) = two64 from rfl,
    Int.emod_eq_of_lt (AxSymExec3Sound.bytes_le_to_Z_bound bs).1 Hsmall]
  exact Int.toNat_of_nonneg (AxSymExec3Sound.bytes_le_to_Z_bound bs).1

/-- `word_to_le_bytes` of the joined literal is the byte list.
     closes this inline in `node_join_sound` (`rewrite <- Mb,
    zbytes_map` … `apply Z_to_le_bytes_to_Z`); this tree states the same chain
    once, so the `Int`/`Nat` cast bookkeeping is in one place. -/
private theorem word_to_le_bytes_zbytes (n : Nat) (bs : List byte) (zs : List Int)
    (Hn : n ≤ 8) (Lb : bs.length = n) (Mb : bs.map bv_unsigned = zs) :
    word_to_le_bytes n (Z_to_bv 64 (zbytes_le_to_Z zs)) = bs := by
  have hbnd := AxSymExec3Sound.bytes_le_to_Z_bound bs
  have hsmall : bytes_le_to_Z bs < two64 := by
    have h := pow_le_two64 bs n Hn Lb
    omega
  have hem : bytes_le_to_Z bs % two64 = bytes_le_to_Z bs :=
    Int.emod_eq_of_lt hbnd.1 hsmall
  have hz : zbytes_le_to_Z zs = bytes_le_to_Z bs % two64 := by
    rw [← Mb, zbytes_map]
  rw [word_to_le_bytes, hz, hem, toNat_Z_to_bv_bytes bs hsmall, ← Lb]
  exact Z_to_le_bytes_to_Z bs

/-- `node_join_sound` — `PJoin` (`AP.node_join`). -/
theorem node_join_sound (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    join_stmt segs A nx0 LIMIT SINV argH FS0 := by
  intro b off n cs cs' E R FULL model T HC _ Hn Hk
  simp only [node_join] at Hn
  split at Hn
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨H1, H8⟩, Hfx⟩ := hg
    cases Hr : kread_bytes segs n (kn cs) b off with
    | none => rw [Hr] at Hn; simp at Hn
    | some zs =>
      rw [Hr] at Hn
      simp only [Option.some.injEq] at Hn
      obtain rfl : cs' = add_kn cs
          [kentry.KWord (SA b off) n (expr.ELit (zbytes_le_to_Z zs))] := Hn.symm
      have HK : know_ok segs E (Mr A argH E cs model FULL) (kn cs) := HC.co_know
      obtain ⟨F1, F2, F3⟩ :=
        flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs) b off
          (expr.ELit (n : Int)) HK Hfx
      have hsmall_n : (n : Int) < two64 := by
        have h : (8 : Int) < two64 := by unfold two64; decide
        omega
      have hnn : bv_unsigned (edenot E (expr.ELit (n : Int))) = (n : Int) := by
        rw [edenot_lit, u_lit64, Int.emod_eq_of_lt (Int.natCast_nonneg n) hsmall_n]
      have F2' : estart E (SA b off) + (n : Int) ≤ 2 ^ 64 := by rw [hnn] at F2; exact F2
      have F3' : 0 < (n : Int) := by rw [hnn] at F3; exact F3
      have Hflat : flat E (SA b off) (n : Int) :=
        ⟨F1, by omega, by omega, F2'⟩
      obtain ⟨bs, Lb, Mb, Rb⟩ :=
        kread_bytes_sound segs E (Mr A argH E cs model FULL) (kn cs) n b off zs HK Hr
          F1 F2'
      -- the continuation, at the successor state
      refine Hk E R FULL model ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ ?_ rfl
      unfold add_kn
      refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model
        ([kentry.KWord (SA b off) n (expr.ELit (zbytes_le_to_Z zs))] ++ kn cs) HC ?_
      show know_ok segs E (Mr A argH E cs model FULL)
        (kentry.KWord (SA b off) n (expr.ELit (zbytes_le_to_Z zs)) :: kn cs)
      intro K' hK'
      rcases List.mem_cons.mp hK' with rfl | hK'
      · -- the new entry: the joined word
        simp only [kentry_ok]
        refine ⟨H8, Hflat, ?_⟩
        rw [rdn_of_bytes1 segs (Mr A argH E cs model FULL) n (adenot E (SA b off)) bs Lb
          (by rw [flat_u E (SA b off) (n : Int) Hflat]; exact F2')
          (by intro j hj; rw [flat_u E (SA b off) (n : Int) Hflat]; exact Rb j hj)]
        simp only [Option.some.injEq]
        exact (word_to_le_bytes_zbytes n bs zs H8 Lb Mb).symm
      · exact HK K' hK'
  · exact absurd Hn (by simp)

end LinuxSem.Common.AsanPlanSound2

