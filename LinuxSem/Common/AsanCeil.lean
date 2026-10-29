/-
  * Common.AsanCeil — the reflective ASan plan checker's CONSTANT allocation
    ceiling and floor, bridged to the run-dependent spec.

  The reflective ASan automation (AsanPlanCore / AsanPlan / AsanPlanSound /
  the AsanNodes* files) assumes that every anonymous grant ends below the
  CONSTANT [alloc_ceiling = 0x7fff7f800000] and that first-fit placement
  starts at [bottomup_floor = 0x2aaaaaaab000].  The spec instead bounds
  grants by [State.alloc_top h = vm_init_sp h - stack_max_size] (the RUN's
  stack pointer) and has no floor (placement is admissibility, not a
  search).  The checker keeps its numeric constants
  ([AsanPlanCore.CEIL] / [FLOOR]); soundness needs only that the constant
  ceiling lies at or below the spec's: for every admissible run
  [sp >= sp_window_lo = 0x7fff80000000] ([Run.valid_sp]), hence
  [alloc_top h = sp - 8 MiB >= 0x7fff7f800000 = alloc_ceiling], exactly, and the
  stack pointer field of the ledger never changes after [init_model].

  [init_sp_ok h] is the invariant the node soundness proofs carry (it is a
  conjunct of [BackingAlgebra.model_ivs_wf]); [alloc_ceiling_le_alloc_top]
  turns a [<= alloc_ceiling] side condition into the spec's [<= alloc_top h].
  [hint_placement_ok_b] is the first-fit placement gate that the checker's
  boolean grant tests use; the spec has no such gate.

  NOTES.  Notation, imports, and proof strategy only; no definition is
  weakened and no statement is changed beyond the `Nat.testBit` carrier
  noted below.

  - Values are `Int`, counts `Nat`, words `BitVec 64`, bytes `BitVec 8`
    (from `Riscv.Prelude`); `BitVec.ofInt n z` makes a word out of an `Int`
    and `(w.toNat : Int)` reads one unsigned; the list side is
    `List.replicate` / `List.take` / `List.drop` / `List.getD`.
  - `!` is `Bool.not`, and a bound test is `decide (a ≤ b)`.
  - The bit test is `c.toNat.testBit 5`, not `c.testBit 5`: `Int` has no
    `testBit` in Lean core.  `c` is non-negative here (`mmap_flags_core`
    subtracts a submask of `flags.toNat`), so the `Nat` bit test on `c.toNat`
    is the same bit — the same shim applied at a non-negative argument.
  - The numeric helpers (`page_size`, `page_round_up_Z`, `stack_max_size`,
    `sp_window_lo`, `two_pow_64`, `VmMaps`) are in
    `LinuxProcessSem.State`, `alloc_top`/`m_vmmaps`/`mkModel` in
    `StateLedger`, `region_free` in `StateVm`, `init_model` in `StateInit`.
    `StackLayout`, `Run`, `Sys.Syscall`, `Sys.Uapi` and `Sys.Mm.Mmap` supply
    the remaining names.
  - `page_round_up_Z_ge_all`: `page_size` is a definition here, so the
    `0 ≤ z` hypothesis of the general form is not needed;
    `PlacementSearch.page_round_up_Z_ge` had already observed this, and the
    lemma below is the same unconditional statement (proved inline with the
    same arithmetic).  Likewise `page_round_up_Z_aligned'` repeats
    `PlacementSearch.page_round_up_Z_aligned` here rather than restating
    it under a primed name.
  - `mmap_anon_b_of_core`: the proof goes through `Nat`'s bit lemmas on
    `mmap_flags_core`'s subtraction form — clearing MAP_NORESERVE (bit 14)
    leaves every bit below 14 untouched, so bit 5 survives.
  - `init_sp_ok_init_model`: `init_model` wraps the record in setters that
    touch other subsystems (`m_proc`, `m_io`, `m_lim`) only, so the `m_vm`
    field — and hence `vm_init_sp` — is copied definitionally.
-/

import LinuxSem.Common.PlacementSearch
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap

set_option autoImplicit false

open LinuxSem.Riscv

namespace LinuxSem.Common.AsanCeil

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Common.PlacementSearch

/-- the checker's constant ceiling -/
def alloc_ceiling : Int := 0x7fff7f800000

theorem alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000 := rfl

/-- the bottom-up placement floor [page_round_up_Z (task_size_min / 3)] for
    an Sv48 task size (2^47 / 3 rounded up = 0x2aaaaaaab000).  The spec has no
    such floor.  Equals the
    checker's [AsanPlanCore.FLOOR]; the ASan layout lemma
    [AsanPlacement.kHighMemBeg_below_mmap_base_min] needs [mmap_base_min < bottomup_floor]. -/
def bottomup_floor : Int := 0x2aaaaaaab000

theorem bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000 := rfl

/- ## A first-fit placement gate, stated over [Common.PlacementSearch]

    The gate [hint_placement_ok_b]: a NULL-hint
    grant lands at or above the bottom-up floor, or no higher free gap exists below the
    recorded [vm_mmap_base] (the top-down search's postcondition).  In the spec,
    placement is pure admissibility, with no such gate.  The ASan plan checker
    RELIES on the gate (every NULL-hint grant is modelled above [kHighMemBeg], below
    [alloc_ceiling]), so the node-soundness layer takes it as ONE named hypothesis,
    [placement_policy], instead of reading it off the spec.  Discharging that hypothesis
    is a question about the spec, not a proof step. -/

/-- A NULL-hint grant lands at or above the bottom-up floor, or no higher
    free gap exists below the recorded [vm_mmap_base]. -/
def placement_ok (h : VmMaps) (aZ nZ : Int) : Prop :=
  bottomup_floor ≤ aZ ∨
  no_higher_fit (h.vm_reserved ++ h.vm_maps) aZ nZ ((h.vm_mmap_base).toNat : Int)

def placement_ok_b (h : VmMaps) (aZ nZ : Int) : Bool :=
  decide (bottomup_floor ≤ aZ) ||
  !(higher_fit_b (h.vm_reserved ++ h.vm_maps) aZ nZ ((h.vm_mmap_base).toNat : Int))

theorem placement_ok_b_iff (h : VmMaps) (aZ nZ : Int)
    (HaPos : 0 ≤ aZ) (HnPos : 0 < nZ)
    (HaAl : aZ % page_size = 0) (HnAl : nZ % page_size = 0) :
    placement_ok_b h aZ nZ = true ↔ placement_ok h aZ nZ := by
  have hb : ((h.vm_mmap_base).toNat : Int) < two_pow_64 := by
    have hlt := h.vm_mmap_base.isLt
    unfold two_pow_64
    omega
  -- `!x = true` is stated on the `Bool` carrier here rather than as a
  -- negated proposition: `Bool.not_eq_true` is `simp`'s rewrite, and the
  -- `Bool.not` spelling keeps it syntactically matched to
  -- `placement_ok_b`'s body.
  have hnot : (Bool.not (higher_fit_b (h.vm_reserved ++ h.vm_maps) aZ nZ
      ((h.vm_mmap_base).toNat : Int)) = true) ↔
      (higher_fit_b (h.vm_reserved ++ h.vm_maps) aZ nZ
        ((h.vm_mmap_base).toNat : Int) = false) := by simp
  unfold placement_ok_b placement_ok
  rw [Bool.or_eq_true, hnot,
    no_higher_fit_iff (h.vm_reserved ++ h.vm_maps) aZ nZ ((h.vm_mmap_base).toNat : Int)
      HaPos HnPos HaAl HnAl hb,
    decide_eq_true_eq]

theorem placement_ok_b_of_floor (h : VmMaps) (aZ nZ : Int)
    (H : bottomup_floor ≤ aZ) : placement_ok_b h aZ nZ = true := by
  unfold placement_ok_b
  simp [H]

/-- The gate the checker's boolean grant tests use: a non-NULL hint is
    accepted unconditionally; a NULL hint is accepted per [placement_ok_b]. -/
def hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Int) : Bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true

theorem hint_placement_ok_b_of_floor (addr : word) (h : VmMaps) (aZ nZ : Int)
    (H : bottomup_floor ≤ aZ) : hint_placement_ok_b addr h aZ nZ = true := by
  unfold hint_placement_ok_b
  cases hw : w_is0 addr with
  | false => rfl
  | true => simp [placement_ok_b_of_floor h aZ nZ H]

theorem hint_placement_ok_b_nonnull (addr : word) (h : VmMaps) (aZ nZ : Int)
    (H : w_is0 addr = false) : hint_placement_ok_b addr h aZ nZ = true := by
  unfold hint_placement_ok_b
  simp [H]

/- THE HYPOTHESIS.  Every admissible NULL-hint grant of the spec ([Mmap.mmap_spec]:
    page-aligned, nonzero, ending at or below [alloc_top h], free) also (i) ends at or
    below the constant ceiling [alloc_ceiling] and (ii) satisfies the first-fit gate.
    Both describe a kernel's placement
    POLICY, which the spec does not pin down.  The ASan node soundness
    ([AsanNodesMmLib]/[AsanNodesMmA]) is parametric in it. -/

def placement_policy : Prop :=
  ∀ (h : VmMaps) (a : word) (nZ : Int),
    0 < nZ → nZ % page_size = 0 →
    (a.toNat : Int) % page_size = 0 → 0 < (a.toNat : Int) →
    (a.toNat : Int) + nZ ≤ alloc_top h →
    region_free (h.vm_reserved ++ h.vm_maps) a (BitVec.ofInt 64 nZ) = true →
    (a.toNat : Int) + nZ ≤ alloc_ceiling ∧
      placement_ok_b h (a.toNat : Int) nZ = true

/-- the ledger's stack pointer is an admissible one -/
def init_sp_ok (h : VmMaps) : Prop := sp_window_lo ≤ (h.vm_init_sp).toNat

theorem alloc_ceiling_le_alloc_top (h : VmMaps) (H : init_sp_ok h) :
    alloc_ceiling ≤ alloc_top h := by
  unfold init_sp_ok at H
  unfold alloc_top alloc_ceiling stack_max_size sp_window_lo at *
  omega

theorem alloc_top_ge_of_ceiling (h : VmMaps) (z : Int) (H : init_sp_ok h)
    (Hz : z ≤ alloc_ceiling) : z ≤ alloc_top h :=
  Int.le_trans Hz (alloc_ceiling_le_alloc_top h H)

theorem init_sp_ok_init_model (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) (H : Run.valid_sp sp) :
    init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  unfold init_sp_ok
  simp [m_vmmaps, init_model, with_abort_terminal, with_sigmask, with_nofile,
    with_net, with_urandom, with_creds]
  exact H.1

/-- every ledger update of the spec and of the checker copies [vm_init_sp] -/
theorem init_sp_ok_same (h h' : VmMaps) (E : h'.vm_init_sp = h.vm_init_sp)
    (H : init_sp_ok h) : init_sp_ok h' := by
  unfold init_sp_ok at *
  rw [E]
  exact H

theorem init_sp_ok_mkVmMapsFull (h : VmMaps) (r m na : List (word × word))
    (sb b : word) (l : Int) (mb : word) (H : init_sp_ok h) :
    init_sp_ok (VmMaps.mkVmMapsFull r m na sb b l mb h.vm_init_sp) := by
  unfold init_sp_ok at *
  simpa using H

/-- The bound holds for every [z].  (`page_size` is a definition, so no
    [0 <= z] hypothesis is needed: this is the unconditional form of
    [State.page_round_up_Z_ge].) -/
theorem page_round_up_Z_ge_all (z : Int) : z ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  have hdm := Int.mul_ediv_add_emod (z + 4096 - 1) 4096
  have h0 := Int.emod_nonneg (z + 4096 - 1) (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos (z + 4096 - 1) (b := 4096) (by decide)
  omega

/- ## Two [check_mmap] gates, for the node lemmas that unfold the checker -/

theorem mmap_off_aligned_b_0 : mmap_off_aligned_b (BitVec.ofInt 64 0) = true := by
  decide

/-- [MAP_ANONYMOUS] (bit 5) survives [mmap_flags_core] (which only clears MAP_NORESERVE, bit 14)

    The bit test is stated as `c.toNat.testBit 5 = true` because Lean core's `Int`
    has no `testBit`.  Here `c` is
    `flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)`, hence non-negative, so
    `Nat.testBit` on `c.toNat` is the same bit . -/
theorem mmap_anon_b_of_core (flags : word) (c : Int)
    (Hc : mmap_flags_core flags = c) (Hb : c.toNat.testBit 5 = true) :
    mmap_anon_b flags = true := by
  -- `mmap_flags_core` is `flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)`;
  -- clearing bit 14 leaves every bit below it — bit 5 included — untouched.
  have hmn : MAP_NORESERVE.toNat = 16384 := by decide
  have hman : MAP_ANONYMOUS.toNat = 32 := by decide
  have hc' : c = (flags.toNat : Int) -
      (((flags.toNat &&& MAP_NORESERVE.toNat) : Nat) : Int) := by
    rw [← Hc]
    rfl
  have hct : c.toNat = flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat) := by
    rw [hc']
    exact Int.toNat_sub _ _
  rw [hct] at Hb
  have hle : flags.toNat &&& MAP_NORESERVE.toNat ≤ flags.toNat := Nat.and_le_left
  have h16384 : (16384 : Nat) % 2 ^ 6 = 0 := by decide
  have hm64 : (flags.toNat &&& MAP_NORESERVE.toNat) % 2 ^ 6 = 0 := by
    rw [hmn, Nat.and_mod_two_pow, h16384, Nat.and_zero]
  -- the low six bits of `a - (a &&& 16384)` are those of `a`
  have hmod : (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) % 2 ^ 6 =
      flags.toNat % 2 ^ 6 := by
    calc (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) % 2 ^ 6
        = ((flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) % 2 ^ 6) % 2 ^ 6 :=
          (Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))).symm
      _ = (((flags.toNat &&& MAP_NORESERVE.toNat) % 2 ^ 6) +
            (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) % 2 ^ 6) % 2 ^ 6 := by
          rw [hm64, Nat.zero_add]
      _ = ((flags.toNat &&& MAP_NORESERVE.toNat) +
            (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat))) % 2 ^ 6 :=
          (Nat.add_mod _ _ _).symm
      _ = flags.toNat % 2 ^ 6 := by rw [Nat.add_sub_cancel' hle]
  have h63 : flags.toNat &&& (2 ^ 6 - 1) =
      (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) &&& (2 ^ 6 - 1) := by
    rw [Nat.and_two_pow_sub_one_eq_mod flags.toNat 6,
      Nat.and_two_pow_sub_one_eq_mod
        (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat)) 6]
    exact hmod.symm
  have hb63 : (2 ^ 6 - 1 : Nat).testBit 5 = true := by decide
  have ha5 : flags.toNat.testBit 5 = true := by
    have h := congrArg (fun x : Nat => x.testBit 5) h63
    rw [Nat.testBit_and, Nat.testBit_and, hb63, Hb] at h
    simpa using h
  have hx5 : (flags.toNat &&& MAP_ANONYMOUS.toNat).testBit 5 = true := by
    rw [Nat.testBit_and, ha5, hman]
    rfl
  have hne : flags.toNat &&& MAP_ANONYMOUS.toNat ≠ 0 := by
    intro h0
    rw [h0] at hx5
    simp at hx5
  unfold mmap_anon_b land_ne0
  simp [hne]

/-- rounding facts the node files use (see also Common.AllocSim/PlacementSearch) -/
theorem page_round_up_Z_aligned' (z : Int) : page_round_up_Z z % page_size = 0 := by
  unfold page_round_up_Z
  rw [Int.mul_comm]
  exact Int.mul_emod_right page_size ((z + page_size - 1) / page_size)

theorem page_round_up_Z_pos' (z : Int) (Hz : 0 < z) : 0 < page_round_up_Z z := by
  have h := page_round_up_Z_ge_all z
  omega

/- ## The AT_RANDOM bytes are a draw

  The 16 bytes the auxv AT_RANDOM entry points at are the fourth [Run.ExecEntry]
  field [en_random], quantified per binary.  The initial knowledge
  [AsanPlanCore.init_kn_zero] asserts that they are ZERO.  The soundness lemma for that entry
  ([AsanInit.atrandom_zero_ok]) therefore holds only under this NAMED hypothesis, which is
  FALSE on every real run: a certificate built on the base [init_kn_zero] proves a
  conditional statement that establishes nothing about the real binary.  Its only purpose is
  to keep certificates built on that base checkable.  The DEFAULT base [init_kn]
  is faithful — the block is byte string [AsanPlanCore.K_RND], bound to the draw — and needs
  no hypothesis. -/

def zero_random_draw (rdraw : BitVec 128) : Prop := rdraw = BitVec.ofInt 128 0

theorem at_random_bytes_zero :
    at_random_bytes (BitVec.ofInt 128 0) = List.replicate 16 (BitVec.ofInt 8 0) := by
  decide

/-- one byte of a byte string, as the slice [RefLayout.at_random_off] reads it -/
theorem firstn1_skipn_nth (l : List byte) (i : Nat) (d : byte) (Hi : i < l.length) :
    (l.drop i).take 1 = [l.getD i d] := by
  induction l generalizing i with
  | nil => simp at Hi
  | cons x l ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i (by simpa using Hi)

end LinuxSem.Common.AsanCeil
