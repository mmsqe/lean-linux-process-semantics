/-
  * Common.AllocSim — union-of-resolutions glue for brk-allocating binaries.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Outcomes are `(List (List byte) × word)` pairs (buffers of `byte`
    bytes, exit code a `word`); break values, requests and growth amounts
    are `word`s; all no-wrap bookkeeping (allocation ceiling, wraparound
    detection, interval bounds) is in `Int` over `toNat`.  Following the
    CatSim conventions the brk syscall number is Int-characterized: the
    `tou_brk` node (and every brk decoding lemma) carries a pending number
    `x8` with `(x8.toNat : Int) = 214`.

    A binary that allocates its output buffer with `brk` does not have a
    single deterministic trace: the environment resolves each brk call
    (Mmap.brk_spec), so the observable behavior is a UNION over
    resolutions of (write buffers, exit code) outcomes.  This file
    provides:

    - `to_outcomes segs ms model U`: from machine state `ms` and model
      `model`, the reachable set of (bufs, code) outcomes is EXACTLY `U`.
      Leaves are `WallSim.to_wallexit` retry loops, which re-offer what a
      short write left behind until the whole buffer is out, so a leaf
      still pins one `(bufs, code)` outcome; interior nodes are brk
      syscalls branching over every admissible resolution.
    - the trace characterization (`alloc_obs_iff`): `obs_trace` is
      exactly the prefixes of `wevents bufs ++ [ExitEv code (in_fs inp)]` for
      outcomes in `U`; plus no-error (`alloc_no_error_run`).  The retry
      loop puts the whole buffer out, so this file quantifies over
      outcomes alone — the per-delivery choices (`CatSim.wpick`) are
      already discharged inside `to_wallexit` and appear nowhere here.
    - the `Equivalence.equiv`-level glue (`alloc_strong_equiv`): two
      binaries with the SAME outcome set are observably equivalent.
    - brk-spec decoding helpers (`brk_ok_iff`, `tou_brk_r`) so per-binary
      proofs work with the resolved break value `r` directly, and the
      `apply_zeros`/`zmem` memory theory for the zero-backed grant.

    NOTES.
 `to_outcomes`, `outcome_trace`'s companions and the
      `to_outcomes_*` family all take `segs` first, so the deferred
      `ShapeAlg` bridges (`AllocSim.to_outcomes segs ms model U`,
      `AllocSim.outcome_trace fs o`) match the spelling they expect.
    - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`; `bv_unsigned w` is
      `(w.toNat : Int)`; `lia` is `omega`; `bv_eq`-style word arithmetic
      is `bv_omega`; `functional_extensionality` is `funext`.
    - `m_vmmaps m` is a `VmMaps` record, so `vm_brk (m_vmmaps m)` is
      `(m_vmmaps m).vm_brk`; the `mkVmMapsFull` constructor is
      `VmMaps.mkVmMapsFull` / the anonymous constructor.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Mm.Mmap
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.WallSim

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.AllocSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Common.SimInv
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.WallSim
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

section WithFP1

variable [fx : FPState]

/- =========================================================================
   Local word-algebra helpers (candidates to lift into BvBase/PropExec if a
   second Common file needs them).
   ========================================================================= -/

/-- Unsigned value of a non-wrapping `bv` sum. -/
theorem u_add_small (a b : word)
    (H : (a.toNat : Int) + (b.toNat : Int) < 2 ^ 64) :
    ((a + b).toNat : Int) = (a.toNat : Int) + (b.toNat : Int) := by
  have hnat : a.toNat + b.toNat < 2 ^ 64 := by
    have := H
    push_cast at this
    omega
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnat]
  push_cast
  rfl

theorem word_add_0_r (a : word) : a + BitVec.ofInt 64 0 = a := by
  bv_omega

/-- `r + t - r = t` in the additive group of `bv 64` (no side conditions). -/
theorem word_add_sub_cancel (r t : word) : r + t - r = t := by
  bv_omega

theorem word_neq0_unsigned (r : word) (Hne : r ≠ BitVec.ofInt 64 0) :
    (r.toNat : Int) ≠ 0 := by
  intro Hu
  apply Hne
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  omega

/-- Address-walk step for `wbytes_app` (`nat_to_word` offset form). -/
theorem word_add_nat_S (a : word) (k : Nat) :
    (a + 1) + nat_to_word k = a + nat_to_word (k + 1) := by
  have h1 : (1 : word) = nat_to_word 1 := rfl
  rw [h1, nat_to_word_add_merge]
  congr 2
  omega

/- =========================================================================
   apply_zeros / zmem: the zero-backed grant as a functional overlay.
   ========================================================================= -/

/-- The zero-fill of a single granted range `b, b+l)`.  Coverage is checked
    in `Int` over unsigned values, mirroring `Run.zeros_cover` (grant ranges
    never wrap). -/
def zmem (mem : word → Option byte) (b l : word) : word → Option byte :=
  fun a =>
    if decide ((b.toNat : Int) ≤ (a.toNat : Int)) &&
       decide ((a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int))
    then some (BitVec.ofInt 8 0) else mem a

theorem apply_zeros_nil (mem : word → Option byte) : apply_zeros mem [] = mem := rfl

theorem apply_zeros_one (mem : word → Option byte) (b l : word) :
    apply_zeros mem [(b, l)] = zmem mem b l := by
  funext a
  simp only [apply_zeros, zeros_cover, zmem, List.any_cons, List.any_nil,
    Bool.or_false]

theorem zmem_out (mem : word → Option byte) (b l : word) (a : word)
    (Hd : (a.toNat : Int) < (b.toNat : Int) ∨
          (b.toNat : Int) + (l.toNat : Int) ≤ (a.toNat : Int)) :
    zmem mem b l a = mem a := by
  unfold zmem
  rcases Hd with Hd | Hd
  · have E : decide ((b.toNat : Int) ≤ (a.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [E]
    rfl
  · have E : decide ((a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int)) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [E, Bool.and_false]
    rfl

/-- No-overflow hypothesis (inherited from `rdn_ext`); trivial at
    call sites — the read window sits far below 2^64. -/
theorem rdn_zmem_out (segs : List Segment) (mem : word → Option byte)
    (b l : word) (a : word) (n : Nat)
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hd : (a.toNat : Int) + (n : Int) ≤ (b.toNat : Int) ∨
          (b.toNat : Int) + (l.toNat : Int) ≤ (a.toNat : Int)) :
    rdn segs (zmem mem b l) a n = rdn segs mem a n := by
  apply rdn_ext segs n
  · exact Hnw
  · intro x Hx
    apply zmem_out
    omega

theorem rdn_zmem_in1 (segs : List Segment) (mem : word → Option byte)
    (b l : word) (a : word)
    (Hin : (b.toNat : Int) ≤ (a.toNat : Int) ∧
           (a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int)) :
    rdn segs (zmem mem b l) a 1 = some [BitVec.ofInt 8 0] := by
  obtain ⟨Hlo, Hhi⟩ := Hin
  have h1 : decide ((b.toNat : Int) ≤ (a.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hlo
  have h2 : decide ((a.toNat : Int) < (b.toNat : Int) + (l.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hhi
  have hz : zmem mem b l a = some (BitVec.ofInt 8 0) := by
    unfold zmem
    rw [h1, h2]
    rfl
  simp only [rdn, hz]

/-- wbytes over a split list — lets a store loop accumulate one flat
    `wbytes` over the granted region. -/
theorem wbytes_app {bs1 bs2 : List byte} (m : word → Option byte) (a : word) :
    wbytes m a (bs1 ++ bs2) =
      wbytes (wbytes m a bs1) (a + nat_to_word bs1.length) bs2 := by
  induction bs1 generalizing m a with
  | nil =>
    simp only [List.nil_append, wbytes, List.length_nil]
    rw [word_add_0]
  | cons b bs ih =>
    simp only [List.cons_append, wbytes, List.length_cons]
    rw [ih, word_add_nat_S, Nat.add_comm bs.length 1]

/- =========================================================================
   Model plumbing for a brk transition.
   ========================================================================= -/

theorem with_vmmaps_fds (h : VmMaps) (m : Model) : m_fds (with_vmmaps h m) = m_fds m :=
  rfl

theorem with_vmmaps_fs (h : VmMaps) (m : Model) : m_fs (with_vmmaps h m) = m_fs m :=
  rfl

theorem with_vmmaps_halted (h : VmMaps) (m : Model) :
    m_halted (with_vmmaps h m) = m_halted m := rfl

theorem with_vmmaps_vm (h : VmMaps) (m : Model) : m_vmmaps (with_vmmaps h m) = h := rfl

theorem with_vmmaps_lazy (h : VmMaps) (m : Model) :
    m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := rfl

theorem fd1chan_with_vmmaps (h : VmMaps) (m : Model) (H : fd1chan m) :
    fd1chan (with_vmmaps h m) := by
  unfold fd1chan at *
  exact H

theorem m_fds_vm_forget_range (lo hi : Int) (m : Model) :
    m_fds (vm_forget_range lo hi m) = m_fds m := rfl

/-- VM lifecycle cleanup rewrites only the sparse-backing ledgers, so it
    carries the fd table across unchanged. -/
theorem fd1chan_forget_vm_ranges (ranges : List (word × word)) (m : Model)
    (H : fd1chan m) : fd1chan (forget_vm_ranges ranges m) := by
  induction ranges generalizing m with
  | nil => exact H
  | cons p rest ih =>
    obtain ⟨a, n⟩ := p
    simp only [forget_vm_ranges]
    apply ih
    unfold fd1chan at H ⊢
    rw [m_fds_vm_forget_range]
    exact H

/-- advance-past-svc of a brk effect applied at the raw ecall record. -/
theorem adv_brk (regs : BvMap word) (pc : word) (x8 : word)
    (mem rom : word → Option byte) (r : word) (zs : List (word × word)) :
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some x8, ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom } (mkEffect r [] zs))
    = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom := by
  have h10 : bv_eqb (10 : reg) 0 = false := bv_eqb_neq _ _ (by decide)
  simp only [apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc,
    h10, apply_writes, apply_copies, apply_unmaps, mkEffect, Bool.false_eq_true,
    reduceIte, mkst, regupd, b_npc4]


/- =========================================================================
   brk syscall-spec decoding, through the verified checker.
   =========================================================================

   The spec-level gates are named once here: this file shadows `brk_r_ok`
   and `brk_grow_ok` with the `VmMaps`-level twins the pure outcome algebra
   uses (`AllocSim.brk_r_ok`, `AllocSim.brk_grow_ok`), so every proof that
   has to speak about the LIVE-state gate goes through these two aliases. -/

/-- `Mmap.brk_r_ok` at a live model. -/
abbrev mmap_brk_r_ok (m : Model) (req r : word) : Bool :=
  LinuxSem.LinuxProcessSem.Sys.Mm.Mmap.brk_r_ok m req r

/-- `Mmap.brk_grow_ok` at a live model. -/
abbrev mmap_brk_grow_ok (m : Model) (req r : word) : Bool :=
  LinuxSem.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok m req r

/-- The three Linux paths of `brk_r_ok`, unfolded once: a query/invalid
    request keeps the break, a shrink resolves to the request or fails, and
    a grow does the same under the physical gate. -/
theorem mmap_brk_r_ok_eq (m : Model) (req r : word) :
    mmap_brk_r_ok m req r =
      (if w_is0 req ||
          decide ((req.toNat : Int) < ((min_brk (m_vmmaps m)).toNat : Int)) then
        r == (m_vmmaps m).vm_brk
      else if decide ((req.toNat : Int) < ((m_vmmaps m).vm_brk.toNat : Int)) then
        r == req || r == (m_vmmaps m).vm_brk
      else (r == req || r == (m_vmmaps m).vm_brk) && mmap_brk_grow_ok m req r) := rfl

/-- The grow gate, unfolded once. -/
theorem mmap_brk_grow_ok_eq (m : Model) (req r : word) :
    mmap_brk_grow_ok m req r =
      (if decide (0 < ((m_vmmaps m).vm_brk.toNat : Int)) &&
          decide (((m_vmmaps m).vm_brk.toNat : Int) < (r.toNat : Int)) then
        (if page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int) <
            page_round_up_Z (r.toNat : Int)
         then decide (page_round_up_Z (r.toNat : Int) ≤ alloc_top (m_vmmaps m)) &&
           region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
             (BitVec.ofInt 64 (page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)))
             (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int) + page_size -
               page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)))
         else true)
        && brk_budget_ok m r
      else true) := rfl

theorem in_sysno_sys_input214 (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem in_arg0_sys_input214 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

/-- Which arm answers this number, on the SPEC side.  `syscall_spec` is
    `dispatch spec_table`, so fixing the number settles the table lookup by
    computation and the dispatcher disappears -- the same one-line argument
    `Checks.Sys.DispatchCompute` makes for `check_syscall`, made here
    instead so that this file needs only the brk checker rather than the
    module that re-exports every arm's. -/
theorem syscall_spec_brk (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : Outcome SyscallEffect Model event)
    (Hno : (x8.toNat : Int) = 214) :
    syscall_spec (sys_input segs ms x8) model o ↔
      brk_spec (ms_gpr ms 0) (sys_input segs ms x8) model o := by
  have hn : ((sys_input segs ms x8).in_sysno.toNat : Int) = 214 := Hno
  have hlook : lookup_arm spec_table ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some (arm 214 (fun i => brk_spec (in_arg i 0))) := by
    rw [hn]
    simp [lookup_arm, spec_table, arm]
  have hd := dispatch_arm spec_table (sys_input segs ms x8) model o
    (arm 214 (fun i => brk_spec (in_arg i 0))) hlook
  simpa only [syscall_spec, arm, SpecArm.sa_spec, in_arg0_sys_input214] using hd

/-- The allocator examples have no lazy mappings or materialized sparse
    pages.  Package a VM ledger with that empty backing state for the pure
    outcome algebra below. -/
def vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] none none none

def brk_grow_ok (h : VmMaps) (req r : word) : Bool :=
  mmap_brk_grow_ok (vm_model h) req r

/-- The admissibility condition used by the pure allocator outcome algebra. -/
def brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  mmap_brk_r_ok (vm_model h) req r = true

/-- The corresponding condition at a live syscall state, whose backing
    ledger is part of the decision. -/
def brk_resolution_ok (m : Model) (req r : word) : Prop :=
  mmap_brk_r_ok m req r = true

/-- The model after adopting resolution `r`. -/
def brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r

/-- ... and so `brk` as a whole does: it retags the break, rewrites the
    VM ledger and forgets the backing of what it unmapped.  Stated at
    `brk_model` rather than at its `with_vmmaps` core so that a proof
    stepping over a brk node does not have to know how `with_brk_next` is
    layered. -/
theorem fd1chan_brk_model (req r : word) (m : Model) (H : fd1chan m) :
    fd1chan (brk_model req r m) := by
  unfold brk_model with_brk_next
  exact fd1chan_forget_vm_ranges _ _ (fd1chan_with_vmmaps _ _ H)

theorem check_brk_ok_inv (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_brk req eff m = .CheckOk m' evs) :
    eff = SyscallEffect.mkEffectU (eff.eff_ret) []
            (brk_zeros req (eff.eff_ret) (m_vmmaps m).vm_brk)
            (brk_unmaps (eff.eff_ret) (m_vmmaps m).vm_brk) [] []
  ∧ evs = []
  ∧ brk_resolution_ok m req (eff.eff_ret)
  ∧ m' = brk_model req (eff.eff_ret) m := by
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_brk at H
  cases ws with
  | cons w ws => exact nomatch H
  | nil =>
    cases cs with
    | cons c cs => exact nomatch H
    | nil =>
      cases copyins with
      | cons ci cis => exact nomatch H
      | nil =>
        dsimp only at H
        by_cases hok : (mmap_brk_r_ok m req r &&
            listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk) &&
            listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
        · rw [ite_eq_left hok] at H
          simp only [check_result.CheckOk.injEq] at H
          obtain ⟨hm, hevs⟩ := H
          obtain ⟨h1, hu⟩ := (Bool.and_eq_true ..).mp hok
          obtain ⟨hr, hz⟩ := (Bool.and_eq_true ..).mp h1
          have hzz : zs = brk_zeros req r (m_vmmaps m).vm_brk :=
            (listNN_eqb_eq zs _).mp hz
          have huu : us = brk_unmaps r (m_vmmaps m).vm_brk :=
            (listNN_eqb_eq us _).mp hu
          subst hzz
          subst huu
          subst hm
          subst hevs
          exact ⟨rfl, rfl, hr, rfl⟩
        · rw [ite_eq_right hok] at H
          exact nomatch H

theorem check_brk_ok_intro (req r : word) (m : Model)
    (HR : brk_resolution_ok m req r) :
    check_brk req (SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
                              (brk_unmaps r (m_vmmaps m).vm_brk) [] []) m
  = .CheckOk (brk_model req r m) [] := by
  have hz : listNN_eqb (brk_zeros req r (m_vmmaps m).vm_brk)
      (brk_zeros req r (m_vmmaps m).vm_brk) = true := (listNN_eqb_eq _ _).mpr rfl
  have hu : listNN_eqb (brk_unmaps r (m_vmmaps m).vm_brk)
      (brk_unmaps r (m_vmmaps m).vm_brk) = true := (listNN_eqb_eq _ _).mpr rfl
  have hok : (mmap_brk_r_ok m req r &&
      listNN_eqb (brk_zeros req r (m_vmmaps m).vm_brk)
        (brk_zeros req r (m_vmmaps m).vm_brk) &&
      listNN_eqb (brk_unmaps r (m_vmmaps m).vm_brk)
        (brk_unmaps r (m_vmmaps m).vm_brk)) = true := by
    rw [hz, hu]
    simp only [Bool.and_true]
    exact HR
  unfold check_brk
  simp only []
  rw [ite_eq_left hok]
  rfl

/-- Admissible outcomes of a brk syscall, in terms of the resolved `r`. -/
theorem brk_ok_iff (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hno : (x8.toNat : Int) = 214) :
    (syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) ↔
     (eff = SyscallEffect.mkEffectU (eff.eff_ret) []
              (brk_zeros (ms_gpr ms 0) (eff.eff_ret) (m_vmmaps model).vm_brk)
              (brk_unmaps (eff.eff_ret) (m_vmmaps model).vm_brk) [] []
      ∧ evs = []
      ∧ brk_resolution_ok model (ms_gpr ms 0) (eff.eff_ret)
      ∧ model' = brk_model (ms_gpr ms 0) (eff.eff_ret) model)) := by
  constructor
  · intro H
    have H2 := (syscall_spec_brk segs ms x8 model _ Hno).mp H
    exact check_brk_ok_inv (ms_gpr ms 0) eff model model' evs
      (check_brk_complete_ok (ms_gpr ms 0) eff model model' evs
        (sys_input segs ms x8) H2)
  · rintro ⟨Heff, rfl, Hok, rfl⟩
    refine (syscall_spec_brk segs ms x8 model _ Hno).mpr ?_
    refine check_brk_sound_ok (ms_gpr ms 0) _ model _ [] (sys_input segs ms x8) ?_
    rw [Heff]
    exact check_brk_ok_intro (ms_gpr ms 0) (eff.eff_ret) model Hok

theorem brk_ok_intro (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (r : word)
    (Hno : (x8.toNat : Int) = 214)
    (Hok : brk_resolution_ok model (ms_gpr ms 0) r) :
    syscall_spec (sys_input segs ms x8) model
      (.ok (SyscallEffect.mkEffectU r []
              (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
              (brk_unmaps r (m_vmmaps model).vm_brk) [] [])
          (brk_model (ms_gpr ms 0) r model) []) := by
  refine (brk_ok_iff segs ms x8 model _ _ _ Hno).mpr ⟨rfl, rfl, Hok, rfl⟩

/-- brk never takes the error transition. -/
theorem brk_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : (x8.toNat : Int) = 214) :
    ¬ syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro H
  have H2 := (syscall_spec_brk segs ms x8 model _ Hno).mp H
  have H3 := check_brk_complete_unmodeled (ms_gpr ms 0) model
    (sys_input segs ms x8) (mkEffect (BitVec.ofInt 64 0) [] []) H2
  unfold check_brk at H3
  simp only [] at H3
  by_cases hok : (mmap_brk_r_ok model (ms_gpr ms 0) (BitVec.ofInt 64 0) &&
      listNN_eqb [] (brk_zeros (ms_gpr ms 0) (BitVec.ofInt 64 0)
        (m_vmmaps model).vm_brk) &&
      listNN_eqb [] (brk_unmaps (BitVec.ofInt 64 0) (m_vmmaps model).vm_brk)) = true
  · rw [ite_eq_left hok] at H3
    exact nomatch H3
  · rw [ite_eq_right hok] at H3
    exact nomatch H3

/-- brk is receptive: some resolution is always admissible.
    KEEPING the current break (`r = vm_brk h`) is admitted by every path
    (query/invalid returns it; shrink and grow both have the failure
    branch that keeps it). -/
theorem brk_receptive (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (Hno : (x8.toNat : Int) = 214) :
    ∃ (eff : SyscallEffect) (model' : Model),
      syscall_spec (sys_input segs ms x8) model (.ok eff model' []) := by
  let r := (m_vmmaps model).vm_brk
  refine ⟨SyscallEffect.mkEffectU r []
      (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
      (brk_unmaps r (m_vmmaps model).vm_brk) [] [],
    brk_model (ms_gpr ms 0) r model, brk_ok_intro segs ms x8 model r Hno ?_⟩
  unfold brk_resolution_ok
  rw [mmap_brk_r_ok_eq]
  simp only [r]
  by_cases h1 : (w_is0 (ms_gpr ms 0) ||
      decide ((ms_gpr ms 0).toNat < ((min_brk (m_vmmaps model)).toNat : Int))) = true
  · -- QUERY / INVALID: the resolution IS the break
    rw [ite_eq_left h1]
    exact PropExec.bv_eqb_refl _
  · rw [ite_eq_right h1]
    by_cases h2 : decide (((ms_gpr ms 0).toNat : Int) <
        ((m_vmmaps model).vm_brk.toNat : Int)) = true
    · -- SHRINK: keeping the break is the failure resolution
      rw [ite_eq_left h2]
      simp [PropExec.bv_eqb_refl]
    · -- GROW: keeping the break passes the gate (`brk_grow_ok` at r = old)
      rw [ite_eq_right h2, mmap_brk_grow_ok_eq]
      have hlt : decide (((m_vmmaps model).vm_brk.toNat : Int) <
            ((m_vmmaps model).vm_brk.toNat : Int)) = false := by
        rw [decide_eq_false_iff_not]
        omega
      rw [hlt, Bool.and_false]
      simp [PropExec.bv_eqb_refl]

/- =========================================================================
   brk effects, read off the guards
   ========================================================================= -/

/-- brk grow of req<>0 from an established nonzero break to r > old:
    the visible zero-fill is exactly the shared page-rounded range helper. -/
theorem brk_zeros_grow (req r old : word) (Hreq : req ≠ BitVec.ofInt 64 0)
    (Hold : 0 < (old.toNat : Int)) (Hlt : (old.toNat : Int) < (r.toNat : Int)) :
    brk_zeros req r old =
      brk_page_range (page_round_up_Z (old.toNat : Int))
                     (page_round_up_Z (r.toNat : Int)) := by
  have e1 : w_is0 req = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ Hreq
  have e2 : decide (0 < (old.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hold
  have e3 : decide ((old.toNat : Int) < (r.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hlt
  unfold brk_zeros brk_is_grow
  rw [e1, e2, e3]
  simp

/-- The logical ledger remains byte-granular across the same grow. -/
theorem brk_grants_grow (req r old : word) (Hreq : req ≠ BitVec.ofInt 64 0)
    (Hold : 0 < (old.toNat : Int)) (Hlt : (old.toNat : Int) < (r.toNat : Int)) :
    brk_grants req r old = [(old, r - old)] := by
  have e1 : w_is0 req = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ Hreq
  have e2 : decide (0 < (old.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hold
  have e3 : decide ((old.toNat : Int) < (r.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hlt
  unfold brk_grants brk_is_grow
  rw [e1, e2, e3]
  simp

theorem brk_zeros_query (r old : word) :
    brk_zeros (BitVec.ofInt 64 0) r old = [] := by
  have e1 : w_is0 (BitVec.ofInt 64 0) = true := PropExec.bv_eqb_refl _
  unfold brk_zeros brk_is_grow
  rw [e1]
  simp

theorem brk_grants_query (r old : word) :
    brk_grants (BitVec.ofInt 64 0) r old = [] := by
  have e1 : w_is0 (BitVec.ofInt 64 0) = true := PropExec.bv_eqb_refl _
  unfold brk_grants brk_is_grow
  rw [e1]
  simp

theorem brk_zeros_keep (req old : word) : brk_zeros req old old = [] := by
  have hlt : decide ((old.toNat : Int) < (old.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  unfold brk_zeros brk_is_grow
  rw [hlt]
  simp

theorem brk_grants_keep (req old : word) : brk_grants req old old = [] := by
  have hlt : decide ((old.toNat : Int) < (old.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  unfold brk_grants brk_is_grow
  rw [hlt]
  simp

/-- brk KEEPS the break: nothing is freed. -/
theorem brk_unmaps_keep (old : word) : brk_unmaps old old = [] := by
  unfold brk_unmaps brk_page_range
  by_cases h : 0 < (old.toNat : Int)
  · rw [ite_eq_left h, ite_eq_right (by omega)]
  · rw [ite_eq_right h]

/-- The QUERY resolution frees nothing — the same `r = vm_brk h` premise
    `brk_model_query` takes, so a query node discharges both from it. -/
theorem brk_unmaps_query (h : VmMaps) (r : word) (H : r = h.vm_brk) :
    brk_unmaps r h.vm_brk = [] := by
  subst H
  exact brk_unmaps_keep _

/-- Any resolution that does not LOWER the break frees nothing: page
    rounding is monotone, so the freed interval is empty.  This covers
    the query/invalid path (`r = old`) and both grow resolutions. -/
theorem brk_unmaps_grow (r old : word) (H : (old.toNat : Int) ≤ (r.toNat : Int)) :
    brk_unmaps r old = [] := by
  have hmono : page_round_up_Z (old.toNat : Int) ≤ page_round_up_Z (r.toNat : Int) :=
    Checks.Sys.Mm.Mmap.page_round_up_Z_mono _ _ H
  unfold brk_unmaps brk_page_range
  by_cases h : 0 < (old.toNat : Int)
  · rw [ite_eq_left h, ite_eq_right (by omega)]
  · rw [ite_eq_right h]

/-- `vm_backing_used` at the pure ledger model is `vm_backed_bytes`. -/
theorem vm_backing_used_vm_model (h : VmMaps) :
    vm_backing_used (vm_model h) = vm_backed_bytes h := by
  have h1 : m_vmmaps (vm_model h) = h := rfl
  have h2 : m_vm_lazy (vm_model h) = [] := rfl
  have h3 : m_vm_materialized (vm_model h) = [] := rfl
  unfold vm_backing_used vm_backed_bytes
  rw [h1, h2, h3]
  simp [maps_subtract_all]

/-- The budget conjunct at the pure ledger model. -/
theorem brk_budget_ok_vm_model (h : VmMaps) (r : word) :
    brk_budget_ok (vm_model h) r =
      decide (vm_backed_bytes h + ((r - h.vm_brk).toNat : Int) ≤ h.vm_limit) := by
  have h1 : m_vmmaps (vm_model h) = h := rfl
  unfold brk_budget_ok
  rw [h1, vm_backing_used_vm_model]

/-- `brk_grow_ok` at the pure ledger model, unfolded once. -/
theorem brk_grow_ok_eq (h : VmMaps) (req r : word) :
    brk_grow_ok h req r =
      (if decide (0 < (h.vm_brk.toNat : Int)) &&
          decide ((h.vm_brk.toNat : Int) < (r.toNat : Int)) then
        (if page_round_up_Z (h.vm_brk.toNat : Int) < page_round_up_Z (r.toNat : Int)
         then decide (page_round_up_Z (r.toNat : Int) ≤ alloc_top h) &&
           region_free (h.vm_reserved ++ h.vm_maps)
             (BitVec.ofInt 64 (page_round_up_Z (h.vm_brk.toNat : Int)))
             (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int) + page_size -
               page_round_up_Z (h.vm_brk.toNat : Int)))
         else true)
        && decide (vm_backed_bytes h + ((r - h.vm_brk).toNat : Int) ≤ h.vm_limit)
      else true) := by
  unfold brk_grow_ok
  rw [mmap_brk_grow_ok_eq, brk_budget_ok_vm_model]
  rfl

/-- `brk_r_ok` at the pure ledger model, unfolded once. -/
theorem brk_r_ok_eq (h : VmMaps) (req r : word) :
    brk_r_ok h req r ↔
      (if w_is0 req ||
          decide ((req.toNat : Int) < ((min_brk h).toNat : Int)) then
        r == h.vm_brk
      else if decide ((req.toNat : Int) < (h.vm_brk.toNat : Int)) then
        r == req || r == h.vm_brk
      else (r == req || r == h.vm_brk) && brk_grow_ok h req r) = true := by
  unfold brk_r_ok
  rw [mmap_brk_r_ok_eq]
  rfl

/-- Unfolding `brk_grow_ok` on an actual grow. -/
theorem brk_grow_ok_grow (h : VmMaps) (req r : word)
    (Hreq : req ≠ BitVec.ofInt 64 0)
    (H0 : 0 < (h.vm_brk.toNat : Int))
    (Hlt : (h.vm_brk.toNat : Int) < (r.toNat : Int)) :
    brk_grow_ok h req r
    = (((if page_round_up_Z ((h.vm_brk).toNat : Int) <
            page_round_up_Z (r.toNat : Int)
         then decide (page_round_up_Z (r.toNat : Int) ≤ alloc_top h) &&
           region_free (h.vm_reserved ++ h.vm_maps)
             (BitVec.ofInt 64 (page_round_up_Z ((h.vm_brk).toNat : Int)))
             (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int) + page_size -
               page_round_up_Z ((h.vm_brk).toNat : Int)))
         else true)
       && decide (vm_backed_bytes h + ((r - h.vm_brk).toNat : Int) ≤ h.vm_limit))) := by
  have e2 : decide (0 < (h.vm_brk.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact H0
  have e3 : decide ((h.vm_brk.toNat : Int) < (r.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    exact Hlt
  rw [brk_grow_ok_eq, e2, e3]
  simp

theorem brk_grow_ok_keep (h : VmMaps) (req : word) :
    brk_grow_ok h req h.vm_brk = true := by
  have hlt : decide ((h.vm_brk.toNat : Int) < (h.vm_brk.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  rw [brk_grow_ok_eq, hlt]
  simp

/- =========================================================================
   Elementary page-rounding facts used by the allocator examples.
   ========================================================================= -/

theorem page_round_up_Z_aligned (z : Int) (Hz : 0 ≤ z) (Hmod : z % page_size = 0) :
    page_round_up_Z z = z := by
  have hps : page_size = 4096 := by decide
  unfold page_round_up_Z
  rw [hps] at Hmod ⊢
  have hq : z = 4096 * (z / 4096) := by
    have := Int.mul_ediv_add_emod z 4096
    omega
  have hdiv : (z + 4096 - 1) / 4096 = z / 4096 := by
    conv => lhs; rw [hq]
    rw [show 4096 * (z / 4096) + 4096 - 1 = 4095 + (z / 4096) * 4096 by omega]
    rw [Int.add_mul_ediv_right 4095 (z / 4096) (by decide : (4096 : Int) ≠ 0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  rw [hdiv]
  exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero Hmod)

theorem page_round_up_Z_bounds (z : Int) (Hz : 0 ≤ z) :
    z ≤ page_round_up_Z z ∧ page_round_up_Z z ≤ z + page_size - 1 := by
  have hps : page_size = 4096 := by decide
  unfold page_round_up_Z
  rw [hps]
  have hdm := Int.mul_ediv_add_emod (z + 4096 - 1) 4096
  have h0 := Int.emod_nonneg (z + 4096 - 1) (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos (z + 4096 - 1) (b := 4096) (by decide)
  constructor <;> omega

/-- The page round-up is a multiple of 8 (4096 = 8 * 512). -/
theorem eight_dvd_page_round_up (z : Int) : (8 : Int) ∣ page_round_up_Z z := by
  refine ⟨(z + 4096 - 1) / 4096 * 512, ?_⟩
  unfold page_round_up_Z page_size
  rw [show (4096 : Int) = 8 * 512 from by decide]
  exact Int.mul_left_comm _ 8 512

/-- Eight-byte chunk rounding is contained in page rounding. -/
theorem round8_le_page_round (z : Int) (Hz : 0 ≤ z) :
    (((z + 7) / 8) * 8) ≤ page_round_up_Z z := by
  have h8le : ((z + 7) / 8) * 8 ≤ z + 7 := by
    have hdm := Int.mul_ediv_add_emod (z + 7) 8
    have h0 := Int.emod_nonneg (z + 7) (b := 8) (by decide)
    omega
  have hzle : z ≤ page_round_up_Z z := (page_round_up_Z_bounds z Hz).1
  obtain ⟨p, hp⟩ := eight_dvd_page_round_up z
  have hnot : ¬ (page_round_up_Z z < ((z + 7) / 8) * 8) := by
    intro hcon
    rw [hp] at hcon hzle
    omega
  omega

theorem round8_le_page_grant (old n : Int) (Hold : 0 ≤ old) (Hn : 0 ≤ n)
    (Hmod : old % page_size = 0) :
    (((n + 7) / 8) * 8) ≤ page_round_up_Z (old + n) - old := by
  have hps : page_size = 4096 := by decide
  rw [hps] at Hmod
  have hq : old = 4096 * (old / 4096) := by
    have := Int.mul_ediv_add_emod old 4096
    omega
  have hdiv : (old + n + 4096 - 1) / 4096 = (n + 4096 - 1) / 4096 + old / 4096 := by
    conv => lhs; rw [hq]
    rw [show 4096 * (old / 4096) + n + 4096 - 1 =
      (n + 4096 - 1) + (old / 4096) * 4096 by omega]
    rw [Int.add_mul_ediv_right _ _ (by decide : (4096 : Int) ≠ 0)]
  have hsplit : page_round_up_Z (old + n) = page_round_up_Z n + old := by
    unfold page_round_up_Z page_size
    rw [hdiv, Int.add_mul]
    have h2 : 4096 * (old / 4096) = old := by rw [← hq]
    rw [Int.mul_comm (old / 4096) 4096, h2]
  rw [hsplit, Int.add_sub_cancel]
  exact round8_le_page_round n Hn

/- =========================================================================
   region_free: prefix, above, below
   ========================================================================= -/

/-- A prefix of a free interval with the same base is free. -/
theorem region_free_prefix (maps : List (word × word)) (b small big : word)
    (Hle : (small.toNat : Int) ≤ (big.toNat : Int))
    (Hfree : region_free maps b big = true) : region_free maps b small = true := by
  induction maps with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨a, sz⟩ := hd
    have hhead : region_free ((a, sz) :: rest) b big = true := Hfree
    have hiv : iv_overlap b big a sz = false :=
      region_free_In ((a, sz) :: rest) b big a sz Hfree (by simp)
    have hnil : region_free rest b big = true := by
      simp only [region_free, Bool.and_eq_true] at hhead
      exact hhead.2
    have hivs : iv_overlap b small a sz = false := by
      unfold iv_overlap at hiv ⊢
      rcases (Bool.and_eq_false_iff.mp hiv) with h | h
      · rw [h]
        rfl
      · rw [show decide ((a.toNat : Int) < (b.toNat : Int) + (small.toNat : Int)) = false from by
          simp only [decide_eq_false_iff_not] at h ⊢
          omega, Bool.and_false]
    simp only [region_free, Bool.and_eq_true, hivs, Bool.not_false, Bool.true_and]
    exact ih hnil

/-- `reserved_top` bounds every reservation from above — the shape the
    ASLR-base bound `Run.valid_brk` hands a `region_free_above`-style
    argument. -/
theorem reserved_top_above (reserved : List (word × word)) (r : Int)
    (Hr : reserved_top reserved ≤ r) :
    ∀ p ∈ reserved, (p.1.toNat : Int) + (p.2.toNat : Int) ≤ r := by
  induction reserved with
  | nil => intro p hp; exact absurd hp (by simp)
  | cons hd rest ih =>
    obtain ⟨a, sz⟩ := hd
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with h | h
    · subst h
      show (a.toNat : Int) + (sz.toNat : Int) ≤ r
      have Hr' : max ((a.toNat : Int) + (sz.toNat : Int)) (reserved_top rest) ≤ r := by
        rw [← show reserved_top ((a, sz) :: rest) = max ((a.toNat : Int) + (sz.toNat : Int))
          (reserved_top rest) from rfl]
        exact Hr
      omega
    · exact ih (by
        have Hr' : max ((a.toNat : Int) + (sz.toNat : Int)) (reserved_top rest) ≤ r := by
          rw [← show reserved_top ((a, sz) :: rest) = max ((a.toNat : Int) + (sz.toNat : Int))
            (reserved_top rest) from rfl]
          exact Hr
        omega) p h

/-- A region at or above the image top is free of every reservation. -/
theorem region_free_above_top (reserved : List (word × word)) (lo n : word)
    (Hr : reserved_top reserved ≤ (lo.toNat : Int)) :
    region_free reserved lo n = true := by
  induction reserved with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨a, sz⟩ := hd
    have Hr' : max ((a.toNat : Int) + (sz.toNat : Int)) (reserved_top rest) ≤ (lo.toNat : Int) := by
      rw [← show reserved_top ((a, sz) :: rest) = max ((a.toNat : Int) + (sz.toNat : Int))
        (reserved_top rest) from rfl]
      exact Hr
    have hhead : ¬ ((lo.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int)) := by omega
    have htail : reserved_top rest ≤ (lo.toNat : Int) := by omega
    simp only [region_free, Bool.and_eq_true]
    refine ⟨?_, ih htail⟩
    unfold iv_overlap
    rw [show decide ((lo.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int)) = false from by
      simp only [decide_eq_false_iff_not]
      exact hhead]
    rfl

/-- A region entirely above every reservation is free. -/
theorem region_free_above (l : List (word × word)) (lo n : word)
    (Hf : ∀ p ∈ l, (p.1.toNat : Int) + (p.2.toNat : Int) ≤ (lo.toNat : Int)) :
    region_free l lo n = true := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨a, sz⟩ := hd
    rw [List.forall_mem_cons] at Hf
    obtain ⟨Ha, Hl⟩ := Hf
    have Ha' : (a.toNat : Int) + (sz.toNat : Int) ≤ (lo.toNat : Int) := Ha
    simp only [region_free, Bool.and_eq_true]
    refine ⟨?_, ih Hl⟩
    unfold iv_overlap
    rw [show decide ((lo.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int)) = false from by
      simp only [decide_eq_false_iff_not]
      omega]
    rfl

/-- A region entirely below every reservation is free. -/
theorem region_free_below (l : List (word × word)) (lo n : word)
    (Hf : ∀ p ∈ l, (lo.toNat : Int) + (n.toNat : Int) ≤ (p.1.toNat : Int)) :
    region_free l lo n = true := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨a, sz⟩ := hd
    rw [List.forall_mem_cons] at Hf
    obtain ⟨Ha, Hl⟩ := Hf
    have Ha' : (lo.toNat : Int) + (n.toNat : Int) ≤ (a.toNat : Int) := Ha
    simp only [region_free, Bool.and_eq_true]
    refine ⟨?_, ih Hl⟩
    unfold iv_overlap
    rw [show decide ((a.toNat : Int) < (lo.toNat : Int) + (n.toNat : Int)) = false from by
      simp only [decide_eq_false_iff_not]
      omega, Bool.and_false]
    rfl

/-- `BitVec.ofInt 64` of an unsigned value is that word. -/
theorem ofInt_toNat (w : word) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt,
    Int.toNat_emod (Int.natCast_nonneg _) (by decide : (0 : Int) ≤ (((2 ^ 64 : Nat) : Int))),
    Int.toNat_natCast, Int.toNat_natCast, Nat.mod_eq_of_lt w.isLt]

/-- `BitVec.ofInt 64` of an `Int` in `[0, 2^64)` reads back as that value. -/
theorem toNat_ofInt_range (z : Int) (Hlo : 0 ≤ z) (Hhi : z < ((2 ^ 64 : Nat) : Int)) :
    ((BitVec.ofInt 64 z).toNat : Int) = z := by
  have hzt : (z.toNat : Int) = z := Int.toNat_of_nonneg Hlo
  have hlt : z.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofInt, Int.toNat_emod Hlo (by decide : (0 : Int) ≤ ((2 ^ 64 : Nat) : Int)),
    Int.toNat_natCast, Nat.mod_eq_of_lt hlt, hzt]

/-- On a page-aligned established break, a genuine grow has a nonempty
    physical page interval, so the gate is the physical ceiling plus the
    free region (and the logical budget). -/
theorem brk_grow_ok_aligned_grow (h : VmMaps) (req r : word)
    (Hreq : req ≠ BitVec.ofInt 64 0)
    (Hpos : 0 < (h.vm_brk.toNat : Int))
    (Hlt : (h.vm_brk.toNat : Int) < (r.toNat : Int))
    (Halign : (h.vm_brk.toNat : Int) % page_size = 0) :
    brk_grow_ok h req r
    = ((decide (page_round_up_Z (r.toNat : Int) ≤ alloc_top h) &&
        region_free (h.vm_reserved ++ h.vm_maps) h.vm_brk
          (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int) + page_size
                            - (h.vm_brk.toNat : Int))))
       && decide (vm_backed_bytes h + ((r - h.vm_brk).toNat : Int) ≤ h.vm_limit)) := by
  rw [brk_grow_ok_grow h req r Hreq Hpos Hlt]
  have hrt : 0 ≤ (h.vm_brk.toNat : Int) := (u64_range h.vm_brk).1
  rw [page_round_up_Z_aligned _ hrt Halign]
  have hb := page_round_up_Z_bounds (r.toNat : Int) (u64_range r).1
  have hround : (h.vm_brk.toNat : Int) < page_round_up_Z (r.toNat : Int) := by omega
  rw [ite_eq_left hround]
  rw [show BitVec.ofInt 64 (h.vm_brk.toNat : Int) = h.vm_brk from ofInt_toNat h.vm_brk]

/-- On a page-aligned established break, the visible zero-fill of a grow is
    one interval starting at the break itself. -/
theorem brk_zeros_aligned_grow (req r old : word)
    (Hreq : req ≠ BitVec.ofInt 64 0)
    (Hpos : 0 < (old.toNat : Int))
    (Hlt : (old.toNat : Int) < (r.toNat : Int))
    (Halign : (old.toNat : Int) % page_size = 0) :
    brk_zeros req r old =
      [(old, BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int) - (old.toNat : Int)))] := by
  rw [brk_zeros_grow req r old Hreq Hpos Hlt]
  have hrt : 0 ≤ (old.toNat : Int) := (u64_range old).1
  rw [page_round_up_Z_aligned _ hrt Halign]
  unfold brk_page_range
  have hb := page_round_up_Z_bounds (r.toNat : Int) (u64_range r).1
  have hround : (old.toNat : Int) < page_round_up_Z (r.toNat : Int) := by omega
  rw [ite_eq_left hround, ofInt_toNat]

/-- Everything a caller needs about the page-rounded grant a successful grow
    from `r` to `r + w` hands back, given only the two facts the brk spec
    leaves on the table: that the new break fits under the run's grant top,
    and that the granted pages and the one page above them are free. -/
theorem brk_aligned_grant_ok (res : List (word × word)) (r w g : word)
    (top ceil : Int)
    (Hnowrap : ((r + w).toNat : Int) = (r.toNat : Int) + (w.toNat : Int))
    (Htop : ((r + w).toNat : Int) = top)
    (Hg : g = BitVec.ofInt 64 (page_round_up_Z ((r + w).toNat : Int) - (r.toNat : Int)))
    (Hacp : ceil + page_size < 2 ^ 64)
    (Hceil : page_round_up_Z ((r + w).toNat : Int) ≤ ceil)
    (Hfree : region_free res r
      (BitVec.ofInt 64 (page_round_up_Z ((r + w).toNat : Int) + page_size
                        - (r.toNat : Int))) = true) :
    ((g.toNat : Int) = page_round_up_Z ((r + w).toNat : Int) - (r.toNat : Int))
    ∧ ((w.toNat : Int) ≤ (g.toNat : Int))
    ∧ ((r.toNat : Int) + (g.toNat : Int) ≤ ceil)
    ∧ (top ≤ ceil)
    ∧ region_free res r w = true
    ∧ region_free res r g = true := by
  have hr := u64_range r
  have hw := u64_range w
  have hrw := u64_range (r + w)
  have hb := page_round_up_Z_bounds ((r + w).toNat : Int) (by omega)
  obtain ⟨hb1, hb2⟩ := hb
  have hps : 0 < page_size := by decide
  have hceil_lt : ceil < ((2 ^ 64 : Nat) : Int) := by omega
  -- the rounded end is nonneg and inside the ceiling's `2^64` window
  have hRnonneg : 0 ≤ page_round_up_Z ((r + w).toNat : Int) - (r.toNat : Int) := by omega
  have hRlt : page_round_up_Z ((r + w).toNat : Int) - (r.toNat : Int)
      < ((2 ^ 64 : Nat) : Int) := by omega
  have HgU : ((g.toNat : Int))
      = page_round_up_Z ((r + w).toNat : Int) - (r.toNat : Int) := by
    rw [Hg]
    exact toNat_ofInt_range _ hRnonneg hRlt
  have hbig_nonneg : 0 ≤ page_round_up_Z ((r + w).toNat : Int) + page_size
      - (r.toNat : Int) := by omega
  have hbig_lt : page_round_up_Z ((r + w).toNat : Int) + page_size - (r.toNat : Int)
      < ((2 ^ 64 : Nat) : Int) := by omega
  have hbig : ((BitVec.ofInt 64 (page_round_up_Z ((r + w).toNat : Int) + page_size
      - (r.toNat : Int))).toNat : Int)
      = page_round_up_Z ((r + w).toNat : Int) + page_size - (r.toNat : Int) :=
    toNat_ofInt_range _ hbig_nonneg hbig_lt
  refine ⟨HgU, by omega, by omega, by omega, ?_, ?_⟩
  · refine region_free_prefix res r w _ ?_ Hfree
    rw [hbig]
    omega
  · refine region_free_prefix res r g _ ?_ Hfree
    rw [hbig, HgU]
    omega

/- =========================================================================
   Two-node brk resolution-set algebra: a binary that queries the break
   (req = 0), then grows it by `t` bytes (req = brk + t), taking the
   failure exit ([([], 4)]) on either an unusable query resolution or a
   refused/wrapping grow, and the success buffers [bufs] otherwise.  This
   is the shared shape behind brk_rev_ns/alloc_join_ns/oob_read_bug_ns:
   only the growth amount `t` and success buffers `bufs` differ per binary
   (all three write `(list (list byte) * word)` outcomes, so no further
   type parameter is needed).  `t = 0` is handled explicitly
   ([oob_read_bug_ns]'s n = 0 case: re-requesting the current break can
   never fail) so every binary can use this algebra whether or not its
   growth amount is provably positive.

   `t` is a `word`; the "wrap" arm of `T1` and the no-wrap bound of
   `growable` are stated in `Int` over `toNat r + toNat t`.
   ========================================================================= -/

/-- Can the break grow from `r` by `t` bytes, against reservation list
    `reserved`, grant top `top` (the run's `State.alloc_top`) and
    allocation budget `lim` (`State.vm_limit` of a fresh ledger: no live
    grants yet, so the `t` added bytes must fit the whole budget)?  The
    free region is the installed pages plus the one above them, as in
    `Mmap.brk_grow_ok`.  `t = 0` (re-requesting the current break) is
    trivially growable regardless of the top/free-region/budget check. -/
def growable (reserved : List (word × word)) (lim top : Int) (t r : word) : Prop :=
  r ≠ BitVec.ofInt 64 0 ∧ ((r.toNat : Int) + (t.toNat : Int) < 2 ^ 64) ∧
  (t = BitVec.ofInt 64 0 ∨
   (((if page_round_up_Z (r.toNat : Int) <
          page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) then
        decide (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) ≤ top) &&
          region_free reserved
            (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int)))
            (BitVec.ofInt 64 (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int))
                              + page_size - page_round_up_Z (r.toNat : Int)))
      else true)
     && decide ((t.toNat : Int) ≤ lim)) = true))

/-- Branch outcome set after the FIRST brk resolved to `r`.  The exit-4
    element is present iff a failing continuation exists: `r = 0`,
    address wraparound, or (`t <> 0` and the kernel may keep the old
    break at the second brk). -/
def T1 (reserved : List (word × word)) (lim top : Int) (t : word)
    (bufs : List (List byte)) (r : word) : (List (List byte) × word) → Prop :=
  fun o => (o = ([], BitVec.ofInt 64 4)
            ∧ (r = BitVec.ofInt 64 0
                ∨ (2 ^ 64 : Int) ≤ (r.toNat : Int) + (t.toNat : Int)
                ∨ t ≠ BitVec.ofInt 64 0))
        ∨ (growable reserved lim top t r ∧ o = (bufs, BitVec.ofInt 64 0))

/-- Branch outcome set after the SECOND brk resolved to `r2`. -/
def T2 (want : word) (bufs : List (List byte)) (r2 : word) :
    (List (List byte) × word) → Prop :=
  fun o => (r2 = want ∧ o = (bufs, BitVec.ofInt 64 0))
        ∨ (r2 ≠ want ∧ o = ([], BitVec.ofInt 64 4))

/-- `brk_r_ok` at the FIRST query (req = 0) on an UNESTABLISHED break
    with `brk(0)` (musl/glibc `sbrk(0)`) — which is DETERMINISTIC: the
    kernel reports the break, established at `execve` (the quantified
    ASLR base `Run.mi_init_brk`). -/
theorem brk_r_ok_query_iff (h : VmMaps) (r : word) :
    brk_r_ok h (BitVec.ofInt 64 0) r ↔ r = h.vm_brk := by
  rw [brk_r_ok_eq]
  have e1 : w_is0 (BitVec.ofInt 64 0) = true := PropExec.bv_eqb_refl _
  rw [e1]
  simp only [Bool.true_or, ite_true]
  exact Fs.bv_eqb_eq r h.vm_brk

/-- The page-rounded disjunct of `growable`, for the shape every example
    grow site has: a page-aligned established break `r` sitting above
    every reservation, grown by a positive `t` that fits under both the
    physical ceiling and the budget. -/
theorem growable_aligned_grow (reserved : List (word × word)) (lim top : Int)
    (t r : word)
    (Halign : (r.toNat : Int) % page_size = 0)
    (Htop : reserved_top reserved ≤ (r.toNat : Int))
    (Hpos : 0 < (t.toNat : Int))
    (Hceil : (r.toNat : Int) + (t.toNat : Int) + page_size - 1 ≤ top)
    (Hlim : (t.toNat : Int) ≤ lim) :
    ((if page_round_up_Z (r.toNat : Int) <
          page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) then
        decide (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) ≤ top) &&
          region_free reserved
            (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int)))
            (BitVec.ofInt 64 (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int))
                              + page_size - page_round_up_Z (r.toNat : Int)))
      else true)
     && decide ((t.toNat : Int) ≤ lim)) = true := by
  have hrt : 0 ≤ (r.toNat : Int) := (u64_range r).1
  have hround : page_round_up_Z (r.toNat : Int) = (r.toNat : Int) :=
    page_round_up_Z_aligned _ hrt Halign
  rw [hround]
  have hb := page_round_up_Z_bounds ((r.toNat : Int) + (t.toNat : Int)) (by omega)
  have hlt : (r.toNat : Int) < page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) := by
    omega
  rw [ite_eq_left hlt]
  have htop' : decide (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) ≤ top) = true := by
    simp only [decide_eq_true_eq]
    omega
  have hlim' : decide ((t.toNat : Int) ≤ lim) = true := by
    simp only [decide_eq_true_eq]
    exact Hlim
  have hfree : region_free reserved (BitVec.ofInt 64 (r.toNat : Int))
      (BitVec.ofInt 64 (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int))
                        + page_size - (r.toNat : Int))) = true := by
    rw [ofInt_toNat]
    exact region_free_above_top reserved r _ Htop
  rw [htop', hfree, hlim']
  simp

theorem brk_aslr_max_val : brk_aslr_max = 1073741824 := rfl

/-- The model after a brk(0) QUERY is unchanged modulo re-tagging the
    break: the resolution is the current break, nothing is granted or
    freed. -/
theorem brk_model_next_query (h : VmMaps) (r : word) (H : r = h.vm_brk) :
    brk_model_next h (BitVec.ofInt 64 0) r
    = VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps h.vm_noaccess
        h.vm_start_brk r h.vm_limit h.vm_mmap_base h.vm_init_sp := by
  subst H
  have hlt : decide ((h.vm_brk.toNat : Int) < (h.vm_brk.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  unfold brk_model_next brk_maps_next
  rw [hlt, brk_grants_query, brk_unmaps_keep]
  simp [maps_subtract_ranges]

theorem brk_model_query (r : word) (m : Model) (H : r = (m_vmmaps m).vm_brk) :
    brk_model (BitVec.ofInt 64 0) r m
    = with_vmmaps
        (VmMaps.mkVmMapsFull ((m_vmmaps m).vm_reserved) ((m_vmmaps m).vm_maps)
          ((m_vmmaps m).vm_noaccess) ((m_vmmaps m).vm_start_brk) r
          ((m_vmmaps m).vm_limit) ((m_vmmaps m).vm_mmap_base)
          ((m_vmmaps m).vm_init_sp)) m := by
  subst H
  unfold brk_model with_brk_next
  simp only []
  rw [brk_unmaps_keep]
  simp only [forget_vm_ranges]
  rw [brk_model_next_query _ _ rfl]

/-- The GROW-node decode: on an established break `r` with heap base
    (`vm_start_brk`) `s`, `brk(req)` with `req >= s` (not below Linux's
    `min_brk` = `start_brk`), `req >= r`, and `req > 0` resolves to `req`
    (grow) or `r` (kept), gated by `brk_grow_ok` — the query/invalid and
    shrink guards are all excluded. -/
theorem brk_r_ok_grow_iff (reserved : List (word × word)) (lim : Int) (s r : word)
    (maps noaccess : List (word × word)) (mb sp req r2 : word)
    (Hpos : 0 < (req.toNat : Int))
    (Hs : (s.toNat : Int) ≤ (req.toNat : Int))
    (Hreq : (r.toNat : Int) ≤ (req.toNat : Int)) :
    (brk_r_ok (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2 ↔
     (r2 = req ∨ r2 = r) ∧
     brk_grow_ok (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp) req r2
       = true) := by
  have hne : req ≠ BitVec.ofInt 64 0 := by
    intro hc
    have h0 : ((BitVec.ofInt 64 0 : word).toNat : Int) = 0 := by
      rw [BitVec.toNat_ofInt]
      simp
    have := congrArg (fun w : word => (w.toNat : Int)) hc
    rw [h0] at this
    omega
  have e0 : w_is0 req = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ hne
  have emin : decide ((req.toNat : Int) < (s.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have ebrk : decide ((req.toNat : Int) < (r.toNat : Int)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have hmin : min_brk (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp) = s := rfl
  have hbrk : (VmMaps.mkVmMapsFull reserved maps noaccess s r lim mb sp).vm_brk = r := rfl
  rw [brk_r_ok_eq, hmin, hbrk, e0]
  simp only [Bool.false_or, emin, ebrk, Bool.false_eq_true, reduceIte, ite_false,
    Bool.and_eq_true, Bool.or_eq_true,
    show ((r2 == req) = true) ↔ (r2 = req) from Fs.bv_eqb_eq r2 req,
    show ((r2 == r) = true) ↔ (r2 = r) from Fs.bv_eqb_eq r2 r]

theorem T2_fail_iff (want : word) (bufs : List (List byte)) (r2 : word)
    (Hne : r2 ≠ want) (o : List (List byte) × word) :
    T2 want bufs r2 o ↔ o = ([], BitVec.ofInt 64 4) := by
  unfold T2
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h Hne
    · exact h
  · intro h
    exact Or.inr ⟨Hne, h⟩

theorem T2_succ_iff (want : word) (bufs : List (List byte))
    (o : List (List byte) × word) :
    T2 want bufs want o ↔ o = (bufs, BitVec.ofInt 64 0) := by
  unfold T2
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd rfl h
  · intro h
    exact Or.inl ⟨rfl, h⟩

theorem word_toNat_eq_zero (w : word) (h : (w.toNat : Int) = 0) :
    w = BitVec.ofInt 64 0 := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (BitVec.ofInt 64 0 : word).toNat = 0 := by decide
  rw [h0]
  omega

/-- `vm_backed_bytes` of the empty ledgers the resolution algebra runs on. -/
theorem vm_backed_bytes_nil (reserved : List (word × word)) (s r mb sp : word) (lim : Int) :
    vm_backed_bytes (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) = 0 := rfl

/-- The grow gate at the SELF-resolution `r + t` on the empty ledgers of the
    resolution algebra: with `r <> 0` and `t <> 0` the live gate is exactly
    `growable`'s page-rounded bool (the budget's `vm_backed_bytes` is `0`,
    `alloc_top` is the caller's `sp - stack_max_size`, and the request is
    `r + t`). -/
theorem brk_grow_ok_self_eq (reserved : List (word × word)) (lim top : Int)
    (t r s mb sp : word)
    (Hr0 : r ≠ BitVec.ofInt 64 0)
    (Ht : t ≠ BitVec.ofInt 64 0)
    (Htop : top = (sp.toNat : Int) - stack_max_size)
    (Hnw : (r.toNat : Int) + (t.toNat : Int) < 2 ^ 64) :
    brk_grow_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) (r + t)
    = ((if page_round_up_Z (r.toNat : Int) <
            page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) then
          decide (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int)) ≤ top) &&
            region_free reserved
              (BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int)))
              (BitVec.ofInt 64 (page_round_up_Z ((r.toNat : Int) + (t.toNat : Int))
                                + page_size - page_round_up_Z (r.toNat : Int)))
        else true)
       && decide ((t.toNat : Int) ≤ lim)) := by
  have Hur := u64_range r
  have Hut := u64_range t
  have Hur0 : (r.toNat : Int) ≠ 0 := word_neq0_unsigned r Hr0
  have Hut0 : (t.toNat : Int) ≠ 0 := word_neq0_unsigned t Ht
  have Huadd : ((r + t).toNat : Int) = (r.toNat : Int) + (t.toNat : Int) :=
    u_add_small r t Hnw
  have hpos : decide (0 < (r.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    omega
  have hlt : decide ((r.toNat : Int) < (r.toNat : Int) + (t.toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    omega
  have hbud : vm_backed_bytes (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) = 0 :=
    vm_backed_bytes_nil reserved s r mb sp lim
  have hsub : ((r + t) - r) = t := word_add_sub_cancel r t
  have hvm : (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp).vm_reserved ++
      (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp).vm_maps = reserved := by
    simp
  have hlim : (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp).vm_limit = lim := rfl
  have htop : alloc_top (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) = top := by
    unfold alloc_top
    rw [Htop]
  rw [brk_grow_ok_eq, Huadd, hpos, hlt, hbud, hsub, hvm, hlim, htop]
  simp only [Bool.true_and, ite_true, Int.zero_add]

/-- The two-node brk resolution-set algebra: the failure continuation exists
    exactly when a second-brk resolution fails, and the success one exactly
    when the grow is admissible. -/
theorem T1_iff_T2 (reserved : List (word × word)) (lim : Int) (s mb sp : word)
    (t : word) (bufs : List (List byte)) (r : word)
    (Hr0 : r ≠ BitVec.ofInt 64 0)
    (Hs : (s.toNat : Int) ≤ (r.toNat : Int))
    (Hnw : (r.toNat : Int) + (t.toNat : Int) < 2 ^ 64) :
    ∀ o, T1 reserved lim ((sp.toNat : Int) - stack_max_size) t bufs r o ↔
      ∃ r2, brk_r_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 ∧
             T2 (r + t) bufs r2 o := by
  intro o
  have Hur := u64_range r
  have Hur0 : (r.toNat : Int) ≠ 0 := word_neq0_unsigned r Hr0
  have Huadd : ((r + t).toNat : Int) = (r.toNat : Int) + (t.toNat : Int) :=
    u_add_small r t Hnw
  have hposreq : 0 < ((r + t).toNat : Int) := by rw [Huadd]; omega
  have hbrk : (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp).vm_brk = r := rfl
  have Bridge : ∀ r2, brk_r_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 ↔
      (r2 = r + t ∨ r2 = r) ∧
      brk_grow_ok (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 = true := by
    intro r2
    exact brk_r_ok_grow_iff reserved lim s r [] [] mb sp (r + t) r2 hposreq
      (by rw [Huadd]; omega) (by rw [Huadd]; omega)
  constructor
  · rintro (⟨ho, hcase⟩ | ⟨Hg, ho⟩)
    · -- exit 4: the failure resolution is the OLD break r
      have Ht0 : t ≠ BitVec.ofInt 64 0 := by
        rcases hcase with hc | hc | hc
        · exact absurd hc Hr0
        · omega
        · exact hc
      have hne : r ≠ r + t := by
        intro he
        apply Ht0
        apply word_toNat_eq_zero
        have h := congrArg (fun w : word => (w.toNat : Int)) he
        rw [Huadd] at h
        omega
      refine ⟨r, (Bridge r).mpr ⟨Or.inr rfl, ?_⟩, ?_⟩
      · simpa [hbrk] using
          brk_grow_ok_keep (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)
      · rw [T2_fail_iff _ _ _ hne]
        exact ho
    · -- success: the second brk resolves to r + t
      refine ⟨r + t, (Bridge (r + t)).mpr ⟨Or.inl rfl, ?_⟩, ?_⟩
      · by_cases Ht0 : t = BitVec.ofInt 64 0
        · -- t = 0: keeping the break passes the gate
          have h0 : r + t = r := by rw [Ht0, word_add_0_r]
          rw [h0]
          simpa [hbrk] using
            brk_grow_ok_keep (VmMaps.mkVmMapsFull reserved [] [] s r lim mb sp) r
        · -- t <> 0: growable's page-rounded bool IS the live gate
          rcases Hg.2.2 with Hzero | Hb
          · exact absurd Hzero Ht0
          · rw [brk_grow_ok_self_eq reserved lim ((sp.toNat : Int) - stack_max_size)
              t r s mb sp Hr0 Ht0 rfl Hnw]
            exact Hb
      · rw [T2_succ_iff]
        exact ho
  · rintro ⟨r2, Hrok, Ht2⟩
    rcases (Bridge r2).mp Hrok with ⟨hr2 | hr2, Hgrow⟩
    · -- success resolution: r2 = r + t
      subst hr2
      refine Or.inr ⟨?_, ?_⟩
      · refine ⟨Hr0, Hnw, ?_⟩
        by_cases Ht0 : t = BitVec.ofInt 64 0
        · exact Or.inl Ht0
        · refine Or.inr ?_
          rw [← brk_grow_ok_self_eq reserved lim ((sp.toNat : Int) - stack_max_size)
            t r s mb sp Hr0 Ht0 rfl Hnw]
          exact Hgrow
      · rw [T2_succ_iff] at Ht2
        exact Ht2
    · -- resolution r2 = r
      subst hr2
      rcases Ht2 with ⟨heq, ho⟩ | ⟨hne, ho⟩
      · -- r = r + t: only possible with t = 0, and then growable is trivial
        have Ht0 : t = BitVec.ofInt 64 0 := by
          apply word_toNat_eq_zero
          have h := congrArg (fun w : word => (w.toNat : Int)) heq
          rw [Huadd] at h
          omega
        exact Or.inr ⟨⟨Hr0, Hnw, Or.inl Ht0⟩, ho⟩
      · -- r <> r + t: the failure continuation
        refine Or.inl ⟨ho, Or.inr (Or.inr ?_)⟩
        intro Ht0
        apply hne
        rw [Ht0, word_add_0_r]

/- =========================================================================
   to_outcomes: the exact outcome set of a brk-branching run.
   ========================================================================= -/

section WithSegs

variable (segs : List Segment)

/-- From machine state `ms` and model `model`, the reachable set of
    (bufs, code) outcomes is EXACTLY `U`.  Leaves are `to_wallexit` retry
    loops; interior nodes are brk syscalls branching over every admissible
    resolution. -/
inductive to_outcomes (segs : List Segment) :
    machine_state → Model → ((List (List byte) × word) → Prop) → Prop where
  | tou_wexit (ms : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (U : (List (List byte) × word) → Prop)
      (hfd : fd1chan model)
      (hte : to_wallexit segs (BitVec.ofInt 64 1) bufs code ms)
      (hbm : bufs_modeled bufs)
      (hU : ∀ o, U o ↔ o = (bufs, code)) :
      to_outcomes segs ms model U
  | tou_step (ms ms' : machine_state) (model : Model)
      (U : (List (List byte) × word) → Prop)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hto : to_outcomes segs ms' model U) :
      to_outcomes segs ms model U
  | tou_brk (ms : machine_state) (model : Model) (x8 : word)
      (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 214)
      (hcont : ∀ (eff : SyscallEffect) (model' : Model) (evs : List event),
         syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
         to_outcomes segs (advance_past_svc (apply_effect ms eff)) model'
           (T eff model'))
      (hU : ∀ o, U o ↔
         (∃ (eff : SyscallEffect) (model' : Model) (evs : List event),
            syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)
            ∧ T eff model' o)) :
      to_outcomes segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tou_msteps (ms ms' : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (H : msteps segs ms ms') (Ht : to_outcomes segs ms' model U) :
    to_outcomes segs ms model U := by
  induction H with
  | mst_refl ms => exact Ht
  | mst_step ms ms' ms'' hsvc hstep hsteps ih =>
    exact to_outcomes.tou_step ms ms' model U hsvc hstep (ih Ht)

/- =========================================================================
   brk step shape: haltedness, the fs/fd frames and the lazy ledger.
   ========================================================================= -/

theorem m_halted_vm_forget_range (lo hi : Int) (m : Model) :
    m_halted (vm_forget_range lo hi m) = m_halted m := rfl

theorem m_fs_vm_forget_range (lo hi : Int) (m : Model) :
    m_fs (vm_forget_range lo hi m) = m_fs m := rfl

theorem m_vm_lazy_vm_forget_range_eq (lo hi : Int) (m : Model) :
    m_vm_lazy (vm_forget_range lo hi m) = maps_subtract (m_vm_lazy m) lo hi := rfl

/-- Forgetting VM ranges preserves the non-VM state and cannot introduce
    sparse mappings. -/
theorem forget_vm_ranges_frame (ranges : List (word × word)) (model : Model) :
    m_halted (forget_vm_ranges ranges model) = m_halted model ∧
    m_fs (forget_vm_ranges ranges model) = m_fs model ∧
    m_fds (forget_vm_ranges ranges model) = m_fds model ∧
    (m_vm_lazy model = [] → m_vm_lazy (forget_vm_ranges ranges model) = []) := by
  induction ranges generalizing model with
  | nil => exact ⟨rfl, rfl, rfl, fun h => h⟩
  | cons hd rest ih =>
    obtain ⟨a, n⟩ := hd
    simp only [forget_vm_ranges]
    obtain ⟨h1, h2, h3, h4⟩ :=
      ih (vm_forget_range (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) model)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, m_halted_vm_forget_range]
    · rw [h2, m_fs_vm_forget_range]
    · rw [h3, m_fds_vm_forget_range]
    · intro hlazy
      apply h4
      rw [m_vm_lazy_vm_forget_range_eq, hlazy]
      rfl

/-- brk transitions keep the model running and the fs/fds untouched.  Starting
    from an eager-only model, lifecycle cleanup also leaves no lazy mappings. -/
theorem brk_step_shape (ms : machine_state) (x8 : word) (model : Model)
    (eff : SyscallEffect) (model' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hno : (x8.toNat : Int) = 214)
    (Hs : syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)) :
    evs = [] ∧ m_halted model' = none ∧ m_fs model' = m_fs model ∧
    m_fds model' = m_fds model ∧ m_vm_lazy model' = m_vm_lazy model := by
  obtain ⟨-, hevs, -, hmodel⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).mp Hs
  subst hevs
  subst hmodel
  unfold brk_model with_brk_next
  simp only []
  obtain ⟨h1, h2, h3, h4⟩ := forget_vm_ranges_frame
    (brk_unmaps (eff.eff_ret) (m_vmmaps model).vm_brk)
    (with_vmmaps (brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff.eff_ret)) model)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first | rfl | trivial
  · rw [h1, with_vmmaps_halted]
    exact Hh
  · rw [h2, with_vmmaps_fs]
  · rw [h3, with_vmmaps_fds]
  · rw [h4 (by rw [with_vmmaps_lazy]; exact Hlazy), Hlazy]

/-- One-step inversion at a brk ecall. -/
theorem sstep_brk_inv (ms : machine_state) (model : Model) (x8 : word)
    (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 214)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    ∃ (eff : SyscallEffect) (model' : Model),
      syscall_spec (sys_input segs ms x8) model (.ok eff model' []) ∧
      evs = [] ∧ st = .SNext ⟨advance_past_svc (apply_effect ms eff), model'⟩ := by
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault ms0 model0 hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled ms0 model0 hh hsvc hstep =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x8' eff model0' model0'' evs0 hh hsvc hspec hh' hmat =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    obtain ⟨hevs, hhalt, -, -, hlazy⟩ :=
      brk_step_shape segs ms x8 model eff model0' evs Hh Hlazy Hno hspec
    subst hevs
    rw [materialize_model_accesses_no_lazy model0' _
      (by rw [hlazy]; exact Hlazy)] at hmat
    obtain rfl := Option.some.inj hmat
    exact ⟨eff, model0', hspec, rfl, rfl⟩
  | syscall_materialization_fault ms0 model0 x8' eff model0' evs0 hh hsvc hspec hh' hmat =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    obtain ⟨-, -, -, -, hlazy⟩ :=
      brk_step_shape segs ms x8 model eff model0' evs0 Hh Hlazy Hno hspec
    rw [materialize_model_accesses_no_lazy model0' _
      (by rw [hlazy]; exact Hlazy)] at hmat
    exact nomatch hmat
  | exit ms0 model0 x8' eff model0' evs0 code hh hsvc hspec hh' hk =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    obtain ⟨-, hhalt, -, -, -⟩ :=
      brk_step_shape segs ms x8 model eff model0' evs0 Hh Hlazy Hno hspec
    rw [hhalt] at hh'
    exact nomatch hh'
  | killed ms0 model0 x8' eff model0' evs0 sig hh hsvc hspec hk =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    obtain ⟨-, hhalt, -, -, -⟩ :=
      brk_step_shape segs ms x8 model eff model0' evs0 Hh Hlazy Hno hspec
    rw [m_killed_of_m_halted_none model0' hhalt] at hk
    exact nomatch hk
  | syscall_unmodeled ms0 model0 x8' hh hsvc hspec =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    exact absurd hspec (brk_no_unmodeled segs ms x8 model Hno)

/- =========================================================================
   Trace characterization.
   ========================================================================= -/

/-- The trace of one outcome: its full-delivery writes, then the exit. -/
def outcome_trace (fs : Fs.Fs) (o : List (List byte) × word) : List event :=
  wevents o.1 ++ [event.ExitEv o.2 fs]

/-- The omni reading of a brk-branching run: every execution ends by
    halting with one of the outcomes, having emitted exactly that
    outcome's trace. -/
def outcomes_post (fs : Fs.Fs) (U : (List (List byte) × word) → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = outcome_trace fs out ∧ exits_with out.2 tr o

/-- The omni reading of a `to_outcomes` derivation: every execution ends by
    halting with one of the outcomes, having emitted exactly that outcome's
    trace.  One induction over `to_outcomes`; the leaves are
    `WallSim.to_wallexit_exec`, the brk node's successors are exactly the
    admissible resolutions (`sstep_brk_inv`). -/
theorem to_outcomes_exec (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    exec segs ⟨ms, model⟩ (outcomes_post (m_fs model) U) := by
  revert Hh Hlazy
  induction Hto with
  | tou_wexit ms model bufs code U hfd hte hbm hU =>
    intro Hh Hlazy
    refine exec_conseq segs ⟨ms, model⟩ _ _
      (to_wallexit_exec segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1 bufs code
        ms model Hh Hlazy (fd1chan_fdchan model hfd) hbm hte) ?_
    rintro tr o ⟨heq, hx⟩
    exact ⟨(bufs, code), (hU _).mpr rfl,
      by rw [outcome_trace, ← wevents_ch_fd1]; exact heq, hx⟩
  | tou_step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy
    refine exec_step_only segs ⟨ms, model⟩ _ [] ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact ExitSim.sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih Hh Hlazy
  | tou_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro Hh Hlazy
    refine exec.step ⟨ms, model⟩ (outcomes_post (m_fs model) U) Hh ?_ ?_ ?_
    · -- progress: brk is receptive
      obtain ⟨eff, model', hspec⟩ := brk_receptive segs ms x8 model hno
      obtain ⟨-, hhalt, -, -, hlazy⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno hspec
      exact ⟨[], .SNext ⟨advance_past_svc (apply_effect ms eff), model'⟩,
        sstep.syscall ms model x8 eff model' model' [] Hh hsvc hspec hhalt
          (by rw [materialize_model_accesses_no_lazy model' _ (by rw [hlazy]; exact Hlazy)])⟩
    · -- the error transition is unreachable
      intro evs herr
      obtain ⟨eff, model', -, -, habs⟩ :=
        sstep_brk_inv segs ms model x8 evs .SError Hh Hlazy hsvc hno herr
      exact absurd habs (by simp)
    · -- every admissible resolution leads to its continuation
      intro evs c' hss
      obtain ⟨eff, model', hspec, hevs, hst⟩ :=
        sstep_brk_inv segs ms model x8 evs (.SNext c') Hh Hlazy hsvc hno hss
      subst hevs
      cases hst
      obtain ⟨-, hhalt, hfs, -, hlazy⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno hspec
      refine exec_conseq segs _ _ _
        (ih eff model' [] hspec hhalt (by rw [hlazy]; exact Hlazy)) ?_
      rintro tr o ⟨out, hout, heq, hx⟩
      refine ⟨out, (hU out).mpr ⟨eff, model', [], hspec, hout⟩, ?_, hx⟩
      rw [heq, ← hfs]
      rfl

/-- Bites: the judgment names the outcome, so a different reading of the
    same run is refuted — no exit code outside the outcome set, and no
    silence. -/
theorem to_outcomes_no_other_exit (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (code' : word) (Hne : ∀ o, U o → o.2 ≠ code') :
    ¬ exec segs ⟨ms, model⟩ (exits_with code') := by
  intro Hex
  obtain ⟨tr, o, Hm, Hx⟩ :=
    exec_realizes segs _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  cases o with
  | OHalt c' =>
    obtain ⟨out, Hout, -, Hx1⟩ := Hx
    have Hx' := exec_sound segs ⟨ms, model⟩ (exits_with code') Hex tr (.OHalt c') Hm
    obtain ⟨h1, -⟩ := Hx1
    obtain ⟨h2, -⟩ := Hx'
    rw [h1] at h2
    exact Hne out Hout (Option.some.inj h2)
  | OError c' =>
    obtain ⟨out, -, -, hx⟩ := Hx
    exact hx

theorem to_outcomes_not_silent (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ cosafe segs ⟨ms, model⟩ (fun tr => tr = []) := by
  intro Hc
  obtain ⟨tr, o, Hm, Hx⟩ :=
    exec_realizes segs _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  cases o with
  | OError c' =>
    obtain ⟨out, -, -, hx⟩ := Hx
    exact hx
  | OHalt c' =>
    obtain ⟨out, -, Heq, -⟩ := Hx
    obtain ⟨Hstar, -⟩ := mexec_halt_star segs ⟨ms, model⟩ tr (.OHalt c') Hm c' rfl
    have Hnil : tr = [] := cosafe_star segs ⟨ms, model⟩ (fun tr => tr = []) tr c' Hc Hstar
    rw [Heq] at Hnil
    unfold outcome_trace at Hnil
    cases hw : wevents out.1 with
    | nil => rw [hw] at Hnil; exact absurd Hnil (by simp)
    | cons b bs => rw [hw] at Hnil; exact absurd Hnil (by simp)

theorem to_outcomes_star_only (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      ∃ o, U o ∧ is_prefix tr (outcome_trace (m_fs model) o) := by
  intro tr c Hstar
  obtain ⟨tr', o, -, Hx⟩ := exec_realizes segs _ _
    (exec_star segs ⟨ms, model⟩ _ tr c
      (to_outcomes_exec segs ms model U Hto Hh Hlazy) Hstar)
  obtain ⟨out, Hout, Heq, -⟩ := Hx
  refine ⟨out, Hout, ?_⟩
  rw [← Heq]
  exact is_prefix_app tr tr'

theorem to_outcomes_star_admits (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ∀ o, U o →
      ∃ c, star segs ⟨ms, model⟩ (outcome_trace (m_fs model) o) c := by
  revert Hh Hlazy
  induction Hto with
  | tou_wexit ms model bufs code U hfd hte hbm hU =>
    intro Hh Hlazy o Ho
    have ho : o = (bufs, code) := (hU o).mp Ho
    subst ho
    simpa only [outcome_trace, wevents_ch_fd1] using
      to_wallexit_star_admits segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        bufs code ms model Hh Hlazy (fd1chan_fdchan model hfd) hbm hte
  | tou_step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := ih Hh Hlazy o Ho
    refine ⟨c, ?_⟩
    exact star.step ⟨ms, model⟩ [] ⟨ms', model⟩ (outcome_trace (m_fs model) o) c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]))
      (by simpa only [outcome_trace] using Hstar)
  | tou_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, hspec, ht⟩ := (hU o).mp Ho
    obtain ⟨hevs, hhalt, hfs, -, hlazy⟩ :=
      brk_step_shape segs ms x8 model eff model' evs Hh Hlazy hno hspec
    subst hevs
    obtain ⟨c, Hstar⟩ := ih eff model' [] hspec hhalt
      (by rw [hlazy]; exact Hlazy) o ht
    refine ⟨c, ?_⟩
    refine star.step ⟨ms, model⟩ [] ⟨advance_past_svc (apply_effect ms eff), model'⟩
      (outcome_trace (m_fs model) o) c ?_
      (by rw [← hfs]; simpa only [outcome_trace] using Hstar)
    exact sstep.syscall ms model x8 eff model' model' [] Hh hsvc hspec hhalt
      (by rw [materialize_model_accesses_no_lazy model' _ (by rw [hlazy]; exact Hlazy)])

theorem to_outcomes_no_error (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ reaches_error segs ⟨ms, model⟩ := by
  apply exec_no_error
  refine exec_conseq segs ⟨ms, model⟩ _ _
    (to_outcomes_exec segs ms model U Hto Hh Hlazy) ?_
  rintro tr o ⟨out, -, -, hx⟩
  exact exits_with_never_errors out.2 tr o hx

/- =========================================================================
   Ergonomic brk node: everything in terms of the resolved break value r.
   ========================================================================= -/

/-- `tou_brk` specialized to a continuation family indexed by the
    resolved break `r`.  Per-binary proofs use this: they receive the
    admissibility facts on `r`, the post state written with
    `apply_zeros`, and the updated model, and must return the branch
    outcome set `T' r`. -/
theorem tou_brk_r (ms : machine_state) (model : Model) (x8 : word)
    (T' : word → (List (List byte) × word) → Prop)
    (U : (List (List byte) × word) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 214)
    (Hcont : ∀ r, brk_resolution_ok model (ms_gpr ms 0) r →
      to_outcomes segs
        (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU r []
            (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
            (brk_unmaps r (m_vmmaps model).vm_brk) [] [])))
        (brk_model (ms_gpr ms 0) r model) (T' r))
    (HU : ∀ o, U o ↔
      (∃ r, brk_resolution_ok model (ms_gpr ms 0) r ∧ T' r o)) :
    to_outcomes segs ms model U := by
  refine to_outcomes.tou_brk ms model x8 (fun eff _ => T' eff.eff_ret) U Hsvc Hno ?_ ?_
  · intro eff model' evs hspec
    obtain ⟨heff, -, hok, hmodel⟩ :=
      (brk_ok_iff segs ms x8 model eff model' evs Hno).mp hspec
    subst hmodel
    rw [heff]
    exact Hcont eff.eff_ret hok
  · intro o
    rw [HU o]
    constructor
    · rintro ⟨r, hok, ht⟩
      exact ⟨SyscallEffect.mkEffectU r []
          (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
          (brk_unmaps r (m_vmmaps model).vm_brk) [] [],
        brk_model (ms_gpr ms 0) r model, [],
        brk_ok_intro segs ms x8 model r Hno hok, ht⟩
    · rintro ⟨eff, model', evs, hspec, ht⟩
      obtain ⟨-, -, hok, -⟩ :=
        (brk_ok_iff segs ms x8 model eff model' evs Hno).mp hspec
      exact ⟨eff.eff_ret, hok, ht⟩

/-- Singleton leaf, ergonomic form. -/
theorem tou_wexit_eq (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (hfd : fd1chan model)
    (hte : to_wallexit segs (BitVec.ofInt 64 1) bufs code ms)
    (hbm : bufs_modeled bufs) :
    to_outcomes segs ms model (fun o => o = (bufs, code)) :=
  to_outcomes.tou_wexit ms model bufs code _ hfd hte hbm (fun _ => Iff.rfl)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tou_equiv (ms : machine_state) (model : Model)
    (U V : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs ms model U)
    (HV : ∀ o, V o ↔ U o) :
    to_outcomes segs ms model V := by
  revert V
  induction Hto with
  | tou_wexit ms model bufs code U hfd hte hbm hU =>
    intro V HV
    exact to_outcomes.tou_wexit ms model bufs code V hfd hte hbm
      (fun o => (HV o).trans (hU o))
  | tou_step ms ms' model U hsvc hstep hto ih =>
    intro V HV
    exact to_outcomes.tou_step ms ms' model V hsvc hstep (ih V HV)
  | tou_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro V HV
    refine to_outcomes.tou_brk ms model x8 T V hsvc hno ?_ ?_
    · intro eff model' evs hspec
      exact hcont eff model' evs hspec
    · intro o
      rw [HV o, hU o]

end WithSegs

/- =========================================================================
   Run-level packaging and the equivalence glue.
   ========================================================================= -/

/-- The run-level omni judgment of a brk-branching run. -/
theorem alloc_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (outcomes_post (in_fs inp) U) := by
  show exec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (outcomes_post (in_fs inp) U)
  exact to_outcomes_exec segs _ _ U Hto rfl rfl

theorem alloc_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ ∃ o, U o ∧ is_prefix tr (outcome_trace (in_fs inp) o) := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none :=
    rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] :=
    rfl
  have Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp :=
    rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨o, Ho, Hp'⟩ :=
      to_outcomes_star_only segs _ _ U Hto Hh Hlazy tr' c Hstar
    rw [Hfs] at Hp'
    exact ⟨o, Ho, is_prefix_trans Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ :=
      to_outcomes_star_admits segs _ _ U Hto Hh Hlazy o Ho
    rw [Hfs] at Hstar
    exact ⟨outcome_trace (in_fs inp) o, c, Hstar, Hp⟩

theorem alloc_no_error_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  refine exec_no_error segs _ ?_
  refine exec_conseq segs _ _ _
    (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) ?_
  rintro tr o ⟨out, -, -, hx⟩
  exact exits_with_never_errors out.2 tr o hx

/-- The omni equivalence for two brk-allocating binaries with the SAME
    outcome set `U`, at the two role budgets. -/
theorem alloc_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _ (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp U Hsource)) ?_
    rintro tr o ⟨out, -, -, hx⟩
    exact never_errors_covered source_segs tr o (exits_with_never_errors out.2 tr o hx)
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
        inp U Hsource tr).trans
        (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit
          inp U Htarget tr).symm
    · refine (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit
        inp U Htarget

/-- The `Equivalence`-level equivalence for two brk-allocating binaries
    with the SAME outcome set `U` (each run at ITS quantified break
    base — `U` must be base-independent, which `Run.valid_brk`'s bounds
    give the examples). -/
theorem alloc_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U) :
    modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
            (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource)
  · right
    constructor
    · intro tr
      exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).trans
        (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
    · exact alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

/-!  They are
    checks, not  lemmas. -/

section Sanity

/-- The ASLR break-base constant is 1 GiB. -/
example : brk_aslr_max = 1073741824 := brk_aslr_max_val

/-- A brk(0) QUERY zero-fills nothing. -/
example : brk_zeros (BitVec.ofInt 64 0) (BitVec.ofInt 64 81920)
    (BitVec.ofInt 64 65536) = [] :=
  brk_zeros_query _ _

/-- A brk(0) QUERY grants nothing. -/
example : brk_grants (BitVec.ofInt 64 0) (BitVec.ofInt 64 81920)
    (BitVec.ofInt 64 65536) = [] :=
  brk_grants_query _ _

/-- Keeping the break zero-fills nothing, at concrete values. -/
example : brk_zeros (BitVec.ofInt 64 81920) (BitVec.ofInt 64 65536)
    (BitVec.ofInt 64 65536) = [] :=
  brk_zeros_keep _ _

/-- Keeping the break unmaps nothing, at concrete values. -/
example : brk_unmaps (BitVec.ofInt 64 65536) (BitVec.ofInt 64 65536) = [] :=
  brk_unmaps_keep _

/-- The brk number predicate is Int-characterized at 214. -/
example : (BitVec.ofInt 64 214).toNat = 214 := by decide

/-- A one-page grow from a page-aligned break zero-fills exactly that page
    (the computable half of `brk_zeros_aligned_grow`). -/
example :
    brk_zeros (BitVec.ofInt 64 77824) (BitVec.ofInt 64 73728)
      (BitVec.ofInt 64 69632)
    = [(BitVec.ofInt 64 69632, BitVec.ofInt 64 4096)] := by
  decide

end Sanity

end WithFP1
