/-
  * Common.AsanInit — the INITIAL checker state of an ASan image and its
    soundness.

    GENERIC over the image: a Section over the segments [segs], the address
    table [A] (AsanPlan.atable: hull, writable window, auxv values, entry
    pc), the program headers [ph], and the run's entry/input
    (sp, brk0, mbase, argv, envp, fs, stdin) with the [Run] validity
    premises; the per-image numeric facts are Section hypotheses
    ([img_facts], discharged by computation for each image).  Contents:
    - the valuation [E0] of the initial variables (AP.V_S1 .. V_S2, see
      the plan format): sp = 32768*v0 + 16*v6, argc = v1,
      envc = v2, strlen argv[0] = v3, W = v4 (string block words),
      brk0/4096 = v5, |argv[1]| = v7, uid = v8 (auxv AT_UID/AT_EUID carry
      the launching uid);
    - the argument-block invariant [SINV0] / [argH0] (hidden: the envp
      pointer array and the string block; what they hold: the initial stack
      image) and the four hypotheses of AsanPlanSound about them;
    - [init_cs_ok]: [APS.cs_ok ... E0 (AP.init_acs_of A) R0 FULL0 model0]
      for the components of [Run.init_config] ([PropExec.init_mkst] form),
      and [init_cfg_eq]: init_config = cfg_of R0 (a_entry A) FULL0 model0.
 Nothing of the Section is
  deferred.
  Back corpus and the registers):
  [split_u] (the keystone), the ten read-back `kentry_ok` lemmas
  ([auxv_word_ok], [auxw_ok], [stack_window_ok], [argc_word_ok],
  [argv0_word_ok], [argv1_word_ok], [atrandom_ok], [atrandom_zero_ok],
  [rw_window_ok], [atr_ptr_eq]), and the two register lemmas
  ([init_regs_nth], [init_regs_ok]) — 13 of the 20 formerly-deferred
  declarations, plus the helpers [u_word_add_nat], [auxv_off_Z],
  [natCast_pow64], [pow47_lt_pow64], [mem_eq_of_rdn_one] and
  [stack_to_mem_ne_none].
 The `Mr` terms the fields mention
  are definitionally equal, so the transport needs no work.
  THE `omega` DISCIPLINE THESE PROOFS NEED : `bv_unsigned sp` and `↑sp.toNat` are the same value
  but DIFFERENT atoms, so each proof first fixes one spelling
  (`have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl`) and states every
  arithmetic fact in that spelling; `((2^64 : Nat) : Int)` and `2 ^ 64` are
  likewise distinct ([natCast_pow64] bridges them); and `omega` is only ever
  asked about quantities bounded by `2 ^ 47`, never by `2 ^ 64`.
  The five `Definition`s above ARE real `def`s
  (`AsanInit.inp`, `AsanInit.vals0`, `AsanInit.E0`, `AsanInit.argH0`,
  `AsanInit.SINV0` exist and are definitionally the terms the notations
  spell).
  Two settings are load-bearing and neither is obvious:
  `local instance : FPState := fx0` (many `PropExec` lemmas carry the
  ambient entry-instance argument) and `set_option quotPrecheck false` (the
  notations expand to terms with projections and `let`s).
  There is no proof hole and no extra postulate in this file.
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
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StreamSim
import LinuxSem.Common.StepTac
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.AgentLib
import LinuxSem.Common.StartupAux
import LinuxSem.Common.RefLayout
import LinuxSem.Common.ArgvEnv
import LinuxSem.Common.AsanAcct
import LinuxSem.Common.AsanAcctShape
import LinuxSem.Common.AsanPlacement
import LinuxSem.Common.BackingAlgebra
import LinuxSem.Common.AsanCeil
import LinuxSem.Common.RocqSpelling
import LinuxSem.Common.AxSymExec3
import LinuxSem.Common.AxSymExec3Sound
import LinuxSem.Common.AxSymRun3
import LinuxSem.Common.AsanPlanCore
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.AsanPlanSound

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.AsanInit

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Common.PropExec
open LinuxSem.Common.AgentLib
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.RefLayout
open LinuxSem.Common.ArgvEnv
open LinuxSem.Common.CatExec
open LinuxSem.Common.AsanCeil
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.StepTac
open VmMaps

/-- The entry FP state: every declaration below that reaches a `PropExec`
    lemma carrying the ambient `[FPState]` instance is elaborated at it, the
    same instance `PropExec.init_mkst` pins. -/
local instance : FPState := fx0

/-! ## 1. The run's allocator budget and the initial stack image's size -/

/-- The run's allocation budget: `Definition LIMIT : Z :=
    target_alloc_limit`. -/
def LIMIT : Int := target_alloc_limit

/-- The per-image facts the initial state needs : the program-header triple, the hull, the reservation top,
    the reservation bounds and total size, the writable window, and the
    shadow offset.  Discharged by computation for each concrete image. -/
structure img_facts (segs : List Segment) (A : atable) (ph : PhdrInfo) : Prop where
  /-- the address table records the program headers -/
  if_ph : A.ph_addr_z = (ph.ph_addr : Int) ∧ A.ph_ent_z = (ph.ph_ent : Int) ∧
    A.ph_num_z = (ph.ph_num : Int)
  /-- the hull is a nonempty page-aligned window below 2^32 -/
  if_hull : 0 ≤ A.img_lo ∧ A.img_lo ≤ A.img_hi ∧ A.img_hi ≤ 2 ^ 32 ∧
    A.img_lo % 4096 = 0 ∧ A.img_hi % 4096 = 0
  /-- the reservations end at the hull's top -/
  if_top : reserved_top (segments_reserved segs) = A.img_hi
  /-- every reservation lies inside the hull -/
  if_res : ∀ iv ∈ segments_reserved segs,
    A.img_lo ≤ (iv.1.toNat : Int) ∧ (iv.1.toNat : Int) + (iv.2.toNat : Int) ≤ A.img_hi
  /-- the reservations tile the hull exactly -/
  if_sizes : sum_sizes (segments_reserved segs) = A.img_hi - A.img_lo
  /-- the writable window is in range, and every byte of it is mapped -/
  if_rw : (0 ≤ A.rw_lo ∧ 0 ≤ A.rw_len ∧ A.rw_lo + A.rw_len < 2 ^ 64) ∧
    ∀ (m : word → Option byte) (x : word),
      A.rw_lo ≤ (x.toNat : Int) ∧ (x.toNat : Int) < A.rw_lo + A.rw_len →
      @wview segs m x ≠ none
  /-- the ASan shadow offset is a 47-bit quantity -/
  if_shadow : 0 ≤ A.shadow_off ∧ A.shadow_off ≤ 2 ^ 47

/-- The EXACT size of the initial stack image (the spec's
    `Run.entry_stack_span` is an upper bound of it): the argument/envp
    pointer arrays with their NULLs, the 160-byte auxv, the string block,
    8-byte padding and 16 bytes of slack. -/
def stack_image_size (argv envp : List (List byte)) : Int :=
  let struct_size : Int :=
    8 + ((argv.length : Int) + 1) * 8 + ((envp.length : Int) + 1) * 8 + 160
  let len : Int := struct_size + total_arg_bytes argv + total_arg_bytes envp
  len + ((8 - len % 8) % 8) + 16

/-! ## 2. Sanity checks -/

/-- The budget is the spec's `target_alloc_limit`. -/
theorem LIMIT_eq : LIMIT = 0x8000000000 := rfl

/-- An empty argument block: 8 (argc) + 8 + 8 (envp NULL) + 160 (auxv) = 184,
    then 8 of padding and 16 of slack. -/
theorem stack_image_size_nil :
    stack_image_size [] [] = 184 + ((8 - (184 : Int) % 8) % 8) + 16 := rfl

/-- A one-argument image whose only string is three bytes: `struct_size = 192`,
    `len = 192 + 4 = 196`, padding `(8 - 196 % 8) % 8 = 4`, slack 16, so 216. -/
theorem stack_image_size_one : stack_image_size [[1, 2, 3]] [] = 216 := rfl


section Init

variable {segs : List Segment} {A : atable} {ph : PhdrInfo} {sp : word}
  {rdraw : EntryDraw} {brk0 mbase : word} {argv envp : List (List byte)}
  {fs : Fs.Fs} {stdin : InputStream} {uid gid : word} {hw : word}
  {groups : List word} {net : NetQueue}

local notation "uE" => LinuxSem.Common.AxSymExec3Sound.uE
local notation "bsb" => build_stack_bytes ph sp argv envp uid hw rdraw
local notation "SIMG" => entry_stack_image ph sp argv envp uid hw rdraw
local notation "usp" => bv_unsigned sp
local notation "argc" => (argv.length : Int)
local notation "envc" => (envp.length : Int)
local notation "L0" => (((argv[0]?).getD []).length : Int)
local notation "L1" => (((argv[1]?).getD []).length : Int)
local notation "W" => (((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
    - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) / 8)
/-!  These five therefore
    exist as real Lean `def`s (a downstream file may name them).  The `local
    notation`s just below spell the same bodies at the use sites, because the
    statements then read verbatim  and, more importantly, because
    `omega` is blind to a `def`: every fact about `usp`/`argc`/`envc`/`W`
    has to be visible as a TERM, not hidden behind a constant. -/
def inp (argv envp : List (List byte)) (fs : Fs.Fs) (stdin : InputStream)
    (uid gid hw : word) (groups : List word) (net : NetQueue) : ProcInput :=
  mkProcInput argv envp fs stdin uid gid groups net default_nofile (Z_to_bv 64 0) hw false .Sv48

/-- `Definition vals0`: the nine words `E0` assigns to `V_S1..V_UID`. -/
def vals0 (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (brk0 uid hw : word)
    (rdraw : EntryDraw) : List word :=
  [Z_to_bv 64 (bv_unsigned sp / 32768), Z_to_bv 64 (argv.length : Int),
   Z_to_bv 64 (envp.length : Int), Z_to_bv 64 ((argv[0]?).getD []).length,
   Z_to_bv 64 ((((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
    - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) / 8)),
   Z_to_bv 64 (bv_unsigned brk0 / 4096),
   Z_to_bv 64 ((bv_unsigned sp % 32768) / 16), Z_to_bv 64 ((argv[1]?).getD []).length, uid]

/-- `Definition E0`: the initial valuation. -/
def E0 (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (brk0 uid hw : word)
    (rdraw : EntryDraw) : env :=
  ⟨fun n => (vals0 ph sp argv envp brk0 uid hw rdraw).getD n (Z_to_bv 64 0),
   fun k => if k == K_RND then at_random_bytes (rdraw.ed_random) else []⟩

/-- `Definition argH0`: the hidden argument-block regions. -/
def argH0 (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (uid hw : word)
    (rdraw : EntryDraw) (E : env) (a : word) : Bool :=
  let z := bv_unsigned a
  (((bv_unsigned sp + 8 * (argv.length : Int) + 16 ≤ z) &&
      (z < bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 24))
   || ((bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184 ≤ z) &&
      (z < bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184
        + 8 * ((((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
          - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) / 8)))))

/-- `Definition SINV0`: the initial argument-block invariant. -/
def SINV0 (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (brk0 uid hw : word)
    (rdraw : EntryDraw) (E : env) (M : word → Option byte) : Prop :=
  (∀ n, n < NX0 → E.ev n
    = (E0 ph sp argv envp brk0 uid hw rdraw).ev n)
  ∧ (∀ a, argH0 ph sp argv envp uid hw rdraw E a = true →
      M a = wrap_mem ph sp argv envp uid hw rdraw a)

local notation "vals0" =>
  [Z_to_bv 64 (bv_unsigned sp / 32768), Z_to_bv 64 (argv.length : Int),
   Z_to_bv 64 (envp.length : Int), Z_to_bv 64 ((argv[0]?).getD []).length,
   Z_to_bv 64 ((((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
    - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) / 8)),
   Z_to_bv 64 (bv_unsigned brk0 / 4096),
   Z_to_bv 64 ((bv_unsigned sp % 32768) / 16), Z_to_bv 64 ((argv[1]?).getD []).length, uid]
local notation "E0" =>
  (⟨fun n => (vals0).getD n (Z_to_bv 64 0),
    fun k => if k == K_RND then at_random_bytes (rdraw.ed_random) else []⟩ : env)
local notation "argH0" =>
  (fun (E : env) (a : word) =>
    let z := bv_unsigned a
    (((bv_unsigned sp + 8 * (argv.length : Int) + 16 ≤ z) &&
        (z < bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 24))
     || ((bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184 ≤ z) &&
        (z < bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184
          + 8 * ((((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
            - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) / 8))))))
local notation "SINV0" =>
  (fun (E : env) (M : word → Option byte) =>
    (∀ n, n < NX0 → E.ev n = (E0).ev n)
    ∧ (∀ a, argH0 E a = true → M a = wrap_mem ph sp argv envp uid hw rdraw a))

theorem Hlo' (Hsp : valid_sp sp) : sp_window_lo ≤ bv_unsigned sp := Hsp.1

theorem Hhi' (Hsp : valid_sp sp) : bv_unsigned sp ≤ sp_window_hi := Hsp.2.1

theorem Hal' (Hsp : valid_sp sp) : bv_unsigned sp % 16 = 0 := Hsp.2.2

theorem Hav0 (Hva : valid_argv argv) : 0 < argv.length := by
  have h := valid_argv_nonempty argv Hva
  omega

theorem len_av (Hva : valid_argv argv) : 1 ≤ argc ∧ argc ≤ 1024 := by
  exact ⟨Hva.1.1, valid_argv_len argv Hva⟩

theorem len_ev (Hve : valid_envp envp) : 0 ≤ envc ∧ envc ≤ 256 := by
  exact ⟨by omega, Hve.1⟩

theorem usp_lo (Hsp : valid_sp sp) : 0x7fff80000000 ≤ usp := by
  have h := Hsp.1
  unfold sp_window_lo at h
  exact h

theorem usp_al (Hsp : valid_sp sp) : usp % 16 = 0 := Hsp.2.2

theorem length_bsb_eq :
    ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) = stack_image_size argv envp := by
  unfold build_stack_bytes stack_image_size
  simp only [List.length_append, List.length_replicate, length_n_to_le_8,
    length_flat_map_le8, length_string_addrs_fst, length_flatten_strings,
    length_auxv_bytes, length_at_random_bytes, total_arg_bytes_Z, auxv_size]
  omega

theorem usp_fit (Hfit : entry_stack_fits sp argv envp) :
    bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int)
      ≤ (2 : Int) ^ 47 := by
  have B := build_stack_bytes_within_span ph sp argv envp uid hw rdraw
  have H := Hfit
  unfold entry_stack_fits at H
  have Hhi : sp_window_hi = (2 : Int) ^ 47 := by decide
  rw [Hhi] at H
  have hc : bv_unsigned sp = (sp.toNat : Int) := rfl
  rw [hc] at *
  omega

private theorem emod8_sub (x y : Int) (hx : x % 8 = 0) (hy : y % 8 = 0) : (x - y) % 8 = 0 := by
  obtain ⟨p, hp⟩ := Int.dvd_of_emod_eq_zero hx
  obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hy
  exact Int.emod_eq_zero_of_dvd ⟨p - q, by rw [hp, hq]; omega⟩

private theorem bsb_ge_arith (L a b tab teb : Int)
    (hL : L = 8 + (a + 1) * 8 + (b + 1) * 8 + 160 + tab + teb)
    (ht1 : 0 ≤ tab) (ht2 : 0 ≤ teb) :
    8 * a + 8 * b + 200 ≤ L + (8 - L % 8) % 8 + 16
    ∧ ((L + (8 - L % 8) % 8 + 16 - 16 - (8 * a + 8 * b + 184)) % 8 = 0) := by
  have hr0 : 0 ≤ L % 8 := Int.emod_nonneg _ (by decide)
  have hr8 : L % 8 < 8 := Int.emod_lt_of_pos _ (by decide)
  have h8 : (L + (8 - L % 8) % 8) % 8 = 0 := by
    rcases Int.lt_or_eq_of_le hr0 with h | h
    · have hpad : (8 - L % 8) % 8 = 8 - L % 8 := Int.emod_eq_of_lt (by omega) (by omega)
      rw [hpad]
      have hEm : L % 8 + 8 * (L / 8) = L := Int.emod_add_mul_ediv L 8
      have hEq : L + (8 - L % 8) = 8 * (L / 8 + 1) := by omega
      rw [hEq]
      exact Int.emod_eq_zero_of_dvd ⟨L / 8 + 1, rfl⟩
    · have hL8 : L % 8 = 0 := h.symm
      have hz : (8 - L % 8) % 8 = 0 := by rw [hL8]; decide
      rw [hz, Int.add_zero]
      exact hL8
  refine ⟨by omega, ?_⟩
  have hS : (8 * a + 8 * b + 184) % 8 = 0 := by
    rw [show 8 * a + 8 * b + 184 = 8 * (a + b + 23) by omega]
    exact Int.emod_eq_zero_of_dvd ⟨a + b + 23, rfl⟩
  rw [show L + (8 - L % 8) % 8 + 16 - 16 - (8 * a + 8 * b + 184)
      = (L + (8 - L % 8) % 8) - (8 * a + 8 * b + 184) by omega]
  exact emod8_sub _ _ h8 hS
theorem bsb_ge :
    8 * (argv.length : Int) + 8 * (envp.length : Int) + 200
        ≤ ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int)
    ∧ (((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
        - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) % 8 = 0 := by
  rw [length_bsb_eq]
  unfold stack_image_size
  simp only []
  exact bsb_ge_arith _ _ _ _ _ rfl
    (by rw [total_arg_bytes_Z]; omega) (by rw [total_arg_bytes_Z]; omega)


theorem W_range (Hva : valid_argv argv) (Hve : valid_envp envp) :
    0 ≤ W ∧ 8 * W = ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
        - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)
      ∧ W ≤ 280000 := by
  obtain ⟨G, M⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have B := bsb_bound ph sp argv envp uid hw rdraw Hva Hve
  have hdvd : (8 : Int) ∣ (((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
      - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184)) := Int.dvd_of_emod_eq_zero M
  have hW : 8 * W = ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
      - (8 * (argv.length : Int) + 8 * (envp.length : Int) + 184) :=
    Int.mul_ediv_cancel' hdvd
  refine ⟨by omega, hW, by omega⟩

theorem brk_range (Hbrk : valid_brk segs brk0) (IMG : img_facts segs A ph) :
    A.img_hi ≤ bv_unsigned brk0 ∧ bv_unsigned brk0 ≤ A.img_hi + BRK_ASLR
      ∧ bv_unsigned brk0 % 4096 = 0 := by
  obtain ⟨H1, H2, H3⟩ := Hbrk
  have htop := IMG.if_top
  have hbam : brk_aslr_max = 1073741824 := rfl
  have hps : page_size = 4096 := rfl
  rw [hbam] at H2
  rw [hps] at H3
  rw [htop] at H1 H2
  have hBA : BRK_ASLR = 2147483648 := rfl
  rw [hBA]
  have hc : bv_unsigned brk0 = (brk0.toNat : Int) := rfl
  rw [hc] at *
  omega

theorem usp_hi (ph : PhdrInfo) (argv envp : List (List byte)) (uid hw : word)
    (rdraw : EntryDraw) (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    bv_unsigned sp + 192 ≤ (2 : Int) ^ 47 := by
  have B := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have ha := valid_argv_nonempty argv Hva
  have he : (0 : Int) ≤ (envp.length : Int) := by omega
  omega

theorem uE0 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    uE E0 (.EVar V_S1) = usp / 32768 ∧ uE E0 (.EVar V_S2) = (usp % 32768) / 16
    ∧ uE E0 (.EVar V_ARGC) = argc ∧ uE E0 (.EVar V_ENVC) = envc
    ∧ uE E0 (.EVar V_L0) = L0
    ∧ uE E0 (.EVar V_W) = W ∧ uE E0 (.EVar V_BRK) = bv_unsigned brk0 / 4096 := by
  have h1 : (0x7fff80000000 : Int) ≤ usp := usp_lo Hsp
  have h2 : usp + 192 ≤ (2 : Int) ^ 47 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨W1, W2, W3⟩ := W_range (ph := ph) (sp := sp) (rdraw := rdraw) (uid := uid) (hw := hw) Hva Hve
  obtain ⟨B1, B2⟩ := u64_range brk0
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hcbrk : bv_unsigned brk0 = (brk0.toNat : Int) := rfl
  rw [hcsp] at *
  rw [hcbrk] at *
  have HL0 : (0 : Int) ≤ L0 ∧ L0 ≤ 131071 := by
    have := valid_argv_str_len argv 0 Hva (Hav0 Hva)
    exact ⟨by omega, this⟩
  have k1 : uE E0 (.EVar V_S1) = bv_unsigned (Z_to_bv 64 (usp / 32768)) := rfl
  have k2 : uE E0 (.EVar V_S2) = bv_unsigned (Z_to_bv 64 ((usp % 32768) / 16)) := rfl
  have k3 : uE E0 (.EVar V_ARGC) = bv_unsigned (Z_to_bv 64 (argv.length : Int)) := rfl
  have k4 : uE E0 (.EVar V_ENVC) = bv_unsigned (Z_to_bv 64 (envp.length : Int)) := rfl
  have k5 : uE E0 (.EVar V_L0) = bv_unsigned (Z_to_bv 64 ((argv[0]?).getD []).length) := rfl
  have k6 : uE E0 (.EVar V_W) = bv_unsigned (Z_to_bv 64 W) := rfl
  have k7 : uE E0 (.EVar V_BRK) = bv_unsigned (Z_to_bv 64 (bv_unsigned brk0 / 4096)) := rfl
  have hq1 : bv_unsigned (Z_to_bv 64 (usp / 32768)) = usp / 32768 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hq2 : bv_unsigned (Z_to_bv 64 ((usp % 32768) / 16)) = (usp % 32768) / 16 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hq3 : bv_unsigned (Z_to_bv 64 (argv.length : Int)) = (argv.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  have hq4 : bv_unsigned (Z_to_bv 64 (envp.length : Int)) = (envp.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  have hq5 : bv_unsigned (Z_to_bv 64 ((argv[0]?).getD []).length) = ((argv[0]?).getD []).length :=
    u64_lit _ ⟨by omega, by omega⟩
  have hq6 : bv_unsigned (Z_to_bv 64 W) = W := u64_lit _ ⟨by omega, by omega⟩
  have hq7 : bv_unsigned (Z_to_bv 64 (bv_unsigned brk0 / 4096)) = bv_unsigned brk0 / 4096 := by
    refine u64_lit _ ⟨Int.ediv_nonneg B1 (by decide), ?_⟩
    refine Int.ediv_lt_of_lt_mul (by decide : (0 : Int) < 4096) ?_
    simp only [bv_unsigned] at *
    rw [pow64] at B2 ⊢
    omega
  rw [k1, k2, k3, k4, k5, k6, k7, hq1, hq2, hq3, hq4, hq5, hq6, hq7]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem L1_range (Hva : valid_argv argv) : 0 ≤ L1 ∧ L1 ≤ 131071 := by
  by_cases h : 1 < argv.length
  · have hs := valid_argv_str_len argv 1 Hva h
    constructor <;> omega
  · have hnone : argv[1]? = none := by
      rw [List.getElem?_eq_none_iff]; omega
    simp only [hnone, Option.getD_none, List.length_nil, Int.ofNat_zero]
    omega

theorem uE0_L1 (Hva : valid_argv argv) : uE E0 (.EVar V_L1) = L1 := by
  obtain ⟨h1, h2⟩ := L1_range Hva
  have k : uE E0 (.EVar V_L1) = bv_unsigned (Z_to_bv 64 L1) := rfl
  rw [k]
  have hq : bv_unsigned (Z_to_bv 64 L1) = L1 := u64_lit _ ⟨by omega, by omega⟩
  exact hq

theorem edenot_uid : uid = edenot E0 (.EVar V_UID) := rfl

theorem uE0_uid : uE E0 (.EVar V_UID) = bv_unsigned uid := rfl

theorem u_e_sp0 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) : uE E0 e_sp0 = usp := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  have h3 := usp_al Hsp
  change bv_unsigned (edenot E0 e_sp0) = bv_unsigned sp
  rw [e_sp0]
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_S1, V_S2,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_mul64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (32768 : Int)) = 32768 := by decide
  have hB : bv_unsigned (Z_to_bv 64 (16 : Int)) = 16 := by decide
  have hC : bv_unsigned (Z_to_bv 64 (usp / 32768)) = usp / 32768 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hD : bv_unsigned (Z_to_bv 64 ((usp % 32768) / 16)) = (usp % 32768) / 16 :=
    u64_lit _ ⟨by omega, by omega⟩
  rw [hA, hB, hC, hD]
  simp only [pow64]
  omega

theorem edenot_e_sp0 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) : edenot E0 e_sp0 = sp := by
  have h : uE E0 e_sp0 = usp := u_e_sp0 Hsp Hva Hve Hfit
  apply BitVec.eq_of_toNat_eq
  have h3 : ((edenot E0 e_sp0).toNat : Int) = (sp.toNat : Int) := h
  omega

theorem u_sp8 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    uE E0 (eadd (escale 4096 (.EVar V_S1)) (escale 2 (.EVar V_S2))) = usp / 8 := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  have h3 := usp_al Hsp
  change bv_unsigned (edenot E0 (eadd (escale 4096 (.EVar V_S1)) (escale 2 (.EVar V_S2))))
    = bv_unsigned sp / 8
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_S1, V_S2,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_mul64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (4096 : Int)) = 4096 := by decide
  have hB : bv_unsigned (Z_to_bv 64 (2 : Int)) = 2 := by decide
  have hC : bv_unsigned (Z_to_bv 64 (usp / 32768)) = usp / 32768 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hD : bv_unsigned (Z_to_bv 64 ((usp % 32768) / 16)) = (usp % 32768) / 16 :=
    u64_lit _ ⟨by omega, by omega⟩
  rw [hA, hB, hC, hD]
  simp only [pow64]
  omega

theorem u_e_envp (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) : uE E0 e_envp = usp + 8 * argc + 16 := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  have hUS : bv_unsigned (edenot E0 e_sp0) = bv_unsigned sp := u_e_sp0 Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_envp) = bv_unsigned sp + 8 * (argv.length : Int) + 16
  rw [e_envp]
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_ARGC,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_add64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (8 : Int)) = 8 := by decide
  have hB : bv_unsigned (Z_to_bv 64 (16 : Int)) = 16 := by decide
  have hC : bv_unsigned (Z_to_bv 64 (argv.length : Int)) = (argv.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  rw [hUS, hA, hB, hC]
  simp only [pow64]
  omega

theorem u_e_auxv (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24 := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  have hUE : bv_unsigned (edenot E0 e_envp) = bv_unsigned sp + 8 * (argv.length : Int) + 16 :=
    u_e_envp Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_auxv)
    = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 24
  rw [e_auxv]
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_ENVC,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_add64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (8 : Int)) = 8 := by decide
  have hC : bv_unsigned (Z_to_bv 64 (envp.length : Int)) = (envp.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  rw [hUE, hA, hC]
  simp only [pow64]
  omega

theorem u_e_str0 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    uE E0 e_str0 = usp + 8 * argc + 8 * envc + 184 := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  have hUA : bv_unsigned (edenot E0 e_auxv)
      = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 24 :=
    u_e_auxv Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_str0)
    = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184
  rw [e_str0]
  simp only [eaddz, eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64]
  have hB : bv_unsigned (Z_to_bv 64 (160 : Int)) = 160 := by decide
  rw [hUA, hB]
  simp only [pow64]
  omega

theorem u_e_str1 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    uE E0 e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1 := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  have h3 := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have HL0 : (0 : Int) ≤ L0 ∧ L0 ≤ 131071 := by
    have hs := valid_argv_str_len argv 0 Hva (Hav0 Hva)
    exact ⟨by omega, hs⟩
  have hUS : bv_unsigned (edenot E0 e_str0)
      = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184 :=
    u_e_str0 Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_str1)
    = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184
      + ((argv[0]?).getD []).length + 1
  rw [e_str1]
  simp only [eaddz, eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_L0,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_add64]
  have hB : bv_unsigned (Z_to_bv 64 (1 : Int)) = 1 := by decide
  have hC : bv_unsigned (Z_to_bv 64 (((argv[0]?).getD []).length : Int))
      = ((argv[0]?).getD []).length := u64_lit _ ⟨by omega, by omega⟩
  rw [hUS, hB, hC]
  simp only [pow64]
  omega

theorem u_e_atrandom (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    uE E0 e_atrandom = usp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 := by
  have h1 := usp_lo Hsp
  have h2 := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨W1, W2, W3⟩ := W_range (ph := ph) (sp := sp) (rdraw := rdraw) (uid := uid) (hw := hw) Hva Hve
  have hUS : bv_unsigned (edenot E0 e_str0)
      = bv_unsigned sp + 8 * (argv.length : Int) + 8 * (envp.length : Int) + 184 :=
    u_e_str0 Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_atrandom)
    = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
  rw [e_atrandom]
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu, V_W,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (8 : Int)) = 8 := by decide
  have hC : bv_unsigned (Z_to_bv 64 W) = W := u64_lit _ ⟨by omega, by omega⟩
  rw [hUS, hA, hC]
  simp only [pow64]
  omega

theorem u_e_atr8 (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) : uE E0 e_atr8 = usp / 8 + argc + envc + W := by
  have h1 := usp_lo Hsp
  have h2 := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  have h3 := usp_al Hsp
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨W1, W2, W3⟩ := W_range (ph := ph) (sp := sp) (rdraw := rdraw) (uid := uid) (hw := hw) Hva Hve
  obtain ⟨U1, U2, U3, U4, U5, U6, U7⟩ :=
    uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  change bv_unsigned (edenot E0 e_atr8)
    = bv_unsigned sp / 8 + (argv.length : Int) + (envp.length : Int) + W
  rw [e_atr8]
  simp only [eadd, escale, mkAlu_denot, mkMd_denot, edenot, alu64, mul_div, alu,
    V_S1, V_S2, V_ARGC, V_ENVC, V_W,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [u_add64, u_add64, u_add64, u_add64, u_mul64, u_mul64]
  have hA : bv_unsigned (Z_to_bv 64 (4096 : Int)) = 4096 := by decide
  have hB : bv_unsigned (Z_to_bv 64 (2 : Int)) = 2 := by decide
  have hS : bv_unsigned (Z_to_bv 64 (usp / 32768)) = usp / 32768 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hT : bv_unsigned (Z_to_bv 64 ((usp % 32768) / 16)) = (usp % 32768) / 16 :=
    u64_lit _ ⟨by omega, by omega⟩
  have hC : bv_unsigned (Z_to_bv 64 (argv.length : Int)) = (argv.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  have hD : bv_unsigned (Z_to_bv 64 (envp.length : Int)) = (envp.length : Int) :=
    u64_lit _ ⟨by omega, by omega⟩
  have hE : bv_unsigned (Z_to_bv 64 W) = W := u64_lit _ ⟨by omega, by omega⟩
  rw [hA, hB, hS, hT, hC, hD, hE]
  simp only [pow64]
  have hq : usp = (usp % 32768) + 32768 * (usp / 32768) := (Int.emod_add_mul_ediv usp 32768).symm
  have hr16 : (usp % 32768) % 16 = 0 := by
    rw [Int.emod_emod_of_dvd usp (m := 16) (k := 32768) (by decide)]
    exact h3
  have hr : usp % 32768 = 16 * ((usp % 32768) / 16) :=
    (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hr16)).symm
  omega

local notation "inp" => mkProcInput argv envp fs stdin uid gid groups net default_nofile (Z_to_bv 64 0) hw false .Sv48
local notation "R0" => regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp
local notation "FULL0" => wrap_mem ph sp argv envp uid hw rdraw
local notation "model0" => init_model (segments_reserved segs) brk0 mbase sp LIMIT inp
local notation "cs0" => init_acs_of A
local notation "cs0z" => init_acs_of_zero A
local notation "hid0" => hid A argH0 E0 cs0 model0
local notation "Mr0" => Mr A argH0 E0 cs0 model0 FULL0

theorem model0_facts :
    m_halted model0 = none ∧ m_fds model0 = fds_std ∧ m_tid model0 = none
    ∧ vm_reserved (m_vmmaps model0) = segments_reserved segs
    ∧ vm_maps (m_vmmaps model0) = []
    ∧ vm_noaccess (m_vmmaps model0) = []
    ∧ m_vm_lazy model0 = [] ∧ m_vm_materialized model0 = []
    ∧ vm_limit (m_vmmaps model0) = LIMIT
    ∧ vm_brk (m_vmmaps model0) = brk0
    ∧ vm_start_brk (m_vmmaps model0) = brk0
    ∧ vm_mmap_base (m_vmmaps model0) = mbase ∧ eager_used model0 = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hid0_eq : ∀ a : word,
    hid0 a = (argH0 E0 a || !(in_hull A (bv_unsigned a) || (CEIL ≤ bv_unsigned a))) := by
  intro a
  have h := model0_facts (segs := segs) (sp := sp) (brk0 := brk0) (mbase := mbase)
    (argv := argv) (envp := envp) (fs := fs) (stdin := stdin) (uid := uid) (gid := gid)
    (hw := hw) (groups := groups) (net := net)
  obtain ⟨_, _, _, _, Hm, _, _, _⟩ := h
  simp only [hid, vis]
  rw [Hm]
  simp only [in_ivs, List.any_nil, Bool.false_and, Bool.or_false]

theorem argH0_high (Hsp : valid_sp sp) (Hva : valid_argv argv) :
    ∀ (E : env) (a : word), argH0 E a = true → CEIL ≤ bv_unsigned a := by
  intro E a H
  have Hlo : (0x7fff80000000 : Int) ≤ bv_unsigned sp := Hsp.1
  have Hav : (1 : Int) ≤ (argv.length : Int) := Hva.1.1
  unfold CEIL
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at H
  clear Hsp Hva
  omega

theorem argH0_agree : ∀ (E E' : env) (a : word),
    env_agree NX0 E E' → argH0 E a = argH0 E' a := by
  intro E E' a _
  rfl

theorem SINV0_frame : ∀ (E : env) (M M' : word → Option byte),
    (∀ a, argH0 E a = true → M' a = M a) → SINV0 E M → SINV0 E M' := by
  intro E M M' Hf H
  obtain ⟨H1, H2⟩ := H
  exact ⟨H1, fun a Ha => by rw [Hf a Ha]; exact H2 a Ha⟩

theorem SINV0_agree : ∀ (E E' : env) (M : word → Option byte),
    env_agree NX0 E E' → SINV0 E M → SINV0 E' M := by
  intro E E' M Hag H
  obtain ⟨H1, H2⟩ := H
  obtain ⟨Hag', _⟩ := Hag
  exact ⟨fun n Hn => by rw [← Hag' n (by unfold NX0 at *; omega)]; exact H1 n Hn, H2⟩


theorem spb_eq : split_lit e_sp0 = (e_sp0, 0) := rfl

theorem adenot_SA (E : env) (b : expr) (k : Int) :
    adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k) := rfl

theorem kr_ok (e : expr) (lo hi : Int) (H : lo ≤ uE E0 e ∧ uE E0 e ≤ hi) :
    kentry_ok segs E0 Mr0 (.KRange e lo hi) := H

theorem Mr0_visible (a : word) (Hc : CEIL ≤ bv_unsigned a) (Ha : argH0 E0 a = false) :
    Mr0 a = FULL0 a := by
  simp only [Mr, mrestrict]
  have hc : decide (CEIL ≤ bv_unsigned a) = true := by simp [Hc]
  simp only [hid0_eq a, Ha, hc, Bool.false_or, Bool.or_true, Bool.not_true]
  simp

theorem FULL0_below (a : word) (Ha : usp - 8388608 ≤ bv_unsigned a ∧ bv_unsigned a < usp) :
    FULL0 a = some (Z_to_bv 8 0) := by
  have hc : bv_unsigned a = (a.toNat : Int) := rfl
  have hcs : bv_unsigned sp = (sp.toNat : Int) := rfl
  rw [hc] at Ha
  unfold wrap_mem
  have hs : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw) a = none := by
    unfold stack_to_mem
    have hlt : ¬ (sp.toNat ≤ a.toNat) := by omega
    simp [hlt]
  rw [hs]
  have hP : (sp.toNat : Int) - stack_max_size ≤ (a.toNat : Int) := by
    unfold stack_max_size at *; omega
  have hQ : (a.toNat : Int) < (sp.toNat : Int) := by omega
  rw [ite_eq_left (by simp [hP, hQ])]

theorem FULL0_low (a : word) (Ha : bv_unsigned a < usp - 8388608) : FULL0 a = none := by
  have hc : bv_unsigned a = (a.toNat : Int) := rfl
  have hcs : bv_unsigned sp = (sp.toNat : Int) := rfl
  rw [hc] at Ha
  unfold wrap_mem
  have hs : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw) a = none := by
    unfold stack_to_mem
    have hlt : ¬ (sp.toNat ≤ a.toNat) := by omega
    simp [hlt]
  rw [hs]
  have hP : ¬ ((sp.toNat : Int) - stack_max_size ≤ (a.toNat : Int)) := by
    unfold stack_max_size at *; omega
  rw [ite_eq_right (by simp [hP])]

theorem argH0_range (Hva : valid_argv argv) (Hve : valid_envp envp) (a : word)
    (H : argH0 E0 a = true) :
    (usp + 8 * argc + 16 ≤ bv_unsigned a ∧ bv_unsigned a < usp + 8 * argc + 8 * envc + 24)
    ∨ (usp + 8 * argc + 8 * envc + 184 ≤ bv_unsigned a
        ∧ bv_unsigned a < usp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16) := by
  obtain ⟨W1, W2, W3⟩ := W_range (ph := ph) (sp := sp) (rdraw := rdraw) (uid := uid) (hw := hw) Hva Hve
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at H
  omega

theorem not_argH0 (Hva : valid_argv argv) (Hve : valid_envp envp) (a : word)
    (H : bv_unsigned a < usp + 8 * argc + 16
      ∨ (usp + 8 * argc + 8 * envc + 24 ≤ bv_unsigned a
          ∧ bv_unsigned a < usp + 8 * argc + 8 * envc + 184)
      ∨ usp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16
          ≤ bv_unsigned a) :
    argH0 E0 a = false := by
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  by_cases hh : argH0 E0 a = true
  · have hr := argH0_range (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve a hh
    omega
  · cases hv : argH0 E0 a
    · rfl
    · exact absurd hv hh

theorem Mr0_below (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) (a : word)
    (Ha : usp - 8388608 ≤ bv_unsigned a ∧ bv_unsigned a < usp) :
    Mr0 a = some (Z_to_bv 8 0) := by
  have hlo := usp_lo Hsp
  have hce : CEIL ≤ bv_unsigned a := by
    unfold CEIL; omega
  have hna : argH0 E0 a = false :=
    not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve a
      (by left; obtain ⟨A1, A2⟩ := len_av Hva; omega)
  rw [Mr0_visible (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
    (envp := envp) (uid := uid) (hw := hw) a hce hna]
  exact FULL0_below (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
    (uid := uid) (hw := hw) a Ha

theorem kimg_ok (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KImg A.img_lo A.img_hi) := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := IMG.if_hull
  have hlo := usp_lo Hsp
  have hp32 : (2 : Int) ^ 32 = 4294967296 := by decide
  refine ⟨I1, by rw [pow64]; omega, ?_⟩
  intro i hi1 hi2
  unfold Mr mrestrict
  by_cases h : hid A argH0 E0 cs0 model0 (Z_to_bv 64 i) = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    apply FULL0_low
    have hb : bv_unsigned (Z_to_bv 64 i) = i := u64_lit _ ⟨by omega, by rw [pow64]; omega⟩
    rw [hb]
    omega

theorem rdn_Mr0_stack (Hsp : valid_sp sp) (a : word) (n : Nat)
    (Ha : usp ≤ bv_unsigned a)
    (Hn : bv_unsigned a + (n : Int) ≤ (2 : Int) ^ 64)
    (Hvis : ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (n : Int)
      → argH0 E0 x = false) :
    rdn segs Mr0 a n
      = rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw)) a n := by
  have hlo := usp_lo Hsp
  have hca : bv_unsigned a = (a.toNat : Int) := rfl
  have hcs : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hp64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  rw [hca] at Ha Hn Hvis
  rw [hcs] at hlo
  rw [pow64] at Hn
  rw [← rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw (by omega) (by rw [hp64]; omega)]
  apply rdn_ext
  · rw [hp64]; exact Hn
  · intro x Hx
    have hce : CEIL ≤ bv_unsigned x := by
      have hsp0 : (0x7fff7f800000 : Int) ≤ bv_unsigned sp := by
        have h := usp_lo Hsp
        unfold sp_window_lo at h
        omega
      have hc : CEIL = 0x7fff7f800000 := rfl
      have hcx : bv_unsigned x = (x.toNat : Int) := rfl
      rw [hcx, hc] at *
      omega
    exact Mr0_visible (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) x hce (Hvis x Hx)

theorem kword_stack (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) (b : expr) (k : Int) (v : expr) (w : word)
    (Hw : bv_unsigned (edenot E0 b) + k = bv_unsigned w)
    (Hlo : usp ≤ bv_unsigned w)
    (Hhi : bv_unsigned w + 8
      ≤ usp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int))
    (Hvis : ∀ x : word, bv_unsigned w ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned w + 8
      → argH0 E0 x = false)
    (Hrd : rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw)) w 8
      = some (word_le8 (edenot E0 v))) :
    kentry_ok segs E0 Mr0 (.KWord (SA b k) 8 v) := by
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
    (hw := hw) (rdraw := rdraw) Hfit
  have hlo := usp_lo Hsp
  obtain ⟨B1, B2⟩ := u64_range w
  have hca : bv_unsigned w = (w.toNat : Int) := rfl
  refine ⟨by decide, ?_, ?_⟩
  · unfold flat estart
    rw [Hw]
    simp only [bv_unsigned] at *
    rw [pow64] at B2 ⊢
    omega
  · rw [adenot_SA, Hw, Z_to_bv_unsigned]
    have h8 : bv_unsigned w + ((8 : Nat) : Int) ≤ (2 : Int) ^ 64 := by
      rw [hca]; rw [pow64] at B2 ⊢; omega
    rw [rdn_Mr0_stack (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp w 8 Hlo h8 Hvis]
    rw [Hrd, ← n_to_le_8_spec]


private theorem pow47_lt_pow64 : (2 : Int) ^ 47 < 2 ^ 64 := by decide

theorem u_word_add_nat (a : word) (n : Nat)
    (h1 : 0 ≤ (a.toNat : Int) + (n : Int))
    (h2 : (a.toNat : Int) + (n : Int) < 2 ^ 64) :
    bv_unsigned (a + nat_to_word n) = (a.toNat : Int) + (n : Int) := by
  rw [word_add_nat]
  exact u64_lit _ ⟨h1, h2⟩

theorem auxv_off_Z : ((auxv_off argv envp : Nat) : Int) = 8 * argc + 8 * envc + 24 := by
  unfold auxv_off
  push_cast
  omega

private theorem natCast_pow64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by exact_mod_cast rfl

theorem split_u (E : env) (e b : expr) (k : Int)
    (Hs : split_lit e = (b, k)) (Hk : 0 ≤ k) (Hle : k ≤ uE E e) :
    bv_unsigned (edenot E b) + k = uE E e := by
  have hd := split_lit_denot E e b k Hs
  simp only [LinuxSem.Common.AxSymExec3Sound.uE] at Hle ⊢
  rw [hd] at Hle ⊢
  rw [u_lit64a] at Hle ⊢
  obtain ⟨B1, B2⟩ := u64_range (edenot E b)
  have hB : bv_unsigned (edenot E b) = ((edenot E b).toNat : Int) := rfl
  rw [hB] at Hle ⊢
  have hM : (0 : Int) < 2 ^ 64 := by omega
  rcases Int.lt_or_le (((edenot E b).toNat : Int) + k) (2 ^ 64) with hlt | hge
  · exact (Int.emod_eq_of_lt (by omega) hlt).symm
  · exfalso
    have hEq : (((edenot E b).toNat : Int) + k) % 2 ^ 64
        + 2 ^ 64 * ((((edenot E b).toNat : Int) + k) / 2 ^ 64)
        = ((edenot E b).toNat : Int) + k := Int.emod_add_mul_ediv _ _
    have hq0 : 0 ≤ (((edenot E b).toNat : Int) + k) / 2 ^ 64 :=
      Int.ediv_nonneg (by omega) (by omega)
    have hq1 : (((edenot E b).toNat : Int) + k) / 2 ^ 64 < 1 := by
      have hm : 2 ^ 64 * ((((edenot E b).toNat : Int) + k) / 2 ^ 64) < 2 ^ 64 * 1 := by
        omega
      exact Int.lt_of_mul_lt_mul_left hm (by omega)
    omega

/-! ## The read-back `kentry_ok` lemmas -/

theorem auxv_word_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) (j : Nat) (v : expr) (Hj : j < 20)
    (Hv : (auxv_words ph (at_random_ptr sp argv envp) uid hw)[j]?.getD (Z_to_bv 64 0)
      = edenot E0 v) :
    kentry_ok segs E0 Mr0 (.KWord (SA e_auxb.1 (e_auxb.2 + 8 * (j : Int))) 8 v) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  rw [hcsp] at hlo
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  rw [hcsp] at hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have hbound : auxv_off argv envp + 160 + 16 ≤ (build_stack_bytes ph sp argv envp uid hw rdraw).length :=
    auxv_off_bound (ph := ph) (sp := sp) (rdw := rdraw) (av := argv) (ev := envp) (uid := uid) (hw := hw)
  have Hab : split_lit e_auxv = (e_auxb.1, e_auxb.2) := rfl
  have Hak : e_auxb.2 = 24 := rfl
  have hua := u_e_auxv (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
    (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  rw [hcsp] at hua
  have Hsu := split_u E0 e_auxv e_auxb.1 e_auxb.2 Hab
    (by rw [Hak]; omega)
    (by rw [hua, Hak]; omega)
  have Ha : bv_unsigned (edenot E0 e_auxb.1) = (sp.toNat : Int) + 8 * argc + 8 * envc := by
    rw [hua, Hak] at Hsu
    omega
  have hno : (0 : Int) ≤ (sp.toNat : Int) + ((auxv_off argv envp + 8 * j : Nat) : Int) := by omega
  have hlt : (sp.toNat : Int) + ((auxv_off argv envp + 8 * j : Nat) : Int) < 2 ^ 64 := by
    refine Int.lt_of_le_of_lt ?_ pow47_lt_pow64
    push_cast
    rw [auxv_off_Z]
    omega
  have hw' : bv_unsigned (edenot E0 e_auxb.1) + (e_auxb.2 + 8 * (j : Int))
      = bv_unsigned (sp + nat_to_word (auxv_off argv envp + 8 * j)) := by
    rw [u_word_add_nat sp (auxv_off argv envp + 8 * j) hno hlt]
    rw [Ha, Hak]
    push_cast
    rw [auxv_off_Z]
    omega
  have hlo' : (sp.toNat : Int) ≤ bv_unsigned (sp + nat_to_word (auxv_off argv envp + 8 * j)) := by
    rw [u_word_add_nat sp (auxv_off argv envp + 8 * j) hno hlt]
    push_cast
    omega
  have hhi' : bv_unsigned (sp + nat_to_word (auxv_off argv envp + 8 * j)) + 8
      ≤ (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
    rw [u_word_add_nat sp (auxv_off argv envp + 8 * j) hno hlt]
    push_cast
    rw [auxv_off_Z]
    omega
  have hvis : ∀ x : word,
      bv_unsigned (sp + nat_to_word (auxv_off argv envp + 8 * j)) ≤ bv_unsigned x ∧
      bv_unsigned x < bv_unsigned (sp + nat_to_word (auxv_off argv envp + 8 * j)) + 8 →
      argH0 E0 x = false := by
    intro x Hx
    apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve x
    rw [u_word_add_nat sp (auxv_off argv envp + 8 * j) hno hlt] at Hx
    push_cast at Hx
    rw [auxv_off_Z] at Hx
    omega
  have hrd : rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw))
      (sp + nat_to_word (auxv_off argv envp + 8 * j)) 8 = some (word_le8 (edenot E0 v)) := by
    have hsp_hi : (sp.toNat : Int) ≤ sp_window_hi := Hhi' Hsp
    have := read_auxv_word (segs := segs) (ph := ph) (sp := sp) (rdw := rdraw) (av := argv)
      (ev := envp) (uid := uid) (hw := hw) Hva Hve hsp_hi j Hj
    rw [← Hv]
    exact this
  exact kword_stack (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
    (uid := uid) (hw := hw) Hsp Hva Hve Hfit e_auxb.1 (e_auxb.2 + 8 * (j : Int)) v
    (sp + nat_to_word (auxv_off argv envp + 8 * j)) hw' hlo' hhi' hvis hrd

theorem auxw_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) (i : Int) (ty : Int) (v : expr)
    (Hi : 0 ≤ i ∧ i ≤ 9)
    (H1 : (auxv_words ph (at_random_ptr sp argv envp) uid hw)[(2 * i).toNat]?.getD (Z_to_bv 64 0)
      = Z_to_bv 64 ty)
    (H2 : (auxv_words ph (at_random_ptr sp argv envp) uid hw)[(2 * i + 1).toNat]?.getD (Z_to_bv 64 0)
      = edenot E0 v) :
    know_ok segs E0 Mr0 (auxw i ty v) := by
  have h0 : (0 : Int) ≤ 2 * i := by omega
  have h2i : (((2 * i).toNat : Nat) : Int) = 2 * i := Int.toNat_of_nonneg h0
  have h2i1 : (((2 * i + 1).toNat : Nat) : Int) = 2 * i + 1 :=
    Int.toNat_of_nonneg (by omega)
  have hj1 : (2 * i).toNat < 20 := by omega
  have hj2 : (2 * i + 1).toNat < 20 := by omega
  intro K HK
  unfold auxw at HK
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at HK
  rcases HK with hK | hK
  · rw [hK]
    rw [show e_auxb.snd + 16 * i = e_auxb.snd + 8 * (((2 * i).toNat : Nat) : Int) by omega]
    exact auxv_word_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit _ _ hj1 H1
  · rw [hK]
    rw [show e_auxb.snd + 16 * i + 8 = e_auxb.snd + 8 * (((2 * i + 1).toNat : Nat) : Int) by omega]
    exact auxv_word_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit _ _ hj2 H2

theorem stack_window_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KWr (SA e_sp0 (-8388608)) (.ELit 8388608))
    ∧ kentry_ok segs E0 Mr0 (.KZero (SA e_sp0 (-8388608)) (.ELit 8388608)) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  rw [hcsp] at hlo
  have hhi := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  rw [hcsp] at hhi
  have hsp0 : bv_unsigned (edenot E0 e_sp0) = (sp.toNat : Int) := by
    have h := u_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
    rw [h]
  have Hst : estart E0 (SA e_sp0 (-8388608)) = (sp.toNat : Int) - 8388608 := by
    show bv_unsigned (edenot E0 e_sp0) + (-8388608) = (sp.toNat : Int) - 8388608
    rw [hsp0]
    omega
  have Hl : elenZ E0 (.ELit 8388608) = 8388608 := by
    show ((Z_to_bv 64 8388608).toNat : Int) = 8388608
    exact u_small ⟨by omega, by omega⟩
  have Hfl : flat E0 (SA e_sp0 (-8388608)) 8388608 := by
    have e1 : 0 ≤ (sp.toNat : Int) - 8388608 := by omega
    have e2 : (sp.toNat : Int) - 8388608 ≤ (2 : Int) ^ 47 := by omega
    have e3 : (sp.toNat : Int) - 8388608 + 8388608 ≤ (2 : Int) ^ 47 := by omega
    unfold flat
    rw [Hst]
    exact ⟨e1, Int.lt_of_le_of_lt e2 pow47_lt_pow64, by omega,
      Int.le_trans e3 (Int.le_of_lt pow47_lt_pow64)⟩
  have hmr : ∀ x : word, (sp.toNat : Int) - 8388608 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < (sp.toNat : Int) →
      Mr0 x = some (Z_to_bv 8 0) := by
    intro x hx
    have hb : bv_unsigned x = (x.toNat : Int) := rfl
    exact Mr0_below (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit x
      ⟨by rw [hb]; exact hx.1, by rw [hb]; exact hx.2⟩
  refine ⟨?_, ?_⟩
  · show flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (.ELit 8388608)) ∧ _
    rw [Hl]
    refine ⟨Hfl, ?_⟩
    intro d m Hd Hdm
    rw [Hst] at ⊢
    refine StoreOk.store_ok_of_all segs Mr0 m (BitVec.ofInt 64 ((sp.toNat : Int) - 8388608 + d)) ?_ ?_
    · have hu : ((BitVec.ofInt 64 ((sp.toNat : Int) - 8388608 + d)).toNat : Int)
          = (sp.toNat : Int) - 8388608 + d := u_small ⟨by omega, by omega⟩
      rw [hu, natCast_pow64]
      refine Int.le_trans ?_ (Int.le_of_lt pow47_lt_pow64)
      omega
    · intro x Hx1 Hx2
      have hu : ((BitVec.ofInt 64 ((sp.toNat : Int) - 8388608 + d)).toNat : Int)
          = (sp.toNat : Int) - 8388608 + d := u_small ⟨by omega, by omega⟩
      rw [hu] at Hx1 Hx2
      unfold wview
      rw [hmr x ⟨by omega, by omega⟩]
      simp
  · show flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (.ELit 8388608)) ∧ _
    rw [Hl]
    refine ⟨Hfl, ?_⟩
    intro i Hi1 Hi2
    rw [Hst]
    have hu : bv_unsigned (BitVec.ofInt 64 ((sp.toNat : Int) - 8388608 + i))
        = (sp.toNat : Int) - 8388608 + i := u_small ⟨by omega, by omega⟩
    exact Mr0_below (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
      (BitVec.ofInt 64 ((sp.toNat : Int) - 8388608 + i)) ⟨by rw [hu]; omega, by rw [hu]; omega⟩

theorem argc_word_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KWord (SA e_sp0 0) 8 (.EVar V_ARGC)) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have hsp0 : bv_unsigned (edenot E0 e_sp0) = bv_unsigned sp := by
    have h := u_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
    exact h
  have hHw : bv_unsigned (edenot E0 e_sp0) + (0 : Int) = bv_unsigned sp := by
    rw [hsp0, Int.add_zero]
  have hHhi : bv_unsigned sp + 8 ≤ bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by omega
  have hHvis : ∀ x : word, bv_unsigned sp ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned sp + 8 →
      argH0 E0 x = false := by
    intro x Hx
    apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve x
    left
    omega
  have hHrd : rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw)) sp 8
      = some (word_le8 (edenot E0 (.EVar V_ARGC))) := by
    have h3 : bv_unsigned (edenot E0 (.EVar V_ARGC)) = (argv.length : Int) := by
      have h := (uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit).2.2.1
      simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
      exact h
    have Hv : len_word argv = edenot E0 (.EVar V_ARGC) := by
      apply BitVec.eq_of_toNat_eq
      have hu : ((len_word argv).toNat : Int) = (argv.length : Int) := u_argcN argv Hva
      have h3' : ((edenot E0 (.EVar V_ARGC)).toNat : Int) = (argv.length : Int) := h3
      omega
    rw [← Hv]
    exact read_argc ph segs sp argv envp uid hw rdraw
      (lay_bsb_nw ph sp rdraw argv envp uid hw Hva Hve (Hhi' Hsp))
  exact kword_stack (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
    (uid := uid) (hw := hw) Hsp Hva Hve Hfit e_sp0 0 (.EVar V_ARGC) sp hHw (Int.le_refl _) hHhi hHvis hHrd

theorem argv0_word_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KWord (SA e_sp0 8) 8 e_str0) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have hsp0 : bv_unsigned (edenot E0 e_sp0) = bv_unsigned sp := by
    have h := u_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
    exact h
  have hno : (0 : Int) ≤ (sp.toNat : Int) + ((8 + 8 * 0 : Nat) : Int) := by omega
  have hlt : (sp.toNat : Int) + ((8 + 8 * 0 : Nat) : Int) < 2 ^ 64 := by
    refine Int.lt_of_le_of_lt ?_ pow47_lt_pow64
    push_cast
    omega
  have hHw : bv_unsigned (edenot E0 e_sp0) + (8 : Int)
      = bv_unsigned (sp + nat_to_word (8 + 8 * 0)) := by
    rw [u_word_add_nat sp (8 + 8 * 0) hno hlt]
    rw [hsp0]
    push_cast
    omega
  have hHlo : bv_unsigned sp ≤ bv_unsigned (sp + nat_to_word (8 + 8 * 0)) := by
    rw [u_word_add_nat sp (8 + 8 * 0) hno hlt]
    push_cast
    omega
  have hHhi : bv_unsigned (sp + nat_to_word (8 + 8 * 0)) + 8
      ≤ bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
    rw [u_word_add_nat sp (8 + 8 * 0) hno hlt]
    push_cast
    omega
  have hHvis : ∀ x : word,
      bv_unsigned (sp + nat_to_word (8 + 8 * 0)) ≤ bv_unsigned x ∧
      bv_unsigned x < bv_unsigned (sp + nat_to_word (8 + 8 * 0)) + 8 → argH0 E0 x = false := by
    intro x Hx
    apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve x
    rw [u_word_add_nat sp (8 + 8 * 0) hno hlt] at Hx
    push_cast at Hx
    left
    omega
  have hHrd : rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw))
      (sp + nat_to_word (8 + 8 * 0)) 8 = some (word_le8 (edenot E0 e_str0)) := by
    have hcs : cat_struct_size argv envp = 8 * argv.length + 8 * envp.length + 184 := by
      unfold cat_struct_size auxv_size
      omega
    have htk : total_arg_bytes_nat (argv.take 0) = 0 := rfl
    have he := u_e_str0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at he
    have Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0 := by
      apply BitVec.eq_of_toNat_eq
      have hu := u_cat_argv_ptr sp argv envp Hva Hve (Hlo' Hsp) (Hhi' Hsp) 0 (Hav0 Hva)
      have he := u_e_str0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
      simp only [LinuxSem.Common.AxSymExec3Sound.uE] at he
      have hu' : ((cat_argv_ptr sp argv envp 0).toNat : Int) = (sp.toNat : Int) + ((cat_struct_size argv envp + total_arg_bytes_nat (argv.take 0) : Nat) : Int) := hu
      have he' : ((edenot E0 e_str0).toNat : Int) = bv_unsigned sp + 8 * argc + 8 * envc + 184 := he
      rw [hcsp] at he'
      have hu2 : ((cat_argv_ptr sp argv envp 0).toNat : Int)
          = (sp.toNat : Int) + ((8 * argv.length + 8 * envp.length + 184 : Nat) : Int) := by
        rw [hu', hcs, htk]
      have he2 : ((edenot E0 e_str0).toNat : Int)
          = (sp.toNat : Int) + ((8 * argv.length + 8 * envp.length + 184 : Nat) : Int) := by
        rw [he']
        push_cast
        omega
      have hgoal : ((cat_argv_ptr sp argv envp 0).toNat : Int) = ((edenot E0 e_str0).toNat : Int) := by
        rw [hu2, he2]
      omega
    rw [← Hv]
    exact read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw (Hav0 Hva)
      (lay_bsb_nw ph sp rdraw argv envp uid hw Hva Hve (Hhi' Hsp))
  exact kword_stack (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
    (uid := uid) (hw := hw) Hsp Hva Hve Hfit e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))
    hHw hHlo hHhi hHvis hHrd

theorem argv1_word_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w) := by
  unfold kw_argv1
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have h3 : ((edenot E0 (.EVar V_ARGC)).toNat : Int) = (argv.length : Int) := by
    have h := (uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit).2.2.1
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
    exact h
  have hltu : bv_ltu (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)) = decide (1 < argc) := by
    by_cases hc : 1 < argc
    · have hc' : (1 : Nat) < (edenot E0 (.EVar V_ARGC)).toNat := by omega
      rw [show bv_ltu (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)) = true from by
            unfold bv_ltu
            rw [show (Z_to_bv 64 1).toNat = 1 from by decide]
            exact decide_eq_true hc',
          show decide (1 < argc) = true from decide_eq_true hc]
    · have hc' : ¬ (1 : Nat) < (edenot E0 (.EVar V_ARGC)).toNat := by omega
      rw [show bv_ltu (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)) = false from by
            unfold bv_ltu
            rw [show (Z_to_bv 64 1).toNat = 1 from by decide]
            exact decide_eq_false hc',
          show decide (1 < argc) = false from decide_eq_false hc]
  have hsltu : bv_unsigned (alu64 .SLTU (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)))
      = if decide (1 < argc) then 1 else 0 := by
    rw [u_sltu64, hltu]
  have hmul : bv_unsigned (edenot E0 e_argv1w)
      = if decide (1 < argc) then bv_unsigned (edenot E0 e_str1) else 0 := by
    show bv_unsigned (mul_div .MUL (alu64 .SLTU (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)))
        (edenot E0 e_str1)) = if decide (1 < argc) then bv_unsigned (edenot E0 e_str1) else 0
    rw [show mul_div .MUL (alu64 .SLTU (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC)))
          (edenot E0 e_str1)
        = (alu64 .SLTU (Z_to_bv 64 1) (edenot E0 (.EVar V_ARGC))) * (edenot E0 e_str1) from rfl]
    rw [u_mul64, hsltu]
    obtain ⟨S1, S2⟩ := u64_range (edenot E0 e_str1)
    by_cases hc : 1 < argc
    · rw [ite_eq_left (decide_eq_true hc), ite_eq_left (decide_eq_true hc), Int.one_mul]
      exact Int.emod_eq_of_lt S1 S2
    · rw [ite_eq_right (by simp [hc]), ite_eq_right (by simp [hc]), Int.zero_mul]
      exact Int.zero_emod _
  have hno : (0 : Int) ≤ (sp.toNat : Int) + ((8 + 8 * 1 : Nat) : Int) := by omega
  have hlt : (sp.toNat : Int) + ((8 + 8 * 1 : Nat) : Int) < 2 ^ 64 := by
    refine Int.lt_of_le_of_lt ?_ pow47_lt_pow64
    push_cast
    omega
  have hsp0 : bv_unsigned (edenot E0 e_sp0) = bv_unsigned sp := by
    have h := u_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at h
    exact h
  have hHw : bv_unsigned (edenot E0 e_sp0) + (16 : Int)
      = bv_unsigned (sp + nat_to_word (8 + 8 * 1)) := by
    rw [u_word_add_nat sp (8 + 8 * 1) hno hlt]
    rw [hsp0]
    push_cast
    omega
  have hHlo : bv_unsigned sp ≤ bv_unsigned (sp + nat_to_word (8 + 8 * 1)) := by
    rw [u_word_add_nat sp (8 + 8 * 1) hno hlt]
    push_cast
    omega
  have hHhi : bv_unsigned (sp + nat_to_word (8 + 8 * 1)) + 8
      ≤ bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
    rw [u_word_add_nat sp (8 + 8 * 1) hno hlt]
    push_cast
    omega
  have hHvis : ∀ x : word,
      bv_unsigned (sp + nat_to_word (8 + 8 * 1)) ≤ bv_unsigned x ∧
      bv_unsigned x < bv_unsigned (sp + nat_to_word (8 + 8 * 1)) + 8 → argH0 E0 x = false := by
    intro x Hx
    apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva Hve x
    rw [u_word_add_nat sp (8 + 8 * 1) hno hlt] at Hx
    push_cast at Hx
    left
    omega
  have hHrd : rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw))
      (sp + nat_to_word (8 + 8 * 1)) 8 = some (word_le8 (edenot E0 e_argv1w)) := by
    have Hnw := lay_bsb_nw ph sp rdraw argv envp uid hw Hva Hve (Hhi' Hsp)
    by_cases hc : 1 < argc
    · have hword : edenot E0 e_argv1w = edenot E0 e_str1 := by
        apply BitVec.eq_of_toNat_eq
        have hm := hmul
        rw [ite_eq_left (decide_eq_true hc)] at hm
        have hgoal : ((edenot E0 e_argv1w).toNat : Int) = ((edenot E0 e_str1).toNat : Int) := hm
        omega
      rw [hword]
      have Hav1 : 1 < argv.length := by omega
      have hcs : cat_struct_size argv envp = 8 * argv.length + 8 * envp.length + 184 := by
        unfold cat_struct_size auxv_size
        omega
      have he := u_e_str1 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
      simp only [LinuxSem.Common.AxSymExec3Sound.uE] at he
      have hL0 : 0 ≤ L0 ∧ L0 ≤ 131071 := by
        have hs := valid_argv_str_len argv 0 Hva (Hav0 Hva)
        exact ⟨by omega, hs⟩
      have htk : total_arg_bytes_nat (argv.take 1) = (argv[0]?.getD []).length + 1 := by
        unfold total_arg_bytes_nat
        cases argv with
        | nil => simp at A1
        | cons x t => rfl
      have Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1 := by
        apply BitVec.eq_of_toNat_eq
        have hu := u_cat_argv_ptr sp argv envp Hva Hve (Hlo' Hsp) (Hhi' Hsp) 1 Hav1
        have hu' : ((cat_argv_ptr sp argv envp 1).toNat : Int)
            = (sp.toNat : Int) + ((cat_struct_size argv envp + total_arg_bytes_nat (argv.take 1) : Nat) : Int) := hu
        have he' : ((edenot E0 e_str1).toNat : Int)
            = bv_unsigned sp + 8 * argc + 8 * envc + 184 + L0 + 1 := he
        rw [hcsp] at he'
        have hu2 : ((cat_argv_ptr sp argv envp 1).toNat : Int)
            = (sp.toNat : Int) + ((8 * argv.length + 8 * envp.length + 184
                + ((argv[0]?.getD []).length + 1) : Nat) : Int) := by
          rw [hu', hcs, htk]
        have he2 : ((edenot E0 e_str1).toNat : Int)
            = (sp.toNat : Int) + ((8 * argv.length + 8 * envp.length + 184
                + ((argv[0]?.getD []).length + 1) : Nat) : Int) := by
          rw [he']
          push_cast
          omega
        have hgoal : ((cat_argv_ptr sp argv envp 1).toNat : Int) = ((edenot E0 e_str1).toNat : Int) := by
          rw [hu2, he2]
        omega
      rw [← Hv]
      exact read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1 Hnw
    · have hargc : argv.length = 1 := by omega
      have hword : edenot E0 e_argv1w = Z_to_bv 64 0 := by
        apply BitVec.eq_of_toNat_eq
        have hm := hmul
        rw [ite_eq_right (by simp [hc])] at hm
        have hz : ((Z_to_bv 64 0).toNat : Int) = 0 := by decide
        have hgoal : ((edenot E0 e_argv1w).toNat : Int) = ((Z_to_bv 64 0).toNat : Int) := by
          rw [hz]; exact hm
        omega
      rw [hword]
      rw [show (8 + 8 * 1 : Nat) = 8 + 8 * argv.length from by rw [hargc]]
      exact read_argv_null (segs := segs) (ph := ph) (sp := sp) (rdw := rdraw) (av := argv)
        (ev := envp) (uid := uid) (hw := hw) Hva Hve (Hhi' Hsp)
  exact kword_stack (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
    (uid := uid) (hw := hw) Hsp Hva Hve Hfit e_sp0 16 e_argv1w
    (sp + nat_to_word (8 + 8 * 1)) hHw hHlo hHhi hHvis hHrd

theorem rw_window_ok (IMG : img_facts segs A ph) :
    kentry_ok segs E0 Mr0 (.KWr (SA (.ELit 0) A.rw_lo) (.ELit A.rw_len)) := by
  obtain ⟨⟨R1, Rz, R2⟩, R3⟩ := IMG.if_rw
  have hz : bv_unsigned (Z_to_bv 64 0) = 0 := by decide
  have Hst : estart E0 (SA (.ELit 0) A.rw_lo) = A.rw_lo := by
    show bv_unsigned (edenot E0 (.ELit 0)) + A.rw_lo = A.rw_lo
    rw [edenot_lit]
    rw [hz]
    omega
  have Hl : elenZ E0 (.ELit A.rw_len) = A.rw_len := by
    show ((Z_to_bv 64 A.rw_len).toNat : Int) = A.rw_len
    exact u_small ⟨Rz, by omega⟩
  show flat E0 (SA (.ELit 0) A.rw_lo) (elenZ E0 (.ELit A.rw_len)) ∧ _
  rw [Hl]
  refine ⟨?_, ?_⟩
  · unfold flat
    rw [Hst]
    refine ⟨R1, ?_, Rz, ?_⟩
    · exact Int.lt_of_le_of_lt (show A.rw_lo ≤ A.rw_lo + A.rw_len by omega) R2
    · exact Int.le_of_lt R2
  · intro d m Hd Hdm
    rw [Hst] at ⊢
    cases m with
    | zero => rfl
    | succ m' =>
      refine StoreOk.store_ok_of_all segs Mr0 (m' + 1) (BitVec.ofInt 64 (A.rw_lo + d)) ?_ ?_
      · have hu : ((BitVec.ofInt 64 (A.rw_lo + d)).toNat : Int) = A.rw_lo + d := u_small ⟨by omega, by omega⟩
        rw [hu, natCast_pow64]
        omega
      · intro x Hx1 Hx2
        have hu : ((BitVec.ofInt 64 (A.rw_lo + d)).toNat : Int) = A.rw_lo + d := u_small ⟨by omega, by omega⟩
        rw [hu] at Hx1 Hx2
        exact R3 (Mr0) x ⟨by omega, by omega⟩

theorem atr_ptr_eq (segs : List Segment) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) :
    at_random_ptr sp argv envp = edenot E0 e_atrandom := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  obtain ⟨off, Hp, Hlen, Hmod, Hrd⟩ := at_random_off (segs := segs) (ph := ph) (sp := sp) (rdw := rdraw)
    (av := argv) (ev := envp) (uid := uid) (hw := hw) Hva Hve (Hhi' Hsp)
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  have hlen' : (off : Int) + 16 = ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
    rw [← Hlen]
    push_cast
    omega
  have hno : (0 : Int) ≤ (sp.toNat : Int) + (off : Int) := by
    have := (u64_range sp).1
    omega
  have hlt : (sp.toNat : Int) + (off : Int) < 2 ^ 64 := by
    refine Int.lt_of_le_of_lt ?_ pow47_lt_pow64
    omega
  have hu0 : bv_unsigned (at_random_ptr sp argv envp) = (sp.toNat : Int) + (off : Int) := by
    rw [Hp, u_word_add_nat sp off hno hlt]
  have hu : ((at_random_ptr sp argv envp).toNat : Int) = (sp.toNat : Int) + (off : Int) := hu0
  have he := u_e_atrandom (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
    (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  simp only [LinuxSem.Common.AxSymExec3Sound.uE] at he
  have he' : ((edenot E0 e_atrandom).toNat : Int)
      = (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 := by
    rw [← he, hcsp]
  apply BitVec.eq_of_toNat_eq
  have hgoal : ((at_random_ptr sp argv envp).toNat : Int) = ((edenot E0 e_atrandom).toNat : Int) := by
    rw [hu, he']
    omega
  omega


/-- A one-byte successful read pins the OVERLAY byte (when the overlay defines
    the address). -/
theorem mem_eq_of_rdn_one (m : word → Option byte) (a : word) (b : byte)
    (h : rdn segs m a 1 = some [b]) (hm : m a ≠ none) : m a = some b := by
  cases hv : m a with
  | none => exact absurd hv hm
  | some c =>
    have h1 : rdn segs m a 1 = some [c] := by simp only [rdn, hv]
    rw [h1] at h
    have hcb : c = b := by simpa using h
    rw [hcb]

/-- The mapped image defines every byte of the block above [sp]. -/
theorem stack_to_mem_ne_none (addr : word)
    (h1 : (sp.toNat : Int) ≤ (addr.toNat : Int))
    (h2 : (addr.toNat : Int) < (sp.toNat : Int)
      + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int)) :
    stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw) addr ≠ none := by
  have himg : (build_stack_bytes ph sp argv envp uid hw rdraw).length
      ≤ (entry_stack_image ph sp argv envp uid hw rdraw).length := by
    unfold entry_stack_image
    rw [List.length_append]
    omega
  unfold stack_to_mem
  rw [ite_eq_left (show sp.toNat ≤ addr.toNat by omega)]
  dsimp only
  rw [ite_eq_left (show ((addr.toNat : Int) - (sp.toNat : Int))
      < ((entry_stack_image ph sp argv envp uid hw rdraw).length : Int) by omega)]
  intro h
  rw [List.getElem?_eq_none_iff] at h
  omega

theorem atrandom_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KBlob (SA e_atrb.1 e_atrb.2) (.ELit 16) K_RND) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have Hab : split_lit e_atrandom = (e_atrb.1, e_atrb.2) := rfl
  have Hak : e_atrb.2 = 184 := rfl
  have hua := u_e_atrandom (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
    (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  simp only [LinuxSem.Common.AxSymExec3Sound.uE] at hua
  have Hsu := split_u E0 e_atrandom e_atrb.1 e_atrb.2 Hab
    (by rw [Hak]; omega)
    (by
      simp only [LinuxSem.Common.AxSymExec3Sound.uE]
      rw [hua, Hak]
      omega)
  have Ha : bv_unsigned (edenot E0 e_atrb.1)
      = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 - 184 := by
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at Hsu
    rw [hua, Hak] at Hsu
    omega
  have Hst : estart E0 (SA e_atrb.1 e_atrb.2)
      = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 := by
    show bv_unsigned (edenot E0 e_atrb.1) + e_atrb.2 = _
    rw [Ha, Hak]
    omega
  have Hl : elenZ E0 (.ELit 16) = 16 := by
    show ((Z_to_bv 64 16).toNat : Int) = 16
    exact u_small ⟨by omega, by omega⟩
  have HE : (E0).eb K_RND = at_random_bytes rdraw.ed_random := by
    show (if (K_RND == K_RND) = true then at_random_bytes rdraw.ed_random else []) = _
    rw [ite_eq_left (by simp)]
  show flat E0 (SA e_atrb.1 e_atrb.2) (elenZ E0 (.ELit 16)) ∧ _
  rw [Hl]
  refine ⟨?_, ?_, ?_⟩
  · unfold flat
    rw [Hst]
    refine ⟨by omega, ?_, by omega, ?_⟩
    · refine Int.lt_of_le_of_lt (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 ≤ (2 : Int) ^ 47) pow47_lt_pow64
    · refine Int.le_trans (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + 16 ≤ (2 : Int) ^ 47) (Int.le_of_lt pow47_lt_pow64)
  · rw [HE, length_at_random_bytes]
    rfl
  · intro i Hi1 Hi2
    obtain ⟨off, Hp, Hlen, Hmod, Hrd⟩ := at_random_off (segs := segs) (ph := ph) (sp := sp) (rdw := rdraw)
      (av := argv) (ev := envp) (uid := uid) (hw := hw) Hva Hve (Hhi' Hsp)
    have hlen' : (off : Int) + 16 = ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
      rw [← Hlen]
      push_cast
      omega
    have hno : (0 : Int) ≤ (sp.toNat : Int) + (off : Int) := by
      have := (u64_range sp).1
      omega
    have hlt : (sp.toNat : Int) + (off : Int) < 2 ^ 64 := by
      refine Int.lt_of_le_of_lt (by omega : (sp.toNat : Int) + (off : Int) ≤ (2 : Int) ^ 47) pow47_lt_pow64
    have hpt : bv_unsigned (at_random_ptr sp argv envp) = (sp.toNat : Int) + (off : Int) := by
      rw [Hp, u_word_add_nat sp off hno hlt]
    have hpt' : ((at_random_ptr sp argv envp).toNat : Int) = (sp.toNat : Int) + (off : Int) := hpt
    -- the read address, as the drawn-block address
    have hi : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg Hi1
    have haeq : at_random_ptr sp argv envp + nat_to_word i.toNat
        = BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i) := by
      apply BitVec.eq_of_toNat_eq
      have hL0 : bv_unsigned (at_random_ptr sp argv envp + nat_to_word i.toNat)
          = (sp.toNat : Int) + (off : Int) + (i.toNat : Int) := by
        rw [u_word_add_nat (a := at_random_ptr sp argv envp) (n := i.toNat) (by omega) (by omega), hpt', hi]
      have hL : ((at_random_ptr sp argv envp + nat_to_word i.toNat).toNat : Int)
          = (sp.toNat : Int) + (off : Int) + (i.toNat : Int) := hL0
      have hR : ((BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int)
          = (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
        u_small ⟨by omega, by omega⟩
      have hgoal : ((at_random_ptr sp argv envp + nat_to_word i.toNat).toNat : Int)
          = ((BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int) := by
        rw [hL, hR]
        omega
      omega
    have hrd := Hrd i.toNat 1 (by omega)
    have hsub : ((at_random_bytes rdraw.ed_random).drop i.toNat).take 1
        = [((at_random_bytes rdraw.ed_random).getD i.toNat (Z_to_bv 8 0))] :=
      firstn1_skipn_nth _ _ _ (by rw [length_at_random_bytes]; omega)
    rw [haeq, hsub] at hrd
    rw [Hst]
    have hz0 : (0 : Int) ≤ bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i := by omega
    have hz1 : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i < 2 ^ 64 := by
      refine Int.lt_of_le_of_lt (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i ≤ (2 : Int) ^ 47) pow47_lt_pow64
    have hu : bv_unsigned (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i))
        = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
      u_small ⟨hz0, hz1⟩
    have hu' : ((BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int)
        = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
      u_small ⟨hz0, hz1⟩
    have hvis : argH0 E0 (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) = false := by
      apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hva Hve
      right; right
      rw [hu]
      omega
    have hce : CEIL ≤ bv_unsigned (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) := by
      rw [hu]
      have hCE : CEIL = 0x7fff7f800000 := rfl
      rw [hCE]
      omega
    have hsome : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw)
        (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) ≠ none :=
      stack_to_mem_ne_none (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw)
        (rdraw := rdraw) _ (by rw [hu']; omega) (by rw [hu']; omega)
    have hmem := mem_eq_of_rdn_one (segs := segs) _ _ _ hrd hsome
    rw [Mr0_visible (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) _ hce hvis]
    rw [wrap_above_sp (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw)
      (rnd := rdraw) _ (by omega)]
    exact hmem

theorem atrandom_zero_ok (Hzr : AsanCeil.zero_random_draw rdraw.ed_random)
    (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    kentry_ok segs E0 Mr0 (.KZero (SA e_atrb.1 e_atrb.2) (.ELit 16)) := by
  have hcsp : bv_unsigned sp = (sp.toNat : Int) := rfl
  have hlo := usp_lo Hsp
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw) (rdraw := rdraw)
  have Hab : split_lit e_atrandom = (e_atrb.1, e_atrb.2) := rfl
  have Hak : e_atrb.2 = 184 := rfl
  have hua := u_e_atrandom (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
    (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  simp only [LinuxSem.Common.AxSymExec3Sound.uE] at hua
  have Hsu := split_u E0 e_atrandom e_atrb.1 e_atrb.2 Hab
    (by rw [Hak]; omega)
    (by
      simp only [LinuxSem.Common.AxSymExec3Sound.uE]
      rw [hua, Hak]
      omega)
  have Ha : bv_unsigned (edenot E0 e_atrb.1)
      = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 - 184 := by
    simp only [LinuxSem.Common.AxSymExec3Sound.uE] at Hsu
    rw [hua, Hak] at Hsu
    omega
  have Hst : estart E0 (SA e_atrb.1 e_atrb.2)
      = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 := by
    show bv_unsigned (edenot E0 e_atrb.1) + e_atrb.2 = _
    rw [Ha, Hak]
    omega
  have Hl : elenZ E0 (.ELit 16) = 16 := by
    show ((Z_to_bv 64 16).toNat : Int) = 16
    exact u_small ⟨by omega, by omega⟩
  show flat E0 (SA e_atrb.1 e_atrb.2) (elenZ E0 (.ELit 16)) ∧ _
  rw [Hl]
  refine ⟨?_, ?_⟩
  · unfold flat
    rw [Hst]
    refine ⟨by omega, ?_, by omega, ?_⟩
    · refine Int.lt_of_le_of_lt (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 ≤ (2 : Int) ^ 47) pow47_lt_pow64
    · refine Int.le_trans (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + 16 ≤ (2 : Int) ^ 47) (Int.le_of_lt pow47_lt_pow64)
  · intro i Hi1 Hi2
    obtain ⟨off, Hp, Hlen, Hmod, Hrd⟩ := at_random_off (segs := segs) (ph := ph) (sp := sp) (rdw := rdraw)
      (av := argv) (ev := envp) (uid := uid) (hw := hw) Hva Hve (Hhi' Hsp)
    have hlen' : (off : Int) + 16 = ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) := by
      rw [← Hlen]
      push_cast
      omega
    have hno : (0 : Int) ≤ (sp.toNat : Int) + (off : Int) := by
      have := (u64_range sp).1
      omega
    have hlt : (sp.toNat : Int) + (off : Int) < 2 ^ 64 := by
      refine Int.lt_of_le_of_lt (by omega : (sp.toNat : Int) + (off : Int) ≤ (2 : Int) ^ 47) pow47_lt_pow64
    have hpt : bv_unsigned (at_random_ptr sp argv envp) = (sp.toNat : Int) + (off : Int) := by
      rw [Hp, u_word_add_nat sp off hno hlt]
    have hpt' : ((at_random_ptr sp argv envp).toNat : Int) = (sp.toNat : Int) + (off : Int) := hpt
    have hi : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg Hi1
    have haeq : at_random_ptr sp argv envp + nat_to_word i.toNat
        = BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i) := by
      apply BitVec.eq_of_toNat_eq
      have hL0 : bv_unsigned (at_random_ptr sp argv envp + nat_to_word i.toNat)
          = (sp.toNat : Int) + (off : Int) + (i.toNat : Int) := by
        rw [u_word_add_nat (a := at_random_ptr sp argv envp) (n := i.toNat) (by omega) (by omega), hpt', hi]
      have hL : ((at_random_ptr sp argv envp + nat_to_word i.toNat).toNat : Int)
          = (sp.toNat : Int) + (off : Int) + (i.toNat : Int) := hL0
      have hR : ((BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int)
          = (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
        u_small ⟨by omega, by omega⟩
      have hgoal : ((at_random_ptr sp argv envp + nat_to_word i.toNat).toNat : Int)
          = ((BitVec.ofInt 64 ((sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int) := by
        rw [hL, hR]
        omega
      omega
    have hrd := Hrd i.toNat 1 (by omega)
    have hsub : ((at_random_bytes rdraw.ed_random).drop i.toNat).take 1 = [Z_to_bv 8 0] := by
      rw [show rdraw.ed_random = BitVec.ofInt 128 0 from Hzr, AsanCeil.at_random_bytes_zero,
        repeat_firstn_skipn (BitVec.ofInt 8 0) 16 i.toNat 1 (by omega)]
      rfl
    rw [haeq, hsub] at hrd
    rw [Hst]
    have hz0 : (0 : Int) ≤ bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i := by omega
    have hz1 : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i < 2 ^ 64 := by
      refine Int.lt_of_le_of_lt (by omega : bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i ≤ (2 : Int) ^ 47) pow47_lt_pow64
    have hu : bv_unsigned (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i))
        = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
      u_small ⟨hz0, hz1⟩
    have hu' : ((BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)).toNat : Int)
        = bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i :=
      u_small ⟨hz0, hz1⟩
    have hvis : argH0 E0 (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) = false := by
      apply not_argH0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hva Hve
      right; right
      rw [hu]
      omega
    have hce : CEIL ≤ bv_unsigned (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) := by
      rw [hu]
      have hCE : CEIL = 0x7fff7f800000 := rfl
      rw [hCE]
      omega
    have hsome : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rdraw)
        (BitVec.ofInt 64 (bv_unsigned sp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 + i)) ≠ none :=
      stack_to_mem_ne_none (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw)
        (rdraw := rdraw) _ (by rw [hu']; omega) (by rw [hu']; omega)
    have hmem := mem_eq_of_rdn_one (segs := segs) _ _ _ hrd hsome
    rw [Mr0_visible (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) _ hce hvis]
    rw [wrap_above_sp (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid) (hw := hw)
      (rnd := rdraw) _ (by omega)]
    exact hmem


theorem init_regs_nth (n : Nat) :
    init_regs.getD n (expr.ELit 0) = if n == 2 then e_sp0 else expr.ELit 0 := by
  unfold init_regs
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | 11 => decide
  | 12 => decide
  | 13 => decide
  | 14 => decide
  | 15 => decide
  | 16 => decide
  | 17 => decide
  | 18 => decide
  | 19 => decide
  | 20 => decide
  | 21 => decide
  | 22 => decide
  | 23 => decide
  | 24 => decide
  | 25 => decide
  | 26 => decide
  | 27 => decide
  | 28 => decide
  | 29 => decide
  | 30 => decide
  | 31 => decide
  | 32 => decide
  | m + 33 =>
    have hb : (m + 33 == 2) = false := by
      have h : ¬ (m + 33 = 2) := by omega
      cases hh : (m + 33 == 2) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hh) h
    rw [hb]
    rfl

theorem init_regs_ok (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    regs_ok E0 init_regs (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) := by
  intro r
  show getr (regupd (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp) r
      = edenot E0 (sr_get init_regs r)
  unfold sr_get getr
  by_cases h0 : bv_eqb r 0 = true
  · rw [ite_eq_left h0, ite_eq_left h0]
    show (0 : word) = Z_to_bv 64 0
    decide
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h2 : r = 2
    · subst h2
      rw [regupd_same]
      have hb2 : (ridx 2 == 2) = true := by decide
      rw [init_regs_nth, ite_eq_left hb2]
      exact (edenot_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
        (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit).symm
    · have hidx : (ridx r == 2) = false := by
        have hne : ridx r ≠ 2 := by
          intro h
          apply h2
          rw [← ridx_roundtrip r, h]
          decide
        cases hh : (ridx r == 2) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hh) hne
      rw [init_regs_nth, ite_eq_right (by rw [hidx]; simp)]
      rw [regupd_other (regupd (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0)) 2 sp r h2]
      by_cases h10 : r = 10
      · subst h10
        rw [regupd_same]
        rfl
      · rw [regupd_other (bvmap_empty : BvMap word) 10 (Z_to_bv 64 0) r h10]
        show w0 = Z_to_bv 64 0
        rfl

theorem init_cfg_eq (apc : Nat) (Hpc : (apc : Int) = A.a_entry) :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp
      = cfg_of segs R0 (A.a_entry) FULL0 model0 := by
  unfold init_config cfg_of
  simp only [mkProcInput]
  rw [init_mkst segs apc ph sp argv envp uid hw rdraw]
  rw [← Hpc]
  rfl

/-! ## 4. The initial knowledge, the allowed set, and `cs_ok` -/

/-- `uE` of `eaddz e z`: a literal offset inside the word range, added to a
    denotation that does not wrap.  — `eaddz` is a smart
    constructor, so its denotation needs `mkAlu_denot` before `u_add64` can
    see the addition. -/
theorem uE_eaddz_lit (E : env) (e : expr) (z : Int) (hz0 : 0 ≤ z) (hzu : z < 2 ^ 64)
    (h0 : 0 ≤ uE E e) (hu : uE E e + z < 2 ^ 64) :
    uE E (eaddz e z) = uE E e + z := by
  have hd : uE E (eaddz e z) = bv_unsigned (alu64 .ADD (edenot E e) (Z_to_bv 64 z)) := by
    simp only [LinuxSem.Common.AxSymExec3Sound.uE, eaddz, mkAlu_denot, edenot_lit]
  rw [hd]
  show bv_unsigned (edenot E e + Z_to_bv 64 z) = bv_unsigned (edenot E e) + z
  have hz : bv_unsigned (Z_to_bv 64 z) = z := u64_lit z ⟨hz0, hzu⟩
  rw [u_add64, hz]
  have h0' : (0 : Int) ≤ bv_unsigned (edenot E e) := h0
  have hu' : bv_unsigned (edenot E e) + z < 2 ^ 64 := hu
  exact Int.emod_eq_of_lt (by omega) hu'

/-- `(b - a) / 8 = b / 8 - a / 8` when both are multiples of 8 (). -/
theorem ediv8_sub (a b : Int) (ha : a % 8 = 0) (hb : b % 8 = 0) (hab : a ≤ b) :
    (b - a) / 8 = b / 8 - a / 8 := by
  have ea : a = 8 * (a / 8) := by
    have h := Int.emod_add_mul_ediv a 8
    rw [ha] at h
    omega
  have eb : b = 8 * (b / 8) := by
    have h := Int.emod_add_mul_ediv b 8
    rw [hb] at h
    omega
  have hmain : b - a = 8 * (b / 8 - a / 8) := by omega
  rw [hmain]
  exact Int.mul_ediv_cancel_left (b / 8 - a / 8) (by decide : (8 : Int) ≠ 0)

/-- `init_kn_with` is sound: every entry of the 39-entry initial knowledge
    list is a `kentry_ok` fact about the INITIAL model's restricted memory.
-/
theorem init_kn_with_ok (IMG : img_facts segs A ph) (Hsp : valid_sp sp)
    (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
    (Huid : valid_id uid) (Hbrk : valid_brk segs brk0) (atr : kentry)
    (Hatr : kentry_ok segs E0 Mr0 atr) :
    know_ok segs E0 Mr0 (init_kn_with atr A) := by
  obtain ⟨U1, U2, U3, U4, U5, U6, U7⟩ :=
    uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  have hlo := usp_lo Hsp
  have hhi := usp_hi ph argv envp uid hw rdraw Hsp Hva Hve Hfit
  have hfit := usp_fit (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
    (hw := hw) (rdraw := rdraw) Hfit
  obtain ⟨A1, A2⟩ := len_av Hva
  obtain ⟨E1, E2⟩ := len_ev Hve
  obtain ⟨W1, W2, W3⟩ := W_range (ph := ph) (sp := sp) (rdraw := rdraw) (uid := uid)
    (hw := hw) Hva Hve
  obtain ⟨G, _⟩ := bsb_ge (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
    (hw := hw) (rdraw := rdraw)
  obtain ⟨I1, I2, I3, I4, I5⟩ := IMG.if_hull
  obtain ⟨P1, P2, P3⟩ := IMG.if_ph
  have HL0 : (0 : Int) ≤ L0 ∧ L0 ≤ 131071 :=
    ⟨by omega, valid_argv_str_len argv 0 Hva (Hav0 Hva)⟩
  have HL1 := L1_range Hva
  have hud : (uid.toNat : Int) < 2 ^ 32 - 1 := Huid
  have hua : uE E0 e_atrandom = usp + ((build_stack_bytes ph sp argv envp uid hw rdraw).length : Int) - 16 :=
    u_e_atrandom (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  have hua0 : (0 : Int) ≤ uE E0 e_atrandom := by rw [hua]; omega
  have huau : uE E0 e_atrandom + 16 < 2 ^ 64 := by
    rw [hua]
    have := Int.lt_of_le_of_lt hfit pow47_lt_pow64
    omega
  have hUAU : uE E0 (eaddz e_atrandom 16) = uE E0 e_atrandom + 16 :=
    uE_eaddz_lit E0 e_atrandom 16 (by decide) (by decide) hua0 huau
  have hSW : kentry_ok segs E0 Mr0 (.KWr (SA e_sp0 (-8388608)) (.ELit 8388608))
      ∧ kentry_ok segs E0 Mr0 (.KZero (SA e_sp0 (-8388608)) (.ELit 8388608)) :=
    stack_window_ok (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
      (hw := hw) (rdraw := rdraw) Hsp Hva Hve Hfit
  intro K HK
  unfold init_kn_with at HK
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, or_assoc] at HK
  rcases HK with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
    | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27
    | rfl | rfl | rfl
  · -- V_S1: sp / 32768
    refine kr_ok _ 0xFFFF0000 0xFFFFFFFF ?_
    rw [U1]
    constructor
    · rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 32768)]
      omega
    · rw [Int.ediv_le_iff_le_mul (by decide : (0 : Int) < 32768)]
      omega
  · -- V_S2: (sp % 32768) / 16
    refine kr_ok _ 0 2047 ?_
    rw [U2]
    have hr0 : 0 ≤ bv_unsigned sp % 32768 := Int.emod_nonneg _ (by decide)
    have hr1 : bv_unsigned sp % 32768 < 32768 := Int.emod_lt_of_pos _ (by decide)
    constructor
    · rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 16)]
      omega
    · rw [Int.ediv_le_iff_le_mul (by decide : (0 : Int) < 16)]
      omega
  · -- at_random + 16
    refine kr_ok _ 0x7fff800000c0 0x800000000000 ?_
    rw [hUAU, hua]
    constructor <;> omega
  · -- (at_random - 184) / 8: sp / 8 + argc + envc + W
    refine kr_ok _ 0xFFFF0000001 0xFFFFFFFFFE9 ?_
    rw [u_e_atr8 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit]
    have h1 : 0xFFFF0000000 ≤ bv_unsigned sp / 8 := by
      rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 8)]
      omega
    constructor <;> omega
  · -- sp0: sp
    refine kr_ok _ 0x7fff80000000 0x7fffffffff40 ?_
    rw [u_e_sp0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit]
    constructor <;> omega
  · -- sp / 8
    refine kr_ok _ 0xFFFF0000000 0xFFFFFFFFFE8 ?_
    rw [u_sp8 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit]
    constructor
    · rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 8)]
      omega
    · rw [Int.ediv_le_iff_le_mul (by decide : (0 : Int) < 8)]
      omega
  · refine kr_ok _ 1 1024 ?_
    rw [U3]
    exact ⟨A1, A2⟩
  · refine kr_ok _ 0 256 ?_
    rw [U4]
    exact ⟨E1, E2⟩
  · refine kr_ok _ 0 131071 ?_
    rw [U5]
    exact HL0
  · refine kr_ok _ 0 131071 ?_
    rw [uE0_L1 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hva]
    exact HL1
  · -- V_UID: the launching uid, a 32-bit id
    refine kr_ok _ 0 0xFFFFFFFE ?_
    rw [uE0_uid]
    have hc : bv_unsigned uid = (uid.toNat : Int) := rfl
    rw [hc]
    exact ⟨Int.natCast_nonneg _, by omega⟩
  · refine kr_ok _ 0 280000 ?_
    rw [U6]
    exact ⟨W1, W3⟩
  · -- brk0 / 4096
    refine kr_ok _ (A.img_hi / 4096) ((A.img_hi + BRK_ASLR) / 4096) ?_
    rw [U7]
    obtain ⟨B1, B2, B3⟩ := brk_range Hbrk IMG
    exact ⟨Int.ediv_le_ediv (by decide : (0 : Int) < 4096) B1,
      Int.ediv_le_ediv (by decide : (0 : Int) < 4096) B2⟩
  · exact hSW.1
  · exact hSW.2
  · exact argc_word_ok (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
      (hw := hw) (rdraw := rdraw) Hsp Hva Hve Hfit
  · exact argv0_word_ok (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
      (hw := hw) (rdraw := rdraw) Hsp Hva Hve Hfit
  · exact argv1_word_ok (ph := ph) (sp := sp) (argv := argv) (envp := envp) (uid := uid)
      (hw := hw) (rdraw := rdraw) Hsp Hva Hve Hfit
  · -- auxv pair 0: (AT_PHDR, ph_addr_z)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 0 3 (.ELit A.ph_addr_z) (by decide) ?_ ?_ K h19
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit, P1]
      rfl
  · -- auxv pair 1: (AT_PHENT, ph_ent_z)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 1 4 (.ELit A.ph_ent_z) (by decide) ?_ ?_ K h20
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit, P2]
      rfl
  · -- auxv pair 2: (AT_PHNUM, ph_num_z)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 2 5 (.ELit A.ph_num_z) (by decide) ?_ ?_ K h21
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit, P3]
      rfl
  · -- auxv pair 4: (AT_PAGESZ, 4096)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 4 6 (.ELit 4096) (by decide) ?_ ?_ K h22
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit]
      rfl
  · -- auxv pair 5: (AT_UID, uid)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 5 11 (.EVar V_UID) (by decide) ?_ ?_ K h23
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq]
      rfl
  · -- auxv pair 6: (AT_EUID, uid)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 6 12 (.EVar V_UID) (by decide) ?_ ?_ K h24
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq]
      rfl
  · -- auxv pair 7: (AT_SECURE, 0)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 7 23 (.ELit 0) (by decide) ?_ ?_ K h25
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit]
      rfl
  · -- auxv pair 8: (AT_RANDOM, the AT_RANDOM pointer)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 8 25 e_atrandom (by decide) ?_ ?_ K h26
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq]
      exact atr_ptr_eq segs Hsp Hva Hve Hfit
  · -- auxv pair 9: (AT_NULL, 0)
    refine auxw_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva Hve Hfit 9 0 (.ELit 0) (by decide) ?_ ?_ K h27
    · rw [auxv_words_eq]
      rfl
    · rw [auxv_words_eq, edenot_lit]
      rfl
  · exact Hatr
  · exact kimg_ok IMG Hsp Hva Hve Hfit
  · exact rw_window_ok IMG

/-- `init_kn` (the default knowledge, with the faithful AT_RANDOM entry) is
    sound. -/
theorem init_kn_ok (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) (Huid : valid_id uid)
    (Hbrk : valid_brk segs brk0) : know_ok segs E0 Mr0 (init_kn A) :=
  init_kn_with_ok IMG Hsp Hva Hve Hfit Huid Hbrk atr_entry
    (atrandom_ok (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit)

/-- `init_kn_zero` (the zero AT_RANDOM entry, under the zero-draw hypothesis)
    is sound. -/
theorem init_kn_zero_ok (Hzr : AsanCeil.zero_random_draw rdraw.ed_random)
    (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) (Huid : valid_id uid)
    (Hbrk : valid_brk segs brk0) : know_ok segs E0 Mr0 (init_kn_zero A) :=
  init_kn_with_ok IMG Hsp Hva Hve Hfit Huid Hbrk atr_entry_zero
    (atrandom_zero_ok (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hzr Hsp Hva Hve Hfit)

/-- `pagedown` is the identity on a page-aligned interval end. -/
theorem pagedown_of_page (z : Int) (hz : z % 4096 = 0) : pagedown z = z := by
  unfold pagedown
  rw [ediv_mul_4096, hz, Int.sub_zero]

/-- `pageup` is the identity on a page-aligned interval end. -/
theorem pageup_of_page (z : Int) (hz : z % 4096 = 0) : pageup z = z := by
  unfold pageup
  have h1 : (z + 4095) % 4096 = 4095 := by
    rw [Int.add_emod, hz]
    decide
  rw [ediv_mul_4096, h1]
  omega

/-- The initial allowed set, spelled out: the hull and the ceiling window with
    their ASan shadows, each rounded outward to a page. -/
theorem allowA_init (IMG : img_facts segs A ph) :
    allowA A E0 cs0 =
      [(pagedown A.img_lo, pageup (A.img_lo + (A.img_hi - A.img_lo))),
       (pagedown (A.shadow_off + A.img_lo / 8),
        pageup (A.shadow_off + (A.img_lo + (A.img_hi - A.img_lo)) / 8)),
       (pagedown CEIL, pageup (CEIL + (2 ^ 47 - CEIL))),
       (pagedown (A.shadow_off + CEIL / 8),
        pageup (A.shadow_off + (CEIL + (2 ^ 47 - CEIL)) / 8))] := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := IMG.if_hull
  have h1 : bv_unsigned (Z_to_bv 64 A.img_lo) = A.img_lo := u64_lit _ ⟨I1, by omega⟩
  have h2 : bv_unsigned (Z_to_bv 64 (A.img_hi - A.img_lo)) = A.img_hi - A.img_lo :=
    u64_lit _ ⟨by omega, by omega⟩
  have h3 : bv_unsigned (Z_to_bv 64 CEIL) = CEIL := by
    refine u64_lit _ ⟨by unfold CEIL; decide, by unfold CEIL; decide⟩
  have h4 : bv_unsigned (Z_to_bv 64 (zpow 2 47 - CEIL)) = 2 ^ 47 - CEIL := by
    refine u64_lit _ ⟨?_, ?_⟩
    · have hz : zpow 2 47 = ((2 : Int) ^ 47) := rfl
      rw [hz]; unfold CEIL; decide
    · have hz : zpow 2 47 = ((2 : Int) ^ 47) := rfl
      rw [hz]; unfold CEIL; decide
  have hz47 : zpow 2 47 = ((2 : Int) ^ 47) := rfl
  unfold allowA init_acs_of init_acs_of_with init_vis
  simp only [List.append_nil, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, allow1, sh_lo, sh_hi,
    LinuxSem.Common.AxSymExec3Sound.uE, LinuxSem.Common.AsanPlanSound.uE,
    edenot_lit, h1, h2, h3, h4, hz47]
  rfl

/-- The initial allowed set costs at most `vis_cost` of each of the two
    windows, and that fits the run's budget. -/
theorem abytes_init (IMG : img_facts segs A ph) :
    A_bytes (allowA A E0 cs0) ≤ vis_cost (A.img_hi - A.img_lo) + vis_cost (2 ^ 47 - CEIL)
    ∧ vis_cost (A.img_hi - A.img_lo) + vis_cost (2 ^ 47 - CEIL) ≤ LIMIT := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := IMG.if_hull
  obtain ⟨S1, S2⟩ := IMG.if_shadow
  have hC8 : CEIL % 4096 = 0 := by unfold CEIL; decide
  have h8lo : A.img_lo % 8 = 0 := by
    rw [← Int.emod_emod_of_dvd (A.img_lo) (m := 8) (k := 4096) (by decide), I4]
    decide
  have h8hi : A.img_hi % 8 = 0 := by
    rw [← Int.emod_emod_of_dvd (A.img_hi) (m := 8) (k := 4096) (by decide), I5]
    decide
  have h8c : CEIL % 8 = 0 := by
    rw [← Int.emod_emod_of_dvd (CEIL) (m := 8) (k := 4096) (by decide), hC8]
    decide
  have h8p : (2 : Int) ^ 47 % 8 = 0 := by decide
  have hd2 : (2 : Int) ^ 47 - CEIL = 2155872256 := by unfold CEIL; decide
  constructor
  · rw [allowA_init IMG]
    simp only [A_bytes, vis_cost]
    rw [show A.img_lo + (A.img_hi - A.img_lo) = A.img_hi by omega]
    rw [pagedown_of_page A.img_lo I4, pageup_of_page A.img_hi I5,
      pagedown_of_page CEIL hC8, show CEIL + (2 ^ 47 - CEIL) = 2 ^ 47 by omega,
      pageup_of_page (2 ^ 47) (by decide)]
    have hp2 := pageup_minus_pagedown (A.shadow_off + A.img_lo / 8)
      (A.shadow_off + A.img_hi / 8) (by omega)
    have hp4 := pageup_minus_pagedown (A.shadow_off + CEIL / 8)
      (A.shadow_off + 2 ^ 47 / 8) (by omega)
    have hq1 : (A.img_hi - A.img_lo) / 8 = A.img_hi / 8 - A.img_lo / 8 :=
      ediv8_sub A.img_lo A.img_hi h8lo h8hi I2
    have hq2 : ((2 : Int) ^ 47 - CEIL) / 8 = 2 ^ 47 / 8 - CEIL / 8 :=
      ediv8_sub CEIL (2 ^ 47) h8c h8p (by omega)
    rw [hq1, hq2]
    omega
  · have hd1 : A.img_hi - A.img_lo ≤ 2 ^ 32 := by omega
    have hq1 : (A.img_hi - A.img_lo) / 8 ≤ 2 ^ 29 := by
      rw [Int.ediv_le_iff_le_mul (by decide : (0 : Int) < 8)]
      omega
    have hq2 : ((2 : Int) ^ 47 - CEIL) / 8 ≤ 269484032 := by
      rw [hd2]
      decide
    simp only [vis_cost, LIMIT, target_alloc_limit]
    omega

/-- `cs_ok` for the initial checker state, with an ARBITRARY initial
    knowledge list: every field but `co_know` is independent of the
    knowledge (in particular `allowA` only reads `a_vis`/`a_ghost`), so the
    faithful and the zero AT_RANDOM entry share one proof.  Both
    `init_cs_ok` and `init_cs_ok_zero` are instances. -/
theorem cs_ok_init_kn (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) (Hmb : valid_mmap_base mbase)
    (Hbrk : valid_brk segs brk0) (kn0 : List kentry) (Hkn : know_ok segs E0 Mr0 kn0) :
    cs_ok segs A LIMIT SINV0 argH0 fs E0 (init_acs_of_with kn0 A) R0 FULL0 model0 := by
  have hAB : A_bytes (allowA A E0 cs0) ≤ vis_cost (A.img_hi - A.img_lo) + vis_cost (2 ^ 47 - CEIL)
      ∧ vis_cost (A.img_hi - A.img_lo) + vis_cost (2 ^ 47 - CEIL) ≤ LIMIT := abytes_init IMG
  refine
    { co_regs := ?_
      co_log := ?_
      co_know := ?_
      co_halt := ?_
      co_fds := ?_
      co_fs := ?_
      co_tid := ?_
      co_res := ?_
      co_limit := ?_
      co_maps := ?_
      co_holes := ?_
      co_seps := ?_
      co_wf := ?_
      co_bounds := ?_
      co_lazyb := ?_
      co_nasub := ?_
      co_none := ?_
      co_kinds := ?_
      co_totsz := ?_
      co_split := ?_
      co_brk := ?_
      co_sbrk := ?_
      co_eager := ?_
      co_abytes := ?_
      co_minv := ?_
      co_zero := ?_
      co_sinv := ?_ }
  · exact init_regs_ok (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv)
      (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  · rfl
  · exact Hkn
  · rfl
  · rfl
  · rfl
  · intro _; rfl
  · rfl
  · rfl
  · rfl
  · intro m hm
    simp only [init_acs_of_with, List.not_mem_nil] at hm
  · exact seps.nil
  · unfold LinuxSem.Common.BackingAlgebra.model_ivs_wf
    exact ⟨LinuxSem.Common.BackingAlgebra.ivs_wf_nil,
      LinuxSem.Common.BackingAlgebra.ivs_wf_nil,
      LinuxSem.Common.BackingAlgebra.ivs_wf_nil,
      init_sp_ok_init_model _ _ _ _ _ _ Hsp⟩
  · intro iv hiv
    have hM : (m_vmmaps model0).vm_maps = [] := rfl
    rw [hM] at hiv
    simp at hiv
  · intro iv hiv
    have hL : m_vm_lazy model0 = [] := rfl
    rw [hL] at hiv
    simp at hiv
  · intro z hz
    exact hz
  · intro m hm
    simp only [init_acs_of_with, List.not_mem_nil] at hm
  · intro m hm
    simp only [init_acs_of_with, List.not_mem_nil] at hm
  · show sum_sizes (segments_reserved segs ++ []) ≤ A.img_hi - A.img_lo
    rw [List.append_nil, IMG.if_sizes]
    omega
  · obtain ⟨Y1, Y2, Y3⟩ := Hmb
    refine ⟨bv_unsigned mbase, ?_, ?_, ?_, ?_⟩
    · show MBASE_MIN ≤ bv_unsigned mbase
      have hc : bv_unsigned mbase = (mbase.toNat : Int) := rfl
      rw [hc]
      have hM : MBASE_MIN = mmap_base_min := rfl
      rw [hM]
      exact Y1
    · show bv_unsigned mbase % 4096 = 0
      have hc : bv_unsigned mbase = (mbase.toNat : Int) := rfl
      rw [hc]
      unfold page_size at Y3
      exact Y3
    · show bv_unsigned mbase ≤ bv_unsigned (m_vmmaps model0).vm_mmap_base
      exact Int.le_refl _
    · show LinuxSem.Common.AsanPlacement.ledger_split
        (segments_reserved segs ++ []) LinuxSem.Common.AsanPlacement.kHighMemBeg
        (bv_unsigned mbase)
      intro b sx Hin
      rw [List.append_nil] at Hin
      left
      show (b.toNat : Int) + (sx.toNat : Int) ≤ LinuxSem.Common.AsanPlacement.kHighMemBeg
      have hr : (b.toNat : Int) + (sx.toNat : Int) ≤ A.img_hi := (IMG.if_res (b, sx) Hin).2
      have h32 : A.img_hi ≤ 2 ^ 32 := IMG.if_hull.2.2.1
      unfold LinuxSem.Common.AsanPlacement.kHighMemBeg
      omega
  · show (m_vmmaps model0).vm_brk = edenot E0 (escale 4096 (.EVar V_BRK))
    have hb : bv_unsigned (edenot E0 (escale 4096 (.EVar V_BRK)))
        = (4096 * (bv_unsigned brk0 / 4096)) % 2 ^ 64 := by
      have h1 : edenot E0 (escale 4096 (.EVar V_BRK))
          = Z_to_bv 64 4096 * edenot E0 (.EVar V_BRK) := by
        simp only [escale, mkMd_denot, edenot, mul_div]
      rw [h1, u_mul64]
      have h4096 : bv_unsigned (Z_to_bv 64 (4096 : Int)) = 4096 := by decide
      obtain ⟨-, -, -, -, -, -, U7⟩ :=
        uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (argv := argv) (envp := envp)
          (uid := uid) (hw := hw) Hsp Hva Hve Hfit
      have hU : bv_unsigned (edenot E0 (.EVar V_BRK)) = bv_unsigned brk0 / 4096 := U7
      rw [h4096, hU]
    obtain ⟨B1, B2, B3⟩ := brk_range Hbrk IMG
    have hb2 : 4096 * (bv_unsigned brk0 / 4096) = bv_unsigned brk0 := by
      have hh := Int.emod_add_mul_ediv (bv_unsigned brk0) 4096
      rw [B3] at hh
      omega
    have hR : bv_unsigned (edenot E0 (escale 4096 (.EVar V_BRK))) = bv_unsigned brk0 := by
      rw [hb, hb2]
      obtain ⟨B4, B5⟩ := u64_range brk0
      have hcbrk : bv_unsigned brk0 = (brk0.toNat : Int) := rfl
      rw [hcbrk]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    apply BitVec.eq_of_toNat_eq
    show brk0.toNat = (edenot E0 (escale 4096 (.EVar V_BRK))).toNat
    have h3 : ((edenot E0 (escale 4096 (.EVar V_BRK))).toNat : Int) = (brk0.toNat : Int) := hR
    omega
  · show bv_unsigned (m_vmmaps model0).vm_start_brk ≤ bv_unsigned (m_vmmaps model0).vm_brk
    exact Int.le_refl _
  · show eager_used model0 ≤ 0
    have h0 : eager_used model0 = 0 := rfl
    omega
  · exact hAB.1
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact List.nodup_nil
    · intro p hp
      have hL : m_vm_materialized model0 = [] := rfl
      rw [hL] at hp
      simp at hp
    · intro p hp
      have hL : m_vm_materialized model0 = [] := rfl
      rw [hL] at hp
      simp at hp
    · intro p hp
      have hL : m_vm_materialized model0 = [] := rfl
      rw [hL] at hp
      simp at hp
    · have h0 : eager_used model0 = 0 := rfl
      show eager_used model0 + A_bytes (allowA A E0 cs0) ≤ LIMIT
      rw [h0]
      omega
  · intro a _ h1 h2 _ _
    have hM : (m_vmmaps model0).vm_maps = [] := rfl
    rw [hM] at h1
    simp [in_ivs] at h1
  · refine ⟨?_, ?_⟩
    · intro n _
      rfl
    · intro a _
      rfl

/-- THE SUMMIT: the initial checker state (over `init_kn`) is sound — all 27
    `cs_ok` fields at once. -/
theorem init_cs_ok (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) (Huid : valid_id uid)
    (Hbrk : valid_brk segs brk0) (Hmb : valid_mmap_base mbase) :
    cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0 :=
  cs_ok_init_kn IMG Hsp Hva Hve Hfit Hmb Hbrk (init_kn A)
    (init_kn_ok IMG Hsp Hva Hve Hfit Huid Hbrk)

/-- ZERO DRAW: the same configuration over `init_kn_zero`, under the
    (false on every real run) zero-draw hypothesis. -/
theorem init_cs_ok_zero (Hzr : AsanCeil.zero_random_draw rdraw.ed_random)
    (IMG : img_facts segs A ph) (Hsp : valid_sp sp) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp) (Huid : valid_id uid)
    (Hbrk : valid_brk segs brk0) (Hmb : valid_mmap_base mbase) :
    cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0z R0 FULL0 model0 :=
  cs_ok_init_kn IMG Hsp Hva Hve Hfit Hmb Hbrk (init_kn_zero A)
    (init_kn_zero_ok Hzr IMG Hsp Hva Hve Hfit Huid Hbrk)

end Init

/-! ## 3.  `init_cs_ok` / `init_cs_ok_zero` are instances of
`cs_ok_init_kn`; `Hzr` is used only by `atrandom_zero_ok` /
`init_kn_zero_ok` / `init_cs_ok_zero`.
-/

/-
--- Lemma init_kn_with_ok  (AsanInit)
Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).

--- Lemma init_kn_ok  (AsanInit)
Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).

--- Lemma init_kn_zero_ok  (AsanInit)
Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).

--- Lemma allowA_init  (AsanInit)
Lemma allowA_init : allowA A E0 cs0 =
  [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
   (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
   (pagedown CEIL, pageup (CEIL + (2 ^ 47 - CEIL)));
   (pagedown (shadow_off A + CEIL / 8), pageup (shadow_off A + (CEIL + (2 ^ 47 - CEIL)) / 8))].

--- Lemma abytes_init  (AsanInit)
Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL)
                    /\ vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL) <= LIMIT.

--- Theorem init_cs_ok  (AsanInit)
Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0.

--- Theorem init_cs_ok_zero  (AsanInit)
Theorem init_cs_ok_zero : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0z R0 FULL0 model0.

-/

end LinuxSem.Common.AsanInit
