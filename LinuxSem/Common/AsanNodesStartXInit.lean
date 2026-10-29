/-

  * AsanNodesStartXInit — XEnvScan / XPnScan / XLayout for ANY class invariant
    [SINV] implying AsanInit's concrete [SINV0 ph sp rdraw brk0 argv envp uid hw]
    (e.g. SINV0 itself, the argument-leaf SINV1, the main-phase SINVm), with
    [argH0 ph sp rdraw argv envp uid hw], for ANY image (segs, A, ph) given the
    two loops' code facts.
  declarations).
  WHAT THIS FILE IS.  `AsanNodesStartX` closes the two start-up argument-block
  nodes and the layout node over an ABSTRACT argument-block invariant: its
  three statements are
    x_sound_envscan ... SINV argH FS0 HULL_ok SINV_frame we1 we2 we3 Xenv Fe1
      Fe2 Fe3 Ee De1 De2 De3 ph sp rdraw argv envp uid hw Hva Hve sp_lo sp_hi
      SINV0_vals SINV0_envp
    x_sound_pnscan  ... SINV argH FS0 HULL_ok argH_high argH_agree SINV_frame
      SINV_agree wp0..wp4 Xpn Fp0..Fp4 Ep Dp0..Dp4 ph sp rdraw argv envp uid hw
      Hva Hve sp_lo sp_hi SINV0_vals SINV0_str0
    x_sound_layout  ... SINV argH FS0
  This file INSTANTIATES them at AsanInit's concrete start-up data — the class
  invariant is an arbitrary [SINV] that implies [SINV0 ph sp rdraw brk0 argv
  envp uid hw], the hidden set is [argH0 ph sp rdraw argv envp uid hw], the
  image is (segs, A, ph) with the two musl loops' code facts — and assembles
  the start-up phase's node obligation: [init_x_sound_envscan],
  [init_x_sound_pnscan], [init_x_sound_layout].  What is PROVED here is only
  the bridge — that [SINV0] provides the three facts `AsanNodesAux`'s
  [SINV_vals]/[SINV_envp]/[SINV_str0] ask for ([SINV0_vals], [SINV0_envp],
  [SINV0_str0]) — plus the stack-pointer window facts ([sp_lo], [sp_hi]) and
  the string-block fitting fact ([s0_fits]).
  PARAMETER BLOCK.
  NOTES.
  - THE FOUR `Let`s.  `usp` is spelled `(sp.toNat : Int)` (NOT
    `bv_unsigned sp`), the spelling `omega` can use (see
    `AsanNodesStartX`'s note on the same abbreviation).
  - WHY THE THEOREMS CARRY `brk0` AND `Hfit`, WHICH NO CONCLUSION MENTIONS.
 `mbase`, `fs`, `stdin` and the `gid`/`groups`/`net` triple are
    dropped because nothing here mentions them.
  SCOPE.   Nothing is deferred, and the four definitions above are extra.
  Word hygiene: this file contains no proof hole and no extra postulate
  (`#print axioms` on the three theorems reports only `propext`,
  `Classical.choice` and `Quot.sound`).
-/

import LinuxSem.Common.AsanNodesStartX
import LinuxSem.Common.AsanInit

namespace LinuxSem.Common.AsanNodesStartXInit

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.AsanNodesAux
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.CatExec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asanxinit_fx : PropExec.FPState := PropExec.fx0

/-! ## 0. -/

/-- `Let usp := bv_unsigned sp`.  Spelled as the numeral cast — the
    one spelling `omega` can atomize consistently (see the header). -/
def usp (sp : word) : Int := (sp.toNat : Int)
def argc (argv : List (List byte)) : Int := (argv.length : Int)
def envc (envp : List (List byte)) : Int := (envp.length : Int)

/-- `Let s0 := nth 0 argv []` (argv[0], closed at the entry point). -/
def s0 (argv : List (List byte)) : List byte := argv[0]?.getD []

/-- `Let W` of `AsanInit`, the string block (strings + padding) in
    8-byte words.  here (see the header): `AsanInit.lean` keeps it as
    a file-local notation, and [argH0] needs it. -/
def W (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) : Int :=
  ((build_stack_bytes ph sp argv envp uid hw rdraw).length - 16
    - (8 * argc argv + 8 * envc envp + 184)) / 8

/-- `Definition E0` of `AsanInit`, the initial valuation: the nine
    words (sp = 32768*v0 + 16*v6, argc, envc, strlen argv[0], W,
    brk0/4096, (sp mod 32768)/16, strlen argv[1], uid) and the byte string
    `[K_RND]` = the AT_RANDOM draw.  here (see the header). -/
def E0 (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word)
    (argv envp : List (List byte)) (uid hw : word) : env :=
  { ev := fun n =>
      [Z_to_bv 64 (bv_unsigned sp / 32768), Z_to_bv 64 (argc argv),
       Z_to_bv 64 (envc envp), Z_to_bv 64 ((s0 argv).length),
       Z_to_bv 64 (W ph sp rdraw argv envp uid hw),
       Z_to_bv 64 (bv_unsigned brk0 / 4096), Z_to_bv 64 (bv_unsigned sp % 32768 / 16),
       Z_to_bv 64 ((argv[1]?.getD []).length), uid].getD n (Z_to_bv 64 0)
    eb := fun k => if (k == K_RND) = true then at_random_bytes rdraw.ed_random else [] }

/-- `Definition argH0` of `AsanInit`: the HIDDEN argument bytes —
    the envp pointer array (with its NULL) and the string block.  
    here (see the header). -/
def argH0 (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (argv envp : List (List byte))
    (uid hw : word) (E : env) (a : word) : Bool :=
  let z := bv_unsigned a
  (((usp sp + 8 * argc argv + 16 ≤ z) && (z < usp sp + 8 * argc argv + 8 * envc envp + 24))
   || ((usp sp + 8 * argc argv + 8 * envc envp + 184 ≤ z) &&
       (z < usp sp + 8 * argc argv + 8 * envc envp + 184 + 8 * W ph sp rdraw argv envp uid hw)))

/-- `Definition SINV0` of `AsanInit`: the class invariant —
    anything implying it (and stable like it) can be the start-up phase's
    [SINV].  here (see the header). -/
def SINV0 (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word)
    (argv envp : List (List byte)) (uid hw : word)
    (E : env) (M : word → Option byte) : Prop :=
  (∀ n, n < NX0 → E.ev n = (E0 ph sp rdraw brk0 argv envp uid hw).ev n)
  ∧ (∀ a, argH0 ph sp rdraw argv envp uid hw E a = true →
      M a = wrap_mem ph sp argv envp uid hw rdraw a)

/-! ## 1. -/

/-- The stack pointer is above the window floor. -/
theorem sp_lo (sp : word) (Hsp : valid_sp sp) : sp_window_lo ≤ usp sp := Hsp.1

/-- The stack pointer is below the window ceiling. -/
theorem sp_hi (sp : word) (Hsp : valid_sp sp) : usp sp ≤ sp_window_hi := Hsp.2.1

/-- What [SINV0] provides, in the form `AsanNodesAux` wants: the values of
    [e_envp], [EVar V_ENVC] and [e_str0] under ANY invariant `SINV` implying
    [SINV0]. -/
theorem SINV0_vals (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word)
    (argv envp : List (List byte)) (uid hw : word)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_SINV0 : ∀ (E : env) (M : word → Option byte),
      SINV E M → SINV0 ph sp rdraw brk0 argv envp uid hw E M)
    (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp)
    (E : env) (M : word → Option byte) (HS : SINV E M) :
    AsanPlanSound.uE E e_envp = usp sp + 8 * argc argv + 16 ∧
      E.ev V_ENVC = Z_to_bv 64 (envc envp) ∧
      AsanPlanSound.uE E e_str0 = usp sp + 8 * argc argv + 8 * envc envp + 184 := by
  obtain ⟨Hev, _⟩ := SINV_SINV0 E M HS
  have U1 : AsanPlanSound.uE (E0 ph sp rdraw brk0 argv envp uid hw) e_envp
      = usp sp + 8 * argc argv + 16 :=
    AsanInit.u_e_envp (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0)
      (argv := argv) (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  have U2 : AsanPlanSound.uE (E0 ph sp rdraw brk0 argv envp uid hw) (.EVar V_ENVC)
      = envc envp :=
    (AsanInit.uE0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0)
      (argv := argv) (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit).2.2.2.1
  have U3 : AsanPlanSound.uE (E0 ph sp rdraw brk0 argv envp uid hw) e_str0
      = usp sp + 8 * argc argv + 8 * envc envp + 184 :=
    AsanInit.u_e_str0 (ph := ph) (sp := sp) (rdraw := rdraw) (brk0 := brk0)
      (argv := argv) (envp := envp) (uid := uid) (hw := hw) Hsp Hva Hve Hfit
  have h1 : AsanPlanSound.uE E e_envp
      = AsanPlanSound.uE (E0 ph sp rdraw brk0 argv envp uid hw) e_envp := by
    simp only [AsanPlanSound.uE]
    rw [edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_envp (by decide) Hev]
  have h3 : AsanPlanSound.uE E e_str0
      = AsanPlanSound.uE (E0 ph sp rdraw brk0 argv envp uid hw) e_str0 := by
    simp only [AsanPlanSound.uE]
    rw [edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) e_str0 (by decide) Hev]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact U1
  · have h2 : edenot E (.EVar V_ENVC)
        = edenot (E0 ph sp rdraw brk0 argv envp uid hw) (.EVar V_ENVC) :=
      edenot_ev_agree NX0 E (E0 ph sp rdraw brk0 argv envp uid hw) (.EVar V_ENVC) (by decide) Hev
    show edenot E (.EVar V_ENVC) = Z_to_bv 64 (envc envp)
    rw [h2]
    have hx : ((edenot (E0 ph sp rdraw brk0 argv envp uid hw) (.EVar V_ENVC)).toNat : Int)
        = envc envp := by
      simpa only [AsanPlanSound.uE, bv_unsigned] using U2
    have hy : ((Z_to_bv 64 (envc envp)).toNat : Int) = envc envp := by
      have h0 : 0 ≤ envc envp := by have := Hve.1; unfold envc; omega
      have h6 : envc envp < 2 ^ 64 := by have := Hve.1; unfold envc; omega
      simpa only [Z_to_bv] using u64_lit (envc envp) ⟨h0, h6⟩
    apply BitVec.eq_of_toNat_eq
    have h : ((edenot (E0 ph sp rdraw brk0 argv envp uid hw) (.EVar V_ENVC)).toNat : Int)
        = ((Z_to_bv 64 (envc envp)).toNat : Int) := by omega
    exact Int.ofNat.inj h
  · rw [h3]; exact U3

/-- The envp pointer array (incl. its NULL) in FULL memory is the initial stack
    image. -/
theorem SINV0_envp (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word)
    (argv envp : List (List byte)) (uid hw : word)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_SINV0 : ∀ (E : env) (M : word → Option byte),
      SINV E M → SINV0 ph sp rdraw brk0 argv envp uid hw E M)
    (E : env) (M : word → Option byte) (a : word) (HS : SINV E M)
    (Ha1 : usp sp + 8 * argc argv + 16 ≤ bv_unsigned a)
    (Ha2 : bv_unsigned a < usp sp + 8 * argc argv + 16 + 8 * envc envp + 8) :
    M a = wrap_mem ph sp argv envp uid hw rdraw a := by
  obtain ⟨_, HM⟩ := SINV_SINV0 E M HS
  refine HM a ?_
  simp only [argH0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  left
  exact ⟨Ha1, by omega⟩

/-- `argv[0]`'s bytes plus their NUL fit in the argument strings. -/
theorem s0_fits (argv : List (List byte)) (Hva : valid_argv argv) :
    ((s0 argv).length : Int) + 1 ≤ total_arg_bytes argv := by
  unfold s0
  rw [total_arg_bytes_Z]
  cases argv with
  | nil =>
    have h : (1 : Int) ≤ 0 := by simpa using Hva.1.1
    have h0 : (((([] : List (List byte))[0]?).getD []).length : Int) = 0 := rfl
    have hz : (total_arg_bytes_nat [] : Int) = 0 := rfl
    rw [h0, hz]
    omega
  | cons a r =>
    rw [total_arg_bytes_cons]
    have h0 : (((a :: r)[0]?).getD []).length = a.length := rfl
    rw [h0]
    omega

/-- The bytes of `argv[0]` (incl. its NUL) likewise: the string block is the
    initial stack image. -/
theorem SINV0_str0 (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 : word)
    (argv envp : List (List byte)) (uid hw : word)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_SINV0 : ∀ (E : env) (M : word → Option byte),
      SINV E M → SINV0 ph sp rdraw brk0 argv envp uid hw E M)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (E : env) (M : word → Option byte) (a : word) (HS : SINV E M)
    (Ha1 : usp sp + 8 * argc argv + 8 * envc envp + 184 ≤ bv_unsigned a)
    (Ha2 : bv_unsigned a
      ≤ usp sp + 8 * argc argv + 8 * envc envp + 184 + ((s0 argv).length : Int)) :
    M a = wrap_mem ph sp argv envp uid hw rdraw a := by
  obtain ⟨_, HM⟩ := SINV_SINV0 E M HS
  refine HM a ?_
  have F := s0_fits argv Hva
  obtain ⟨W1, W2, W3⟩ := AsanInit.W_range (ph := ph) (sp := sp) (rdraw := rdraw)
    (argv := argv) (envp := envp) (uid := uid) (hw := hw) Hva Hve
  have htab : 0 ≤ total_arg_bytes argv := by rw [total_arg_bytes_Z]; omega
  have hteb : 0 ≤ total_arg_bytes envp := by rw [total_arg_bytes_Z]; omega
  have hp : 0 ≤ ((8 - (8 + (argc argv + 1) * 8 + (envc envp + 1) * 8 + 160
      + total_arg_bytes argv + total_arg_bytes envp) % 8) % 8) := Int.emod_nonneg _ (by decide)
  have hW8 : 8 * W ph sp rdraw argv envp uid hw
      = total_arg_bytes argv + total_arg_bytes envp
        + ((8 - (8 + (argc argv + 1) * 8 + (envc envp + 1) * 8 + 160
            + total_arg_bytes argv + total_arg_bytes envp) % 8) % 8) := by
    unfold W argc envc
    rw [W2]
    rw [AsanInit.length_bsb_eq]
    unfold AsanInit.stack_image_size
    simp only []
    omega
  simp only [argH0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine Or.inr ⟨Ha1, ?_⟩
  unfold argc envc at *
  omega

/-! ## 2. -/

/-- `XEnvScan` is sound at the concrete start-up data: the envp NULL-scan
    loop's node statement. -/
theorem init_x_sound_envscan (segs : List Segment) (A : atable) (ph : PhdrInfo) (sp : word)
    (rdraw : EntryDraw) (brk0 : word) (argv envp : List (List byte)) (uid hw : word)
    (FS0 : Fs.Fs) (SINV : env → (word → Option byte) → Prop)
    (SEGS_wx : wx_segs_nowrap segs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV_SINV0 : ∀ (E : env) (M : word → Option byte),
      SINV E M → SINV0 ph sp rdraw brk0 argv envp uid hw E M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH0 ph sp rdraw argv envp uid hw E a = true → M' a = M a) →
        SINV E M → SINV E M')
    (we1 we2 we3 : BitVec 32)
    (Xenv : 0 ≤ A.x_envscan ∧ A.x_envscan + 12 < 2 ^ 64 ∧ A.x_envscan_k = A.x_envscan + 12)
    (Fe1 : fetch_word segs (Z_to_bv 64 A.x_envscan) = some we1)
    (Fe2 : fetch_word segs (Z_to_bv 64 (A.x_envscan + 4)) = some we2)
    (Fe3 : fetch_word segs (Z_to_bv 64 (A.x_envscan + 8)) = some we3)
    (Ee : is_ecall we1 = false ∧ is_ecall we2 = false ∧ is_ecall we3 = false)
    (De1 : decodeAny we1 = some (Instr.load .SZ8 true 10 9 0, 4))
    (De2 : decodeAny we2 = some (Instr.opImm .ADD 9 9 8, 4))
    (De3 : decodeAny we3 = some (Instr.branch .NE 10 0 8184, 4))
    (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    x_stmt segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 .XEnvScan :=
  AsanNodesStartX.x_sound_envscan segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
    SEGS_wx SEGS_in_hull HULL_ok SINV_frame
    we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
    ph sp rdraw argv envp uid hw Hva Hve
    (sp_lo sp Hsp) (sp_hi sp Hsp)
    (SINV0_vals ph sp rdraw brk0 argv envp uid hw SINV SINV_SINV0 Hsp Hva Hve Hfit)
    (SINV0_envp ph sp rdraw brk0 argv envp uid hw SINV SINV_SINV0)

/-- `XPnScan` is sound at the concrete start-up data: the program-name scan's
    node statement. -/
theorem init_x_sound_pnscan (segs : List Segment) (A : atable) (ph : PhdrInfo) (sp : word)
    (rdraw : EntryDraw) (brk0 : word) (argv envp : List (List byte)) (uid hw : word)
    (FS0 : Fs.Fs) (SINV : env → (word → Option byte) → Prop)
    (SEGS_wx : wx_segs_nowrap segs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV_SINV0 : ∀ (E : env) (M : word → Option byte),
      SINV E M → SINV0 ph sp rdraw brk0 argv envp uid hw E M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH0 ph sp rdraw argv envp uid hw E a = true → M' a = M a) →
        SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree NX0 E E' → SINV E M → SINV E' M)
    (wp0 wp1 wp2 wp3 wp4 : BitVec 32)
    (Xpn : 8 ≤ A.x_pnscan ∧ A.x_pnscan + 12 < 2 ^ 64 ∧ A.x_pnscan_k = A.x_pnscan + 12)
    (Fp0 : fetch_word segs (Z_to_bv 64 (A.x_pnscan - 8)) = some wp0)
    (Fp1 : fetch_word segs (Z_to_bv 64 (A.x_pnscan - 4)) = some wp1)
    (Fp2 : fetch_word segs (Z_to_bv 64 (A.x_pnscan)) = some wp2)
    (Fp3 : fetch_word segs (Z_to_bv 64 (A.x_pnscan + 4)) = some wp3)
    (Fp4 : fetch_word segs (Z_to_bv 64 (A.x_pnscan + 8)) = some wp4)
    (Ep : is_ecall wp0 = false ∧ is_ecall wp1 = false ∧ is_ecall wp2 = false ∧
      is_ecall wp3 = false ∧ is_ecall wp4 = false)
    (Dp0 : decodeAny wp0 = some (Instr.store .SZ8 10 11 0, 4))
    (Dp1 : decodeAny wp1 = some (Instr.opImm .ADD 11 11 1, 4))
    (Dp2 : decodeAny wp2 = some (Instr.load .SZ1 false 13 11 4095, 4))
    (Dp3 : decodeAny wp3 = some (Instr.branch .EQ 13 12 8180, 4))
    (Dp4 : decodeAny wp4 = some (Instr.branch .NE 13 0 8180, 4))
    (Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hfit : entry_stack_fits sp argv envp) :
    x_stmt segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 .XPnScan :=
  AsanNodesStartX.x_sound_pnscan segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0
    SEGS_wx SEGS_in_hull HULL_ok
    (AsanInit.argH0_high (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw) Hsp Hva)
    (AsanInit.argH0_agree (ph := ph) (sp := sp) (rdraw := rdraw) (argv := argv) (envp := envp)
      (uid := uid) (hw := hw))
    SINV_frame SINV_agree
    wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
    ph sp rdraw argv envp uid hw Hva Hve
    (sp_lo sp Hsp) (sp_hi sp Hsp)
    (SINV0_vals ph sp rdraw brk0 argv envp uid hw SINV SINV_SINV0 Hsp Hva Hve Hfit)
    (SINV0_str0 ph sp rdraw brk0 argv envp uid hw SINV SINV_SINV0 Hva Hve)

/-- `XLayout` is sound at the concrete start-up data. -/
theorem init_x_sound_layout (segs : List Segment) (A : atable) (ph : PhdrInfo) (sp : word)
    (rdraw : EntryDraw) (argv envp : List (List byte)) (uid hw : word) (FS0 : Fs.Fs)
    (SINV : env → (word → Option byte) → Prop) :
    x_stmt segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0 .XLayout :=
  AsanNodesStartX.x_sound_layout segs A NX0 AsanInit.LIMIT SINV (argH0 ph sp rdraw argv envp uid hw) FS0

end LinuxSem.Common.AsanNodesStartXInit
