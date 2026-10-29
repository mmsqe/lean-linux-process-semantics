/-

  * AsanNodesStartX — soundness of the start-up argument-block nodes XEnvScan /
    XPnScan (on AsanNodesAux's Section context) and XLayout, on APS (srealizes).
  declarations).
    Proved against [AsanPlan] / [AsanPlanSound]
    (obligations [APS.x_stmt ... XEnvScan], [APS.x_stmt ... XPnScan]).
    The Section is parametric in the APS context (SEGS, A, nx0, LIMIT,
    SINV, argH and the APS image hypotheses), in the code facts of the two
    musl loops at [x_envscan A] / [x_pnscan A], and in WHAT THE
    ARGUMENT-BLOCK INVARIANT [SINV] MUST PROVIDE about an initial stack
    (sp, argv, envp, ph):
      - [SINV_vals]: the values of [e_envp], [EVar V_ENVC], [e_str0];
      - [SINV_envp]: the envp pointer array (incl. its NULL) in FULL memory
        is the initial stack image;
      - [SINV_str0]: the bytes of argv[0] (incl. its NUL) likewise.
    AsanNodesStartXInit instantiates this for AsanInit's [SINV0]/[argH0].
    Method: the loops read bytes hidden from the
    knowledge ([argH]) but VISIBLE w.r.t. [vis] (they are >= CEIL), so the
    machine steps are taken on [restrict (negb ∘ vis) ms]
    ([AsanAcctShape.srz_msteps_restricted_T] with [lazy_cover_vis] /
    [H_off_segments_vis], the [vis]-only twins of APS's lemmas), the loop
    itself being the image-independent [AsanNodesAux.env_loop] / [pn_loop].
    The entry draw ([Run.en_draw]) gives the AT_RANDOM bytes (= the draw's
    [ed_random]); AT_HWCAP is the auxv's fourth pair (10 pairs / 20 words,
    auxv_size 160); the mapped image is [Run.entry_stack_image] (block ++
    page slack).
  PARAMETER BLOCK.
  - `Z` is `Int`, `nat` is `Nat`, `word` is `BitVec 64`, `byte` is
    `BitVec 8`, `Z_to_bv n z` is `BitVec.ofInt n z`, `bv_unsigned w` is
    `(w.toNat : Int)`, `Z.of_nat n` is `(n : Int)`, `some` is `some`
    (`Option.some`), `fst`/`snd` are `.1`/`.2`.
    The same holds for `page_base_le'`/`A_wf_allowA'`: the node file calls
    `AsanPlanSound.page_base_le` / `AsanPlanSound.A_wf_allowA` through the
    `AsanNodesAux` aliases of those names.
  - `2^64` is spelled `two64` (`AxSymExec3.two64`, the tree's `2^64 : Int`)
    in every statement of THIS file, so that `omega` keeps it an opaque
    constant; every tree lemma whose statement spells it `↑(2 ^ 64)` is
    applied by conversion (`two64` and `↑(2 ^ 64)` are the same numeral).
  - `List.Forall` does not exist in this core, so `know_ok` is
    `∀ K ∈ kn, kentry_ok …`; `existsb` is `List.any`, `Forall_forall` is
    `List.all_eq_true`/`mem_*`, `nth 0 argv []` is `argv[0]?.getD []`.
  - `Z.leb_le` / `Z.ltb_lt` are `Int.le_of_decide`-style `omega` steps; the
    checker's `if` stays a `Bool` test, split with `by_cases`.
  - declarations : `two64_big` (the one constant
    bound `omega` consumes when the goal's ceiling is the opaque `two64`),
    and the five bound/witness lemmas the two `omega`-heavy identity steps
    are factored through — `EA_bounds`, `env_post_s1` (the envp scan's
    `s1`-value as a word identity), `STR0_bounds`, `ptr_bounds`,
    `ptr_below_STR0` (the `&__progname` cell is inside the hull, hence
    strictly below `argv[0]`'s bytes).
  SCOPE.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.AsanPlanCore
import LinuxSem.Common.AsanNodesAux
import LinuxSem.Common.AsanStartLoops
import LinuxSem.Common.RefLayout
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanNodesStartX

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
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.BackingAlgebra
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanAcctShape
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.StoreOk
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.RefLayout
open LinuxSem.Common.AsanNodesAux
open LinuxSem.Common.CatSim

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asannodesstartx_fx : PropExec.FPState := PropExec.fx0

/-! ## 0. -/

/-- `usp` — the stack pointer as a `Z`.   -/
def usp (sp : word) : Int := (sp.toNat : Int)

/-- `argc` — the argument count as a `Z`. -/
def argc (argv : List (List byte)) : Int := (argv.length : Int)

/-- `envc` — the environment count as a `Z`. -/
def envc (envp : List (List byte)) : Int := (envp.length : Int)

/-- `s0` — `argv[0]`. -/
def s0 (argv : List (List byte)) : List byte := argv[0]?.getD []

/-- The initial stack image of this placement ( section `Let bsb`). -/
def bsb (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (uid hw : word)
    (rdraw : EntryDraw) : List byte :=
  build_stack_bytes ph sp argv envp uid hw rdraw

/-- `EA` — the envp array base (`usp + 8 * argc + 16`). -/
def EA (sp : word) (argv : List (List byte)) : Int := usp sp + 8 * argc argv + 16

/-- `STR0` — the address of `argv[0]`'s bytes (`184` includes the 16-byte
    AT_HWCAP pair). -/
def STR0 (sp : word) (argv envp : List (List byte)) : Int :=
  usp sp + 8 * argc argv + 8 * envc envp + 184

/-! ## 1. Layout facts -/

/-- `1 ≤ argc ≤ 1024`. -/
theorem len_av (argv : List (List byte)) (Hva : valid_argv argv) :
    1 ≤ argc argv ∧ argc argv ≤ 1024 :=
  Hva.1

/-- `0 ≤ envc ≤ 256`. -/
theorem len_ev (envp : List (List byte)) (Hve : valid_envp envp) :
    0 ≤ envc envp ∧ envc envp ≤ 256 := by
  have h : (envp.length : Int) ≤ 256 := Hve.1
  unfold envc
  constructor <;> omega

/-- `argv[0]`'s length is bounded by `valid_argv`'s per-string bound. -/
theorem len_s0 (argv : List (List byte)) (Hva : valid_argv argv) :
    ((s0 argv).length : Int) ≤ 131071 := by
  have h1 : 1 ≤ argc argv := (len_av argv Hva).1
  unfold argc at h1
  unfold s0
  exact valid_argv_str_len argv 0 Hva (by omega)

/-- The stack pointer is above the window floor. -/
theorem usp_lo (sp : word) (H : sp_window_lo ≤ usp sp) : 0x7fff80000000 ≤ usp sp := by
  unfold sp_window_lo at H
  exact H

/-- The stack pointer is below the window ceiling. -/
theorem usp_hi (sp : word) (H : usp sp ≤ sp_window_hi) : usp sp ≤ 0x800000000000 := by
  unfold sp_window_hi at H
  exact H

/-- The initial stack image fits below `2^64`. -/
theorem bsb_nw (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (uid hw : word)
    (rdraw : EntryDraw) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_hi : usp sp ≤ sp_window_hi) :
    usp sp + ((bsb ph sp argv envp uid hw rdraw).length : Int) < two64 := by
  unfold usp bsb
  exact lay_bsb_nw ph sp rdraw argv envp uid hw Hva Hve Hsp_hi

/-- `2^64` is beyond every figure the argument block produces (the window
    ceiling `0x800000000000`, `1024` arguments, `256` environment entries,
    and slack).  The hypothesis form `omega` consumes when the goal's bound
    is the opaque constant `two64`. -/
theorem two64_big : 0x800000000000 + 8 * 1024 + 8 * 256 + 200000 < two64 := by decide

/-- `argv[0]`'s address is the first argv pointer. -/
theorem STR0_eq (sp : word) (argv envp : List (List byte)) (Hva : valid_argv argv)
    (Hsp_hi : usp sp ≤ sp_window_hi) :
    cat_argv_ptr sp argv envp 0 = Z_to_bv 64 (STR0 sp argv envp) := by
  have hav : 0 < argv.length := by
    have h1 : 1 ≤ argc argv := (len_av argv Hva).1
    unfold argc at h1
    omega
  rw [cat_argv_ptr_offset sp argv envp 0 hav]
  unfold cat_string_base
  rw [nat_to_word_add_merge, word_add_nat]
  have hargc := (len_av argv Hva).1
  have hu2 := usp_hi sp Hsp_hi
  have h0 : total_arg_bytes_nat (argv.take 0) = 0 := rfl
  have h : (sp.toNat : Int) + ((cat_struct_size argv envp + total_arg_bytes_nat (argv.take 0) : Nat) : Int)
      = STR0 sp argv envp := by
    rw [h0]
    unfold STR0 argc envc cat_struct_size auxv_size usp at *
    push_cast
    omega
  rw [h]

/-- Reading the envp array out of a memory that holds the image there. -/
theorem rd_envp_k (segs : List Segment) (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw)
    (argv envp : List (List byte)) (uid hw : word)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi)
    (M : word → Option byte) (k : Nat) (Hk : k < envp.length)
    (HM : ∀ a : word, EA sp argv ≤ bv_unsigned a →
        bv_unsigned a < EA sp argv + 8 * envc envp + 8 →
        M a = wrap_mem ph sp argv envp uid hw rdraw a) :
    rdn segs M (Z_to_bv 64 (EA sp argv + 8 * (k : Int))) 8
      = some (word_to_le_bytes 8 (cat_envp_ptr sp argv envp k)) := by
  simp only [bv_unsigned] at *
  have hargc := len_av argv Hva
  have henvc := len_ev envp Hve
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hk0 : (k : Int) < envc envp := by unfold envc at *; omega
  have hT := two64_big
  have hz : EA sp argv + 8 * (k : Int) + 8 < two64 := by unfold EA argc usp at *; omega
  have hz8 : EA sp argv + 8 * (k : Int) + 8 ≤ two64 := by omega
  have ha : ((Z_to_bv 64 (EA sp argv + 8 * (k : Int))).toNat : Int)
      = EA sp argv + 8 * (k : Int) :=
    u_lit _ ⟨by unfold EA argc usp at *; omega, by show _ < two64; omega⟩
  have h8nw : ((Z_to_bv 64 (EA sp argv + 8 * (k : Int))).toNat : Int) + 8 ≤ two64 := by
    rw [ha]; exact hz8
  have hsp : (sp.toNat : Int) ≤ ((Z_to_bv 64 (EA sp argv + 8 * (k : Int))).toNat : Int) := by
    rw [ha]; unfold EA argc usp at *; omega
  have hext : ∀ x : word,
      ((Z_to_bv 64 (EA sp argv + 8 * (k : Int))).toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < ((Z_to_bv 64 (EA sp argv + 8 * (k : Int))).toNat : Int) + 8 →
      M x = wrap_mem ph sp argv envp uid hw rdraw x := by
    intro x hx
    rw [ha] at hx
    exact HM x (by omega) (by omega)
  rw [rdn_ext segs 8 M (wrap_mem ph sp argv envp uid hw rdraw) _ h8nw hext]
  rw [rdn_wrap_stack_above segs ph sp argv envp _ 8 uid hw rdraw hsp h8nw]
  rw [← n_to_le_8_spec, ← read_envp_ptr_k segs ph sp rdraw argv envp uid hw Hva Hve Hsp_hi k Hk]
  have haddr : Z_to_bv 64 (EA sp argv + 8 * (k : Int))
      = sp + nat_to_word (envp_off argv + 8 * k) := by
    rw [word_add_nat]
    apply congrArg (Z_to_bv 64)
    unfold EA argc usp envp_off at *
    push_cast
    omega
  rw [haddr]

/-- The envp NULL terminator. -/
theorem rd_envp_null (segs : List Segment) (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw)
    (argv envp : List (List byte)) (uid hw : word)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi)
    (M : word → Option byte)
    (HM : ∀ a : word, EA sp argv ≤ bv_unsigned a →
        bv_unsigned a < EA sp argv + 8 * envc envp + 8 →
        M a = wrap_mem ph sp argv envp uid hw rdraw a) :
    rdn segs M (Z_to_bv 64 (EA sp argv + 8 * envc envp)) 8
      = some (word_to_le_bytes 8 (Z_to_bv 64 0)) := by
  simp only [bv_unsigned] at *
  have hargc := len_av argv Hva
  have henvc := len_ev envp Hve
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hT := two64_big
  have hz : EA sp argv + 8 * envc envp + 8 < two64 := by unfold EA argc envc usp at *; omega
  have hz8 : EA sp argv + 8 * envc envp + 8 ≤ two64 := by omega
  have ha : ((Z_to_bv 64 (EA sp argv + 8 * envc envp)).toNat : Int)
      = EA sp argv + 8 * envc envp :=
    u_lit _ ⟨by unfold EA argc envc usp at *; omega, by show _ < two64; omega⟩
  have h8nw : ((Z_to_bv 64 (EA sp argv + 8 * envc envp)).toNat : Int) + 8 ≤ two64 := by
    rw [ha]; exact hz8
  have hsp : (sp.toNat : Int) ≤ ((Z_to_bv 64 (EA sp argv + 8 * envc envp)).toNat : Int) := by
    rw [ha]; unfold EA argc usp at *; omega
  have hext : ∀ x : word,
      ((Z_to_bv 64 (EA sp argv + 8 * envc envp)).toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < ((Z_to_bv 64 (EA sp argv + 8 * envc envp)).toNat : Int) + 8 →
      M x = wrap_mem ph sp argv envp uid hw rdraw x := by
    intro x hx
    rw [ha] at hx
    exact HM x (by omega) (by omega)
  rw [rdn_ext segs 8 M (wrap_mem ph sp argv envp uid hw rdraw) _ h8nw hext]
  rw [rdn_wrap_stack_above segs ph sp argv envp _ 8 uid hw rdraw hsp h8nw]
  rw [← n_to_le_8_spec, ← read_envp_null segs ph sp rdraw argv envp uid hw Hva Hve Hsp_hi]
  have haddr : Z_to_bv 64 (EA sp argv + 8 * envc envp)
      = sp + nat_to_word (envp_off argv + 8 * envp.length) := by
    rw [word_add_nat]
    apply congrArg (Z_to_bv 64)
    unfold EA argc envc usp envp_off at *
    push_cast
    omega
  rw [haddr]

/-- One byte of `argv[0]`. -/
theorem rd_str0_j (segs : List Segment) (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw)
    (argv envp : List (List byte)) (uid hw : word)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi)
    (M : word → Option byte) (j : Nat) (Hj : j ≤ (s0 argv).length)
    (HM : ∀ a : word, STR0 sp argv envp ≤ bv_unsigned a →
        bv_unsigned a ≤ STR0 sp argv envp + ((s0 argv).length : Int) →
        M a = wrap_mem ph sp argv envp uid hw rdraw a) :
    rdn segs M (Z_to_bv 64 (STR0 sp argv envp + (j : Int))) 1
      = some [byte_at (s0 argv) j] := by
  simp only [bv_unsigned] at *
  have hargc := len_av argv Hva
  have henvc := len_ev envp Hve
  have hs0 := len_s0 argv Hva
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hT := two64_big
  have hav : 0 < argv.length := by have h := hargc.1; unfold argc at h; omega
  have hbsb := bsb_nw ph sp argv envp uid hw rdraw Hva Hve Hsp_hi
  have hz : STR0 sp argv envp + (j : Int) + 1 < two64 := by
    unfold STR0 argc envc usp at *
    omega
  have hz1 : STR0 sp argv envp + (j : Int) + 1 ≤ two64 := by omega
  have ha : ((Z_to_bv 64 (STR0 sp argv envp + (j : Int))).toNat : Int)
      = STR0 sp argv envp + (j : Int) :=
    u_lit _ ⟨by unfold STR0 argc envc usp at *; omega, by show _ < two64; omega⟩
  have h2 : ((Z_to_bv 64 (STR0 sp argv envp + (j : Int))).toNat : Int) + 1 ≤ two64 := by
    rw [ha]; exact hz1
  have hsp : (sp.toNat : Int) ≤ ((Z_to_bv 64 (STR0 sp argv envp + (j : Int))).toNat : Int) := by
    rw [ha]; unfold STR0 argc usp at *; omega
  have hext : ∀ x : word,
      ((Z_to_bv 64 (STR0 sp argv envp + (j : Int))).toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < ((Z_to_bv 64 (STR0 sp argv envp + (j : Int))).toNat : Int) + 1 →
      M x = wrap_mem ph sp argv envp uid hw rdraw x := by
    intro x hx
    rw [ha] at hx
    exact HM x (by omega) (by omega)
  have hs : ((Z_to_bv 64 (STR0 sp argv envp)).toNat : Int) = STR0 sp argv envp :=
    u_lit _ ⟨by unfold STR0 argc envc usp at *; omega,
      by show _ < two64; unfold STR0 argc envc usp at *; omega⟩
  have haddr : Z_to_bv 64 (STR0 sp argv envp + (j : Int))
      = cat_argv_ptr sp argv envp 0 + nat_to_word j := by
    rw [STR0_eq sp argv envp Hva Hsp_hi, word_add_nat, hs]
  rw [rdn_ext segs 1 M (wrap_mem ph sp argv envp uid hw rdraw) _ h2 hext]
  rw [rdn_wrap_stack_above segs ph sp argv envp _ 1 uid hw rdraw hsp h2]
  rw [haddr]
  exact read_argv_byte_k ph segs sp argv envp 0 j uid hw rdraw hav Hj hbsb

/-! ## 2. `XEnvScan` — musl's envp-counting loop -/

/-- The `x_sound_envscan` bound bundle: `EA`'s range and `envc`'s, all in
    terms of the (unfolded) abbreviations so `omega` sees one atom per
    variable. -/
theorem EA_bounds (sp : word) (argv envp : List (List byte)) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi) :
    0 ≤ EA sp argv ∧ EA sp argv + 8 * envc envp + 16 < two64 := by
  have hargc := len_av argv Hva
  have henvc := len_ev envp Hve
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hT := two64_big
  unfold EA argc envc usp at *
  constructor <;> omega

/-- The word `s1` holds after the envp scan: `EA + 8*envc + 8`, which is the
    checker's `s1 + 8*envc + 8` read back as a word. -/
theorem env_post_s1 (sp : word) (argv envp : List (List byte))
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi) :
    Z_to_bv 64 (EA sp argv + 8 * envc envp + 8)
      = Z_to_bv 64 (EA sp argv)
        + (Z_to_bv 64 8 * Z_to_bv 64 (envc envp) + Z_to_bv 64 8) := by
  obtain ⟨hargc0, hargc1⟩ := len_av argv Hva
  obtain ⟨henvc0, henvc1⟩ := len_ev envp Hve
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hT := two64_big
  unfold envc at *
  have hE0 : 0 ≤ EA sp argv := by unfold EA argc usp at *; omega
  have hEhi : EA sp argv + 8 * (envp.length : Int) + 16 < two64 := by
    unfold EA argc usp at *; omega
  have key : bv_unsigned (Z_to_bv 64 (EA sp argv + 8 * (envp.length : Int) + 8))
      = bv_unsigned (Z_to_bv 64 (EA sp argv)
        + (Z_to_bv 64 8 * Z_to_bv 64 ((envp.length : Int)) + Z_to_bv 64 8)) := by
    rw [u_lit (EA sp argv + 8 * (envp.length : Int) + 8)
        ⟨by omega, by show _ < two64; omega⟩,
      u_add64, u_add64, u_mul64,
      u_lit (EA sp argv) ⟨hE0, by show _ < two64; omega⟩,
      u_lit 8 ⟨by decide, by decide⟩,
      u_lit ((envp.length : Int)) ⟨by omega, by show _ < two64; omega⟩]
    have h8n : 8 * (envp.length : Int) % 2 ^ 64 = 8 * (envp.length : Int) :=
      Int.emod_eq_of_lt (by omega)
        (by show 8 * (envp.length : Int) < two64; omega)
    have h8n8 : (8 * (envp.length : Int) % 2 ^ 64 + 8) % 2 ^ 64
        = 8 * (envp.length : Int) + 8 := by
      rw [h8n]
      exact Int.emod_eq_of_lt (by omega)
        (by show 8 * (envp.length : Int) + 8 < two64; omega)
    have hfinal : (EA sp argv + (8 * (envp.length : Int) % 2 ^ 64 + 8) % 2 ^ 64) % 2 ^ 64
        = EA sp argv + 8 * (envp.length : Int) + 8 := by
      rw [h8n8]
      exact Int.emod_eq_of_lt (by omega)
        (by show EA sp argv + 8 * (envp.length : Int) + 8 < two64; omega)
    rw [hfinal]
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj key)

/-- `XEnvScan` is sound: the envp NULL-scan loop, run on the restricted
    memory, lands on the checker's post-state. -/
theorem x_sound_envscan (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (Hwx : wx_segs_nowrap segs)
    (HSEGS : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (we1 we2 we3 : BitVec 32)
    (Xenv : 0 ≤ A.x_envscan ∧ A.x_envscan + 12 < two64 ∧ A.x_envscan_k = A.x_envscan + 12)
    (Fe1 : fetch_word segs (Z_to_bv 64 A.x_envscan) = some we1)
    (Fe2 : fetch_word segs (Z_to_bv 64 (A.x_envscan + 4)) = some we2)
    (Fe3 : fetch_word segs (Z_to_bv 64 (A.x_envscan + 8)) = some we3)
    (Ee : is_ecall we1 = false ∧ is_ecall we2 = false ∧ is_ecall we3 = false)
    (De1 : decodeAny we1 = some (Instr.load .SZ8 true 10 9 0, 4))
    (De2 : decodeAny we2 = some (Instr.opImm .ADD 9 9 8, 4))
    (De3 : decodeAny we3 = some (Instr.branch .NE 10 0 8184, 4))
    (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (argv envp : List (List byte))
    (uid hw : word)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi)
    (SINV_vals : ∀ (E : env) (M : word → Option byte), SINV E M →
      AsanPlanSound.uE E e_envp = EA sp argv ∧ E.ev V_ENVC = Z_to_bv 64 (envc envp) ∧
        AsanPlanSound.uE E e_str0 = STR0 sp argv envp)
    (SINV_envp : ∀ (E : env) (M : word → Option byte) (a : word), SINV E M →
      EA sp argv ≤ bv_unsigned a → bv_unsigned a < EA sp argv + 8 * envc envp + 8 →
      M a = wrap_mem ph sp argv envp uid hw rdraw a) :
    x_stmt segs A nx0 LIMIT SINV argH FS0 .XEnvScan := by
  intro args cs cs' E R FULL model T HC _ Hn Hk
  simp only [node_x, node_envscan] at Hn
  split at Hn
  · rename_i Hc
    simp only [Option.some.injEq] at Hn
    subst cs'
    -- the checker's two tests
    have Hpc : pc cs = A.x_envscan := by
      have h := Hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have Heq : len_eqb (kn cs) (reg cs 9) e_envp = true := by
      have h := Hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    -- the successor's pc
    have hpc' : pc (AsanPlanCore.set_pc (AsanPlanCore.set_reg (AsanPlanCore.set_reg cs 9
        (eadd (reg cs 9) (eadd (escale 8 (.EVar V_ENVC)) (.ELit 8)))) 10 (.ELit 0))
        A.x_envscan_k) = A.x_envscan + 12 := by
      simp only [pc, AsanPlanCore.set_pc, AsanPlanCore.set_reg, with_ss, mk_ss]
      exact Xenv.2.2
    rw [hpc'] at Hk
    -- what `SINV` says
    have HS := HC.co_sinv
    obtain ⟨V1, V2, V3⟩ := SINV_vals E FULL HS
    have V1' : bv_unsigned (edenot E e_envp) = EA sp argv := V1
    -- `a0` and `s1`
    have H9e := len_eqb_sound segs E (Mr A argH E cs model FULL) (kn cs) (reg cs 9) e_envp
      HC.co_know Heq
    have H9 := reg_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model 9 HC
      ⟨by omega, by omega⟩
    have hE : edenot E e_envp = Z_to_bv 64 (EA sp argv) := by
      rw [show edenot E e_envp
        = Z_to_bv 64 (bv_unsigned (edenot E e_envp)) from
        (ofInt_toNat _).symm, V1']
    have h9' : getr R (9 : reg) = Z_to_bv 64 (EA sp argv + 8 * (0 : Int)) := by
      rw [show (9 : reg) = Z_to_bv 5 ((9 : Nat) : Int) from by decide, H9, H9e, hE,
        show EA sp argv + 8 * (0 : Int) = EA sp argv from by omega]
    -- the memory hypothesis for the loop
    have HM : ∀ a : word, EA sp argv ≤ bv_unsigned a →
        bv_unsigned a < EA sp argv + 8 * envc envp + 8 →
        mrestrict (Hv A E cs model) FULL a = wrap_mem ph sp argv envp uid hw rdraw a := by
      intro a Ha1 Ha2
      rw [mrestrict_Hv_high A E cs model FULL a (by
        have hCEIL : CEIL ≤ EA sp argv := by
          have hargc := len_av argv Hva
          have hu1 := usp_lo sp Hsp_lo
          unfold EA argc usp CEIL at *
          omega
        omega)]
      exact SINV_envp E FULL a HS Ha1 Ha2
    -- the loop
    have hHe : 0 ≤ EA sp argv ∧ EA sp argv + 8 * (envp.length : Int) + 16 < two64 := by
      have h := EA_bounds sp argv envp Hva Hve Hsp_lo Hsp_hi
      exact h
    have hRk : ∀ k, k < envp.length →
        rdn segs (mrestrict (Hv A E cs model) FULL) (Z_to_bv 64 (EA sp argv + 8 * (k : Int))) 8
          = some (word_to_le_bytes 8 (cat_envp_ptr sp argv envp k)) ∧
        (cat_envp_ptr sp argv envp k).toNat ≠ 0 := by
      intro k hk
      refine ⟨rd_envp_k segs ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi
          (mrestrict (Hv A E cs model) FULL) k hk HM, ?_⟩
      intro h0
      exact cat_envp_ptr_nz sp argv envp Hva Hve Hsp_lo Hsp_hi k hk (by rw [h0]; rfl)
    have hRn : rdn segs (mrestrict (Hv A E cs model) FULL)
        (Z_to_bv 64 (EA sp argv + 8 * (envp.length : Int))) 8
          = some (word_to_le_bytes 8 (Z_to_bv 64 0)) :=
      rd_envp_null segs ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi
        (mrestrict (Hv A E cs model) FULL) HM
    obtain ⟨R', Hms, Hpost⟩ := AsanStartLoops.env_loop segs A.x_envscan we1 we2 we3
      ⟨Xenv.1, Xenv.2.1⟩ Fe1 Fe2 Fe3 Ee.1 Ee.2.1 Ee.2.2 De1 De2 De3
      (mrestrict (Hv A E cs model) FULL) (seg_rom segs) (EA sp argv) envp.length
      (cat_envp_ptr sp argv envp) hHe hRk hRn envp.length 0 R (by omega) h9'
    -- the same chain, seen from the restricted source state
    have Hms' : msteps segs (restrict (Hv A E cs model)
        (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)))
        (mkst R' (Z_to_bv 64 (A.x_envscan + 12))
          (mrestrict (Hv A E cs model) FULL) (seg_rom segs)) := by
      rw [restrict_mkst, Hpc]
      exact Hms
    show srealizes segs (AsanAcct.mkCfg
      (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)) model) T
    refine srz_msteps_restricted_T segs (Hv A E cs model)
      (H_off_segments_vis segs A HSEGS E cs model) Hwx (allowA A E cs)
      (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs))
      (mkst R' (Z_to_bv 64 (A.x_envscan + 12))
        (mrestrict (Hv A E cs model) FULL) (seg_rom segs))
      model T ?_ ?_ HC.co_minv HC.co_halt Hms' ?_
    · exact lazy_cover_vis segs A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC
    · exact A_wf_allowA' A E cs
    · intro model' Hinv' Hsame Hclean
      show srealizes segs (AsanAcct.mkCfg
        (unrestrict (Hv A E cs model) FULL
          (mkst R' (Z_to_bv 64 (A.x_envscan + 12))
            (mrestrict (Hv A E cs model) FULL) (seg_rom segs))) model') T
      have hmk : unrestrict (Hv A E cs model) FULL
          (mkst R' (Z_to_bv 64 (A.x_envscan + 12))
            (mrestrict (Hv A E cs model) FULL) (seg_rom segs))
          = mkst R' (Z_to_bv 64 (A.x_envscan + 12)) FULL (seg_rom segs) := by
        show mkst R' (Z_to_bv 64 (A.x_envscan + 12))
          (munrestrict (Hv A E cs model) FULL (mrestrict (Hv A E cs model) FULL))
          (seg_rom segs)
          = mkst R' (Z_to_bv 64 (A.x_envscan + 12)) FULL (seg_rom segs)
        rw [AsanNodesAux.munrestrict_mrestrict]
      rw [hmk]
      refine Hk E R' FULL model' ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ ?_ ?_
      · -- `cs_ok` of the successor state
        refine cs_ok_frame segs A LIMIT SINV argH FS0 SINV_frame E cs R FULL model _ R' FULL
          model' HC Hsame Hinv' ?_ rfl HC.co_know (fun a _ => rfl)
        -- the two registers the loop wrote
        obtain ⟨P9, P10, Pag⟩ := Hpost
        refine regs_ok_post2 E cs.a_ss.s_regs R R' 9 (9 : reg)
          (eadd (reg cs 9) (eadd (escale 8 (.EVar V_ENVC)) (.ELit 8))) 10 (10 : reg) (.ELit 0)
          HC.co_regs ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by decide) (by decide)
          ?_ ?_ ?_
        · -- `s1` after the loop
          rw [P9, eadd, eadd, escale, mkAlu_denot, mkAlu_denot, mkMd_denot]
          show Z_to_bv 64 (EA sp argv + 8 * (envp.length : Int) + 8)
            = (edenot E (reg cs 9)) + ((Z_to_bv 64 8) * (E.ev V_ENVC) + Z_to_bv 64 8)
          rw [show edenot E (reg cs 9) = edenot E e_envp from H9e, hE, V2]
          exact env_post_s1 sp argv envp Hva Hve Hsp_lo Hsp_hi
        · rw [P10]
          rfl
        · intro r N1 N2
          exact Pag r (fun h => h.elim N1 N2)
      · -- the file system never moves
        exact (same_but_materialized_frame model model' Hsame).2.2.2.2.2.2.2.2.2.2.2.1
  · simp at Hn

/-! ## 3. `XPnScan` — musl's program-name scan -/

/-- `STR0`'s range and the room for `argv[0]`'s bytes and its NUL. -/
theorem STR0_bounds (sp : word) (argv envp : List (List byte)) (Hva : valid_argv argv)
    (Hve : valid_envp envp) (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi) :
    0 ≤ STR0 sp argv envp ∧ STR0 sp argv envp + ((s0 argv).length : Int) + 2 < two64 := by
  obtain ⟨hargc0, hargc1⟩ := len_av argv Hva
  obtain ⟨henvc0, henvc1⟩ := len_ev envp Hve
  have hs0 := len_s0 argv Hva
  have hu1 := usp_lo sp Hsp_lo
  have hu2 := usp_hi sp Hsp_hi
  have hT := two64_big
  unfold STR0 argc envc usp at *
  constructor <;> omega

/-- The literal cell's range: `p` is inside the image hull. -/
theorem ptr_bounds (A : atable) (HULL_ok : hull_ok A) (p : Int)
    (Hlo : A.img_lo ≤ p) (Hhi : p + 8 ≤ A.img_hi) :
    0 ≤ p ∧ p + 8 ≤ two64 := by
  obtain ⟨HU0, -, -, HU3⟩ := HULL_ok
  have hKHI : KHI < two64 := by decide
  unfold KHI at *
  constructor <;> omega

/-- The cell lies strictly below `argv[0]`'s bytes (the hull ends below the
    ceiling, the argument block starts at `sp`). -/
theorem ptr_below_STR0 (A : atable) (sp : word) (argv envp : List (List byte))
    (HULL_ok : hull_ok A) (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (p : Int) (Hhi : p + 8 ≤ A.img_hi) :
    p + 8 ≤ STR0 sp argv envp := by
  obtain ⟨hargc0, hargc1⟩ := len_av argv Hva
  obtain ⟨henvc0, henvc1⟩ := len_ev envp Hve
  obtain ⟨-, -, -, HU3⟩ := HULL_ok
  have hu1 := usp_lo sp Hsp_lo
  have hKHI : KHI ≤ CEIL := by decide
  unfold STR0 argc envc usp CEIL at *
  omega

/-- `XPnScan` is sound: the program-name scan, run on the restricted memory,
    lands on the checker's post-state (a havoc'd cell and a fresh variable). -/
theorem x_sound_pnscan (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (Hwx : wx_segs_nowrap segs)
    (HSEGS : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (wp0 wp1 wp2 wp3 wp4 : BitVec 32)
    (Xpn : 8 ≤ A.x_pnscan ∧ A.x_pnscan + 12 < two64 ∧ A.x_pnscan_k = A.x_pnscan + 12)
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
    (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (argv envp : List (List byte))
    (uid hw : word)
    (Hva : valid_argv argv) (Hve : valid_envp envp)
    (Hsp_lo : sp_window_lo ≤ usp sp) (Hsp_hi : usp sp ≤ sp_window_hi)
    (SINV_vals : ∀ (E : env) (M : word → Option byte), SINV E M →
      AsanPlanSound.uE E e_envp = EA sp argv ∧ E.ev V_ENVC = Z_to_bv 64 (envc envp) ∧
        AsanPlanSound.uE E e_str0 = STR0 sp argv envp)
    (SINV_str0 : ∀ (E : env) (M : word → Option byte) (a : word), SINV E M →
      STR0 sp argv envp ≤ bv_unsigned a →
      bv_unsigned a ≤ STR0 sp argv envp + ((s0 argv).length : Int) →
      M a = wrap_mem ph sp argv envp uid hw rdraw a) :
    x_stmt segs A nx0 LIMIT SINV argH FS0 .XPnScan := by
  intro args cs cs' E R FULL model T HC _ Hn Hk
  simp only [node_x] at Hn
  unfold node_pnscan at Hn
  cases hp10 : reg_lit cs 10 with
  | none => rw [hp10] at Hn; simp at Hn
  | some p =>
    cases hp12 : reg_lit cs 12 with
    | none => rw [hp10, hp12] at Hn; simp at Hn
    | some c =>
      rw [hp10, hp12] at Hn
      split at Hn
      · rename_i heqp heqc
        simp only [Option.some.injEq] at heqp heqc
        subst heqp
        subst heqc
        try dsimp only at Hn
        split at Hn
        · rename_i Hc
          simp only [Option.some.injEq] at Hn
          subst Hn
          -- the guard's six conjuncts
          have Hc' := Hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at Hc'
          obtain ⟨⟨⟨⟨⟨Hpcx, Heq⟩, Hwr⟩, Hlo⟩, Hhi⟩, Hfresh⟩ := Hc'
          have HS := HC.co_sinv
          obtain ⟨V1, V2, V3⟩ := SINV_vals E FULL HS
          have V3' : edenot E e_str0 = Z_to_bv 64 (STR0 sp argv envp) := by
            rw [show edenot E e_str0 = Z_to_bv 64 (bv_unsigned (edenot E e_str0)) from
              (ofInt_toNat _).symm,
              show bv_unsigned (edenot E e_str0) = STR0 sp argv envp from V3]
          obtain ⟨hp0, hp8⟩ := ptr_bounds A HULL_ok p Hlo Hhi
          obtain ⟨hpn0, hpn2⟩ := STR0_bounds sp argv envp Hva Hve Hsp_lo Hsp_hi
          have hpstr0 : p + 8 ≤ STR0 sp argv envp :=
            ptr_below_STR0 A sp argv envp HULL_ok Hva Hve Hsp_lo p Hhi
          have hav : 0 < argv.length := by
            have h := (len_av argv Hva).1
            unfold argc at h
            omega
          -- the successor's pc
          have hpc' : pc (with_ss cs
              (mk_ss A.x_pnscan_k
                (sr_upd (sr_upd cs.a_ss.s_regs 11 (.EVar (nxt cs))) 13 (.ELit 0))
                (kn_havoc (kimg_cut (kn cs) p 8) (.ELit 0) p (.ELit 8))
                (nxt cs + 1))) = A.x_pnscan + 12 := by
            simp only [pc, with_ss, mk_ss]
            exact Xpn.2.2
          rw [hpc'] at Hk
          -- registers
          obtain ⟨H10, -⟩ := reg_lit_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 p
            HC ⟨by omega, by omega⟩ hp10
          obtain ⟨H12, -⟩ := reg_lit_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 47
            HC ⟨by omega, by omega⟩ hp12
          have H11e := len_eqb_sound segs E (Mr A argH E cs model FULL) (kn cs)
            (reg cs 11) (eaddz e_str0 1) HC.co_know Heq
          have H11 := reg_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 HC
            ⟨by omega, by omega⟩
          have H11' : getr R (11 : reg) = Z_to_bv 64 (STR0 sp argv envp + (0 : Int) + 1) := by
            rw [show (11 : reg) = Z_to_bv 5 ((11 : Nat) : Int) from by decide, H11, H11e]
            rw [eaddz, mkAlu_denot]
            show edenot E e_str0 + Z_to_bv 64 1 = Z_to_bv 64 (STR0 sp argv envp + (0 : Int) + 1)
            rw [V3']
            have key : bv_unsigned (Z_to_bv 64 (STR0 sp argv envp) + Z_to_bv 64 1)
                = bv_unsigned (Z_to_bv 64 (STR0 sp argv envp + (0 : Int) + 1)) := by
              rw [u_add64, u_lit (STR0 sp argv envp) ⟨by omega, by show _ < two64; omega⟩,
                u_lit 1 ⟨by decide, by decide⟩,
                u_lit (STR0 sp argv envp + (0 : Int) + 1) ⟨by omega, by show _ < two64; omega⟩]
              exact Int.emod_eq_of_lt (by omega) (by show _ < two64; omega)
            exact BitVec.eq_of_toNat_eq (Int.ofNat.inj key)
          -- the cell is writable
          obtain ⟨HKW, -, -⟩ := kwritable_sound segs E (Mr A argH E cs model FULL) (kn cs) (kn cs)
            (.ELit 0) p 8 HC.co_know HC.co_know Hwr (by omega)
          have HKW' : store_ok segs (Mr A argH E cs model FULL) (Z_to_bv 64 p) 8 = true := by
            have h := HKW
            simp only [estart, SA] at h
            rw [edenot_lit] at h
            rw [show bv_unsigned (Z_to_bv 64 0) = (0 : Int) from by decide, Int.zero_add] at h
            simpa using h
          -- the loop
          have Hst0 : store_ok segs (mrestrict (Hv A E cs model) FULL) (Z_to_bv 64 p) 8 = true :=
            store_ok_mono segs 8 (Mr A argH E cs model FULL) (mrestrict (Hv A E cs model) FULL)
              (Z_to_bv 64 p) (Mr_grows_Hv A argH E cs model FULL) HKW'
          have HM : ∀ a : word, STR0 sp argv envp ≤ bv_unsigned a →
              bv_unsigned a ≤ STR0 sp argv envp + ((s0 argv).length : Int) →
              mrestrict (Hv A E cs model) FULL a = wrap_mem ph sp argv envp uid hw rdraw a := by
            intro a Ha1 Ha2
            rw [mrestrict_Hv_high A E cs model FULL a (by
              have hCEIL : CEIL ≤ STR0 sp argv envp := by
                have hargc := len_av argv Hva
                have henvc := len_ev envp Hve
                have hu1 := usp_lo sp Hsp_lo
                unfold STR0 argc envc usp CEIL at *
                omega
              omega)]
            exact SINV_str0 E FULL a HS Ha1 Ha2
          obtain ⟨R', M', Hms, Hpost, HM'⟩ := AsanStartLoops.pn_loop segs A.x_pnscan wp0 wp1 wp2 wp3 wp4
            ⟨Xpn.1, Xpn.2.1⟩ Fp0 Fp1 Fp2 Fp3 Fp4 Ep.1 Ep.2.1 Ep.2.2.1 Ep.2.2.2.1 Ep.2.2.2.2
            Dp0 Dp1 Dp2 Dp3 Dp4
            (mrestrict (Hv A E cs model) FULL) (seg_rom segs) p (STR0 sp argv envp) (s0 argv)
            ⟨hp0, hp8⟩ ⟨hpn0, hpn2⟩ (Or.inl hpstr0) (valid_argv_str_nz argv 0 Hva hav)
            (fun j Hj => rd_str0_j segs ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi
              (mrestrict (Hv A E cs model) FULL) j Hj HM)
            Hst0 (s0 argv) 0 R (mrestrict (Hv A E cs model) FULL) rfl (by omega) H10 H11' H12
            (AsanStartLoops.cellrel_refl (mrestrict (Hv A E cs model) FULL) p)
          have Hms' : msteps segs (restrict (Hv A E cs model)
              (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)))
              (mkst R' (Z_to_bv 64 (A.x_pnscan + 12)) M' (seg_rom segs)) := by
            rw [restrict_mkst, Hpcx]
            exact Hms
          show srealizes segs (AsanAcct.mkCfg
            (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)) model) T
          refine srz_msteps_restricted_T segs (Hv A E cs model)
            (H_off_segments_vis segs A HSEGS E cs model) Hwx (allowA A E cs)
            (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs))
            (mkst R' (Z_to_bv 64 (A.x_pnscan + 12)) M' (seg_rom segs))
            model T ?_ ?_ HC.co_minv HC.co_halt Hms' ?_
          · exact lazy_cover_vis segs A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC
          · exact A_wf_allowA' A E cs
          · intro model' Hinv' Hsame Hclean
            show srealizes segs (AsanAcct.mkCfg
              (unrestrict (Hv A E cs model) FULL
                (mkst R' (Z_to_bv 64 (A.x_pnscan + 12)) M' (seg_rom segs))) model') T
            have hmk : unrestrict (Hv A E cs model) FULL
                (mkst R' (Z_to_bv 64 (A.x_pnscan + 12)) M' (seg_rom segs))
                = mkst R' (Z_to_bv 64 (A.x_pnscan + 12))
                    (munrestrict (Hv A E cs model) FULL M') (seg_rom segs) := by
              show mkst R' (Z_to_bv 64 (A.x_pnscan + 12))
                (munrestrict (Hv A E cs model) FULL M') (seg_rom segs) = _
              rfl
            rw [hmk]
            obtain ⟨Hp11, Hp13, Pag⟩ := Hpost
            obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs Hfresh
            have Hag : env_agree (nxt cs) E (ext1 E (nxt cs) (getr R' 11)) :=
              ext1_agree E (nxt cs) (getr R' 11)
            have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
              E (ext1 E (nxt cs) (getr R' 11)) cs R FULL model Hag Hfresh HC
            have Hhid := hid_agree A nx0 argH argH_agree (nxt cs) E
              (ext1 E (nxt cs) (getr R' 11)) cs model Hag Fle Fallow
            -- the cell relation gives back the untouched bytes
            have HF : ∀ a : word, bv_unsigned a < p ∨ p + 8 ≤ bv_unsigned a →
                munrestrict (Hv A E cs model) FULL M' a = FULL a := by
              intro a Ha
              unfold munrestrict
              cases h2 : Hv A E cs model a with
              | true => rfl
              | false =>
                rw [HM'.1 a Ha]
                unfold mrestrict
                rw [h2]
                rfl
            refine Hk (ext1 E (nxt cs) (getr R' 11)) R'
              (munrestrict (Hv A E cs model) FULL M') model'
              ⟨env_agree_le nx0 (nxt cs) E (ext1 E (nxt cs) (getr R' 11)) Hag Fle, Hag⟩ ?_ ?_
            · -- `cs_ok` of the successor state
              refine cs_ok_frame segs A LIMIT SINV argH FS0 SINV_frame
                (ext1 E (nxt cs) (getr R' 11)) cs R FULL model _ R'
                (munrestrict (Hv A E cs model) FULL M') model' HC' Hsame ?_ ?_ rfl ?_ ?_
              · rw [allowA_agree A (nxt cs) E (ext1 E (nxt cs) (getr R' 11)) cs Hag Fallow]
                exact Hinv'
              · refine regs_ok_post2 (ext1 E (nxt cs) (getr R' 11)) cs.a_ss.s_regs R R'
                  11 (11 : reg) (.EVar (nxt cs)) 13 (13 : reg) (.ELit 0) HC'.co_regs
                  ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by decide) (by decide)
                  ?_ ?_ ?_
                · rw [show edenot (ext1 E (nxt cs) (getr R' 11)) (.EVar (nxt cs)) = getr R' 11 from
                    ext1_at E (nxt cs) (getr R' 11), Hp11]
                · rw [Hp13]
                  rfl
                · intro r N1 N2
                  exact Pag r (fun h => h.elim N1 N2)
              · -- the havoc'd knowledge
                show know_ok segs (ext1 E (nxt cs) (getr R' 11))
                  (mrestrict (hid A argH (ext1 E (nxt cs) (getr R' 11)) cs model)
                    (munrestrict (Hv A E cs model) FULL M'))
                  (kn_havoc (kimg_cut (kn cs) p 8) (.ELit 0) p (.ELit 8))
                rw [Hhid]
                refine know_ok_havoc segs (ext1 E (nxt cs) (getr R' 11))
                  (mrestrict (hid A argH E cs model) FULL)
                  (mrestrict (hid A argH E cs model) (munrestrict (Hv A E cs model) FULL M'))
                  (kimg_cut (kn cs) p 8) (.ELit 0) (.ELit 8) p ?_ ?_ ?_
                · have HK' := HC'.co_know
                  unfold Mr at HK'
                  rw [Hhid] at HK'
                  exact kimg_cut_sound segs (ext1 E (nxt cs) (getr R' 11))
                    (mrestrict (hid A argH E cs model) FULL) (kn cs) p 8 HK'
                · -- stores to the cell land outside the knowledge
                  intro x Hx
                  have hxp : bv_unsigned x < p ∨ p + 8 ≤ bv_unsigned x := by
                    have h1 : estart (ext1 E (nxt cs) (getr R' 11)) (SA (.ELit 0) p) = p := by
                      unfold estart SA
                      rw [edenot_lit, show bv_unsigned (Z_to_bv 64 0) = (0 : Int) from by decide,
                        Int.zero_add]
                    have h2 : elenZ (ext1 E (nxt cs) (getr R' 11)) (.ELit 8) = 8 := by
                      unfold elenZ
                      rw [edenot_lit, show bv_unsigned (Z_to_bv 64 8) = (8 : Int) from by decide]
                    rw [h1, h2] at Hx
                    omega
                  unfold mrestrict
                  rw [HF x hxp]
                · -- the overlay only grew
                  intro x Hx
                  by_cases hh : hid A argH E cs model x = true
                  · rw [show mrestrict (hid A argH E cs model) FULL x = none from by
                      simp [mrestrict, hh]] at Hx
                    exact absurd Hx (by simp)
                  · have hhid : hid A argH E cs model x = false := by simpa using hh
                    show mrestrict (hid A argH E cs model)
                      (munrestrict (Hv A E cs model) FULL M') x ≠ none
                    rw [show mrestrict (hid A argH E cs model)
                        (munrestrict (Hv A E cs model) FULL M') x
                        = munrestrict (Hv A E cs model) FULL M' x from by
                      simp [mrestrict, hhid]]
                    by_cases hv : Hv A E cs model x = true
                    · rw [show munrestrict (Hv A E cs model) FULL M' x = FULL x from by
                        simp [munrestrict, hv]]
                      rw [show mrestrict (hid A argH E cs model) FULL x = FULL x from by
                        simp [mrestrict, hhid]] at Hx
                      exact Hx
                    · have hvf : Hv A E cs model x = false := by simpa using hv
                      rw [show munrestrict (Hv A E cs model) FULL M' x = M' x from by
                        simp [munrestrict, hvf]]
                      exact HM'.2 x (by
                        rw [show mrestrict (Hv A E cs model) FULL x = FULL x from by
                          simp [mrestrict, hvf]]
                        rw [show mrestrict (hid A argH E cs model) FULL x = FULL x from by
                          simp [mrestrict, hhid]] at Hx
                        exact Hx)
              · -- `FULL'` agrees with `FULL` on `hid`-hidden addresses
                intro a Ha
                rw [Hhid] at Ha
                unfold hid at Ha
                rw [Bool.or_eq_true] at Ha
                rcases Ha with Ha | Ha
                · refine HF a (Or.inr ?_)
                  have h1 := argH_high E a Ha
                  have h2 : p + 8 ≤ A.img_hi := Hhi
                  have h3 : A.img_hi ≤ KHI := HULL_ok.2.2.2
                  unfold CEIL KHI at *
                  omega
                · unfold munrestrict
                  have hv : Hv A E cs model a = true := by
                    unfold Hv
                    rw [Ha]
                  simp [hv]
            · -- the file system never moves
              exact (same_but_materialized_frame model model' Hsame).2.2.2.2.2.2.2.2.2.2.2.1
        · simp at Hn
      · simp at Hn

/-! ## 4. `Some`-injectivity for `acs`

     needs this because `injection` diverges on the states
    `XLayout` produces. -/

/-- `some` is injective at `acs`. -/
theorem some_inj_acs (a b : acs) (H : some a = some b) : a = b := Option.some.inj H

/-! ## 5. `XLayout` — re-spelling the conditional `argv[1]` fact -/

/-- With `2 ≤ argc`, the conditional word at `sp+16` is `argv[1]`. -/
theorem e_argv1w_ge2 (E : env) (H : 2 ≤ bv_unsigned (E.ev V_ARGC)) :
    edenot E e_argv1w = edenot E e_str1 := by
  have key : bv_unsigned (edenot E e_argv1w) = bv_unsigned (edenot E e_str1) := by
    change bv_unsigned ((alu64 .SLTU (Z_to_bv 64 1) (E.ev V_ARGC)) * (edenot E e_str1))
      = bv_unsigned (edenot E e_str1)
    rw [u_mul64, u_sltu64]
    have h1 : bv_unsigned (Z_to_bv 64 1) = (1 : Int) := by decide
    have hlt : bv_ltu (Z_to_bv 64 1) (E.ev V_ARGC) = true := by
      rw [bv_ltu_eq_true, h1]
      omega
    rw [ite_eq_left hlt, Int.one_mul]
    exact Int.emod_eq_of_lt (u64_range _).1 (u64_range _).2
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj key)

/-- With `argc ≤ 1`, the conditional word at `sp+16` is the NULL terminator. -/
theorem e_argv1w_le1 (E : env) (H : bv_unsigned (E.ev V_ARGC) ≤ 1) :
    edenot E e_argv1w = edenot E (.ELit 0) := by
  have key : bv_unsigned (edenot E e_argv1w) = bv_unsigned (edenot E (.ELit 0)) := by
    change bv_unsigned ((alu64 .SLTU (Z_to_bv 64 1) (E.ev V_ARGC)) * (edenot E e_str1))
      = bv_unsigned (edenot E (.ELit 0))
    rw [u_mul64, u_sltu64]
    have h1 : bv_unsigned (Z_to_bv 64 1) = (1 : Int) := by decide
    have hlt : ¬ (bv_ltu (Z_to_bv 64 1) (E.ev V_ARGC) = true) := by
      rw [bv_ltu_eq_true, h1]
      omega
    rw [ite_eq_right hlt, edenot_lit]
    rw [show bv_unsigned (Z_to_bv 64 0) = (0 : Int) from by decide]
    simp
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj key)

/-- Re-spelling the conditional `argv[1]` fact's value. -/
theorem kw_argv1_respell (segs : List Segment) (E : env) (M : word → Option byte)
    (v v' : expr) (HK : kentry_ok segs E M (kw_argv1 v))
    (Hv : edenot E v' = edenot E v) : kentry_ok segs E M (kw_argv1 v') := by
  unfold kw_argv1 at *
  simp only [kentry_ok] at *
  rw [Hv]
  exact HK

/-- `XLayout` is sound: once `argc`'s class is known, the conditional
    `argv[1]` fact is re-spelled as `e_str1` (argc ≥ 2) or `0` (argc ≤ 1). -/
theorem x_sound_layout (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    x_stmt segs A nx0 LIMIT SINV argH FS0 .XLayout := by
  intro args cs cs' E R FULL model T HC _ Hn Hk
  simp only [node_x] at Hn
  unfold node_layout at Hn
  by_cases Hex : ((kn cs).any (kentry_eqb (kw_argv1 e_argv1w))) = true
  · rw [ite_eq_right (by simp [Hex])] at Hn
    have HK0 : kentry_ok segs E (Mr A argH E cs model FULL) (kw_argv1 e_argv1w) := by
      obtain ⟨K0, Hin, Heqb⟩ := List.any_eq_true.mp Hex
      have hK0 : K0 = kw_argv1 e_argv1w := (kentry_eqb_eq (kw_argv1 e_argv1w) K0 Heqb).symm
      subst hK0
      exact HC.co_know _ Hin
    have HK' : know_ok segs E (Mr A argH E cs model FULL)
        (List.filter (fun K => !(kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)) :=
      know_ok_filter segs E (Mr A argH E cs model FULL) _ (kn cs) HC.co_know
    have FIN : ∀ v : expr, edenot E v = edenot E e_argv1w →
        cs' = set_kn cs (kw_argv1 v ::
          List.filter (fun K => !(kentry_eqb (kw_argv1 e_argv1w) K)) (kn cs)) →
        srealizes segs (cfg_of segs R (pc cs) FULL model) T := by
      intro v Hv hcs'
      subst hcs'
      simp only [pc, set_kn, with_ss, mk_ss] at Hk
      refine Hk E R FULL model ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ ?_ rfl
      refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
      intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact kw_argv1_respell segs E (Mr A argH E cs model FULL) e_argv1w v HK0 Hv
      · exact HK' K hK
    split at Hn
    · -- `[ELit 1]`: `argc ≥ 2`
      cases hx : xlo (kn cs) (.EVar V_ARGC) with
      | none => simp [hx] at Hn
      | some lo =>
        by_cases hle : 2 ≤ lo
        · simp only [hx, ite_eq_left hle, Option.some.injEq] at Hn
          have hb := xlo_sound segs E (Mr A argH E cs model FULL) (kn cs) (.EVar V_ARGC) lo
            HC.co_know hx
          refine FIN e_str1 ?_ Hn.symm
          rw [e_argv1w_ge2 E]
          show 2 ≤ bv_unsigned (edenot E (.EVar V_ARGC))
          omega
        · simp [hx, ite_eq_right hle] at Hn
    · -- `[ELit 0]`: `argc ≤ 1`
      cases hx : xhi (kn cs) (.EVar V_ARGC) with
      | none => simp [hx] at Hn
      | some hi =>
        by_cases hle : hi ≤ 1
        · simp only [hx, ite_eq_left hle, Option.some.injEq] at Hn
          have hb := xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) (.EVar V_ARGC) hi
            HC.co_know hx
          refine FIN (.ELit 0) ?_ Hn.symm
          rw [e_argv1w_le1 E]
          show bv_unsigned (edenot E (.EVar V_ARGC)) ≤ 1
          omega
        · simp [hx, ite_eq_right hle] at Hn
    · simp at Hn
  · rw [ite_eq_left (by simp [Hex])] at Hn
    simp at Hn
