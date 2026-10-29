/-
  * Common.AsanPlanSound — soundness of the reflective ASan plan checker
    `AsanPlan`, in `SpinAlg.srealizes` form with spec nodes
    (PMmap/PMmapIn/PMprotect/PSpin).

    [check_sound]: if `AP.check SEGS IT A nx0 LIMIT HS bfuel fuel cs p = COk s`
    then every concrete configuration matching the checker state [cs]
    ([cs_ok E cs R FULL model]: registers, knowledge about the RESTRICTED
    memory, exact mmap ledger, budget invariant [AsanAcct.MInv], the hidden
    argument block [SINV]) realizes ([ShapeAlg.realizes], fault-free, exact)
    the trace set `sd E (m_fs model) s` denoted by the shape [s].

    Image-independent: the segment list [SEGS], the instruction table [IT], the
    address table [A], the budget [LIMIT], the argument-block invariant
    [SINV]/[argH], the hole denotations [HOLES] and stored states [HS] are
    Section variables with the hypotheses listed in Section [Sound].  The
    per-node soundness obligations that are NOT proved in this file are the
    `Hypothesis node_*_sound` items of part 7 (statements `*_stmt`); they are
    listed in `AsanNodesIface`.

    DESIGN:
    * VISIBILITY IS SEMANTIC.  [vis E cs model a] (part 2) is computed from
      the MODEL (vm_maps / vm_noaccess / m_vm_lazy) and the allowed set
      [allowA E cs]: a byte is visible iff it is in the image hull, or at/above
      the allocation ceiling, or inside a mapping, not PROT_NONE, and — when
      its page is lazy — inside a visible APPLICATION RANGE [a_vis] or inside
      the ASan SHADOW of one (UNROUNDED; the budgeted set [allowA] is the
      page-outward rounding of both).  Hidden = argument block part
      [argH E] (strings, envp array: read only by dedicated nodes) or not
      visible.  Consequences: [lazy_cover] holds by definition; the checker
      needs no mirror of vm_noaccess / m_vm_lazy; PROT_NONE slices, guard
      pages, commits inside reservations are all described by the model alone.
    * [co_maps] is EXACT (in ledger order); entry KINDS: [KRWLAZY] ([co_kinds]:
      bytes outside vm_noaccess, pages lazy), [KNONE]/[KNONELAZY] ([co_none]:
      the interval is verbatim an element of vm_noaccess; arms E/G/mprotect
      re-kind the entry to [KRW]), [KRW] no constraint; [co_nasub]: noaccess
      bytes are mapped bytes.
    * [a_ghost]: munmapped visible ranges stay in the budgeted set [allowA]
      (their shadow pages may be materialized) but not in [vis].
    * [co_zero]: every hidden byte that is mapped, not PROT_NONE and on a lazy
      page holds 0.
    * the allowed set is the page-OUTWARD rounding of the checker's intervals
      ([allowA]); [A_wf] then holds by construction, [A_bytes] is bounded by
      Σ (len + 8192) = [a_abytes].
    * placement: [co_split] ([AsanPlacement.ledger_split] with an existential
      high mark [Y >= a_ylo]); gap: [co_totsz]; budget: [co_eager] + MInv.
    * [SINV E FULL] (Section variable): the initial stack image above sp,
      needed by the start-up loop nodes and the openat node; framed by
      [argH] (hidden, >= CEIL, never written).
 The contents, part by part:
  - Part `1` (small vocabulary), ALL of it: `uE`, `pagedown`, `pageup` and
    their five arithmetic lemmas, `in_ivs` (+ `in_ivs_true`), `in_hull`,
    `iv_disjoint`, `seps`, `sum_sizes`, `cfg_of`.
  - Part `2` (denotations), ALL DEFINITIONS: `res_len_ok`, `hull_ok`,
    `shadow_ok`, `Wz`, `piece_den`, `Wp`, `sd`, `sh_lo`, `sh_hi`, `allow1`,
    `allowA`, `amap_den`, `in_vis`, `in_sh`, `in_allow`, `in_ghost`, `vis`,
    `hid`, `Mr`, `fds_std`, `CH`, `chunk`, `flen`, `fds3`, `fds_ok`,
    `maps_match`, `hole_ok`, and the record `cs_ok`; plus its lemmas that do
    not run the executor: `holes_mono`, `holes_sublist`, `holes_none`.
  - Part `3/4/5` lemmas proved: `A_wf_allowA`, `page_base_le`,
    `page_in_ranges_bounds`, `page_allowedb_app_r`, `A_bytes_app`, `MInv_app`,
    `in_ivs_true`, `pageup_pagedown_gap`, `filter_all_true`,
    `aluop_eqb_refl'`, `mulop_eqb_refl'`, `expr_eqb_refl'`, `amap_eqb_refl'`,
    `existsb_false_forall`, and the whole `maps_match` family that does not
    need `map_remove`: `maps_match_exact`, `maps_match_In`,
    `in_ivs_maps_match`, `maps_match_cons`, `maps_match_length`,
    `maps_match_elem`, `maps_match_rekind`, `in_ivs_map_den`.
  - Part `3`+ ALL remaining DEFINITIONS: `kfoot`, `kfoot_apart`, `pw_kind`,
    `kimg_in_hull`, `node1_stmt`, `always` and the `*_stmt` obligations
    (`sys_stmt`, `x_stmt`, `fresh_stmt`, `join_stmt`, `brk2_stmt`,
    `exit_stmt`, `ext_stmt`, `ext2_stmt`, `mm2_stmt`, `mm3_stmt`,
    `emit_stmt`, `holes_stmt`), the valuation helpers `ext1`, `ext_list`,
    `kn_bigexprs`, `upd`, `is_havoc`, `henv`, and the loop context `LCOK`,
    `lc_guard`.
  - The valuation-agreement family (part `4`–`5`): `env_agree_le`,
    `env_agree_refl`, `env_agree_trans`, `ext1_agree`, `ext1_at`,
    `upd_agree`, `upd_at`, `upd_same`, `upd_upd`, `is_havoc_range`,
    `u_small`, `ext_list_agree`, `ext_list_at`, `henv_agree`, `henv_high`.
  - One `ediv_mul_4096` (`z / 4096 * 4096 = z - z % 4096`),
    the shape the rounding lemmas need (`Int.ediv_mul_cancel_add_emod` has no
    Lean counterpart in this toolchain).
  - `## Sanity checks` at the end: the decidable checks.
 The `DEFERRED` block at
  the end of the file is therefore EMPTY: it lists nothing and states nothing
  further.  What has landed of the later
  parts: the whole `env_agree` transport family (`edenot_agree'` …
  `cs_ok_agree`), the allowed-set/visibility arithmetic (`allowA_agree`,
  `in_allow_agree`, `in_ghost_agree`, `hid_agree`, `vis_mono`,
  `in_allow_cons`, `hid_hull`, `H_off_segments_cs`, the `A_bytes` lemmas),
  all the `*_vars_lt` monotonicity lemmas, the trace-set algebra
  (`t_*`, `sd_agree`, `sd_has_nil`, `sd_salt2`, `salt2_vars`), the
  knowledge-GC/forgetting lemmas (`know_ok_filter`, `cs_ok_set_kn`,
  `cs_gc_ok`, `drop_ixs_incl`, `forget_sound`), every `*_eqb_eq` reflection,
  and the part-7 boundary nodes `split_sound`, `bump_sound`, `LCOK_bnd`.
  The most recent pass added the `kcut` consumer chain and the fog nodes:
  `kentry_apart_bp_eq`, `havoc1p_eq`, `cutout1p_eq` (they need
  `AxSymExec3Sound.ranges_apart_p_eq`, which has landed), `pw_kind_wr`,
  `kcut_pw_sound` (with the `pw_kind` twins of the three
  `zf_kind` cut pieces, `kcut_low_piece_pw` / `kcut_high_piece_pw` /
  `kcut_high_bounds_pw`), `kwr_cut_sound`, `know_ok_havoc`, `know_ok_cutout`,
  `droprange_sound`, `entails_sound`, `hid_cons_sub`, `regs_ok_sr_fresh`,
  `node_havoc_nxt`, and the fog chain `list_set_nth_maps_match` →
  `list_insert_nth_maps_match` → `cs_ok_with_maps` → `fog_sound` /
  `fognew_sound`.
 With them the cover chain
  is closed end to end: `rdn_bytes_some` (:2762) -> `cover1_sound` ->
  `cover_x_sound` -> `kunk_covered_sound` -> `kn_incl_h_sound` ->
  `entails_h_sound` -> `diamond_join_sound`.  The pass before this one landed
  seven more, all in section 10: `adenot_eq_of_estart`
  (a helper), `kentry_eqb_h_sound` (:2713), the `PHavocWords` chain
  `hw_apply_ok` (:3954) -> `hw_go_ok` (:3991) -> `havocwords_sound` (:4003),
  which COMPLETES chain 3 and gives `check_sound` its node lemma for the
  `PHavocWords` arm, and `rdn_bytes_some` (:2762), the first missing link of
  the cover chain `kn_incl_h_sound` needs.  Measured: `kn_incl_h_sound` was
  NOT "one dependency away": `kn_incl1_h` ends in `kunk_covered A k K`, so it
  also needs `kunk_covered_sound` (:2837) -> `cover_x_sound` (:2822) ->
  `cover1_sound` (:2779) -> `rdn_bytes_some` (:2762) ->
  `seg_rom_off_hull` (:2754), plus a local `kimg_sub_covered` argument for the
  `KImg` arm — all of which have now landed.  The pass before this one
  landed six, all in the
  `PShDisj` / register-havoc corner of the node chain: `shadow_of_val`
  (:2292), `shdisj_sound` (:2316), `regs_match_h_char` (:2913),
  `regs_match_h_sound` (:2968), `cs_ok_reenv` (:2980) — which is
  `cs_ok_agree`'s proof with `set_regs cs sr'` in place of `cs` — and, with
  them, the discovery that `AsanPlanCore.node_shdisj` was missing the `end`
  of its guard's `match`, so it never tested the apartness it claimed: the
  statement was FALSE as stated, the definition is now fixed at both twins
  and `shdisj_sound` is proved against it.
  The pass before this one proved `check_vars` — every shape the
  checker returns keeps the variable bound `shape_vars_lt nx0` — and
  `cont_agree` (:4121), the continuation adapter that turns the induction
  hypothesis of `check_sound` from the loop context's valuation into any
  valuation agreeing below `nxt cs`; they are the first consumers of the
  `AsanPlan.check_succ` unfolding that the `check_go` refactor in
  `AsanPlan.lean` provides.  `check_vars` is a plain induction on `fuel`
  (base case `check_zero_lc`) with one case per plan constructor and `lc`
  shape, 90 arms in all.  The pass before it proved `check_all_ok`
 — the first state of a successfully checked list checks
  with the returned shape — on top of the fold lemmas
  `check_all_fold_err` / `check_all_fold_ok`, which is what `check_vars` uses
  for the destroyed-case shapes of `PMmapIn` / `PMmapInH`.
  The pass before that landed the BLOCK-RUN SPINE — the two theorems the
  `DEFERRED` block used to record as blocked — plus the two boundary lemmas
  they need: `lazy_cover_cs`, `cs_ok_frame` (:453),
  `run_block_sound` (:2060) and `run_block_gc_sound` (:2114), together with
  the rounding helpers `pagedown_mono` / `bv_unsigned_page_base` /
  `aligned_le_pagedown` / `aligned_gt_pagedown` / `in_allow_page` and the
  `fds_ok_frame`.  Every dependency they need
  (`AxSymExec3Sound.sym_execTX_ex`, `AxSymExec3Sound.carry_sound`,
  `AxSymRun3.runTX_sound`, `AxSymRun3.carry_after`) is present in this tree.
  What was still missing of the part `7`–`9` node soundness chain is now
  ONLY `check_sound` itself: the two `symexec`-style nodes
  and the `cs_ok_rename` Section they need LANDED in this pass
  (`rename_sound` / `compact_sound`, section 10 — the `node_rename` body's
  two auxiliary matches are the reason they were thought to be "just the
  case analysis"; see the MEASURED note on them in section 10).
  `node_fresh_sound_pf` (:2138) LANDED — see the MEASURED note on the
  `match base` auxiliary in the `DEFERRED` prose.
  `vis_add_sound` (:1245) LANDED — and it is now UNCONDITIONAL, because the
  `AsanPlanCore` guard gained the shadow-flatness conjunct.
  `unvis_sound` (:3447) LANDED in the
  latest pass (with the helper `A_bytes_unvis_le`, its `HAB`).
  `rdn_visible` (:919) and `know_ok_unhide` (:943) — the two
  `mrestrict`/`mem_grows` lemmas `unvis_sound` rests on — LANDED in the
  latest pass, as did `maps_match_remove` (:1184), the ledger half of the
  fog obligation (and the last prerequisite of `vis_add_sound`).
  `havocbig_sound` (:2504) LANDED in the pass before, on the (already
  landed) `kn_bigsubst_sound` (:2477).
  DEFERRED: NOTHING.   A reader looking for a declaration should therefore trust the section
  number, not the position in the file.
  NOTES.
  - `Z` is `Int`, `nat` is `Nat`, `Z.of_nat` is `↑`/`(· : Int)`,
    `Z.leb`/`Z.ltb`/`Z.eqb` become `≤`/`<`/`==`, `negb` is `!`,
    `existsb`/`forallb` are `List.any`/`List.all`,
    `Z.min` is `min`, `2 ^ k` on `Int` is `zpow 2 k` (`AsanPlanCore`).
  - `List.Forall` does not exist in this core: every `Forall P l` becomes
    `∀ x ∈ l, P x` (and `Forall2` is spelled out).
  - a `match ...   - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.AsanAcct
import LinuxSem.Common.AsanAcctShape
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.SpinAlg
import LinuxSem.Common.AsanPlacement
import LinuxSem.Common.BackingAlgebra
import LinuxSem.Common.StoreOk
import LinuxSem.Common.AxSymRun3
import LinuxSem.Common.AgentLib

namespace LinuxSem.Common.AsanPlanSound

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.BackingAlgebra
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asanplansound_fx : PropExec.FPState := PropExec.fx0

/-! ## 1. Small vocabulary -/

/-- `uE`: the unsigned value of a symbolic expression. -/
def uE (E : env) (e : expr) : Int := bv_unsigned (edenot E e)

/-- Round down to a page. -/
def pagedown (z : Int) : Int := z / 4096 * 4096

/-- Round up to a page. -/
def pageup (z : Int) : Int := (z + 4095) / 4096 * 4096

/-- `z / 4096 * 4096 = z - z % 4096` (the shape the rounding lemmas use). -/
theorem ediv_mul_4096 (z : Int) : z / 4096 * 4096 = z - z % 4096 := by
  have h := Int.emod_add_mul_ediv z 4096
  have h' : 4096 * (z / 4096) = z - z % 4096 := by omega
  rw [Int.mul_comm]; omega

/-- `pagedown` never increases its argument. -/
theorem pagedown_le (z : Int) : pagedown z ≤ z := by
  unfold pagedown
  have h1 := Int.emod_nonneg z (by decide : (4096 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos z (by decide : (0 : Int) < 4096)
  rw [ediv_mul_4096]
  omega

/-- `pageup` never decreases its argument. -/
theorem pageup_ge (z : Int) : z ≤ pageup z := by
  unfold pageup
  have h1 := Int.emod_nonneg (z + 4095) (by decide : (4096 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos (z + 4095) (by decide : (0 : Int) < 4096)
  have e : (z + 4095) / 4096 * 4096 = (z + 4095) - (z + 4095) % 4096 := by
    have h := Int.emod_add_mul_ediv (z + 4095) 4096
    have h' : 4096 * ((z + 4095) / 4096) = (z + 4095) - (z + 4095) % 4096 := by omega
    rw [Int.mul_comm]; omega
  rw [e]
  omega

/-- `pagedown` lands on a page. -/
theorem pagedown_mod (z : Int) : pagedown z % 4096 = 0 := by
  unfold pagedown
  rw [Int.mul_comm]
  exact Int.mul_emod_right 4096 (z / 4096)

/-- `pageup` lands on a page. -/
theorem pageup_mod (z : Int) : pageup z % 4096 = 0 := by
  unfold pageup
  rw [Int.mul_comm]
  exact Int.mul_emod_right 4096 ((z + 4095) / 4096)

/-- The page-outward rounding of an interval is at most 8192 bytes wider. -/
theorem pageup_minus_pagedown (a b : Int) (H : a ≤ b) :
    pageup b - pagedown a ≤ b - a + 8192 := by
  unfold pageup pagedown
  have h1 := Int.emod_nonneg (b + 4095) (by decide : (4096 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos (b + 4095) (by decide : (0 : Int) < 4096)
  have h3 := Int.emod_nonneg a (by decide : (4096 : Int) ≠ 0)
  have h4 := Int.emod_lt_of_pos a (by decide : (0 : Int) < 4096)
  have e1 : (b + 4095) / 4096 * 4096 = (b + 4095) - (b + 4095) % 4096 := by
    have h := Int.emod_add_mul_ediv (b + 4095) 4096
    have h' : 4096 * ((b + 4095) / 4096) = (b + 4095) - (b + 4095) % 4096 := by omega
    rw [Int.mul_comm]; omega
  have e2 : a / 4096 * 4096 = a - a % 4096 := ediv_mul_4096 a
  rw [e1, e2]
  omega

/-- Interval membership over a (base, size) word list, in `Int`. -/
def in_ivs (z : Int) (l : List (word × word)) : Bool :=
  l.any (fun iv => (bv_unsigned iv.1 ≤ z) && (z < bv_unsigned iv.1 + bv_unsigned iv.2))

/-- Inside the loaded-image hull of the address table. -/
def in_hull (A : atable) (z : Int) : Bool := (A.img_lo ≤ z) && (z < A.img_hi)

/-- Pairwise disjoint intervals. -/
def iv_disjoint (p q : word × word) : Prop :=
  bv_unsigned p.1 + bv_unsigned p.2 ≤ bv_unsigned q.1 ∨
  bv_unsigned q.1 + bv_unsigned q.2 ≤ bv_unsigned p.1

/-- A list of pairwise-disjoint intervals. -/
inductive seps : List (word × word) → Prop
  | nil : seps []
  | cons (p : word × word) (l : List (word × word)) :
      (∀ x ∈ l, iv_disjoint p x) → seps l → seps (p :: l)

/-- The sum of the interval sizes. -/
def sum_sizes : List (word × word) → Int
  | [] => 0
  | iv :: r => bv_unsigned iv.2 + sum_sizes r

/-- The concrete configuration the checker state denotes. -/
def cfg_of (segs : List Segment) (R : BvMap word) (p : Int)
    (M : word → Option byte) (model : Model) : config :=
  AsanAcct.mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom segs)) model

/-! ## The `Section Sound` context

 opens `Section Sound` with the following variables and hypotheses;
this tree threads them explicitly (see the header).
    Variable SEGS : list Segment.
    Variable IT : itab.
    Hypothesis IT_ok : itab_sound SEGS IT.
    Variable A : atable.
    Variable nx0 : nat.
    Variable LIMIT : Z.
    Variable HS : nat -> option acs.
    Variable XN : nat -> list expr -> acs -> option acs.               (hooked extension nodes)
    Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
    Variable XB : nat -> list expr -> acs -> option (acs * acs).
    Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
    Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false ->
                                        find_segment SEGS (bv_unsigned a) 1 = None.
    Definition res_len_ok := length (segments_reserved SEGS) = n_res A.
    Definition hull_ok := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0
                          /\ img_hi A <= KHI.
    Definition shadow_ok := 0 <= shadow_off A <= 2 ^ 47.
    Hypothesis RES_len : res_len_ok.
    Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\
                                           bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                                 (segments_reserved SEGS).
    Hypothesis HULL_ok : hull_ok.
    Hypothesis SHADOW_ok : shadow_ok.
    Variable SINV : env -> (word -> option byte) -> Prop.
    Variable argH : env -> word -> bool.
    Hypothesis argH_high : forall E a, argH E a = true -> CEIL <= bv_unsigned a.
    Hypothesis argH_agree : forall E E' a, env_agree nx0 E E' -> argH E a = argH E' a.
    Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) ->
                                           SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
    Variable HOLES : nat -> env -> Fs.Fs -> TSet.
    Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
    Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
    Variable FS0 : Fs.Fs.
    Variable KC : nat.
Of these, only the ones a declaration actually USES become parameters of it. -/

section Sound

/-- Per-image fact (vm_compute per image): the reserved intervals fit in the hull. -/
def res_len_ok (segs : List Segment) (A : atable) : Prop :=
  (segments_reserved segs).length = A.n_res

/-- Per-image fact: the image hull is page aligned and below the high memory mark. -/
def hull_ok (A : atable) : Prop :=
  0 ≤ A.img_lo ∧ A.img_lo % 4096 = 0 ∧ A.img_hi % 4096 = 0 ∧ A.img_hi ≤ KHI

/-- Per-image fact: the ASan shadow offset is in range. -/
def shadow_ok (A : atable) : Prop := 0 ≤ A.shadow_off ∧ A.shadow_off ≤ 2 ^ 47

/-! ## 2. Denotations: shapes, allowed set, visibility, `cs_ok` -/

/-- A literal byte list written to `fd`. -/
def Wz (fd : Int) (bs : List Int) : List event :=
  bs.map (fun z => event.WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z))

/-- Emitted pieces: literal bytes / the bytes of blob variable `k`. -/
def piece_den (E : env) (p : spiece) : List byte :=
  match p with
  | .SPLit bs => bs.map (Z_to_bv 8)
  | .SPBlob k => E.eb k

/-- The writes of a piece list. -/
def Wp (E : env) (fd : Int) (ps : List spiece) : List event :=
  (ps.flatMap (piece_den E)).map (event.WriteEv (Z_to_bv 64 fd))

/-- `D` = the denotation of `SNext` (the rest of the enclosing loop; any set
    outside loop bodies). -/
def sd (HOLES : Nat → env → Fs.Fs → TSet) (D : TSet) (E : env) (fs : Fs.Fs) :
    shape → TSet
  | .SNil => t_nil
  | .SExit c => t_exit (Z_to_bv 64 c) fs
  | .SEmitP fd ps s' => t_emit (Wp E fd ps) (sd HOLES D E fs s')
  | .SAlt2 a b => t_alt2 (sd HOLES D E fs a) (sd HOLES D E fs b)
  | .SCase e mid s1 s2 =>
      if bv_unsigned (edenot E e) ≤ mid then sd HOLES D E fs s1 else sd HOLES D E fs s2
  | .SHole h => HOLES h E fs
  | .SNext => D

/-- The shadow interval of an application range `[b, b+n)`, low end. -/
def sh_lo (A : atable) (E : env) (p : expr × expr) : Int :=
  A.shadow_off + uE E p.1 / 8

/-- The shadow interval of an application range `[b, b+n)`, high end. -/
def sh_hi (A : atable) (E : env) (p : expr × expr) : Int :=
  A.shadow_off + (uE E p.1 + uE E p.2) / 8

/-- The allowed set: page-outward rounding of every visible application range
    and of its shadow interval. -/
def allow1 (A : atable) (E : env) (p : expr × expr) : List (Int × Int) :=
  [(pagedown (uE E p.1), pageup (uE E p.1 + uE E p.2)),
   (pagedown (sh_lo A E p), pageup (sh_hi A E p))]

/-- The allowed set: the page-outward rounding of every visible application
    range and of its shadow interval (`a_vis ++ a_ghost`). -/
def allowA (A : atable) (E : env) (cs : acs) : List (Int × Int) :=
  (cs.a_vis ++ cs.a_ghost).flatMap (allow1 A E)

/-- A ledger entry's denotation. -/
def amap_den (E : env) (m : amap) : word × word :=
  (edenot E m.am_base, edenot E m.am_len)

/-- A byte inside one of the visible application ranges (UNROUNDED). -/
def in_vis (E : env) (cs : acs) (z : Int) : Bool :=
  cs.a_vis.any (fun p => (uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2))

/-- A byte inside one of the visible application ranges' shadows (UNROUNDED). -/
def in_sh (A : atable) (E : env) (cs : acs) (z : Int) : Bool :=
  cs.a_vis.any (fun p => (sh_lo A E p ≤ z) && (z < sh_hi A E p))

/-- A byte inside an allowed (visible range or shadow) interval. -/
def in_allow (A : atable) (E : env) (cs : acs) (z : Int) : Bool :=
  in_vis E cs z || in_sh A E cs z

/-- A byte inside a GHOST range: no longer described (exempt from `co_zero`). -/
def in_ghost (E : env) (cs : acs) (z : Int) : Bool :=
  cs.a_ghost.any (fun p => (uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2))

/-- VISIBILITY (see the header). -/
def vis (A : atable) (E : env) (cs : acs) (model : Model) (a : word) : Bool :=
  let h := m_vmmaps model
  let z := bv_unsigned a
  in_hull A z ||
  (CEIL ≤ z) ||
  (in_ivs z h.vm_maps && !(in_ivs z h.vm_noaccess) &&
   (!(page_in_ranges (page_base a) (m_vm_lazy model)) || in_allow A E cs z))

/-- Hidden: part of the argument block, or not visible. -/
def hid (A : atable) (argH : env → word → Bool) (E : env) (cs : acs) (model : Model)
    (a : word) : Bool :=
  argH E a || !(vis A E cs model a)

/-- The memory the knowledge talks about. -/
def Mr (A : atable) (argH : env → word → Bool) (E : env) (cs : acs) (model : Model)
    (FULL : word → Option byte) : word → Option byte :=
  mrestrict (fun a => hid A argH E cs model a) FULL

/-- The standard fd table. -/
def fds_std : List (word × FdEntry) :=
  [(Z_to_bv 64 0, .FdChannel (Z_to_bv 64 0)), (Z_to_bv 64 1, .FdChannel (Z_to_bv 64 1)),
   (Z_to_bv 64 2, .FdChannel (Z_to_bv 64 2))]

/-- 64 KiB — the blob chunk size. -/
def CH : Nat := (65536 : Int).toNat

/-- Chunk `j` of a content. -/
def chunk (j : Nat) (c : List byte) : List byte := (c.drop (CH * j)).take CH

/-- The fd-3 content length. -/
def flen (c : List byte) : Int := min (c.length : Int) (2 ^ 26)

/-- The fd table with fd 3 = `e`. -/
def fds3 (e : FdEntry) : List (word × FdEntry) := (Z_to_bv 64 3, e) :: fds_std

/-- fd table denotation: fd 3 is a regular file whose 64 KiB chunk `j` is blob
    variable `k+j`, or a directory. -/
def fds_ok (E : env) (f : afd) (model : Model) : Prop :=
  match f with
  | .FdStd => m_fds model = fds_std
  | .FdDir => m_fds model = fds3 .FdDir
  | .FdFile k len off =>
      ∃ p c, m_fds model = fds3 (.FdFile p (edenot E off)) ∧
        fs_lookup (m_fs model) p = some c ∧
        uE E len = flen c ∧ uE E off ≤ uE E len ∧
        (∀ j : Nat, 65536 * (j : Int) < 2 ^ 26 → E.eb (k + j) = chunk j c)

/-- fog: the tracked ledger `a_maps` MATCHES `vm_maps`: every non-token element
    is exactly the next entry; a `KFOG` token of size `sz` stands for zero or
    one untracked entry of size at most `sz`. -/
def maps_match (E : env) : List amap → List (word × word) → Prop
  | [], l => l = []
  | m :: ms', l =>
      if is_fog m then
        maps_match E ms' l ∨
        ∃ iv l', l = iv :: l' ∧ bv_unsigned iv.2 ≤ uE E m.am_len ∧ maps_match E ms' l'
      else ∃ l', l = amap_den E m :: l' ∧ maps_match E ms' l'

/-- The HOLE tokens: no reserved or mapped interval meets `base, base+len`, and
    the hole lies on one side of the placement split (below `KHI`, or above the
    NULL-hint frontier `a_ylo`) — both inherited from the tracked entry the
    hole was punched into. -/
def hole_ok (E : env) (ylo : Int) (l : List (word × word)) (m : amap) : Prop :=
  is_hole m = true →
  (∀ iv ∈ l, bv_unsigned iv.1 + bv_unsigned iv.2 ≤ uE E m.am_base ∨
    uE E m.am_base + uE E m.am_len ≤ bv_unsigned iv.1) ∧
  (uE E m.am_base + uE E m.am_len ≤ KHI ∨ ylo ≤ uE E m.am_base)

/-- `holes_mono`: lowering the placement mark keeps every hole free. -/
theorem holes_mono (E : env) (y y' : Int) (l : List (word × word)) (ms : List amap)
    (H : ∀ m ∈ ms, hole_ok E y l m) (Hy : y' ≤ y) : ∀ m ∈ ms, hole_ok E y' l m := by
  intro m Hm Hh
  obtain ⟨H1, H2⟩ := H m Hm Hh
  refine ⟨H1, ?_⟩
  rcases H2 with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- A sub-list of intervals keeps every hole free. -/
theorem holes_sublist (E : env) (y : Int) (l l' : List (word × word)) (ms : List amap)
    (H : ∀ m ∈ ms, hole_ok E y l m) (Hs : ∀ iv ∈ l', iv ∈ l) :
    ∀ m ∈ ms, hole_ok E y l' m := by
  intro m Hm Hh
  obtain ⟨H1, H2⟩ := H m Hm Hh
  exact ⟨fun iv Hiv => H1 iv (Hs iv Hiv), H2⟩

/-- A list without holes satisfies every hole obligation. -/
theorem holes_none (E : env) (y : Int) (l : List (word × word)) (ms : List amap)
    (H : ∀ m ∈ ms, is_hole m = false) : ∀ m ∈ ms, hole_ok E y l m := by
  intro m Hm Hh
  rw [H m Hm] at Hh
  exact (by simp at Hh : False).elim

/-- The checker state's denotation. -/
structure cs_ok (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model) :
    Prop where
  /-- registers -/
  co_regs : regs_ok E cs.a_ss.s_regs R
  /-- empty store log -/
  co_log : cs.a_ss.s_log = []
  /-- knowledge about the RESTRICTED memory -/
  co_know : know_ok segs E (Mr A argH E cs model FULL) (kn cs)
  /-- the model has not halted -/
  co_halt : m_halted model = none
  /-- the fd table -/
  co_fds : fds_ok E cs.a_fd model
  /-- the file system never changes -/
  co_fs : m_fs model = FS0
  /-- set_tid_address has not run, or the tid is set -/
  co_tid : cs.a_tidset = false → m_tid model = none
  /-- the reservations are the image's -/
  co_res : (m_vmmaps model).vm_reserved = segments_reserved segs
  /-- the budget is the run's -/
  co_limit : (m_vmmaps model).vm_limit = LIMIT
  /-- the tracked ledger MATCHES the model's -/
  co_maps : maps_match E cs.a_maps (m_vmmaps model).vm_maps
  /-- the HOLE tokens are free -/
  co_holes : ∀ m ∈ cs.a_maps,
      hole_ok E cs.a_ylo ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) m
  /-- the mapped intervals are disjoint -/
  co_seps : seps (m_vmmaps model).vm_maps
  /-- the interval well-formedness of the model -/
  co_wf : model_ivs_wf model
  /-- the mapped intervals are page-aligned, above the hull and below the ceiling -/
  co_bounds : ∀ iv ∈ (m_vmmaps model).vm_maps,
      0 < bv_unsigned iv.2 ∧
      bv_unsigned iv.1 % 4096 = 0 ∧ bv_unsigned iv.2 % 4096 = 0 ∧
      A.img_hi ≤ bv_unsigned iv.1 ∧
      bv_unsigned iv.1 + bv_unsigned iv.2 ≤ CEIL
  /-- the lazy reservations are above the hull and below the ceiling -/
  co_lazyb : ∀ iv ∈ m_vm_lazy model,
      A.img_hi ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ CEIL
  /-- noaccess bytes are mapped bytes -/
  co_nasub : ∀ z, in_ivs z (m_vmmaps model).vm_noaccess = true →
      in_ivs z (m_vmmaps model).vm_maps = true
  /-- `KNONE`/`KNONELAZY` entries are verbatim `vm_noaccess` elements -/
  co_none : ∀ m ∈ cs.a_maps, m.am_kind = .KNONE ∨ m.am_kind = .KNONELAZY →
      amap_den E m ∈ (m_vmmaps model).vm_noaccess
  /-- `KRWLAZY` entries are outside `vm_noaccess` and on lazy pages -/
  co_kinds : ∀ m ∈ cs.a_maps, m.am_kind = .KRWLAZY →
      ∀ a : word,
        bv_unsigned (edenot E m.am_base) ≤ bv_unsigned a ∧
        bv_unsigned a < bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) →
        in_ivs (bv_unsigned a) (m_vmmaps model).vm_noaccess = false ∧
        page_in_ranges (page_base a) (m_vm_lazy model) = true
  /-- the gap lemma's accumulated size -/
  co_totsz : sum_sizes ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) ≤ cs.a_totsz
  /-- the placement split at or above the checker's mark -/
  co_split : ∃ Y, cs.a_ylo ≤ Y ∧ Y % 4096 = 0 ∧
      Y ≤ bv_unsigned (m_vmmaps model).vm_mmap_base ∧
      ledger_split ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) kHighMemBeg Y
  /-- the program break -/
  co_brk : (m_vmmaps model).vm_brk = edenot E cs.a_brk
  /-- the initial break is below the current one -/
  co_sbrk : bv_unsigned (m_vmmaps model).vm_start_brk ≤ bv_unsigned (m_vmmaps model).vm_brk
  /-- the eager byte budget -/
  co_eager : eager_used model ≤ cs.a_eager
  /-- the allowed-set byte budget -/
  co_abytes : A_bytes (allowA A E cs) ≤ cs.a_abytes
  /-- the budget invariant -/
  co_minv : MInv (allowA A E cs) model
  /-- memory outside the knowledge: hidden, mapped, not PROT_NONE, lazy ⇒ 0 -/
  co_zero : ∀ a : word, hid A argH E cs model a = true →
      in_ivs (bv_unsigned a) (m_vmmaps model).vm_maps = true →
      in_ivs (bv_unsigned a) (m_vmmaps model).vm_noaccess = false →
      page_in_ranges (page_base a) (m_vm_lazy model) = true →
      in_ghost E cs (bv_unsigned a) = false →
      FULL a = some (Z_to_bv 8 0)
  /-- the argument-block invariant -/
  co_sinv : SINV E FULL

end Sound

/-! ## 5. Knowledge-entry footprints (`kfoot`, `kfoot_apart`, `pw_kind`) -/

/-- The footprint of a knowledge entry, in `Int` and `estart` form. -/
def kfoot (E : env) : kentry → Option (Int × Int)
  | .KWord a w _ => some (estart E a, (w : Int))
  | .KZero a l => some (estart E a, elenZ E l)
  | .KBlob a l _ => some (estart E a, elenZ E l)
  | .KImg lo hi => some (lo, hi - lo)
  | .KWr a n => some (estart E a, elenZ E n)
  | .KFill a l _ => some (estart E a, elenZ E l)
  | .KUnk a l => some (estart E a, elenZ E l)
  | .KAlign _ _ | .KRange _ _ _ | .KDisj _ _ _ _ => none

/-- The entry's footprint is disjoint from `[lo, lo+n)`. -/
def kfoot_apart (E : env) (K : kentry) (lo n : Int) : Prop :=
  match kfoot E K with
  | none => True
  | some sl => sl.1 + sl.2 ≤ lo ∨ lo + n ≤ sl.1

/-- `pw_kind mk P`: the entries built by `mk` are exactly the `P`-entries. -/
def pw_kind (segs : List Segment) (mk : saddr → expr → kentry)
    (P : (word → Option byte) → word → Prop) : Prop :=
  ∀ E M a n, kentry_ok segs E M (mk a n) ↔
    (flat E a (elenZ E n) ∧ ∀ i, 0 ≤ i ∧ i < elenZ E n → P M (Z_to_bv 64 (estart E a + i)))

/-- `KImg` facts lie inside the image hull (what `kimg_clip` guarantees). -/
def kimg_in_hull (A : atable) (k : List kentry) : Prop :=
  ∀ K ∈ k, match K with
    | .KImg lo hi => A.img_lo ≤ lo ∧ hi ≤ A.img_hi
    | _ => True

/-! ## 6. The per-node soundness obligations (`*_stmt`) -/

/-- The uniform one-child node obligation. -/
def node1_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (pre : acs → Bool) (node : acs → Option acs) : Prop :=
  ∀ cs cs' E R FULL model T,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model → pre cs = true → node cs = some cs' →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc cs') FULL' model') T) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) T

/-- The trivial precondition. -/
def always (_cs : acs) : Bool := true

/-- Syscall nodes. -/
def sys_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (y : snode) : Prop :=
  node1_stmt segs A nx0 LIMIT SINV argH FS0 (is_ecall_at segs) (node_sys A nx0 y)

/-- Extension nodes (routine summaries). -/
def x_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (x : xnode) : Prop :=
  ∀ args, node1_stmt segs A nx0 LIMIT SINV argH FS0 always (node_x segs A nx0 x args)

/-- Fresh-variable node. -/
def fresh_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) : Prop :=
  ∀ r logc base,
    node1_stmt segs A nx0 LIMIT SINV argH FS0 always (fun cs => node_fresh nx0 cs r logc base)

/-- Byte-join node. -/
def join_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) : Prop :=
  ∀ b off n, node1_stmt segs A nx0 LIMIT SINV argH FS0 always (fun cs => node_join segs cs b off n)

/-- Brk grow with both outcomes. -/
def brk2_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) : Prop :=
  ∀ cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model →
    is_ecall_at segs cs = true → node_brk2 A LIMIT cs = some (csa, csb) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csa R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csb R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB)

/-- Exit leaf. -/
def exit_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) : Prop :=
  ∀ cs code E R FULL model,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model →
    is_ecall_at segs cs = true → node_exit cs = some code →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model))

/-- Hooked extension nodes. -/
def ext_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (XN : Nat → List expr → acs → Option acs) : Prop :=
  ∀ id args, node1_stmt segs A nx0 LIMIT SINV argH FS0 always (XN id args)

/-- Hooked two-child nodes. -/
def ext2_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (XB : Nat → List expr → acs → Option (acs × acs)) : Prop :=
  ∀ id args cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model → XB id args cs = some (csa, csb) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csa R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csb R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB)

/-- TWO-child memory-syscall nodes (refused / granted: `node_mmap2`,
    `node_mprotect2`).  The children are listed in the spec's `alt` order;
    every child must be realized by some resolution (exactness), which is why
    the checker keeps the grant guards. -/
def mm2_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (node : acs → Option (acs × acs)) : Prop :=
  ∀ cs csa csb E R FULL model TA TB,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model →
    is_ecall_at segs cs = true → node cs = some (csa, csb) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csa R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csb R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA TB)

/-- THREE-child MAP_FIXED-inside node (`node_mmapin`: refused-kept / ok /
    refused-destroyed). -/
def mm3_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (node : acs → Option (acs × acs × List acs)) : Prop :=
  ∀ cs csa csb cscs E R FULL model TA TB TC,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model →
    is_ecall_at segs cs = true → node cs = some (csa, csb, cscs) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csa R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csa) FULL' model') TA) →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csb R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csb) FULL' model') TB) →
    (∀ csc ∈ cscs, ∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' csc R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc csc) FULL' model') TC) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC))

/-- Hooked emitting nodes: the writes happen first, then the continuation. -/
def emit_stmt (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs)) : Prop :=
  ∀ id args cs fd ps cs' E R FULL model T,
    cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model → XE id args cs = some (fd, ps, cs') →
    T [] →
    (∀ E' R' FULL' model',
        env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' → m_fs model' = m_fs model →
        srealizes segs (cfg_of segs R' (pc cs') FULL' model') T) →
    srealizes segs (cfg_of segs R (pc cs) FULL model) (t_emit (Wp E fd ps) T)

/-- The hand-off certificates. -/
def holes_stmt (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HS : Nat → Option acs) (HOLES : Nat → env → Fs.Fs → TSet) : Prop :=
  ∀ h ch, HS h = some ch →
  ∀ E R FULL model, cs_ok segs A LIMIT SINV argH FS0 E ch R FULL model →
    srealizes segs (cfg_of segs R (pc ch) FULL model) (HOLES h E (m_fs model))

/-! ## 7+. Valuation helpers (`ext1`, `ext_list`, `upd`, `henv`) -/

/-- Extend the valuation at one variable. -/
def ext1 (E : env) (v : Nat) (a : word) : env :=
  ⟨fun n => if n == v then a else E.ev n, E.eb⟩

/-- Extend the valuation with a list of words. -/
def ext_list (E : env) (nx : Nat) (vals : List word) : env :=
  match vals with
  | [] => E
  | v :: rest => ext_list (ext1 E nx v) (nx + 1) rest

/-- The big `KWord` values of a knowledge list. -/
def kn_bigexprs (K : Nat) : List kentry → List expr
  | [] => []
  | .KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
  | _ :: r => kn_bigexprs K r

/-- Overwrite variable `J`. -/
def upd (E : env) (J : Nat) (w : word) : env :=
  ⟨fun n => if n == J then w else E.ev n, E.eb⟩

/-- The valuation giving the havoc registers their actual values. -/
def is_havoc (lo hi : Nat) (t : expr) : Option Nat :=
  match t with
  | .EVar v => if lo ≤ v && v < hi then some v else none
  | _ => none

/-- The valuation after the havoc substitution. -/
def henv (lo hi : Nat) (E : env) (rs ts : List expr) : env :=
  match rs, ts with
  | r :: rs', t :: ts' =>
      let E1 := henv lo hi E rs' ts'
      match is_havoc lo hi t with
      | some v => upd E1 v (edenot E r)
      | none => E1
  | _, _ => E

/-! ## 9+. The loop context -/

/-- The loop-context template: under any valuation agreeing below the bound,
    the loop head realizes `D`. -/
def LCOK (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HOLES : Nat → env → Fs.Fs → TSet)
    (lc : Option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
  match lc with
  | none => True
  | some (.LC h nx lo hi) =>
      (nx0 ≤ lo ∧ lo ≤ hi ∧ nx.a_ss.s_regs.length = 32) ∧
      ∀ E' R' F' m', env_agree lo E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' nx R' F' m' → m_fs m' = fs →
        srealizes segs (cfg_of segs R' h F' m') D
  /- the join frame of `PVia j js lo karms k`: from the join state `js`, under
     any valuation agreeing below the frozen bound `b`, the configuration
     realizes the continuation's shape `sk` -/
  | some (.JC j js sk b lo) =>
      (nx0 ≤ b ∧ b ≤ lo ∧ js.a_ss.s_regs.length = 32) ∧
      ∀ E' R' F' m', env_agree b E E' →
        cs_ok segs A LIMIT SINV argH FS0 E' js R' F' m' → m_fs m' = fs →
        srealizes segs (cfg_of segs R' (pc js) F' m') (sd HOLES D E' fs sk)

/-- The loop guard. -/
def lc_guard (lc : Option loopctx) (cs : acs) : Bool :=
  match lc with
  | some c => lc_bnd c ≤ nxt cs
  | none => true

/-! ## 3. The restricted-memory side conditions hold for every `cs_ok` state -/

/-- `A_wf_allowA`: the allowed set is page-aligned at both ends by
    construction. -/
theorem A_wf_allowA (A : atable) (E : env) (cs : acs) : A_wf (allowA A E cs) := by
  intro iv Hiv
  rw [allowA, List.mem_flatMap] at Hiv
  obtain ⟨p, _, Hp⟩ := Hiv
  have hb : 0 ≤ uE E p.1 := Int.natCast_nonneg _
  have hn : 0 ≤ uE E p.2 := Int.natCast_nonneg _
  have hsl : sh_lo A E p ≤ sh_hi A E p := by
    unfold sh_lo sh_hi
    have := Int.ediv_le_ediv (c := 8) (by decide) (by omega : uE E p.1 ≤ uE E p.1 + uE E p.2)
    omega
  simp only [allow1, List.mem_cons, List.not_mem_nil, or_false, List.mem_singleton] at Hp
  rcases Hp with rfl | rfl
  · refine ⟨by have := pagedown_le (uE E p.1); have := pageup_ge (uE E p.1 + uE E p.2); omega,
      pagedown_mod _, pageup_mod _⟩
  · exact ⟨by have := pagedown_le (sh_lo A E p); have := pageup_ge (sh_hi A E p); omega,
      pagedown_mod _, pageup_mod _⟩

/-- `page_base_le`: the page base of a word is at or below it, the word is
    inside the page, and the base is aligned. -/
theorem page_base_le (a : word) : bv_unsigned (page_base a) ≤ bv_unsigned a ∧
    bv_unsigned a < bv_unsigned (page_base a) + 4096 ∧
    bv_unsigned (page_base a) % 4096 = 0 := by
  have Ha := u64_range a
  have hq : (a.toNat : Int) / 4096 * 4096 = (a.toNat : Int) - (a.toNat : Int) % 4096 :=
    ediv_mul_4096 _
  have hge : 0 ≤ (a.toNat : Int) / 4096 * 4096 := by
    have := Int.emod_nonneg (a.toNat : Int) (by decide : (4096 : Int) ≠ 0); omega
  have hlt : (a.toNat : Int) / 4096 * 4096 < 2 ^ 64 := by omega
  have hu : ((page_base a).toNat : Int) = (a.toNat : Int) / 4096 * 4096 := by
    unfold page_base page_base_of page_size
    exact u64_lit _ ⟨hge, hlt⟩
  have hm := Int.emod_lt_of_pos (a.toNat : Int) (by decide : (0 : Int) < 4096)
  have hnn := Int.emod_nonneg (a.toNat : Int) (by decide : (4096 : Int) ≠ 0)
  simp only [bv_unsigned]
  rw [hu]
  exact ⟨by omega, by omega, Int.mul_emod_left _ 4096⟩

/-- `page_in_ranges_bounds`: a page wholly inside an interval that starts at or
    above an aligned bound `b` cannot hold a byte below `b`; dually for an
    aligned upper bound. -/
theorem page_in_ranges_bounds (a : word) (l : List (word × word)) (lo hi : Int)
    (Hl : ∀ iv ∈ l, lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ hi)
    (Hp : page_in_ranges (page_base a) l = true) :
    lo ≤ bv_unsigned a ∧ bv_unsigned a + 1 ≤ hi + 4095 := by
  rw [page_in_ranges, List.any_eq_true] at Hp
  obtain ⟨iv, Hin, Hb⟩ := Hp
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hb
  obtain ⟨L1, L2⟩ := Hl iv Hin
  obtain ⟨P1, P2, P3⟩ := page_base_le a
  unfold page_size at Hb
  simp only [bv_unsigned] at *
  constructor <;> omega

/-! ## 4. Block running: the lemmas that do not need the executor's carry -/

/-- A sub-list of an allowed set allows every page it allows. -/
theorem page_allowedb_app_r (l1 l2 : List (Int × Int)) (p : word)
    (H : page_allowedb l2 p = true) : page_allowedb (l1 ++ l2) p = true := by
  unfold page_allowedb at *
  rw [List.any_append, H, Bool.or_true]

/-- `A_bytes` is additive over list concatenation. -/
theorem A_bytes_app (l1 l2 : List (Int × Int)) :
    A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2 := by
  induction l1 with
  | nil => simp [A_bytes]
  | cons iv r ih => simp [A_bytes, ih]; omega

/-- The budget invariant is monotone in the allowed set. -/
theorem MInv_app (l1 l2 : List (Int × Int)) (m : Model)
    (H : MInv l2 m) (Hb : eager_used m + A_bytes (l1 ++ l2) ≤ (m_vmmaps m).vm_limit) :
    MInv (l1 ++ l2) m where
  minv_nodup := H.minv_nodup
  minv_aligned := H.minv_aligned
  minv_allowed := fun p Hp => page_allowedb_app_r l1 l2 p (H.minv_allowed p Hp)
  minv_lazy := H.minv_lazy
  minv_budget := Hb

/-- `in_ivs`, semantically. -/
theorem in_ivs_true (z : Int) (l : List (word × word)) :
    in_ivs z l = true ↔
      ∃ iv, iv ∈ l ∧ bv_unsigned iv.1 ≤ z ∧ z < bv_unsigned iv.1 + bv_unsigned iv.2 := by
  unfold in_ivs
  rw [List.any_eq_true]
  constructor
  · rintro ⟨iv, Hin, Hb⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hb
    exact ⟨iv, Hin, Hb.1, Hb.2⟩
  · rintro ⟨iv, Hin, H1, H2⟩
    exact ⟨iv, Hin, by rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨H1, H2⟩⟩

/-- The page-outward rounding of a non-empty interval is at most 8190 bytes wider. -/
theorem pageup_pagedown_gap (a b : Int) (H : a ≤ b) :
    pageup b - pagedown a ≤ b - a + 8190 := by
  unfold pageup pagedown
  have h1 := Int.emod_nonneg (b + 4095) (by decide : (4096 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos (b + 4095) (by decide : (0 : Int) < 4096)
  have h3 := Int.emod_nonneg a (by decide : (4096 : Int) ≠ 0)
  have h4 := Int.emod_lt_of_pos a (by decide : (0 : Int) < 4096)
  have e1 : (b + 4095) / 4096 * 4096 = (b + 4095) - (b + 4095) % 4096 := by
    have h := Int.emod_add_mul_ediv (b + 4095) 4096
    have h' : 4096 * ((b + 4095) / 4096) = (b + 4095) - (b + 4095) % 4096 := by omega
    rw [Int.mul_comm]; omega
  have e2 : a / 4096 * 4096 = a - a % 4096 := ediv_mul_4096 a
  rw [e1, e2]
  omega

/-! ## 4b. The `maps_match` family (fog tokens) -/

/-- With no fog token the ledger matches exactly. -/
theorem maps_match_exact (E : env) (ms : List amap) (l : List (word × word))
    (Hnf : no_fog ms = true) : maps_match E ms l ↔ l = ms.map (amap_den E) := by
  induction ms generalizing l with
  | nil =>
    simp only [maps_match]
    exact ⟨fun h => h, fun h => h⟩
  | cons m ms ih =>
    have Hsplit : is_fog m = false ∧ no_fog ms = true := by
      simpa [no_fog, Bool.and_eq_true] using Hnf
    obtain ⟨Hm, Hr⟩ := Hsplit
    rw [maps_match]
    simp only [Hm, ite_false, List.map_cons]
    constructor
    · rintro ⟨l', rfl, HM⟩
      rw [(ih l' Hr).mp HM]
    · intro h
      exact ⟨_, h, (ih _ Hr).mpr rfl⟩

/-- A tracked (non-token) entry's denotation is a member of the matched ledger. -/
theorem maps_match_In (E : env) (ms : List amap) :
    ∀ (l : List (word × word)) (m : amap), maps_match E ms l → m ∈ ms →
      is_fog m = false → amap_den E m ∈ l := by
  induction ms with
  | nil => intro l m _ Hin; simp at Hin
  | cons m0 ms ih =>
    intro l m HM Hin Hf
    rw [maps_match] at HM
    rcases List.mem_cons.mp Hin with rfl | Hin
    · simp only [Hf, ite_false] at HM
      obtain ⟨l', rfl, _⟩ := HM
      exact List.mem_cons_self ..
    · by_cases h0 : is_fog m0 = true
      · simp only [h0, ite_true] at HM
        rcases HM with HM | ⟨iv, l', rfl, _, HM⟩
        · exact ih l m HM Hin Hf
        · exact List.mem_cons_of_mem _ (ih l' m HM Hin Hf)
      · simp only [h0, ite_false, Bool.not_eq_true] at HM
        obtain ⟨l', rfl, HM⟩ := HM
        exact List.mem_cons_of_mem _ (ih l' m HM Hin Hf)

/-- A byte of a tracked entry's interval is inside the matched ledger. -/
theorem in_ivs_maps_match (E : env) (ms : List amap) (l : List (word × word)) (m : amap)
    (z : Int) (HM : maps_match E ms l) (Hin : m ∈ ms) (Hf : is_fog m = false)
    (Hz : bv_unsigned (edenot E m.am_base) ≤ z ∧
      z < bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)) :
    in_ivs z l = true := by
  rw [in_ivs_true]
  exact ⟨amap_den E m, maps_match_In E ms l m HM Hin Hf, Hz⟩

/-- Pushing a non-token entry on the ledger. -/
theorem maps_match_cons (E : env) (ms : List amap) (l : List (word × word))
    (b n : expr) (k : mkind) (Hk : is_tok_kind k = false)
    (HM : maps_match E ms l) :
    maps_match E (⟨b, n, k⟩ :: ms) ((edenot E b, edenot E n) :: l) := by
  simp only [maps_match]
  have : is_fog ⟨b, n, k⟩ = false := by simp [is_fog, Hk]
  simp only [this, ite_false]
  exact ⟨l, rfl, HM⟩

/-- The matched ledger is no longer than the tracked one. -/
theorem maps_match_length (E : env) (ms : List amap) :
    ∀ l, maps_match E ms l → l.length ≤ ms.length := by
  induction ms with
  | nil =>
    intro l HM
    rw [maps_match] at HM
    subst HM
    simp
  | cons m ms ih =>
    intro l HM
    rw [maps_match] at HM
    by_cases h0 : is_fog m = true
    · simp only [h0, ite_true] at HM
      rcases HM with HM | ⟨iv, l', rfl, _, HM⟩
      · have := ih l HM; simp only [List.length_cons]; omega
      · have := ih l' HM; simp only [List.length_cons]; omega
    · simp only [h0, ite_false, Bool.not_eq_true] at HM
      obtain ⟨l', rfl, HM⟩ := HM
      have := ih l' HM
      simp only [List.length_cons]
      omega

/-- Every actual entry is a tracked element's denotation or a fogged entry. -/
theorem maps_match_elem (E : env) (ms : List amap) :
    ∀ (l : List (word × word)) (iv : word × word), maps_match E ms l → iv ∈ l →
      ∃ m, m ∈ ms ∧ ((is_fog m = false ∧ iv = amap_den E m) ∨
        (is_fog m = true ∧ bv_unsigned iv.2 ≤ uE E m.am_len)) := by
  induction ms with
  | nil =>
    intro l iv HM Hin
    rw [maps_match] at HM
    subst HM
    simp at Hin
  | cons m ms ih =>
    intro l iv HM Hin
    rw [maps_match] at HM
    by_cases h0 : is_fog m = true
    · simp only [h0, ite_true] at HM
      rcases HM with HM | ⟨iv0, l', rfl, Hsz, HM⟩
      · obtain ⟨m', Hm', H'⟩ := ih l iv HM Hin
        exact ⟨m', List.mem_cons_of_mem _ Hm', H'⟩
      · rcases List.mem_cons.mp Hin with rfl | Hin
        · exact ⟨m, List.mem_cons_self .., Or.inr ⟨h0, Hsz⟩⟩
        · obtain ⟨m', Hm', H'⟩ := ih l' iv HM Hin
          exact ⟨m', List.mem_cons_of_mem _ Hm', H'⟩
    · simp only [h0, ite_false, Bool.not_eq_true] at HM
      obtain ⟨l', rfl, HM⟩ := HM
      rcases List.mem_cons.mp Hin with rfl | Hin
      · exact ⟨m, List.mem_cons_self .., Or.inl ⟨by simp [h0], rfl⟩⟩
      · obtain ⟨m', Hm', H'⟩ := ih l' iv HM Hin
        exact ⟨m', List.mem_cons_of_mem _ Hm', H'⟩

/-- Kinds may be re-spelled freely among the non-token kinds. -/
theorem maps_match_rekind (E : env) (ms : List amap) (l : List (word × word)) (f : amap → amap)
    (Hf : ∀ m, (f m).am_base = m.am_base ∧ (f m).am_len = m.am_len ∧
      is_fog (f m) = is_fog m)
    (HM : maps_match E ms l) : maps_match E (ms.map f) l := by
  induction ms generalizing l with
  | nil =>
    simpa only [maps_match, List.map_nil] using HM
  | cons m ms ih =>
    obtain ⟨Hb, Hn, Hk⟩ := Hf m
    simp only [List.map_cons]
    rw [maps_match] at HM ⊢
    rw [Hk]
    have hden : amap_den E (f m) = amap_den E m := by
      simp only [amap_den, Hb, Hn]
    by_cases h0 : is_fog m = true
    · simp only [h0, ite_true] at HM ⊢
      rcases HM with HM | ⟨iv, l', rfl, Hsz, HM⟩
      · exact Or.inl (ih l HM)
      · have hlen : uE E (f m).am_len = uE E m.am_len := by rw [Hn]
        rw [hlen]
        exact Or.inr ⟨iv, l', rfl, Hsz, ih l' HM⟩
    · simp only [h0, ite_false, Bool.not_eq_true] at HM ⊢
      obtain ⟨l', rfl, HM⟩ := HM
      exact ⟨l', by rw [hden], ih l' HM⟩

/-- A tracked entry's interval is inside the mapped ledger. -/
theorem in_ivs_map_den (E : env) (ms : List amap) (m : amap) (z : Int) (Hin : m ∈ ms)
    (Hz : bv_unsigned (edenot E m.am_base) ≤ z ∧
      z < bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)) :
    in_ivs z (ms.map (amap_den E)) = true := by
  rw [in_ivs_true]
  exact ⟨amap_den E m, List.mem_map_of_mem Hin, Hz⟩

/-! ### Boolean-equality reflexivity and list helpers -/

/-- A predicate true on every member filters nothing. -/
theorem filter_all_true {T : Type} (f : T → Bool) (l : List T)
    (H : ∀ x, x ∈ l → f x = true) : l.filter f = l := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [List.filter_cons, H x (List.mem_cons_self ..)]
    rw [ih (fun y Hy => H y (List.mem_cons_of_mem _ Hy))]
    rfl

/-- `aluop_eqb` is reflexive. -/
theorem aluop_eqb_refl' (o : AluOp) : aluop_eqb o o = true := by cases o <;> rfl

/-- `mulop_eqb` is reflexive. -/
theorem mulop_eqb_refl' (o : MulOp) : mulop_eqb o o = true := by cases o <;> rfl

/-- `expr_eqb` is reflexive. -/
theorem expr_eqb_refl' : ∀ e : expr, expr_eqb e e = true
  | .ELit a => by simp [expr_eqb]
  | .EVar a => by simp [expr_eqb]
  | .EAlu o a b => by simp [expr_eqb, aluop_eqb_refl', expr_eqb_refl' a, expr_eqb_refl' b]
  | .EAluw o a b => by simp [expr_eqb, aluop_eqb_refl', expr_eqb_refl' a, expr_eqb_refl' b]
  | .EMd o a b => by simp [expr_eqb, mulop_eqb_refl', expr_eqb_refl' a, expr_eqb_refl' b]
  | .EMdw o a b => by simp [expr_eqb, mulop_eqb_refl', expr_eqb_refl' a, expr_eqb_refl' b]
  | .EExt s l n a => by simp [expr_eqb, expr_eqb_refl' a]
  | .EBlob s k i n => by simp [expr_eqb]

/-- `amap_eqb` is reflexive. -/
theorem amap_eqb_refl' (m : amap) : amap_eqb m m = true := by
  obtain ⟨b, l, k⟩ := m
  simp only [amap_eqb, expr_eqb_refl', mkind_eqb]
  cases k <;> rfl

/-- A predicate false on every member scans to `false`. -/
theorem existsb_false_forall {T : Type} (f : T → Bool) (l : List T)
    (H : ∀ x, x ∈ l → f x = false) : l.any f = false := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [List.any_cons, H x (List.mem_cons_self ..), Bool.false_or]
    exact ih (fun y Hy => H y (List.mem_cons_of_mem _ Hy))

/-! ## 7b. The valuation-agreement family -/

/-- Agreement below a smaller bound. -/
theorem env_agree_le (b b' : Nat) (E E' : env) (H : env_agree b' E E') (Hle : b ≤ b') :
    env_agree b E E' :=
  ⟨fun n hn => H.1 n (by omega), H.2⟩

/-- Agreement is reflexive. -/
theorem env_agree_refl (b : Nat) (E : env) : env_agree b E E :=
  ⟨fun _ _ => rfl, rfl⟩

/-- Agreement is transitive. -/
theorem env_agree_trans (b : Nat) (E1 E2 E3 : env) (H1 : env_agree b E1 E2)
    (H2 : env_agree b E2 E3) : env_agree b E1 E3 :=
  ⟨fun n hn => (H1.1 n hn).trans (H2.1 n hn), H1.2.trans H2.2⟩

/-- Extending a valuation at `v` keeps agreement below `v`. -/
theorem ext1_agree (E : env) (v : Nat) (a : word) : env_agree v E (ext1 E v a) := by
  refine ⟨?_, rfl⟩
  intro n hn
  have hne : n ≠ v := by omega
  simp only [ext1]
  simp [hne]

/-- The extended valuation reads `a` at `v`. -/
theorem ext1_at (E : env) (v : Nat) (a : word) : (ext1 E v a).ev v = a := by
  simp only [ext1]
  simp

/-- Overwriting `J` keeps agreement below `J`. -/
theorem upd_agree (E : env) (J : Nat) (w : word) : env_agree J E (upd E J w) := by
  refine ⟨?_, rfl⟩
  intro n hn
  have hne : n ≠ J := by omega
  simp only [upd]
  simp [hne]

/-- The overwritten valuation reads `w` at `J`. -/
theorem upd_at (E : env) (J : Nat) (w : word) : (upd E J w).ev J = w := by
  simp only [upd]
  simp

/-- Overwriting with the current value changes nothing. -/
theorem upd_same (E : env) (J : Nat) : upd E J (E.ev J) = E := by
  obtain ⟨ev, eb⟩ := E
  simp only [upd]
  congr 1
  funext n
  by_cases h : n = J <;> simp [h]

/-- Two overwrites at the same variable: the last wins. -/
theorem upd_upd (E : env) (J : Nat) (w w' : word) :
    upd (upd E J w) J w' = upd E J w' := by
  obtain ⟨ev, eb⟩ := E
  simp only [upd]
  congr 1
  funext n
  by_cases h : n = J <;> simp [h]

/-- `is_havoc` only names variables of the havoc range. -/
theorem is_havoc_range (lo hi : Nat) (t : expr) (v : Nat)
    (H : is_havoc lo hi t = some v) : t = .EVar v ∧ lo ≤ v ∧ v < hi := by
  cases t with
  | EVar n =>
    simp only [is_havoc] at H
    split at H
    · rename_i hc
      injection H with hv
      subst hv
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
      exact ⟨rfl, hc.1, hc.2⟩
    · exact absurd H (by simp)
  | _ => exact absurd H (by simp [is_havoc])

/-- A literal in range reads back as itself. -/
theorem u_small (z : Int) (H : 0 ≤ z ∧ z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z :=
  u64_lit z H

/-- Extending a valuation with a list keeps agreement below the counter. -/
theorem ext_list_agree (E : env) (nx : Nat) (vals : List word) :
    env_agree nx E (ext_list E nx vals) := by
  induction vals generalizing E nx with
  | nil => exact env_agree_refl nx E
  | cons v rest ih =>
    simp only [ext_list]
    exact env_agree_trans nx E (ext1 E nx v) _
      (ext1_agree E nx v)
      (env_agree_le nx (nx + 1) _ _ (ih (ext1 E nx v) (nx + 1)) (by omega))

/-- The extended valuation reads the list back. -/
theorem ext_list_at (E : env) (nx : Nat) : ∀ (vals : List word) (i : Nat),
    i < vals.length → (ext_list E nx vals).ev (nx + i) = vals.getD i (Z_to_bv 64 0) := by
  intro vals
  induction vals generalizing E nx with
  | nil => intro i hi; simp at hi
  | cons v rest ih =>
    intro i hi
    simp only [ext_list]
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.getD_cons_zero]
      exact ((ext_list_agree (ext1 E nx v) (nx + 1) rest).1 nx
        (Nat.lt_succ_self nx)).symm.trans (ext1_at E nx v)
    | succ i =>
      simp only [List.getD_cons_succ]
      have h1 : nx + (i + 1) = nx + 1 + i := by omega
      rw [h1]
      exact ih (ext1 E nx v) (nx + 1) i (by simpa using hi)

/-- `henv` keeps agreement below the havoc range. -/
theorem henv_agree (lo hi : Nat) (E : env) : ∀ (rs ts : List expr),
    env_agree lo E (henv lo hi E rs ts)
  | [], _ => env_agree_refl lo E
  | _ :: _, [] => env_agree_refl lo E
  | r :: rs', t :: ts' => by
    simp only [henv]
    have ih := henv_agree lo hi E rs' ts'
    split
    · next v hv =>
      have hle : lo ≤ v := (is_havoc_range lo hi t v hv).2.1
      exact env_agree_trans lo E _ _
        ih (env_agree_le lo v _ _ (upd_agree _ v _) hle)
    · exact ih

/-- `henv` never touches variables at or above the havoc range. -/
theorem henv_high (lo hi : Nat) (E : env) : ∀ (rs ts : List expr) (n : Nat),
    hi ≤ n → (henv lo hi E rs ts).ev n = E.ev n
  | [], _, _ => fun _ => rfl
  | _ :: _, [], _ => fun _ => rfl
  | r :: rs', t :: ts', n => fun hn => by
    simp only [henv]
    split
    · next v hv =>
      have hlt : v < hi := (is_havoc_range lo hi t v hv).2.2
      have hne : n ≠ v := by omega
      have hstep : (upd (henv lo hi E rs' ts') v (edenot E r)).ev n
          = (henv lo hi E rs' ts').ev n := by
        simp only [upd]
        simp [hne]
      rw [hstep]
      exact henv_high lo hi E rs' ts' n hn
    · exact henv_high lo hi E rs' ts' n hn

/-! ## Sanity checks ( states no decidable goal in this file) -/

theorem pagedown_check : pagedown 4097 = 4096 := by decide
theorem pagedown_check0 : pagedown 4096 = 4096 := by decide
theorem pageup_check : pageup 4097 = 8192 := by decide
theorem pageup_check0 : pageup 4096 = 4096 := by decide
theorem pageup_check2 : pageup 10000 = 12288 := by decide

/-- The address table of the sanity checks: hull `[10, 20)`. -/
private def chkA : atable where
  img_lo := 10
  img_hi := 20
  n_res := 3
  shadow_off := 0
  a_entry := 0
  rw_lo := 0
  rw_len := 0
  ph_addr_z := 0
  ph_ent_z := 0
  ph_num_z := 0
  x_imemset := 0
  x_imemcpy := 0
  x_memset := 0
  x_memcpy := 0
  x_memiszero := 0
  x_istrncpy := 0
  x_sealed := 0
  x_popfree := 0
  x_sniff := 0
  sniff_tab := 0
  sniff_cell := 0
  x_envscan := 0
  x_envscan_k := 0
  x_pnscan := 0
  x_pnscan_k := 0
  stops_more := []

theorem in_hull_check : in_hull chkA 15 = true := by decide
theorem in_hull_check2 : in_hull chkA 20 = false := by decide
theorem in_ivs_check : in_ivs 5 [(BitVec.ofInt 64 0, BitVec.ofInt 64 8)] = true := by decide
theorem in_ivs_check2 : in_ivs 9 [(BitVec.ofInt 64 0, BitVec.ofInt 64 8)] = false := by decide
theorem CH_check : CH = 65536 := by decide
theorem flen_check : flen [0, 1, 2] = 3 := by decide
theorem chunk_check : chunk 0 [0, 1, 2] = [0, 1, 2] := by decide
theorem chunk_check2 : chunk 1 [0, 1, 2] = [] := by decide
theorem maps_match_nil_check : maps_match ⟨fun _ => 0, fun _ => []⟩ [] [] := rfl
theorem sum_sizes_check : sum_sizes [] = 0 := rfl
theorem sd_nil_check (HOLES : Nat → env → Fs.Fs → TSet) (D : TSet) (E : env) (fs : Fs.Fs) :
    sd HOLES D E fs .SNil = t_nil := rfl
theorem lc_guard_none_check (cs : acs) : lc_guard none cs = true := rfl

/-! ## 10. -/

/-! ### Trace-set algebra -/

/-- `t_exit` contains the empty trace. -/
theorem t_exit_has_nil (code : word) (fs : Fs.Fs) : t_exit code fs [] :=
  t_emit_has_nil _ _

/-- Shape equality is reflexive. -/
theorem t_eq_refl' (T : TSet) : t_eq T T := fun _ => Iff.rfl

/-- `t_alt2 t_nil T` is `T` when `T` is nonempty. -/
theorem t_alt2_nil_l (T : TSet) (HT : T []) : t_eq (t_alt2 t_nil T) T := by
  intro tr
  show (tr = [] ∨ T tr) ↔ T tr
  constructor
  · rintro (h | H)
    · rw [h]; exact HT
    · exact H
  · intro H; exact Or.inr H

/-- `t_alt2 T t_nil` is `T` when `T` is nonempty. -/
theorem t_alt2_nil_r (T : TSet) (HT : T []) : t_eq (t_alt2 T t_nil) T := by
  intro tr
  show (T tr ∨ tr = []) ↔ T tr
  constructor
  · rintro (H | h)
    · exact H
    · rw [h]; exact HT
  · intro H; exact Or.inl H

/-- `t_alt2` is a congruence. -/
theorem t_eq_alt2 (TA TA' TB TB' : TSet) (HA : t_eq TA TA') (HB : t_eq TB TB') :
    t_eq (t_alt2 TA TB) (t_alt2 TA' TB') := by
  intro tr
  show (TA tr ∨ TB tr) ↔ (TA' tr ∨ TB' tr)
  constructor
  · rintro (h | h)
    · exact Or.inl ((HA tr).mp h)
    · exact Or.inr ((HB tr).mp h)
  · rintro (h | h)
    · exact Or.inl ((HA tr).mpr h)
    · exact Or.inr ((HB tr).mpr h)

/-- `existsb` over a `map`. -/
theorem existsb_map' {X Y : Type} (f : Y → Bool) (g : X → Y) (l : List X) :
    (l.map g).any f = l.any (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x r ih => simp only [List.map_cons, List.any_cons, ih]

/-- The `SAlt2` case of `shape_vars_lt`, in the shape the proofs want. -/
theorem shape_vars_lt_alt2 (b : Nat) (x y : shape) :
    shape_vars_lt b (.SAlt2 x y) = (shape_vars_lt b x && shape_vars_lt b y) := rfl

/-- `salt2` mentions only variables below `b` when both arguments do. -/
theorem salt2_vars (b : Nat) (x y : shape) (Hx : shape_vars_lt b x = true)
    (Hy : shape_vars_lt b y = true) : shape_vars_lt b (salt2 x y) = true := by
  cases x <;> cases y <;>
    first
      | exact Hx
      | exact Hy
      | (simp only [salt2]; rw [shape_vars_lt_alt2, Hx, Hy]; rfl)

/-! ### Boolean-equality reflections -/

theorem mkind_eqb_eq {a b : mkind} (H : mkind_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [mkind_eqb]

/-- `listZ_eqb` reflects equality. -/
theorem listZ_eqb_eq : ∀ x y : List Int, listZ_eqb x y = true → x = y
  | [], [] => by intro _; rfl
  | a :: x, b :: y => by
      intro H
      simp only [listZ_eqb, Bool.and_eq_true, beq_iff_eq] at H
      rw [H.1, listZ_eqb_eq x y H.2]
  | [], _ :: _ => by intro H; simp [listZ_eqb] at H
  | _ :: _, [] => by intro H; simp [listZ_eqb] at H

/-- `spiece_eqb` reflects equality. -/
theorem spiece_eqb_eq : ∀ x y : spiece, spiece_eqb x y = true → x = y
  | .SPLit a, .SPLit b => by
      intro H; simp only [spiece_eqb] at H; rw [listZ_eqb_eq a b H]
  | .SPBlob k, .SPBlob k' => by
      intro H; simp only [spiece_eqb, beq_iff_eq] at H; rw [H]
  | .SPLit _, .SPBlob _ => by intro H; simp [spiece_eqb] at H
  | .SPBlob _, .SPLit _ => by intro H; simp [spiece_eqb] at H

/-- `spieces_eqb` reflects equality. -/
theorem spieces_eqb_eq : ∀ x y : List spiece, spieces_eqb x y = true → x = y
  | [], [] => by intro _; rfl
  | a :: x, b :: y => by
      intro H
      simp only [spieces_eqb, Bool.and_eq_true] at H
      rw [spiece_eqb_eq a b H.1, spieces_eqb_eq x y H.2]
  | [], _ :: _ => by intro H; simp [spieces_eqb] at H
  | _ :: _, [] => by intro H; simp [spieces_eqb] at H

/-- `amap_eqb` reflects equality. -/
theorem amap_eqb_eq {x y : amap} (H : amap_eqb x y = true) : x = y := by
  obtain ⟨b, l, k⟩ := x
  obtain ⟨b', l', k'⟩ := y
  simp only [amap_eqb, Bool.and_eq_true] at H
  obtain ⟨⟨hb, hl⟩, hk⟩ := H
  rw [expr_eqb_eq _ _ hb, expr_eqb_eq _ _ hl, mkind_eqb_eq hk]

/-- `pair_eqb` reflects equality. -/
theorem pair_eqb_eq {x y : expr × expr} (H : pair_eqb x y = true) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [pair_eqb, Bool.and_eq_true] at H
  rw [expr_eqb_eq _ _ H.1, expr_eqb_eq _ _ H.2]

/-- `afd_eqb` reflects equality. -/
theorem afd_eqb_eq : ∀ x y : afd, afd_eqb x y = true → x = y := by
  intro x
  cases x with
  | FdStd => intro y H; cases y <;> simp_all [afd_eqb]
  | FdDir => intro y H; cases y <;> simp_all [afd_eqb]
  | FdFile k l o =>
      intro y H
      cases y with
      | FdFile k' l' o' =>
          simp only [afd_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨hk, hl⟩, ho⟩ := H
          rw [hk, expr_eqb_eq _ _ hl, expr_eqb_eq _ _ ho]
      | _ => simp_all [afd_eqb]

/-- `list_eqb` reflects equality. -/
theorem list_eqb_eq {T : Type} (eqb : T → T → Bool)
    (Heq : ∀ x y, eqb x y = true → x = y) :
    ∀ x y : List T, list_eqb eqb x y = true → x = y
  | [], [] => by intro _; rfl
  | a :: x, b :: y => by
      intro H
      simp only [list_eqb, Bool.and_eq_true] at H
      rw [Heq _ _ H.1, list_eqb_eq eqb Heq x y H.2]
  | [], _ :: _ => by intro H; simp [list_eqb] at H
  | _ :: _, [] => by intro H; simp [list_eqb] at H

/-- `shape_eqb` reflects equality. -/
theorem shape_eqb_eq : ∀ x y : shape, shape_eqb x y = true → x = y := by
  intro x
  induction x with
  | SNil => intro y H; cases y <;> simp_all [shape_eqb]
  | SExit c => intro y H; cases y <;> simp_all [shape_eqb, beq_iff_eq]
  | SEmitP fd ps s ih =>
      intro y H
      cases y with
      | SEmitP fd' ps' s' =>
          simp only [shape_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨h1, h2⟩, h3⟩ := H
          rw [h1, spieces_eqb_eq ps ps' h2, ih s' h3]
      | _ => simp_all [shape_eqb]
  | SAlt2 a b iha ihb =>
      intro y H
      cases y with
      | SAlt2 a' b' =>
          simp only [shape_eqb, Bool.and_eq_true] at H
          rw [iha a' H.1, ihb b' H.2]
      | _ => simp_all [shape_eqb]
  | SCase e m a b iha ihb =>
      intro y H
      cases y with
      | SCase e' m' a' b' =>
          simp only [shape_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
          rw [expr_eqb_eq _ _ h1, h2, iha a' h3, ihb b' h4]
      | _ => simp_all [shape_eqb]
  | SHole h => intro y H; cases y <;> simp_all [shape_eqb, beq_iff_eq]
  | SNext => intro y H; cases y <;> simp_all [shape_eqb]

/-- `kentry_eqb` reflects equality. -/
theorem kentry_eqb_eq : ∀ x y : kentry, kentry_eqb x y = true → x = y := by
  intro x
  cases x with
  | KWord a w v =>
      intro y H
      cases y with
      | KWord a' w' v' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨ha, hw⟩, hv⟩ := H
          rw [saddr_eqb_eq ha, hw, expr_eqb_eq _ _ hv]
      | _ => simp_all [kentry_eqb]
  | KZero a n =>
      intro y H
      cases y with
      | KZero a' n' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨ha, hn⟩ := H
          rw [saddr_eqb_eq ha, expr_eqb_eq _ _ hn]
      | _ => simp_all [kentry_eqb]
  | KBlob a n k =>
      intro y H
      cases y with
      | KBlob a' n' k' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨ha, hn⟩, hk⟩ := H
          rw [saddr_eqb_eq ha, expr_eqb_eq _ _ hn, hk]
      | _ => simp_all [kentry_eqb]
  | KImg lo hi =>
      intro y H
      cases y with
      | KImg lo' hi' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          rw [H.1, H.2]
      | _ => simp_all [kentry_eqb]
  | KAlign e m =>
      intro y H
      cases y with
      | KAlign e' m' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          rw [expr_eqb_eq _ _ H.1, H.2]
      | _ => simp_all [kentry_eqb]
  | KRange e lo hi =>
      intro y H
      cases y with
      | KRange e' lo' hi' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨he, h1⟩, h2⟩ := H
          rw [expr_eqb_eq _ _ he, h1, h2]
      | _ => simp_all [kentry_eqb]
  | KWr a n =>
      intro y H
      cases y with
      | KWr a' n' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨ha, hn⟩ := H
          rw [saddr_eqb_eq ha, expr_eqb_eq _ _ hn]
      | _ => simp_all [kentry_eqb]
  | KDisj a1 n1 a2 n2 =>
      intro y H
      cases y with
      | KDisj a1' n1' a2' n2' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
          rw [saddr_eqb_eq h1, expr_eqb_eq _ _ h2, saddr_eqb_eq h3, expr_eqb_eq _ _ h4]
      | _ => simp_all [kentry_eqb]
  | KFill a n c =>
      intro y H
      cases y with
      | KFill a' n' c' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨⟨ha, hn⟩, hc⟩ := H
          rw [saddr_eqb_eq ha, expr_eqb_eq _ _ hn, hc]
      | _ => simp_all [kentry_eqb]
  | KUnk a n =>
      intro y H
      cases y with
      | KUnk a' n' =>
          simp only [kentry_eqb, Bool.and_eq_true, beq_iff_eq] at H
          obtain ⟨ha, hn⟩ := H
          rw [saddr_eqb_eq ha, expr_eqb_eq _ _ hn]
      | _ => simp_all [kentry_eqb]

/-! ### `AP`'s variable-bound tests agree with `AxSymRun3`'s -/
theorem expr_vars_lt_eq (b : Nat) (e : expr) :
    AsanPlanCore.expr_vars_lt b e = AxSymRun3.expr_vars_lt b e := by
  induction e with
  | ELit z => rfl
  | EVar n => rfl
  | EAlu op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, AxSymRun3.expr_vars_lt, ihx, ihy]
  | EAluw op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, AxSymRun3.expr_vars_lt, ihx, ihy]
  | EMd op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, AxSymRun3.expr_vars_lt, ihx, ihy]
  | EMdw op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, AxSymRun3.expr_vars_lt, ihx, ihy]
  | EExt sx lo n x ih =>
      simp only [AsanPlanCore.expr_vars_lt, AxSymRun3.expr_vars_lt, ih]
  | EBlob sx k i n => rfl
theorem kentry_vars_lt_eq (b : Nat) (K : kentry) :
    AsanPlanCore.kentry_vars_lt b K = AxSymRun3.kentry_vars_lt b K := by
  cases K with
  | KWord a w v =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KZero a n =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KBlob a n k =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KImg lo hi => rfl
  | KAlign e m =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt, expr_vars_lt_eq]
  | KRange e lo hi =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt, expr_vars_lt_eq]
  | KWr a n =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KDisj a1 n1 a2 n2 =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KFill a n c =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
  | KUnk a n =>
      simp only [AsanPlanCore.kentry_vars_lt, AxSymRun3.kentry_vars_lt,
        AsanPlanCore.saddr_vars_lt, AxSymRun3.saddr_vars_lt, expr_vars_lt_eq]
theorem kn_vars_lt_eq (b : Nat) (k : List kentry) :
    AsanPlanCore.kn_vars_lt b k = AxSymRun3.kn_vars_lt b k := by
  induction k with
  | nil => rfl
  | cons K r ih =>
      simp only [AsanPlanCore.kn_vars_lt, AxSymRun3.kn_vars_lt,
        kentry_vars_lt_eq, ih]
theorem sr_vars_lt_eq (b : Nat) (sr : List expr) :
    AsanPlanCore.sr_vars_lt b sr = AxSymRun3.sr_vars_lt b sr := by
  induction sr with
  | nil => rfl
  | cons e r ih =>
      simp only [AsanPlanCore.sr_vars_lt, AxSymRun3.sr_vars_lt, expr_vars_lt_eq, ih]

/-! ### The partial instruction table is sound -/
theorem mk_itab_ranges_acc_sound (segs : List Segment) (rs : List (Int × Nat)) (t : itab)
    (Ht : itab_sound segs t) : itab_sound segs (mk_itab_ranges_acc segs rs t) := by
  induction rs generalizing t with
  | nil => exact Ht
  | cons p rs ih =>
      obtain ⟨lo, n⟩ := p
      exact ih _ (mk_itab_fuel_sound segs n lo t Ht)
theorem mk_itab_ranges_sound (segs : List Segment) (rs : List (Int × Nat)) :
    itab_sound segs (mk_itab_ranges segs rs) := by
  refine mk_itab_ranges_acc_sound segs rs .PTLeaf ?_
  intro pc i H
  by_cases h : 0 < pc <;> simp [itab_lookup, pt_get_leaf, h] at H


/-! ### `cs_ok` is monotone in the knowledge -/
theorem pc_set_kn (cs : acs) (k : List kentry) : pc (set_kn cs k) = pc cs := rfl
theorem pc_cs_gc (gb : Nat) (cs : acs) : pc (cs_gc gb cs) = pc cs := rfl
theorem know_ok_filter (segs : List Segment) (E : env) (M : word → Option byte)
    (f : kentry → Bool) (k : List kentry) (HK : know_ok segs E M k) :
    know_ok segs E M (List.filter f k) := by
  intro K hK
  exact HK K (List.mem_filter.mp hK).1
theorem cs_ok_set_kn (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (k' : List kentry) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (HK : know_ok segs E (Mr A argH E cs model FULL) k') :
    cs_ok segs A LIMIT SINV argH FS0 E (set_kn cs k') R FULL model :=
  ⟨HC.co_regs, rfl, HK, HC.co_halt, HC.co_fds, HC.co_fs, HC.co_tid, HC.co_res,
   HC.co_limit, HC.co_maps, HC.co_holes, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb,
   HC.co_nasub, HC.co_none, HC.co_kinds, HC.co_totsz, HC.co_split, HC.co_brk, HC.co_sbrk,
   HC.co_eager, HC.co_abytes, HC.co_minv, HC.co_zero, HC.co_sinv⟩
theorem cs_gc_ok (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (gb : Nat) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 E (cs_gc gb cs) R FULL model := by
  refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
  exact know_ok_filter segs E (Mr A argH E cs model FULL) _ (kn cs) HC.co_know
theorem drop_ixs_incl (ixs : List Nat) (i : Nat) (k : List kentry) (K : kentry)
    (Hin : K ∈ drop_ixs ixs i k) : K ∈ k := by
  induction k generalizing i with
  | nil => exact Hin
  | cons K' r ih =>
      have he : drop_ixs ixs i (K' :: r)
          = if (ixs.any (fun x => i == x)) then drop_ixs ixs (i + 1) r
            else K' :: drop_ixs ixs (i + 1) r := rfl
      rw [he] at Hin
      split at Hin
      · exact List.mem_cons_of_mem _ (ih (i + 1) Hin)
      · rcases List.mem_cons.mp Hin with rfl | Hin
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih (i + 1) Hin)
theorem forget_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (ixs : List Nat) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 E (set_kn cs (drop_ixs ixs 0 (kn cs))) R FULL model :=
  cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _
    HC (fun K hK => HC.co_know K (drop_ixs_incl ixs 0 (kn cs) K hK))
theorem regs_ok_ext_eq (E : env) (sr sr' : List expr) (R : BvMap word)
    (h : sr = sr') (H : regs_ok E sr R) : regs_ok E sr' R := h ▸ H

/-! ### The valuation-agreement transport family -/
theorem edenot_agree' (b : Nat) (E E' : env) (e : expr) (Hag : env_agree b E E')
    (Hv : AsanPlanCore.expr_vars_lt b e = true) : edenot E e = edenot E' e :=
  edenot_agree b E E' Hag e (by simpa only [expr_vars_lt_eq] using Hv)
theorem know_ok_agree' (segs : List Segment) (b : Nat) (E E' : env)
    (M : word → Option byte) (k : List kentry) (Hag : env_agree b E E')
    (Hv : AsanPlanCore.kn_vars_lt b k = true) (HK : know_ok segs E M k) :
    know_ok segs E' M k :=
  know_ok_agree segs b E E' M Hag k (by simpa only [kn_vars_lt_eq] using Hv) HK
theorem regs_ok_agree' (b : Nat) (E E' : env) (sr : List expr) (R : BvMap word)
    (Hag : env_agree b E E') (Hv : AsanPlanCore.sr_vars_lt b sr = true)
    (HR : regs_ok E sr R) : regs_ok E' sr R :=
  regs_ok_agree b E E' sr R Hag (by simpa only [sr_vars_lt_eq] using Hv) HR

/-- A piece's byte list does not depend on the valuation's words. -/
theorem piece_den_agree (E E' : env) (Heb : E.eb = E'.eb) (p : spiece) :
    piece_den E p = piece_den E' p := by
  cases p with
  | SPLit bs => rfl
  | SPBlob k => simp only [piece_den, Heb]

/-- The emitted writes do not depend on the valuation's words. -/
theorem Wp_agree (E E' : env) (Heb : E.eb = E'.eb) (fd : Int) :
    ∀ ps : List spiece, Wp E fd ps = Wp E' fd ps
  | [] => rfl
  | p :: r => by
      have ih := Wp_agree E E' Heb fd r
      simp only [Wp, List.flatMap_cons, List.map_append, piece_den_agree E E' Heb p] at ih ⊢
      rw [ih]
theorem sd_agree (nx0 : Nat) (HOLES : Nat → env → Fs.Fs → TSet) (D : TSet) (E E' : env)
    (fs : Fs.Fs)
    (HOLES_agree : ∀ (h : Nat) (E E' : env) (fs : Fs.Fs),
      env_agree nx0 E E' → HOLES h E fs = HOLES h E' fs)
    (Hag : env_agree nx0 E E') :
    ∀ s : shape, shape_vars_lt nx0 s = true → sd HOLES D E fs s = sd HOLES D E' fs s := by
  intro s
  induction s with
  | SNil => intro _; rfl
  | SExit c => intro _; rfl
  | SEmitP fd ps s ih =>
      intro H
      have hw : Wp E fd ps = Wp E' fd ps := Wp_agree E E' Hag.2 fd ps
      simp only [sd]
      rw [hw, ih H]
  | SAlt2 a b iha ihb =>
      intro H
      simp only [shape_vars_lt, Bool.and_eq_true] at H
      simp only [sd]
      rw [iha H.1, ihb H.2]
  | SCase e mid s1 s2 ih1 ih2 =>
      intro H
      simp only [shape_vars_lt, Bool.and_eq_true] at H
      obtain ⟨⟨he, h1⟩, h2⟩ := H
      simp only [sd]
      rw [edenot_agree' nx0 E E' e Hag he, ih1 h1, ih2 h2]
  | SHole h => intro _; exact HOLES_agree h E E' fs Hag
  | SNext => intro _; rfl
theorem sd_has_nil (HOLES : Nat → env → Fs.Fs → TSet) (D : TSet) (E : env) (fs : Fs.Fs)
    (HOLES_nil : ∀ (h : Nat) (E : env) (fs : Fs.Fs), HOLES h E fs []) :
    ∀ s : shape, D [] → sd HOLES D E fs s [] := by
  intro s
  induction s with
  | SNil => intro _; rfl
  | SExit c => intro _; exact t_exit_has_nil _ _
  | SEmitP fd ps s ih => intro _; exact t_emit_has_nil _ _
  | SAlt2 a b iha ihb => intro HD; exact Or.inl (iha HD)
  | SCase e mid s1 s2 ih1 ih2 =>
      intro HD
      simp only [sd]
      split
      · exact ih1 HD
      · exact ih2 HD
  | SHole h => intro _; exact HOLES_nil h E fs
  | SNext => intro HD; exact HD
theorem sd_salt2 (HOLES : Nat → env → Fs.Fs → TSet) (D : TSet) (E : env) (fs : Fs.Fs)
    (HOLES_nil : ∀ (h : Nat) (E : env) (fs : Fs.Fs), HOLES h E fs [])
    (a b : shape) (HD : D []) :
    t_eq (t_alt2 (sd HOLES D E fs a) (sd HOLES D E fs b)) (sd HOLES D E fs (salt2 a b)) := by
  have Ha := sd_has_nil HOLES D E fs HOLES_nil a HD
  have Hb := sd_has_nil HOLES D E fs HOLES_nil b HD
  cases a <;> cases b <;>
    first
      | exact t_alt2_nil_l _ Hb
      | exact t_alt2_nil_r _ Ha
      | exact t_eq_refl _

/-! ### `mrestrict`/`munrestrict` and the model-only frames of `vis`/`hid` -/
theorem mrestrict_munrestrict_clean (H : word → Bool) (FULL m' : word → Option byte)
    (Hc : ∀ a, H a = true → m' a = none) : mrestrict H (munrestrict H FULL m') = m' := by
  funext a
  simp only [mrestrict, munrestrict]
  cases h : H a with
  | false => rfl
  | true => exact (Hc a h).symm
theorem vis_same (A : atable) (E : env) (cs : acs) (model model' : Model)
    (Hs : same_but_materialized model model') : vis A E cs model' = vis A E cs model := by
  obtain ⟨-, hmap, hlazy, -⟩ := same_but_materialized_frame model model' Hs
  funext a
  simp only [vis, hmap, hlazy]
theorem hid_same (A : atable) (argH : env → word → Bool) (E : env) (cs : acs)
    (model model' : Model) (Hs : same_but_materialized model model') :
    hid A argH E cs model' = hid A argH E cs model := by
  funext a
  simp only [hid, vis_same A E cs model model' Hs]
theorem vis_ext (A : atable) (E : env) (cs cs' : acs) (model : Model)
    (Ha : cs'.a_vis = cs.a_vis) : vis A E cs' model = vis A E cs model := by
  funext a
  simp only [vis, in_allow, in_vis, in_sh, Ha]
theorem hid_ext (A : atable) (argH : env → word → Bool) (E : env) (cs cs' : acs) (model : Model)
    (Ha : cs'.a_vis = cs.a_vis) : hid A argH E cs' model = hid A argH E cs model := by
  funext a
  simp only [hid, vis_ext A E cs cs' model Ha]


/-! ### Element facts from the `*_vars_lt` list tests, and list congruences -/

/-- Every entry of a ledger that passes `maps_vars_lt` mentions only variables
    below `b`. -/
theorem maps_vars_lt_elem (b : Nat) (ms : List amap) (m : amap) (Hm : m ∈ ms)
    (H : maps_vars_lt b ms = true) :
    AsanPlanCore.expr_vars_lt b m.am_base = true ∧ AsanPlanCore.expr_vars_lt b m.am_len = true := by
  have h := (List.all_eq_true.mp H) m Hm
  simpa only [Bool.and_eq_true] using h

/-- Every range of a list that passes `pairs_vars_lt` mentions only variables
    below `b`. -/
theorem pairs_vars_lt_elem (b : Nat) (l : List (expr × expr)) (p : expr × expr)
    (Hp : p ∈ l) (H : pairs_vars_lt b l = true) :
    AsanPlanCore.expr_vars_lt b p.1 = true ∧ AsanPlanCore.expr_vars_lt b p.2 = true := by
  have h := (List.all_eq_true.mp H) p Hp
  simpa only [Bool.and_eq_true] using h

/-- A prefix of a `pairs_vars_lt` list passes the test. -/
theorem pairs_vars_lt_app_l (b : Nat) (l1 l2 : List (expr × expr))
    (H : pairs_vars_lt b (l1 ++ l2) = true) : pairs_vars_lt b l1 = true := by
  simp only [pairs_vars_lt, List.all_append, Bool.and_eq_true] at H
  exact H.1

/-- A suffix of a `pairs_vars_lt` list passes the test. -/
theorem pairs_vars_lt_app_r (b : Nat) (l1 l2 : List (expr × expr))
    (H : pairs_vars_lt b (l1 ++ l2) = true) : pairs_vars_lt b l2 = true := by
  simp only [pairs_vars_lt, List.all_append, Bool.and_eq_true] at H
  exact H.2

/-- `List.any` only looks at the members. -/
theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a r ih =>
      simp only [List.any_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-- `List.map` only looks at the members. -/
theorem map_congr_mem {α β : Type} {l : List α} {f g : α → β}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a r ih =>
      simp only [List.map_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-- `List.flatMap` only looks at the members. -/
theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a r ih =>
      simp only [List.flatMap_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-! ### `a_vis`/`a_ghost`-only and valuation-only components -/

/-- The `uE` of an expression with variables below `b` does not depend on the
    valuation. -/
theorem uE_agree (b : Nat) (E E' : env) (e : expr) (Hag : env_agree b E E')
    (Hv : AsanPlanCore.expr_vars_lt b e = true) : uE E' e = uE E e := by
  simp only [uE]
  rw [edenot_agree' b E E' e Hag Hv]
theorem allowA_agree (A : atable) (b : Nat) (E E' : env) (cs : acs)
    (Hag : env_agree b E E') (H : pairs_vars_lt b (cs.a_vis ++ cs.a_ghost) = true) :
    allowA A E' cs = allowA A E cs := by
  have hfun : ∀ p ∈ cs.a_vis ++ cs.a_ghost, allow1 A E' p = allow1 A E p := by
    intro p hp
    obtain ⟨h1, h2⟩ := pairs_vars_lt_elem b _ p hp H
    have e1 : uE E' p.1 = uE E p.1 := uE_agree b E E' p.1 Hag h1
    have e2 : uE E' p.2 = uE E p.2 := uE_agree b E E' p.2 Hag h2
    simp only [allow1, sh_lo, sh_hi, e1, e2]
  simp only [allowA]
  exact flatMap_congr_mem hfun
theorem in_allow_agree (A : atable) (b : Nat) (E E' : env) (cs : acs)
    (Hag : env_agree b E E') (H : pairs_vars_lt b cs.a_vis = true) :
    in_allow A E' cs = in_allow A E cs := by
  funext z
  have hv : ∀ p ∈ cs.a_vis,
      ((uE E' p.1 ≤ z) && (z < uE E' p.1 + uE E' p.2))
        = ((uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := pairs_vars_lt_elem b _ p hp H
    rw [uE_agree b E E' p.1 Hag h1, uE_agree b E E' p.2 Hag h2]
  have hs : ∀ p ∈ cs.a_vis,
      ((sh_lo A E' p ≤ z) && (z < sh_hi A E' p))
        = ((sh_lo A E p ≤ z) && (z < sh_hi A E p)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := pairs_vars_lt_elem b _ p hp H
    obtain ⟨_, h2'⟩ := pairs_vars_lt_elem b _ p hp H
    have e1 : uE E' p.1 = uE E p.1 := uE_agree b E E' p.1 Hag h1
    have e2 : uE E' p.2 = uE E p.2 := uE_agree b E E' p.2 Hag h2'
    simp only [sh_lo, sh_hi, e1, e2]
    rfl
  simp only [in_allow, in_vis, in_sh]
  rw [any_congr_mem hv, any_congr_mem hs]
theorem in_ghost_agree (b : Nat) (E E' : env) (cs : acs)
    (Hag : env_agree b E E') (H : pairs_vars_lt b (cs.a_vis ++ cs.a_ghost) = true) :
    in_ghost E' cs = in_ghost E cs := by
  funext z
  have hg : ∀ p ∈ cs.a_ghost,
      ((uE E' p.1 ≤ z) && (z < uE E' p.1 + uE E' p.2))
        = ((uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := pairs_vars_lt_elem b _ p (by simp [hp]) H
    rw [uE_agree b E E' p.1 Hag h1, uE_agree b E E' p.2 Hag h2]
  simp only [in_ghost]
  exact any_congr_mem hg
theorem hid_agree (A : atable) (nx0 : Nat) (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (b : Nat) (E E' : env) (cs : acs) (model : Model) (Hag : env_agree b E E')
    (Hle : nx0 ≤ b) (H : pairs_vars_lt b (cs.a_vis ++ cs.a_ghost) = true) :
    hid A argH E' cs model = hid A argH E cs model := by
  funext a
  have harg : argH E' a = argH E a :=
    (argH_agree E E' a (env_agree_le nx0 b E E' Hag Hle)).symm
  have hallow := in_allow_agree A b E E' cs Hag (pairs_vars_lt_app_l b cs.a_vis cs.a_ghost H)
  simp only [hid, vis, harg, hallow]
theorem maps_den_agree (b : Nat) (E E' : env) (ms : List amap) (Hag : env_agree b E E')
    (H : maps_vars_lt b ms = true) : ms.map (amap_den E') = ms.map (amap_den E) := by
  apply map_congr_mem
  intro m hm
  obtain ⟨h1, h2⟩ := maps_vars_lt_elem b ms m hm H
  simp only [amap_den, Prod.mk.injEq]
  exact ⟨(edenot_agree' b E E' m.am_base Hag h1).symm,
    (edenot_agree' b E E' m.am_len Hag h2).symm⟩
theorem maps_match_agree (b : Nat) (E E' : env) (ms : List amap) (Hag : env_agree b E E')
    (Hv : maps_vars_lt b ms = true) :
    ∀ l : List (word × word), maps_match E ms l → maps_match E' ms l := by
  revert Hv
  induction ms with
  | nil => intro _ l H; simpa only [maps_match] using H
  | cons m ms ih =>
      intro Hv l HM
      have hhead := maps_vars_lt_elem b (m :: ms) m (List.mem_cons_self ..) Hv
      have htail : maps_vars_lt b ms = true := by
        have h := Hv
        simp only [maps_vars_lt, List.all_cons, Bool.and_eq_true] at h
        exact h.2
      obtain ⟨hb, hl⟩ := hhead
      have hden : amap_den E' m = amap_den E m := by
        simp only [amap_den, Prod.mk.injEq]
        exact ⟨(edenot_agree' b E E' m.am_base Hag hb).symm,
          (edenot_agree' b E E' m.am_len Hag hl).symm⟩
      have e1 : uE E' m.am_base = uE E m.am_base := uE_agree b E E' m.am_base Hag hb
      have e2 : uE E' m.am_len = uE E m.am_len := uE_agree b E E' m.am_len Hag hl
      cases hf : is_fog m with
      | true =>
          simp only [maps_match, hf] at HM ⊢
          rcases HM with HM | ⟨iv, l', rfl, hsz, HM⟩
          · exact Or.inl (ih htail l HM)
          · exact Or.inr ⟨iv, l', rfl, by rw [e2]; exact hsz, ih htail l' HM⟩
      | false =>
          simp only [maps_match, hf] at HM ⊢
          obtain ⟨l', rfl, HM⟩ := HM
          exact ⟨l', by rw [hden], ih htail l' HM⟩
theorem holes_agree (b : Nat) (E E' : env) (y : Int) (l : List (word × word))
    (ms : List amap) (Hag : env_agree b E E') (Hv : maps_vars_lt b ms = true)
    (H : ∀ m ∈ ms, hole_ok E y l m) : ∀ m ∈ ms, hole_ok E' y l m := by
  intro m hm hh
  obtain ⟨hb, hl⟩ := maps_vars_lt_elem b ms m hm Hv
  have e1 : uE E' m.am_base = uE E m.am_base := uE_agree b E E' m.am_base Hag hb
  have e2 : uE E' m.am_len = uE E m.am_len := uE_agree b E E' m.am_len Hag hl
  have h := H m hm
  simp only [hole_ok] at h ⊢
  rw [e1, e2]
  exact h hh
theorem fds_ok_agree (b : Nat) (E E' : env) (f : afd) (model : Model)
    (Hag : env_agree b E E') (Hv : fd_vars_lt b f = true) (H : fds_ok E f model) :
    fds_ok E' f model := by
  cases f with
  | FdStd => simpa only [fds_ok] using H
  | FdDir => simpa only [fds_ok] using H
  | FdFile k len off =>
      simp only [fd_vars_lt, Bool.and_eq_true] at Hv
      obtain ⟨h1, h2⟩ := Hv
      have hlen := edenot_agree' b E E' len Hag h1
      have hoff := edenot_agree' b E E' off Hag h2
      simp only [fds_ok] at H ⊢
      obtain ⟨p, c, hfds, hlook, hl, ho, hch⟩ := H
      refine ⟨p, c, ?_, hlook, ?_, ?_, ?_⟩
      · rw [hfds, hoff]
      · simp only [uE]; rw [← hlen]; exact hl
      · simp only [uE]; rw [← hlen, ← hoff]; exact ho
      · intro j; rw [← Hag.2]; exact hch j
theorem fresh_ok_parts (nx0 : Nat) (cs : acs) (H : fresh_ok nx0 cs = true) :
    AsanPlanCore.sr_vars_lt (nxt cs) cs.a_ss.s_regs = true ∧
    AsanPlanCore.kn_vars_lt (nxt cs) (kn cs) = true ∧
    maps_vars_lt (nxt cs) cs.a_maps = true ∧
    pairs_vars_lt (nxt cs) (cs.a_vis ++ cs.a_ghost) = true ∧
    AsanPlanCore.expr_vars_lt (nxt cs) cs.a_brk = true ∧
    fd_vars_lt (nxt cs) cs.a_fd = true ∧ nx0 ≤ nxt cs := by
  simp only [fresh_ok, Bool.and_eq_true] at H
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := H
  have happ : pairs_vars_lt (nxt cs) (cs.a_vis ++ cs.a_ghost) = true := by
    have hsplit : pairs_vars_lt (nxt cs) (cs.a_vis ++ cs.a_ghost)
        = (pairs_vars_lt (nxt cs) cs.a_vis && pairs_vars_lt (nxt cs) cs.a_ghost) := by
      simp only [pairs_vars_lt, List.all_append]
    rw [hsplit, h4, h5]
    rfl
  exact ⟨h1, h2, h3, happ, h6, h7, of_decide_eq_true h8⟩
theorem cs_ok_agree (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E E' : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (Hag : env_agree (nxt cs) E E') (Hf : fresh_ok nx0 cs = true)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 E' cs R FULL model := by
  obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs Hf
  have HH : hid A argH E' cs model = hid A argH E cs model :=
    hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow
  have HA : allowA A E' cs = allowA A E cs :=
    allowA_agree A (nxt cs) E E' cs Hag Fallow
  have hden : ∀ m ∈ cs.a_maps, amap_den E' m = amap_den E m := by
    intro m hm
    obtain ⟨h1, h2⟩ := maps_vars_lt_elem (nxt cs) cs.a_maps m hm Fmaps
    simp only [amap_den, Prod.mk.injEq]
    exact ⟨(edenot_agree' (nxt cs) E E' m.am_base Hag h1).symm,
      (edenot_agree' (nxt cs) E E' m.am_len Hag h2).symm⟩
  refine ⟨?_, HC.co_log, ?_, HC.co_halt, ?_, HC.co_fs, HC.co_tid, HC.co_res, HC.co_limit,
    ?_, ?_, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb, HC.co_nasub, ?_, ?_,
    HC.co_totsz, HC.co_split, ?_, HC.co_sbrk, HC.co_eager, ?_, ?_, ?_, ?_⟩
  · exact regs_ok_agree' (nxt cs) E E' cs.a_ss.s_regs R Hag Fsr HC.co_regs
  · show know_ok segs E' (mrestrict (fun a => hid A argH E' cs model a) FULL) (kn cs)
    rw [HH]
    exact know_ok_agree' segs (nxt cs) E E' _ (kn cs) Hag Fkn HC.co_know
  · exact fds_ok_agree (nxt cs) E E' cs.a_fd model Hag Ffd HC.co_fds
  · exact maps_match_agree (nxt cs) E E' cs.a_maps Hag Fmaps _ HC.co_maps
  · exact holes_agree (nxt cs) E E' cs.a_ylo _ cs.a_maps Hag Fmaps HC.co_holes
  · intro m hm hk
    show amap_den E' m ∈ (m_vmmaps model).vm_noaccess
    rw [hden m hm]
    exact HC.co_none m hm hk
  · intro m hm hk a Ha
    obtain ⟨hb, hl⟩ := maps_vars_lt_elem (nxt cs) cs.a_maps m hm Fmaps
    have hd1 : edenot E' m.am_base = edenot E m.am_base :=
      (edenot_agree' (nxt cs) E E' m.am_base Hag hb).symm
    have hd2 : edenot E' m.am_len = edenot E m.am_len :=
      (edenot_agree' (nxt cs) E E' m.am_len Hag hl).symm
    rw [hd1, hd2] at Ha
    exact HC.co_kinds m hm hk a Ha
  · rw [HC.co_brk]
    exact edenot_agree' (nxt cs) E E' cs.a_brk Hag Fbrk
  · rw [HA]; exact HC.co_abytes
  · rw [HA]; exact HC.co_minv
  · intro a hh hm1 hm2 hm3 hm4
    rw [HH] at hh
    rw [in_ghost_agree (nxt cs) E E' cs Hag Fallow] at hm4
    exact HC.co_zero a hh hm1 hm2 hm3 hm4
  · exact SINV_agree E E' FULL (env_agree_le nx0 (nxt cs) E E' Hag Fle) HC.co_sinv


/-! ### Monotonicity of the syntactic variable-bound tests -/
theorem expr_vars_lt_mono (b b' : Nat) (e : expr) (H : AsanPlanCore.expr_vars_lt b e = true)
    (Hle : b ≤ b') : AsanPlanCore.expr_vars_lt b' e = true := by
  induction e with
  | ELit z => rfl
  | EVar n =>
      simp only [AsanPlanCore.expr_vars_lt] at H ⊢
      exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true H) Hle)
  | EAlu op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨ihx H.1, ihy H.2⟩
  | EAluw op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨ihx H.1, ihy H.2⟩
  | EMd op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨ihx H.1, ihy H.2⟩
  | EMdw op x y ihx ihy =>
      simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨ihx H.1, ihy H.2⟩
  | EExt sx lo n x ih =>
      simp only [AsanPlanCore.expr_vars_lt] at H ⊢
      exact ih H
  | EBlob sx k i n => rfl

/-- The `saddr` form of `expr_vars_lt_mono`. -/
theorem saddr_vars_lt_mono (b b' : Nat) (a : saddr)
    (H : AsanPlanCore.saddr_vars_lt b a = true) (Hle : b ≤ b') :
    AsanPlanCore.saddr_vars_lt b' a = true :=
  expr_vars_lt_mono b b' a.a_base H Hle
theorem sr_vars_lt_mono (b b' : Nat) (sr : List expr)
    (H : AsanPlanCore.sr_vars_lt b sr = true) (Hle : b ≤ b') :
    AsanPlanCore.sr_vars_lt b' sr = true := by
  induction sr with
  | nil => rfl
  | cons e r ih =>
      simp only [AsanPlanCore.sr_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨expr_vars_lt_mono b b' e H.1 Hle, ih H.2⟩
theorem kentry_vars_lt_mono (b b' : Nat) (K : kentry)
    (H : AsanPlanCore.kentry_vars_lt b K = true) (Hle : b ≤ b') :
    AsanPlanCore.kentry_vars_lt b' K = true := by
  cases K with
  | KWord a w v =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' v H.2 Hle⟩
  | KZero a n =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' n H.2 Hle⟩
  | KBlob a n k =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' n H.2 Hle⟩
  | KImg lo hi => rfl
  | KAlign e m =>
      simpa only [AsanPlanCore.kentry_vars_lt] using expr_vars_lt_mono b b' e H Hle
  | KRange e lo hi =>
      simpa only [AsanPlanCore.kentry_vars_lt] using expr_vars_lt_mono b b' e H Hle
  | KWr a n =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' n H.2 Hle⟩
  | KDisj a1 n1 a2 n2 =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
      exact ⟨⟨⟨saddr_vars_lt_mono b b' a1 h1 Hle, expr_vars_lt_mono b b' n1 h2 Hle⟩,
        saddr_vars_lt_mono b b' a2 h3 Hle⟩, expr_vars_lt_mono b b' n2 h4 Hle⟩
  | KFill a n c =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' n H.2 Hle⟩
  | KUnk a n =>
      simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨saddr_vars_lt_mono b b' a H.1 Hle, expr_vars_lt_mono b b' n H.2 Hle⟩
theorem kn_vars_lt_mono' (b b' : Nat) (k : List kentry)
    (H : AsanPlanCore.kn_vars_lt b k = true) (Hle : b ≤ b') :
    AsanPlanCore.kn_vars_lt b' k = true := by
  induction k with
  | nil => rfl
  | cons K r ih =>
      simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at H ⊢
      exact ⟨kentry_vars_lt_mono b b' K H.1 Hle, ih H.2⟩
theorem sr_vars_lt_upd (b : Nat) (sr : List expr) (n : Nat) (e : expr)
    (Hsr : AsanPlanCore.sr_vars_lt b sr = true)
    (He : AsanPlanCore.expr_vars_lt b e = true) :
    AsanPlanCore.sr_vars_lt b (sr_upd sr n e) = true := by
  revert sr
  induction n with
  | zero =>
      intro sr Hsr
      cases sr with
      | nil => simpa [sr_upd, AsanPlanCore.sr_vars_lt] using He
      | cons h t =>
          simp only [sr_upd, AsanPlanCore.sr_vars_lt, Bool.and_eq_true] at Hsr ⊢
          exact ⟨He, Hsr.2⟩
  | succ n ih =>
      intro sr Hsr
      cases sr with
      | nil =>
          show AsanPlanCore.sr_vars_lt b (.ELit 0 :: sr_upd [] n e) = true
          simp only [AsanPlanCore.sr_vars_lt, Bool.and_eq_true]
          exact ⟨rfl, ih [] Hsr⟩
      | cons h t =>
          simp only [sr_upd, AsanPlanCore.sr_vars_lt, Bool.and_eq_true] at Hsr ⊢
          exact ⟨Hsr.1, ih t Hsr.2⟩
theorem nth_sr_vars_lt (b : Nat) (sr : List expr) (r : Nat)
    (H : AsanPlanCore.sr_vars_lt b sr = true) (Hr : r < 32) :
    AsanPlanCore.expr_vars_lt b (sr.getD r (.ELit 0)) = true := by
  induction sr generalizing r with
  | nil => cases r <;> rfl
  | cons x t ih =>
      simp only [AsanPlanCore.sr_vars_lt, Bool.and_eq_true] at H
      cases r with
      | zero => simpa using H.1
      | succ r => exact ih r H.2 (by omega)
theorem fresh_ok_mono (nx0 gb : Nat) (cs : acs) (Hle : nx0 ≤ gb)
    (H : fresh_ok gb cs = true) : fresh_ok nx0 cs = true := by
  simp only [fresh_ok, Bool.and_eq_true] at H ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := H
  exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩,
    decide_eq_true (Nat.le_trans Hle (of_decide_eq_true h8))⟩


/-! ### Literal and address arithmetic -/
theorem elenZ_lit (E : env) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) : elenZ E (.ELit z) = z := by
  simp only [elenZ, edenot_lit]
  exact u_small z Hz
theorem estart_SA (E : env) (b : expr) (k : Int) :
    estart E (SA b k) = bv_unsigned (edenot E b) + k := rfl
theorem pc_inst (inv : acs) (J : Nat) (e : expr) : pc (inst inv J e) = pc inv := rfl
theorem nxt_inst (inv : acs) (J : Nat) (e : expr) : nxt (inst inv J e) = nxt inv := rfl
theorem ridx_lit (n : Nat) (Hn : n < 32) : ridx (Z_to_bv 5 (n : Int)) = n := by
  simp only [ridx, bv_unsigned, Z_to_bv, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-! ### The allowed set: monotonicity and non-negativity of `A_bytes` -/
theorem page_allowedb_app_l (l1 l2 : List (Int × Int)) (p : word)
    (H : page_allowedb l1 p = true) : page_allowedb (l1 ++ l2) p = true := by
  unfold page_allowedb at *
  rw [List.any_append, H, Bool.true_or]
theorem MInv_app_r (l1 l2 : List (Int × Int)) (m : Model) (H : MInv l1 m)
    (Hb : eager_used m + A_bytes (l1 ++ l2) ≤ (m_vmmaps m).vm_limit) :
    MInv (l1 ++ l2) m where
  minv_nodup := H.minv_nodup
  minv_aligned := H.minv_aligned
  minv_allowed := fun p Hp => page_allowedb_app_l l1 l2 p (H.minv_allowed p Hp)
  minv_lazy := H.minv_lazy
  minv_budget := Hb
theorem vis_here_eq (b n : expr) (p : expr × expr) (H : vis_here b n p = true) :
    p = (b, n) := by
  obtain ⟨pb, pn⟩ := p
  simp only [vis_here, Bool.and_eq_true] at H
  rw [expr_eqb_eq _ _ H.1, expr_eqb_eq _ _ H.2]
theorem In_list_set_nth {T : Type} (l : List T) (i : Nat) (x y : T)
    (H : y ∈ list_set_nth i x l) : y = x ∨ y ∈ l := by
  induction l generalizing i with
  | nil => simp [list_set_nth] at H
  | cons a r ih =>
      cases i with
      | zero =>
          simp only [list_set_nth, List.mem_cons] at H
          rcases H with rfl | H
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ H)
      | succ i =>
          simp only [list_set_nth, List.mem_cons] at H
          rcases H with rfl | H
          · exact Or.inr (List.mem_cons_self ..)
          · rcases ih i H with rfl | H'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ H')
theorem In_list_insert_nth {T : Type} (l : List T) (i : Nat) (x y : T)
    (H : y ∈ list_insert_nth i x l) : y = x ∨ y ∈ l := by
  induction l generalizing i with
  | nil =>
      cases i with
      | zero => simpa [list_insert_nth] using H
      | succ i => simpa [list_insert_nth] using H
  | cons a r ih =>
      cases i with
      | zero =>
          simp only [list_insert_nth, List.mem_cons] at H
          rcases H with rfl | rfl | H
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inr (List.mem_cons_of_mem _ H)
      | succ i =>
          simp only [list_insert_nth, List.mem_cons] at H
          rcases H with rfl | H
          · exact Or.inr (List.mem_cons_self ..)
          · rcases ih i H with rfl | H'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ H')
theorem A_bytes_fm_split (A : atable) (E : env) (f : expr × expr → Bool) :
    ∀ l : List (expr × expr),
      A_bytes (l.flatMap (allow1 A E))
        = A_bytes ((l.filter f).flatMap (allow1 A E))
          + A_bytes ((l.filter (fun p => !f p)).flatMap (allow1 A E)) := by
  intro l
  induction l with
  | nil => simp [A_bytes]
  | cons p r ih =>
      cases h : f p with
      | true =>
          have h' : (fun q => !f q) p = false := by simp [h]
          rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h'])]
          simp only [List.flatMap_cons]
          rw [A_bytes_app, A_bytes_app, ih]
          omega
      | false =>
          have h' : (fun q => !f q) p = true := by simp [h]
          rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h'])]
          simp only [List.flatMap_cons]
          rw [A_bytes_app, A_bytes_app, ih]
          omega
theorem A_bytes_allow1_nonneg (A : atable) (E : env) (p : expr × expr) :
    0 ≤ A_bytes (allow1 A E p) := by
  obtain ⟨b, n⟩ := p
  have hb : 0 ≤ uE E b := bv_unsigned_nonneg _
  have hn : 0 ≤ uE E n := bv_unsigned_nonneg _
  have hs : uE E b / 8 ≤ (uE E b + uE E n) / 8 :=
    Int.ediv_le_ediv (by decide : (0 : Int) < 8) (by omega)
  have h1 : pagedown (uE E b) ≤ uE E b := pagedown_le _
  have h2 : uE E b + uE E n ≤ pageup (uE E b + uE E n) := pageup_ge _
  have h3 : pagedown (sh_lo A E (b, n)) ≤ sh_lo A E (b, n) := pagedown_le _
  have h4 : sh_hi A E (b, n) ≤ pageup (sh_hi A E (b, n)) := pageup_ge _
  have h5 : sh_lo A E (b, n) ≤ sh_hi A E (b, n) := by
    simp only [sh_lo, sh_hi]
    omega
  simp only [allow1, A_bytes]
  omega
theorem A_bytes_fm_here (A : atable) (E : env) (b n : expr) :
    ∀ l : List (expr × expr), (∀ p ∈ l, p = (b, n)) →
      A_bytes (l.flatMap (allow1 A E))
        = (l.length : Int) * A_bytes (allow1 A E (b, n)) := by
  intro l
  induction l with
  | nil => intro _; simp [A_bytes]
  | cons p r ih =>
      intro H
      have hp : p = (b, n) := H p (by simp)
      have hr : ∀ q ∈ r, q = (b, n) := fun q hq => H q (by simp [hq])
      simp only [List.flatMap_cons, List.length_cons]
      rw [A_bytes_app, ih hr, hp, Int.natCast_add_one, Int.add_mul, Int.one_mul]
      omega

theorem LCOK_bnd (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HOLES : Nat → env → Fs.Fs → TSet) (lc : Option loopctx) (D : TSet) (E : env)
    (fs : Fs.Fs) (HL : LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E fs) :
    nx0 ≤ (match lc with | some c => lc_bnd c | none => nx0) := by
  cases lc with
  | none => exact Nat.le_refl nx0
  | some c =>
      cases c with
      | LC h nx lo hi =>
          obtain ⟨⟨h1, h2, _⟩, _⟩ := HL
          simpa only [lc_bnd] using Nat.le_trans h1 h2
      | JC j js sk b lo =>
          obtain ⟨⟨h1, _, _⟩, _⟩ := HL
          simpa only [lc_bnd] using h1

/-! ### `PBump`: raising the variable counter -/
theorem bump_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : Nat) (cs' : acs) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_bump cs m = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_bump at H
  split at H
  · rename_i hle
    injection H with hEq
    subst hEq
    exact ⟨⟨HC.co_regs, rfl, HC.co_know, HC.co_halt, HC.co_fds, HC.co_fs, HC.co_tid,
      HC.co_res, HC.co_limit, HC.co_maps, HC.co_holes, HC.co_seps, HC.co_wf, HC.co_bounds,
      HC.co_lazyb, HC.co_nasub, HC.co_none, HC.co_kinds, HC.co_totsz, HC.co_split,
      HC.co_brk, HC.co_sbrk, HC.co_eager, HC.co_abytes, HC.co_minv, HC.co_zero,
      HC.co_sinv⟩, rfl⟩
  · simp at H


/-! ### `KImg` clipping, the visibility monotonicity, and hull bytes -/
theorem pw_kind_zf (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (H : zf_kind segs mk byteof) :
    pw_kind segs mk (fun M x => byteof (M x)) := by
  intro E M a n
  rw [H E M a n]
  constructor
  · rintro ⟨hf, h⟩; exact ⟨hf, fun i hi => h i hi.1 hi.2⟩
  · rintro ⟨hf, h⟩; exact ⟨hf, fun i h1 h2 => h i ⟨h1, h2⟩⟩
theorem kimg_clip_incl (A : atable) (k : List kentry) (K : kentry)
    (H : K ∈ kimg_clip A k) : K ∈ k := by
  rw [kimg_clip, List.mem_filter] at H
  exact H.1
theorem kimg_clip_in_hull (A : atable) (k : List kentry) :
    kimg_in_hull A (kimg_clip A k) := by
  intro K hK
  have hb := (List.mem_filter.mp hK).2
  cases K with
  | KImg lo hi =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨hb.1.1, hb.2⟩
  | KWord a w v => trivial
  | KZero a n => trivial
  | KBlob a n k => trivial
  | KAlign e m => trivial
  | KRange e lo hi => trivial
  | KWr a n => trivial
  | KDisj a1 n1 a2 n2 => trivial
  | KFill a n c => trivial
  | KUnk a n => trivial
theorem kimg_in_hull_app (A : atable) (k1 k2 : List kentry)
    (H1 : kimg_in_hull A k1) (H2 : kimg_in_hull A k2) : kimg_in_hull A (k1 ++ k2) := by
  intro K hK
  rcases List.mem_append.mp hK with h | h
  · exact H1 K h
  · exact H2 K h

/-- `a || b = false` projects to both components. -/
theorem or_eq_false_left {a b : Bool} (h : (a || b) = false) : a = false := by
  cases a <;> cases b <;> simp_all

/-- `a || b = false` projects to both components. -/
theorem or_eq_false_right {a b : Bool} (h : (a || b) = false) : b = false := by
  cases a <;> cases b <;> simp_all

/-- `a && b = true` projects to both components. -/
theorem and_eq_true_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

/-- `a && b = true` projects to both components. -/
theorem and_eq_true_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

/-- hull bytes are always visible, never hidden. -/
theorem hid_hull (A : atable) (argH : env → word → Bool) (E : env) (cs : acs)
    (model : Model) (HULL_ok : hull_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (a : word) (Hh : in_hull A (bv_unsigned a) = true) :
    hid A argH E cs model a = false := by
  cases ha : argH E a with
  | false =>
      have hv : vis A E cs model a = true := by simp only [vis, Hh, Bool.true_or]
      simp only [hid, ha, hv, Bool.not_true, Bool.false_or, Bool.false_eq_true]
  | true =>
      exfalso
      have h1 := argH_high E a ha
      have h2 : A.img_hi ≤ KHI := HULL_ok.2.2.2
      have h3 : KHI < CEIL := by decide
      simp only [in_hull, Bool.and_eq_true, decide_eq_true_eq] at Hh
      omega
theorem H_off_segments_cs (segs : List Segment) (A : atable) (argH : env → word → Bool)
    (E : env) (cs : acs) (model : Model) (HULL_ok : hull_ok A)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a) :
    H_off_segments segs (hid A argH E cs model) := by
  intro a hh
  cases ha : argH E a with
  | true =>
      have h1 := argH_high E a ha
      have h2 : A.img_hi ≤ KHI := HULL_ok.2.2.2
      have h3 : KHI < CEIL := by decide
      apply SEGS_in_hull
      simp only [in_hull]
      rw [show decide (bv_unsigned a < A.img_hi) = false from decide_eq_false (by omega)]
      simp
  | false =>
      simp only [hid, ha, Bool.false_or] at hh
      apply SEGS_in_hull
      have hv : vis A E cs model a = false := by simpa using hh
      simp only [vis] at hv
      exact or_eq_false_left (or_eq_false_left hv)

theorem vis_mono (A : atable) (E : env) (cs cs' : acs) (model : Model) (a : word)
    (Hm : ∀ z : Int, in_allow A E cs z = true → in_allow A E cs' z = true)
    (H : vis A E cs model a = true) : vis A E cs' model a = true := by
  simp only [vis] at H ⊢
  rw [Bool.or_eq_true] at H ⊢
  rcases H with h | h
  · exact Or.inl h
  · rw [Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine Or.inr ⟨h1, ?_⟩
    rw [Bool.or_eq_true] at h2 ⊢
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Hm _ h2)
theorem in_allow_cons (A : atable) (E : env) (cs : acs) (p : expr × expr) (ss : sym_state)
    (tot ylo eg : Int) (gh : List (expr × expr)) (ab : Int) (brk : expr) (fd : afd) (tid : Bool)
    (z : Int) (H : in_allow A E cs z = true) :
    in_allow A E (ACS ss cs.a_maps tot ylo eg (p :: cs.a_vis) gh ab brk fd tid) z = true := by
  simp only [in_allow, in_vis, in_sh, List.any_cons] at H ⊢
  rw [Bool.or_eq_true] at H ⊢
  rcases H with h | h
  · exact Or.inl (by rw [Bool.or_eq_true]; exact Or.inr h)
  · exact Or.inr (by rw [Bool.or_eq_true]; exact Or.inr h)


/-! ### Part 7: the `PCase2` split node and `map_remove` -/
theorem split_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (e : expr) (mid lo hi : Int) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hr : erange (kn cs) e = some (lo, hi)) :
    (bv_unsigned (edenot E e) ≤ mid →
      cs_ok segs A LIMIT SINV argH FS0 E (set_kn cs (.KRange e lo mid :: kn cs)) R FULL model)
    ∧ (mid < bv_unsigned (edenot E e) →
      cs_ok segs A LIMIT SINV argH FS0 E (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) R FULL model) := by
  have Hb := erange_sound segs E (Mr A argH E cs model FULL) (kn cs) e lo hi HC.co_know Hr
  constructor
  · intro Hm
    refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact ⟨Hb.1, Hm⟩
    · exact HC.co_know K hK
  · intro Hm
    refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact ⟨by omega, Hb.2⟩
    · exact HC.co_know K hK
theorem map_remove_notin' (l : List (word × word)) (a : word)
    (H : ∀ b sz, (b, sz) ∈ l → b ≠ a) : map_remove l a = l := by
  rw [map_remove, List.filter_eq_self]
  intro p hp
  obtain ⟨b, sz⟩ := p
  simpa using beq_eq_false_iff_ne.mpr (H b sz hp)

/-! ### 7b: template instantiation (`esubst` and friends) -/

/-- This tree's `AP.esubst`, disambiguated from `AxSymExec3.esubst` . -/
abbrev esubst (J : Nat) (e x : expr) : expr := AsanPlanCore.esubst J e x

/-- `upd` leaves the byte-string variables alone. -/
theorem upd_eb (E : env) (J : Nat) (w : word) : (upd E J w).eb = E.eb := rfl

/-- `upd` at the overwritten variable. -/
theorem upd_ev (E : env) (J : Nat) (w : word) (n : Nat) :
    (upd E J w).ev n = if n == J then w else E.ev n := rfl

/-- Substitution commutes with the denotation. -/
theorem esubst_denot (E : env) (J : Nat) (e x : expr) :
    edenot E (esubst J e x) = edenot (upd E J (edenot E e)) x := by
  induction x with
  | ELit z => rfl
  | EVar n =>
      show edenot E (if n == J then e else .EVar n) =
        edenot (upd E J (edenot E e)) (.EVar n)
      by_cases h : n = J <;> simp [h, upd, edenot]
  | EAlu op a b iha ihb =>
      simp only [esubst, AsanPlanCore.esubst, edenot, mkAlu_denot, iha, ihb]
  | EAluw op a b iha ihb =>
      simp only [esubst, AsanPlanCore.esubst, edenot, mkAluw_denot, iha, ihb]
  | EMd op a b iha ihb =>
      simp only [esubst, AsanPlanCore.esubst, edenot, mkMd_denot, iha, ihb]
  | EMdw op a b iha ihb =>
      simp only [esubst, AsanPlanCore.esubst, edenot, mkMdw_denot, iha, ihb]
  | EExt sx lo n a iha =>
      simp only [esubst, AsanPlanCore.esubst, edenot, iha]
  | EBlob sx k i n =>
      simp only [esubst, AsanPlanCore.esubst, edenot, upd]

/-- `estart` of a substituted address. -/
theorem estart_asubst (E : env) (J : Nat) (e : expr) (a : saddr) :
    estart E (asubst J e a) = estart (upd E J (edenot E e)) a := by
  obtain ⟨b, o⟩ := a
  simp only [asubst, estart, esubst_denot]

/-- `adenot` of a substituted address. -/
theorem adenot_asubst (E : env) (J : Nat) (e : expr) (a : saddr) :
    adenot E (asubst J e a) = adenot (upd E J (edenot E e)) a := by
  obtain ⟨b, o⟩ := a
  simp only [asubst, adenot, esubst_denot]

/-- Substitution commutes with the knowledge-entry denotation. -/
theorem kentry_ok_ksubst (segs : List Segment) (E : env) (J : Nat) (e : expr)
    (M : word → Option byte) (K : kentry) :
    kentry_ok segs E M (ksubst J e K) ↔ kentry_ok segs (upd E J (edenot E e)) M K := by
  cases K <;> simp only [ksubst, kentry_ok, flat, elenZ, estart_asubst, adenot_asubst,
    esubst_denot, upd_eb]

/-- Substitution commutes with the knowledge-list denotation. -/
theorem know_ok_ksubst (segs : List Segment) (E : env) (J : Nat) (e : expr)
    (M : word → Option byte) (k : List kentry) :
    know_ok segs E M (k.map (ksubst J e)) ↔
      know_ok segs (upd E J (edenot E e)) M k := by
  simp only [know_ok]
  constructor
  · intro H K hK
    exact (kentry_ok_ksubst segs E J e M K).mp (H _ (List.mem_map_of_mem hK))
  · intro H K hK
    obtain ⟨K', hK', rfl⟩ := List.mem_map.mp hK
    exact (kentry_ok_ksubst segs E J e M K').mpr (H _ hK')


/-- One allowed interval is unchanged by substitution. -/
theorem inst_allow1 (A : atable) (E : env) (J : Nat) (e : expr) (p : expr × expr) :
    allow1 A E (psubst J e p) = allow1 A (upd E J (edenot E e)) p := by
  obtain ⟨b, n⟩ := p
  simp only [allow1, psubst, sh_lo, sh_hi, uE, esubst_denot]

/-- The allowed set is unchanged by substitution. -/
theorem inst_allowA (A : atable) (E : env) (J : Nat) (e : expr) (inv : acs) :
    allowA A E (inst inv J e) = allowA A (upd E J (edenot E e)) inv := by
  simp only [allowA, inst]
  rw [← List.map_append, List.flatMap_map]
  exact flatMap_congr_mem (fun p _ => inst_allow1 A E J e p)

/-- The allowed predicate is unchanged by substitution. -/
theorem inst_in_allow (A : atable) (E : env) (J : Nat) (e : expr) (inv : acs) (z : Int) :
    in_allow A E (inst inv J e) z = in_allow A (upd E J (edenot E e)) inv z := by
  simp only [in_allow, in_vis, in_sh, inst, existsb_map']
  congr 1
  · apply any_congr_mem
    intro p _
    simp only [psubst, uE, esubst_denot]
    rfl
  · apply any_congr_mem
    intro p _
    simp only [psubst, sh_lo, sh_hi, uE, esubst_denot]
    rfl

/-- The ghost predicate is unchanged by substitution. -/
theorem inst_in_ghost (E : env) (J : Nat) (e : expr) (inv : acs) (z : Int) :
    in_ghost E (inst inv J e) z = in_ghost (upd E J (edenot E e)) inv z := by
  simp only [in_ghost, inst, existsb_map']
  apply any_congr_mem
  intro p _
  simp only [psubst, uE, esubst_denot]
  rfl

/-- Hiding is unchanged by substitution. -/
theorem inst_hid (A : atable) (nx0 : Nat) (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (E : env) (J : Nat) (e : expr) (inv : acs) (model : Model) (HJ : nx0 ≤ J) :
    hid A argH E (inst inv J e) model = hid A argH (upd E J (edenot E e)) inv model := by
  funext a
  have harg : argH E a = argH (upd E J (edenot E e)) a :=
    argH_agree E (upd E J (edenot E e)) a
      (env_agree_le nx0 J E _ (upd_agree E J _) HJ)
  simp only [hid, vis, harg, inst_in_allow]

/-- One ledger entry's denotation is unchanged by substitution. -/
theorem amap_den_msubst (E : env) (J : Nat) (e : expr) (m : amap) :
    amap_den E (msubst J e m) = amap_den (upd E J (edenot E e)) m := by
  simp only [amap_den, msubst, esubst_denot]

/-- The ledger denotation is unchanged by substitution. -/
theorem inst_maps (E : env) (J : Nat) (e : expr) (inv : acs) :
    ((inst inv J e).a_maps.map (amap_den E)) =
      inv.a_maps.map (amap_den (upd E J (edenot E e))) := by
  simp only [inst]
  rw [List.map_map]
  apply map_congr_mem
  intro m _
  simp only [Function.comp, amap_den, msubst, esubst_denot]

/-- The ledger match is unchanged by substitution. -/
theorem maps_match_msubst (E : env) (J : Nat) (e : expr) (ms : List amap)
    (l : List (word × word)) :
    maps_match E (ms.map (msubst J e)) l ↔
      maps_match (upd E J (edenot E e)) ms l := by
  induction ms generalizing l with
  | nil => simp only [List.map_nil, maps_match]
  | cons m ms ih =>
      have hlen : uE E (msubst J e m).am_len =
          uE (upd E J (edenot E e)) m.am_len := by
        simp only [uE, msubst, esubst_denot]
      have hfog : is_fog (msubst J e m) = is_fog m := rfl
      simp only [List.map_cons, maps_match, hfog, hlen, ih, amap_den_msubst]

/-- A hole obligation is unchanged by substitution (helper). -/
theorem hole_ok_msubst (E : env) (J : Nat) (e : expr) (y : Int)
    (l : List (word × word)) (m : amap) :
    hole_ok E y l (msubst J e m) ↔ hole_ok (upd E J (edenot E e)) y l m := by
  simp only [hole_ok, msubst, is_hole, uE, esubst_denot]

/-- The hole obligations are unchanged by substitution. -/
theorem holes_msubst (E : env) (J : Nat) (e : expr) (y : Int)
    (l : List (word × word)) (ms : List amap) :
    (∀ m ∈ ms.map (msubst J e), hole_ok E y l m) ↔
      (∀ m ∈ ms, hole_ok (upd E J (edenot E e)) y l m) := by
  constructor
  · intro H m hm
    exact (hole_ok_msubst E J e y l m).mp (H _ (List.mem_map_of_mem hm))
  · intro H m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    exact (hole_ok_msubst E J e y l m').mpr (H _ hm')

/-- The instantiated ledger matches. -/
theorem inst_maps_match (E : env) (J : Nat) (e : expr) (inv : acs)
    (l : List (word × word)) :
    maps_match E ((inst inv J e).a_maps) l ↔
      maps_match (upd E J (edenot E e)) inv.a_maps l := by
  simp only [inst, maps_match_msubst]

/-- `getD` commutes with a `map` up to the default (helper). -/
theorem getD_map' {α β : Type} (f : α → β) (l : List α) (i : Nat) (d : β) (x : α)
    (h : d = f x) : (l.map f).getD i d = f (l.getD i x) := by
  induction l generalizing i with
  | nil => simp [List.getD, h]
  | cons a r ih =>
      cases i with
      | zero => rfl
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j

/-- The register file is unchanged by substitution. -/
theorem regs_ok_inst (E : env) (J : Nat) (e : expr) (sr : List expr) (R : BvMap word) :
    regs_ok E (sr.map (esubst J e)) R ↔ regs_ok (upd E J (edenot E e)) sr R := by
  have G : ∀ r : reg, edenot E (sr_get (sr.map (esubst J e)) r) =
      edenot (upd E J (edenot E e)) (sr_get sr r) := by
    intro r
    simp only [sr_get]
    by_cases h : bv_eqb r 0
    · simp only [h, ite_true]
      rfl
    · simp only [h, ite_false, Bool.false_eq_true]
      rw [getD_map' (esubst J e) sr (ridx r) (.ELit 0) (.ELit 0) rfl]
      exact esubst_denot E J e _
  simp only [regs_ok]
  constructor
  · intro H r; rw [← G r]; exact H r
  · intro H r; rw [G r]; exact H r

/-- The fd table is unchanged by substitution. -/
theorem fds_ok_inst (E : env) (J : Nat) (e : expr) (f : afd) (model : Model) :
    fds_ok E (fsubst J e f) model ↔
      fds_ok (upd E J (edenot E e)) f model := by
  cases f <;> simp only [fsubst, fds_ok, uE, esubst_denot, upd_eb]


/-- Agreement is symmetric (helper). -/
theorem env_agree_sym (b : Nat) (E E' : env) (H : env_agree b E E') : env_agree b E' E :=
  ⟨fun n hn => (H.1 n hn).symm, H.2.symm⟩

/-- The instantiated checker state denotes the same configurations. -/
theorem cs_ok_inst (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (J : Nat) (e : expr) (inv : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (HJ : nx0 ≤ J)
    (Hlog : inv.a_ss.s_log = []) :
    cs_ok segs A LIMIT SINV argH FS0 E (inst inv J e) R FULL model ↔
      cs_ok segs A LIMIT SINV argH FS0 (upd E J (edenot E e)) inv R FULL model := by
  have AG : env_agree nx0 E (upd E J (edenot E e)) :=
    env_agree_le nx0 J E _ (upd_agree E J _) HJ
  have HH : hid A argH E (inst inv J e) model =
      hid A argH (upd E J (edenot E e)) inv model :=
    inst_hid A nx0 argH argH_agree E J e inv model HJ
  have HA : allowA A E (inst inv J e) = allowA A (upd E J (edenot E e)) inv :=
    inst_allowA A E J e inv
  have HG : ∀ z : Int,
      in_ghost E (inst inv J e) z = in_ghost (upd E J (edenot E e)) inv z :=
    fun z => inst_in_ghost E J e inv z
  have hMr : mrestrict (fun a => hid A argH E (inst inv J e) model a) FULL =
      mrestrict (fun a => hid A argH (upd E J (edenot E e)) inv model a) FULL := by
    rw [HH]
  constructor
  · intro HC
    refine ⟨?_, Hlog, ?_, HC.co_halt, ?_, HC.co_fs, HC.co_tid, HC.co_res, HC.co_limit,
      ?_, ?_, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb, HC.co_nasub, ?_, ?_,
      HC.co_totsz, HC.co_split, ?_, HC.co_sbrk, HC.co_eager, ?_, ?_, ?_, ?_⟩
    · exact (regs_ok_inst E J e inv.a_ss.s_regs R).mp
        (by simpa only [inst, mk_ss] using HC.co_regs)
    · show know_ok segs (upd E J (edenot E e))
        (mrestrict (fun a => hid A argH (upd E J (edenot E e)) inv model a) FULL) (kn inv)
      rw [← hMr]
      exact (know_ok_ksubst segs E J e _ (kn inv)).mp
        (by simpa only [inst, mk_ss, kn, Mr] using HC.co_know)
    · exact (fds_ok_inst E J e inv.a_fd model).mp
        (by simpa only [inst] using HC.co_fds)
    · exact (maps_match_msubst E J e inv.a_maps _).mp
        (by simpa only [inst] using HC.co_maps)
    · exact (holes_msubst E J e inv.a_ylo _ inv.a_maps).mp
        (by simpa only [inst] using HC.co_holes)
    · intro m hm hk
      have hkind : (msubst J e m).am_kind = .KNONE ∨ (msubst J e m).am_kind = .KNONELAZY := by
        simpa only [msubst] using hk
      have h := HC.co_none (msubst J e m) (List.mem_map_of_mem hm) hkind
      simpa only [amap_den_msubst] using h
    · intro m hm hk a Ha
      obtain ⟨h1, h2⟩ := Ha
      have hkind : (msubst J e m).am_kind = .KRWLAZY := by simpa only [msubst] using hk
      refine HC.co_kinds (msubst J e m) (List.mem_map_of_mem hm) hkind a ⟨?_, ?_⟩
      · simpa only [msubst, ← esubst_denot] using h1
      · simpa only [msubst, ← esubst_denot] using h2
    · rw [← esubst_denot]
      simpa only [inst] using HC.co_brk
    · rw [← HA]; exact HC.co_abytes
    · rw [← HA]; exact HC.co_minv
    · intro a h1 h2 h3 h4 h5
      rw [← HH] at h1
      rw [← HG (bv_unsigned a)] at h5
      exact HC.co_zero a h1 h2 h3 h4 h5
    · exact SINV_agree E (upd E J (edenot E e)) FULL AG HC.co_sinv
  · intro HC
    have AG' : env_agree nx0 (upd E J (edenot E e)) E := env_agree_sym nx0 _ _ AG
    refine ⟨?_, ?_, ?_, HC.co_halt, ?_, HC.co_fs, HC.co_tid, HC.co_res, HC.co_limit,
      ?_, ?_, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb, HC.co_nasub, ?_, ?_,
      HC.co_totsz, HC.co_split, ?_, HC.co_sbrk, HC.co_eager, ?_, ?_, ?_, ?_⟩
    · exact (regs_ok_inst E J e inv.a_ss.s_regs R).mpr HC.co_regs
    · simp only [inst, mk_ss]
    · show know_ok segs E
        (mrestrict (fun a => hid A argH E (inst inv J e) model a) FULL)
        ((kn inv).map (ksubst J e))
      exact (know_ok_ksubst segs E J e _ (kn inv)).mpr
        (by rw [hMr]; exact HC.co_know)
    · exact (fds_ok_inst E J e inv.a_fd model).mpr HC.co_fds
    · exact (maps_match_msubst E J e inv.a_maps _).mpr HC.co_maps
    · exact (holes_msubst E J e inv.a_ylo _ inv.a_maps).mpr HC.co_holes
    · intro m hm hk
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
      rw [amap_den_msubst]
      exact HC.co_none m' hm' (by simpa only [msubst] using hk)
    · intro m hm hk a Ha
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
      obtain ⟨h1, h2⟩ := Ha
      refine HC.co_kinds m' hm' (by simpa only [msubst] using hk) a ⟨?_, ?_⟩
      · simpa only [msubst, esubst_denot] using h1
      · simpa only [msubst, esubst_denot] using h2
    · simp only [inst]
      rw [esubst_denot]
      exact HC.co_brk
    · rw [HA]; exact HC.co_abytes
    · rw [HA]; exact HC.co_minv
    · intro a h1 h2 h3 h4 h5
      rw [HH] at h1
      rw [HG] at h5
      exact HC.co_zero a h1 h2 h3 h4 h5
    · exact SINV_agree (upd E J (edenot E e)) E FULL AG' HC.co_sinv


/-- Loop-context transport to an agreeing valuation. -/
theorem LCOK_agree (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HOLES : Nat → env → Fs.Fs → TSet)
    (lc : Option loopctx) (D : TSet) (E E' : env) (fs : Fs.Fs) (cs : acs)
    (HL : LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E fs)
    (Hg : lc_guard lc cs = true) (Hag : env_agree (nxt cs) E E') :
    LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E' fs := by
  cases lc with
  | none => trivial
  | some c =>
      cases c with
      | LC h nx lo hi =>
          simp only [LCOK, lc_guard, lc_bnd] at HL Hg ⊢
          obtain ⟨⟨H1, H2, H3⟩, HL⟩ := HL
          /- `of_decide_eq_true`, not `simpa using Hg`: this toolchain's
             `simpa` leaves the hypothesis at `decide (…) = true` here. -/
          have hhi : hi ≤ nxt cs := of_decide_eq_true Hg
          have hle : lo ≤ nxt cs := by omega
          exact ⟨⟨H1, H2, H3⟩, fun E2 R' F' m' Hag2 HC Hfs =>
            HL E2 R' F' m'
              (env_agree_trans lo E E' E2 (env_agree_le lo (nxt cs) E E' Hag hle) Hag2) HC Hfs⟩
      | JC j js sk b lo =>
          simp only [LCOK, lc_guard, lc_bnd] at HL Hg ⊢
          obtain ⟨⟨H1, H2, H3⟩, HL⟩ := HL
          have hle : b ≤ nxt cs := of_decide_eq_true Hg
          exact ⟨⟨H1, H2, H3⟩, fun E2 R' F' m' Hag2 HC Hfs =>
            HL E2 R' F' m'
              (env_agree_trans b E E' E2 (env_agree_le b (nxt cs) E E' Hag hle) Hag2) HC Hfs⟩

/-- Loop-context transport at the GC bound. -/
theorem LCOK_agree_gb (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HOLES : Nat → env → Fs.Fs → TSet)
    (lc : Option loopctx) (D : TSet) (E E' : env) (fs : Fs.Fs)
    (HL : LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E fs)
    (Hag : env_agree (match lc with | some c => lc_bnd c | none => nx0) E E') :
    LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E' fs := by
  cases lc with
  | none => trivial
  | some c =>
      cases c with
      | LC h nx lo hi =>
          simp only [LCOK, lc_bnd] at HL Hag ⊢
          obtain ⟨⟨H1, H2, H3⟩, HL⟩ := HL
          exact ⟨⟨H1, H2, H3⟩, fun E2 R' F' m' Hag2 HC Hfs =>
            HL E2 R' F' m'
              (env_agree_trans lo E E' E2 (env_agree_le lo hi E E' Hag H2) Hag2) HC Hfs⟩
      | JC j js sk b lo =>
          simp only [LCOK, lc_bnd] at HL Hag ⊢
          obtain ⟨⟨H1, H2, H3⟩, HL⟩ := HL
          exact ⟨⟨H1, H2, H3⟩, fun E2 R' F' m' Hag2 HC Hfs =>
            HL E2 R' F' m' (env_agree_trans b E E' E2 Hag Hag2) HC Hfs⟩

/-- `hw_apply` never invents entries. -/
theorem hw_apply_true_incl (r : List kentry) (a : saddr) (x : Nat) (K : kentry)
    (H : K ∈ hw_apply r a x true) : K ∈ r := by
  induction r with
  | nil => simp only [hw_apply, List.not_mem_nil] at H
  | cons X r ih =>
      cases X with
      | KWord a' w v =>
          cases hsb : saddr_eqb a' a with
          | true =>
              simp only [hw_apply, hsb, ite_true] at H
              exact List.mem_cons_of_mem _ (ih H)
          | false =>
              simp only [hw_apply, hsb, Bool.false_eq_true, ite_false, List.mem_cons] at H
              rcases H with rfl | H
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih H)
      | KZero a' n =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KBlob a' n bk =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KImg lo hi =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KAlign e m =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KRange e lo hi =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KWr a' n =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KDisj a1 n1 a2 n2 =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KFill a' n c =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)
      | KUnk a' n =>
          simp only [hw_apply, List.mem_cons] at H
          rcases H with rfl | H
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih H)

/-- `hw_apply` keeps the variable bound. -/
theorem hw_apply_true_vars (r : List kentry) (a : saddr) (x b : Nat)
    (H : AsanPlanCore.kn_vars_lt b r = true) :
    AsanPlanCore.kn_vars_lt b (hw_apply r a x true) = true := by
  induction r with
  | nil => rfl
  | cons X r ih =>
      simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at H
      obtain ⟨HX, Hr⟩ := H
      cases X with
      | KWord a' w v =>
          cases hsb : saddr_eqb a' a with
          | true =>
              simp only [hw_apply, hsb, ite_true]
              exact ih Hr
          | false =>
              simp only [hw_apply, hsb, Bool.false_eq_true, ite_false, AsanPlanCore.kn_vars_lt,
                Bool.and_eq_true]
              exact ⟨HX, ih Hr⟩
      | KZero a' n =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KBlob a' n bk =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KImg lo hi =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, AsanPlanCore.kentry_vars_lt,
            Bool.true_and]
          exact ih Hr
      | KAlign e m =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KRange e lo hi =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KWr a' n =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KDisj a1 n1 a2 n2 =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KFill a' n c =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩
      | KUnk a' n =>
          simp only [hw_apply, AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨HX, ih Hr⟩

/-- The running count of `kn_bigsubst` is the length of the big values. -/
theorem kn_bigsubst_len (K : Nat) (k : List kentry) (nx : Nat) :
    (kn_bigsubst K k nx).2 = (kn_bigexprs K k).length := by
  induction k generalizing nx with
  | nil => rfl
  | cons x r ih =>
      cases x with
      | KWord a w v =>
          by_cases hb : bigb K v = true
          · cases h : kn_bigsubst K r (nx + 1) with
            | mk r' c =>
                simp only [kn_bigsubst, hb, ite_true, kn_bigexprs, h, List.length_cons, Prod.snd]
                have hc : c = (kn_bigexprs K r).length := by
                  have h2 := ih (nx + 1)
                  rw [h] at h2
                  simpa only [Prod.snd] using h2
                omega
          · cases h : kn_bigsubst K r nx with
            | mk r' c =>
                simp only [kn_bigsubst, hb, ite_false, Bool.false_eq_true, kn_bigexprs, h, Prod.snd]
                have hc : c = (kn_bigexprs K r).length := by
                  have h2 := ih nx
                  rw [h] at h2
                  simpa only [Prod.snd] using h2
                exact hc
      | KZero a' n =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KBlob a' n bk =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KImg lo hi =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KAlign e m =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KRange e lo hi =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KWr a' n =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KDisj a1 n1 a2 n2 =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KFill a' n c =>
          cases h : kn_bigsubst K r nx with
          | mk r' c' =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2
      | KUnk a' n =>
          cases h : kn_bigsubst K r nx with
          | mk r' c =>
              simp only [kn_bigsubst, kn_bigexprs, h, Prod.snd]
              have h2 := ih nx
              rw [h] at h2
              simpa only [Prod.snd] using h2


/-! ### Reading registers back -/

/-- The 5-bit index of a small register number is non-zero. -/
theorem Z_to_bv_five_ne_zero (n : Nat) (Hn : 0 < n) (Hn32 : n < 32) :
    Z_to_bv 5 (n : Int) ≠ 0 := by
  intro h
  have h2 : bv_unsigned (Z_to_bv 5 (n : Int)) = 0 := by rw [h]; rfl
  have h3 : bv_unsigned (Z_to_bv 5 (n : Int)) = n := by
    simp only [bv_unsigned, Z_to_bv, BitVec.toNat_ofInt]
    omega
  omega

/-- A symbolic register reads back its concrete value. -/
theorem reg_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (n : Nat) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hn : 0 < n ∧ n < 32) :
    getr R (Z_to_bv 5 (n : Int)) = edenot E (AsanPlanCore.reg cs n) := by
  rw [HC.co_regs]
  have h0 : bv_eqb (Z_to_bv 5 (n : Int)) 0 = false :=
    bv_eqb_neq _ _ (Z_to_bv_five_ne_zero n Hn.1 Hn.2)
  simp only [sr_get, h0, Bool.false_eq_true, ite_false, AsanPlanCore.reg, ridx_lit n Hn.2]

/-- The literal reading of a plain literal. -/
theorem lit_of_sound (E : env) (e : expr) (z : Int) (H : lit_of e = some z) :
    edenot E e = Z_to_bv 64 z ∧ 0 ≤ z ∧ z < two64 := by
  cases e with
  | ELit z' =>
      simp only [lit_of, Option.some.injEq] at H
      subst H
      refine ⟨?_, Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
      show Z_to_bv 64 z' = Z_to_bv 64 (z' % two64)
      exact (Z_to_bv_emod64 z').symm
  | EVar n => simp only [lit_of] at H; cases H
  | EAlu op a b => simp only [lit_of] at H; cases H
  | EAluw op a b => simp only [lit_of] at H; cases H
  | EMd op a b => simp only [lit_of] at H; cases H
  | EMdw op a b => simp only [lit_of] at H; cases H
  | EExt sx lo n a => simp only [lit_of] at H; cases H
  | EBlob sx k i n => simp only [lit_of] at H; cases H

/-- The literal reading of a register. -/
theorem reg_lit_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (n : Nat) (z : Int) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hn : 0 < n ∧ n < 32) (H : reg_lit cs n = some z) :
    getr R (Z_to_bv 5 (n : Int)) = Z_to_bv 64 z ∧ 0 ≤ z ∧ z < two64 := by
  obtain ⟨He, Hz1, Hz2⟩ := lit_of_sound E (reg cs n) z H
  rw [reg_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model n HC Hn, He]
  exact ⟨rfl, Hz1, Hz2⟩

/-- Respelling a register's expression. -/
theorem regs_ok_respell (E : env) (sr : List expr) (R : BvMap word) (n : Nat) (e : expr)
    (HR : regs_ok E sr R) (Hn : 0 < n ∧ n < 32)
    (He : edenot E e = edenot E (sr.getD n (.ELit 0))) :
    regs_ok E (sr_upd sr n e) R := by
  rw [show n = ridx (Z_to_bv 5 (n : Int)) from (ridx_lit n Hn.2).symm]
  refine regs_ok_pin E sr R (Z_to_bv 5 (n : Int)) e HR ?_
  rw [HR (Z_to_bv 5 (n : Int))]
  have h0 : bv_eqb (Z_to_bv 5 (n : Int)) 0 = false :=
    bv_eqb_neq _ _ (Z_to_bv_five_ne_zero n Hn.1 Hn.2)
  simp only [sr_get, h0, Bool.false_eq_true, ite_false, ridx_lit n Hn.2]
  exact He.symm

/-- Setting a register to a new value. -/
theorem regs_ok_set_n (E : env) (sr : List expr) (R : BvMap word) (n : Nat) (e : expr)
    (v : word) (HR : regs_ok E sr R) (Hn : 0 < n ∧ n < 32) (He : edenot E e = v) :
    regs_ok E (sr_upd sr n e) (regupd R (Z_to_bv 5 (n : Int)) v) := by
  rw [show n = ridx (Z_to_bv 5 (n : Int)) from (ridx_lit n Hn.2).symm]
  simp only [ridx_roundtrip]
  exact regs_ok_set E sr R (Z_to_bv 5 (n : Int)) v e HR
    (Z_to_bv_five_ne_zero n Hn.1 Hn.2) He


/-! ### Knowledge bounds: `xlo1`/`xhi1` -/

theorem xlo1_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (lo : Int) (HK : know_ok segs E M k)
    (H : xlo1 k e = some lo) : lo ≤ bv_unsigned (edenot E e) := by
  cases e with
  | ELit z =>
      simp only [xlo1, Option.some.injEq] at H
      subst H
      rw [edenot, zlit64_eq, u_lit64]
      exact Int.le_refl _
  | EVar n =>
      simp only [xlo1] at H
      cases he : erange k (.EVar n) with
      | none =>
          cases hb : lin_brange k (.EVar n) with
          | none =>
              cases hs : lin_srange k (.EVar n) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EVar n) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EVar n) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EVar n) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EVar n) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EVar n) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EVar n) l2 h2 HK hb).1
              omega
  | EAlu op a b =>
      simp only [xlo1] at H
      cases he : erange k (.EAlu op a b) with
      | none =>
          cases hb : lin_brange k (.EAlu op a b) with
          | none =>
              cases hs : lin_srange k (.EAlu op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EAlu op a b) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EAlu op a b) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EAlu op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAlu op a b) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAlu op a b) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EAlu op a b) l2 h2 HK hb).1
              omega
  | EAluw op a b =>
      simp only [xlo1] at H
      cases he : erange k (.EAluw op a b) with
      | none =>
          cases hb : lin_brange k (.EAluw op a b) with
          | none =>
              cases hs : lin_srange k (.EAluw op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EAluw op a b) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EAluw op a b) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EAluw op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAluw op a b) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAluw op a b) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EAluw op a b) l2 h2 HK hb).1
              omega
  | EMd op a b =>
      simp only [xlo1] at H
      cases he : erange k (.EMd op a b) with
      | none =>
          cases hb : lin_brange k (.EMd op a b) with
          | none =>
              cases hs : lin_srange k (.EMd op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EMd op a b) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EMd op a b) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EMd op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMd op a b) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMd op a b) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EMd op a b) l2 h2 HK hb).1
              omega
  | EMdw op a b =>
      simp only [xlo1] at H
      cases he : erange k (.EMdw op a b) with
      | none =>
          cases hb : lin_brange k (.EMdw op a b) with
          | none =>
              cases hs : lin_srange k (.EMdw op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EMdw op a b) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EMdw op a b) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EMdw op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMdw op a b) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMdw op a b) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EMdw op a b) l2 h2 HK hb).1
              omega
  | EExt sx w m a =>
      simp only [xlo1] at H
      cases he : erange k (.EExt sx w m a) with
      | none =>
          cases hb : lin_brange k (.EExt sx w m a) with
          | none =>
              cases hs : lin_srange k (.EExt sx w m a) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EExt sx w m a) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EExt sx w m a) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EExt sx w m a) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EExt sx w m a) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EExt sx w m a) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EExt sx w m a) l2 h2 HK hb).1
              omega
  | EBlob sx kk i m =>
      simp only [xlo1] at H
      cases he : erange k (.EBlob sx kk i m) with
      | none =>
          cases hb : lin_brange k (.EBlob sx kk i m) with
          | none =>
              cases hs : lin_srange k (.EBlob sx kk i m) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EBlob sx kk i m) l3 h3 HK hs).1
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EBlob sx kk i m) l2 h2 HK hb).1
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EBlob sx kk i m) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EBlob sx kk i m) l1 h1 HK he).1
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EBlob sx kk i m) l1 h1 HK he).1
              have h2' := (lin_brange_sound segs E M k (.EBlob sx kk i m) l2 h2 HK hb).1
              omega

theorem xhi1_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (hi : Int) (HK : know_ok segs E M k)
    (H : xhi1 k e = some hi) : bv_unsigned (edenot E e) ≤ hi := by
  cases e with
  | ELit z =>
      simp only [xhi1, Option.some.injEq] at H
      subst H
      rw [edenot, zlit64_eq, u_lit64]
      exact Int.le_refl _
  | EVar n =>
      simp only [xhi1] at H
      cases he : erange k (.EVar n) with
      | none =>
          cases hb : lin_brange k (.EVar n) with
          | none =>
              cases hs : lin_srange k (.EVar n) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EVar n) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EVar n) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EVar n) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EVar n) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EVar n) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EVar n) l2 h2 HK hb).2
              omega
  | EAlu op a b =>
      simp only [xhi1] at H
      cases he : erange k (.EAlu op a b) with
      | none =>
          cases hb : lin_brange k (.EAlu op a b) with
          | none =>
              cases hs : lin_srange k (.EAlu op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EAlu op a b) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EAlu op a b) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EAlu op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAlu op a b) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAlu op a b) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EAlu op a b) l2 h2 HK hb).2
              omega
  | EAluw op a b =>
      simp only [xhi1] at H
      cases he : erange k (.EAluw op a b) with
      | none =>
          cases hb : lin_brange k (.EAluw op a b) with
          | none =>
              cases hs : lin_srange k (.EAluw op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EAluw op a b) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EAluw op a b) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EAluw op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAluw op a b) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EAluw op a b) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EAluw op a b) l2 h2 HK hb).2
              omega
  | EMd op a b =>
      simp only [xhi1] at H
      cases he : erange k (.EMd op a b) with
      | none =>
          cases hb : lin_brange k (.EMd op a b) with
          | none =>
              cases hs : lin_srange k (.EMd op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EMd op a b) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EMd op a b) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EMd op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMd op a b) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMd op a b) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EMd op a b) l2 h2 HK hb).2
              omega
  | EMdw op a b =>
      simp only [xhi1] at H
      cases he : erange k (.EMdw op a b) with
      | none =>
          cases hb : lin_brange k (.EMdw op a b) with
          | none =>
              cases hs : lin_srange k (.EMdw op a b) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EMdw op a b) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EMdw op a b) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EMdw op a b) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMdw op a b) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EMdw op a b) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EMdw op a b) l2 h2 HK hb).2
              omega
  | EExt sx w m a =>
      simp only [xhi1] at H
      cases he : erange k (.EExt sx w m a) with
      | none =>
          cases hb : lin_brange k (.EExt sx w m a) with
          | none =>
              cases hs : lin_srange k (.EExt sx w m a) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EExt sx w m a) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EExt sx w m a) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EExt sx w m a) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EExt sx w m a) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EExt sx w m a) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EExt sx w m a) l2 h2 HK hb).2
              omega
  | EBlob sx kk i m =>
      simp only [xhi1] at H
      cases he : erange k (.EBlob sx kk i m) with
      | none =>
          cases hb : lin_brange k (.EBlob sx kk i m) with
          | none =>
              cases hs : lin_srange k (.EBlob sx kk i m) with
              | none =>
                  simp only [he, hb, hs] at H
                  exact absurd H (by simp)
              | some p =>
                  obtain ⟨l3, h3⟩ := p
                  simp only [he, hb, hs] at H
                  injection H with hH
                  have h3' := (lin_srange_sound segs E M k (.EBlob sx kk i m) l3 h3 HK hs).2
                  omega
          | some p =>
              obtain ⟨l2, h2⟩ := p
              simp only [he, hb] at H
              injection H with hH
              have h2' := (lin_brange_sound segs E M k (.EBlob sx kk i m) l2 h2 HK hb).2
              omega
      | some p =>
          obtain ⟨l1, h1⟩ := p
          cases hb : lin_brange k (.EBlob sx kk i m) with
          | none =>
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EBlob sx kk i m) l1 h1 HK he).2
              omega
          | some p2 =>
              obtain ⟨l2, h2⟩ := p2
              simp only [he, hb] at H
              injection H with hH
              have h1' := (erange_sound segs E M k (.EBlob sx kk i m) l1 h1 HK he).2
              have h2' := (lin_brange_sound segs E M k (.EBlob sx kk i m) l2 h2 HK hb).2
              omega


/-! ### Knowledge bounds: `AsanPlanCore.deand`, `xb2` and their projections -/

/-- The two copies of `deand` agree (helper). -/
theorem deand_eq_ax (e : expr) : AsanPlanCore.deand e = AxSymExec3.deand e := by
  induction e with
  | ELit z => rfl
  | EVar n => rfl
  | EAluw op a b iha ihb => rfl
  | EMd op a b iha ihb => rfl
  | EMdw op a b iha ihb => rfl
  | EExt sx w m a iha => rfl
  | EBlob sx kk i m => rfl
  | EAlu op a b iha ihb =>
      cases op with
      | ADD =>
          simp only [AsanPlanCore.deand, AxSymExec3.deand, iha, ihb]
      | AND =>
          cases b with
          | ELit m =>
              simp only [AsanPlanCore.deand, AxSymExec3.deand, iha]
          | EVar n => rfl
          | EAlu op' a' b' => rfl
          | EAluw op' a' b' => rfl
          | EMd op' a' b' => rfl
          | EMdw op' a' b' => rfl
          | EExt sx w m a' => rfl
          | EBlob sx kk i m => rfl
      | SUB => rfl
      | SLL => rfl
      | SLT => rfl
      | SLTU => rfl
      | XOR => rfl
      | SRL => rfl
      | SRA => rfl
      | OR => rfl

/-- The bit-mask residue decomposition of `AsanPlanCore.deand`. -/
theorem deand_sound (E : env) (e e' : expr) (s : Int) (Hd : AsanPlanCore.deand e = (e', s)) :
    0 ≤ s ∧ ∃ rho : Int, 0 ≤ rho ∧ rho ≤ s ∧
      bv_unsigned (edenot E e) =
        (bv_unsigned (edenot E e') - rho) % 2 ^ 64 := by
  have Hd' : AxSymExec3.deand e = (e', s) := by rw [← deand_eq_ax]; exact Hd
  obtain ⟨hs, rho, ⟨h0, h1⟩, heqm⟩ := AxSymExec3Sound.deand_sound E e e' s Hd'
  refine ⟨hs, rho, h0, h1, ?_⟩
  obtain ⟨q, hq⟩ := heqm
  have ha0 : 0 ≤ bv_unsigned (edenot E e) := (u64_range (edenot E e)).1
  have ha1 : bv_unsigned (edenot E e) < 2 ^ 64 := (u64_range (edenot E e)).2
  have hmod : bv_unsigned (edenot E e) % 2 ^ 64 =
      (bv_unsigned (edenot E e') - rho) % 2 ^ 64 := by
    rw [hq, Int.add_mul_emod_self_right]
  rwa [Int.emod_eq_of_lt ha0 ha1] at hmod

/-- A power-of-two mask keeps the variable bound. -/
theorem deand_vars (bnd : Nat) (e e' : expr) (s : Int) (Hd : AsanPlanCore.deand e = (e', s))
    (Hv : AsanPlanCore.expr_vars_lt bnd e = true) :
    AsanPlanCore.expr_vars_lt bnd e' = true := by
  induction e generalizing e' s with
  | ELit z => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EVar n => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EAluw op a b iha ihb =>
      simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EMd op a b iha ihb =>
      simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EMdw op a b iha ihb =>
      simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EExt sx w m a iha =>
      simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EBlob sx kk i m =>
      simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv
  | EAlu op a b iha ihb =>
      have Hv0 : AsanPlanCore.expr_vars_lt bnd (.EAlu op a b) = true := Hv
      simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at Hv
      obtain ⟨Hva, Hvb⟩ := Hv
      obtain ⟨a', s1, Ha⟩ : ∃ (a' : expr) (s1 : Int), AsanPlanCore.deand a = (a', s1) :=
        ⟨(AsanPlanCore.deand a).1, (AsanPlanCore.deand a).2, rfl⟩
      cases op with
      | ADD =>
          obtain ⟨b', s2, Hb⟩ : ∃ (b' : expr) (s2 : Int), AsanPlanCore.deand b = (b', s2) :=
            ⟨(AsanPlanCore.deand b).1, (AsanPlanCore.deand b).2, rfl⟩
          simp only [AsanPlanCore.deand, Ha, Hb, Prod.mk.injEq] at Hd
          obtain ⟨rfl, -⟩ := Hd
          simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true]
          exact ⟨iha a' s1 Ha Hva, ihb b' s2 Hb Hvb⟩
      | AND =>
          cases b with
          | ELit m =>
              simp only [AsanPlanCore.deand, Ha] at Hd
              split at Hd
              · simp only [Prod.mk.injEq] at Hd
                obtain ⟨rfl, -⟩ := Hd
                exact iha a' s1 Ha Hva
              · simp only [Prod.mk.injEq] at Hd
                obtain ⟨rfl, -⟩ := Hd
                exact Hv0
          | EVar n =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EAlu op' a' b' =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EAluw op' a' b' =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EMd op' a' b' =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EMdw op' a' b' =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EExt sx w m a'' =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
          | EBlob sx kk i m =>
              simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SUB => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SLL => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SLT => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SLTU => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | XOR => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SRL => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | SRA => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0
      | OR => simp only [AsanPlanCore.deand, Prod.mk.injEq] at Hd; obtain ⟨rfl, -⟩ := Hd; exact Hv0

/-- Two-sided bounds from `xb2`. -/
theorem xb2_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (lo hi : Int) (HK : know_ok segs E M k)
    (H : xb2 k e = some (lo, hi)) :
    lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
  have HP : ∀ l h : Int, (match xlo1 k e, xhi1 k e with
      | some l0, some h0 => some (l0, h0)
      | _, _ => none) = some (l, h) →
      l ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ h := by
    intro l h Hp
    cases h1 : xlo1 k e with
    | none => simp only [h1] at Hp; cases Hp
    | some l0 =>
        cases h2 : xhi1 k e with
        | none => simp only [h1, h2] at Hp; cases Hp
        | some h0 =>
            simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at Hp
            obtain ⟨rfl, rfl⟩ := Hp
            exact ⟨xlo1_sound segs E M k e l0 HK h1, xhi1_sound segs E M k e h0 HK h2⟩
  obtain ⟨e', s, Hd⟩ : ∃ (e' : expr) (s : Int), AsanPlanCore.deand e = (e', s) :=
    ⟨(AsanPlanCore.deand e).1, (AsanPlanCore.deand e).2, rfl⟩
  by_cases hs0 : (s == 0) = true
  · simp only [xb2, Hd, hs0, ite_eq_left] at H
    exact HP lo hi H
  · simp only [xb2, Hd, hs0, Bool.false_eq_true, ite_eq_right, ite_false] at H
    cases h1 : xlo1 k e' with
    | none => simp only [h1] at H; exact HP lo hi H
    | some lo' =>
        cases h2 : xhi1 k e' with
        | none => simp only [h1, h2] at H; exact HP lo hi H
        | some hi' =>
            by_cases hsl : s ≤ lo'
            · simp only [h1, h2, hsl, ite_eq_left] at H
              obtain ⟨hs0', rho, hrho0, hrhos, hE⟩ := deand_sound E e e' s Hd
              have HL : lo' ≤ bv_unsigned (edenot E e') := xlo1_sound segs E M k e' lo' HK h1
              have HH : bv_unsigned (edenot E e') ≤ hi' := xhi1_sound segs E M k e' hi' HK h2
              have h1' : 0 ≤ bv_unsigned (edenot E e') - rho := by
                clear hE
                omega
              have h2' : bv_unsigned (edenot E e') - rho < 2 ^ 64 := by
                clear hE
                have hb : bv_unsigned (edenot E e') < 2 ^ 64 := (u64_range (edenot E e')).2
                omega
              have hval : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho := by
                rw [hE, Int.emod_eq_of_lt h1' h2']
              have HGEN : ∀ (P : Option (Int × Int)) (l h a b : Int),
                  a ≤ bv_unsigned (edenot E e) → bv_unsigned (edenot E e) ≤ b →
                  (∀ l0 h0, P = some (l0, h0) →
                    l0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ h0) →
                  (match P with
                    | some (l0, h0) => some (max l0 a, min h0 b)
                    | none => some (a, b)) = some (l, h) →
                  l ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ h := by
                intro P l h a b ha hb HP' Heq
                cases P with
                | none =>
                    simp only [Option.some.injEq, Prod.mk.injEq] at Heq
                    obtain ⟨rfl, rfl⟩ := Heq
                    exact ⟨ha, hb⟩
                | some p =>
                    obtain ⟨l0, h0⟩ := p
                    simp only [Option.some.injEq, Prod.mk.injEq] at Heq
                    obtain ⟨rfl, rfl⟩ := Heq
                    obtain ⟨Hb1, Hb2⟩ := HP' l0 h0 rfl
                    exact ⟨by omega, by omega⟩
              refine HGEN (match xlo1 k e, xhi1 k e with
                  | some l0, some h0 => some (l0, h0)
                  | _, _ => none) lo hi (lo' - s) hi' ?_ ?_ HP H
              · omega
              · omega
            · simp only [h1, h2, hsl, ite_eq_right] at H
              exact HP lo hi H

/-- The lower bound from `xlo2`. -/
theorem xlo2_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (lo : Int) (HK : know_ok segs E M k)
    (H : xlo2 k e = some lo) : lo ≤ bv_unsigned (edenot E e) := by
  simp only [xlo2] at H
  cases hb : xb2 k e with
  | none => simp only [hb] at H; cases H
  | some p =>
      obtain ⟨l, h⟩ := p
      simp only [hb, Option.some.injEq] at H
      subst H
      exact (xb2_sound segs E M k e l h HK hb).1

/-- The upper bound from `xhi2`. -/
theorem xhi2_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (hi : Int) (HK : know_ok segs E M k)
    (H : xhi2 k e = some hi) : bv_unsigned (edenot E e) ≤ hi := by
  simp only [xhi2] at H
  cases hb : xb2 k e with
  | none => simp only [hb] at H; cases H
  | some p =>
      obtain ⟨l, h⟩ := p
      simp only [hb, Option.some.injEq] at H
      subst H
      exact (xb2_sound segs E M k e l h HK hb).2


/-! ### The prepared apartness tests versus the reference ones -/

/-- `kentry_apart_b` implies the semantic footprint apartness. -/
theorem kentry_apart_b_sem (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) (K : kentry) (ub : expr) (uk : Int) (un : expr)
    (Hall : know_ok segs E M allkn) (Hb : kentry_apart_b allkn ub uk un K = true) :
    kfoot_apart E K (estart E (SA ub uk)) (elenZ E un) := by
  cases K with
  | KWord a w v =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b, Bool.and_eq_true] at Hb
      obtain ⟨Hw, Hb⟩ := Hb
      have Hw8 : w ≤ 8 := of_decide_eq_true Hw
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k (.ELit (w : Int)) Hall Hb
      have hlen : elenZ E (.ELit (w : Int)) = (w : Int) :=
        elenZ_lit E (w : Int) ⟨by omega, by omega⟩
      simp only [kfoot_apart, kfoot, hlen] at Hd ⊢
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KZero a nn =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b] at Hb
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k nn Hall Hb
      simp only [kfoot_apart, kfoot]
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KBlob a nn bk =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b] at Hb
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k nn Hall Hb
      simp only [kfoot_apart, kfoot]
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KImg lo hi =>
      simp only [kentry_apart_b, Bool.and_eq_true] at Hb
      obtain ⟨⟨⟨H0, Hle⟩, Hlt⟩, Hap⟩ := Hb
      have h0 : 0 ≤ lo := of_decide_eq_true H0
      have hle : lo ≤ hi := of_decide_eq_true Hle
      have hlt : hi - lo < two64 := of_decide_eq_true Hlt
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un (.ELit 0) lo
        (.ELit (hi - lo)) Hall Hap
      have hstart : estart E (SA (.ELit 0) lo) = lo := by
        simp only [estart, edenot_lit, u_lit0, Int.zero_add]
      have hlen : elenZ E (.ELit (hi - lo)) = hi - lo :=
        elenZ_lit E (hi - lo) ⟨by omega, by simpa only [two64] using hlt⟩
      simp only [kfoot_apart, kfoot, hstart, hlen] at Hd ⊢
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KAlign e m => simp only [kentry_apart_b] at Hb; simp only [kfoot_apart, kfoot]
  | KRange e lo hi => simp only [kentry_apart_b] at Hb; simp only [kfoot_apart, kfoot]
  | KWr a nn =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b] at Hb
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k nn Hall Hb
      simp only [kfoot_apart, kfoot]
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KDisj a1 n1 a2 n2 => simp only [kentry_apart_b] at Hb; simp only [kfoot_apart, kfoot]
  | KFill a nn c =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b] at Hb
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k nn Hall Hb
      simp only [kfoot_apart, kfoot]
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h
  | KUnk a nn =>
      obtain ⟨b, k⟩ := a
      simp only [kentry_apart_b] at Hb
      have Hd := ranges_apart_x_sound segs E M allkn ub uk un b k nn Hall Hb
      simp only [kfoot_apart, kfoot]
      rcases Hd with h | h
      · exact Or.inr h
      · exact Or.inl h


/-- The `toNat`-cast and `bv_unsigned` spellings of a word are the same
    integer (`omega` and `rw` see the two spellings as
    different atoms, so the proofs convert explicitly). -/
theorem toNat_cast_eq_bv_unsigned (a : word) : ((a.toNat : Int)) = bv_unsigned a := rfl

/-- The other direction of `toNat_cast_eq_bv_unsigned` (helper). -/
theorem bv_unsigned_eq_toNat_cast (a : word) : bv_unsigned a = ((a.toNat : Int)) := rfl

/-- `wview` only looks at the byte it is asked about (helper). -/
theorem wview_congr' (segs : List Segment) (M M' : word → Option byte) (x : word)
    (h : M' x = M x) : wview segs M' x = wview segs M x := by
  unfold wview
  rw [h]

/-- A knowledge entry survives a memory change outside its footprint. -/
theorem kentry_keep_sem (segs : List Segment) (E : env) (M M' : word → Option byte)
    (K : kentry) (lo n : Int) (HK : kentry_ok segs E M K)
    (Hap : kfoot_apart E K lo n)
    (Hout : ∀ x : word, bv_unsigned x < lo ∨ lo + n ≤ bv_unsigned x → M' x = M x) :
    kentry_ok segs E M' K := by
  have RD : ∀ (a : word) (k : Nat), ((a.toNat : Int)) + (k : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (bv_unsigned a + (k : Int) ≤ lo ∨ lo + n ≤ bv_unsigned a) →
      rdn segs M' a k = rdn segs M a k := by
    intro a k Hnw Hd
    refine rdn_ext segs k M' M a Hnw ?_
    intro x Hx
    obtain ⟨h1, h2⟩ := Hx
    apply Hout
    simp only [bv_unsigned] at h1 h2 Hd ⊢
    rcases Hd with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  cases K with
  | KWord a w v =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hw, Hfl, Hrd⟩ := HK
      refine ⟨Hw, Hfl, ?_⟩
      have hu : bv_unsigned (adenot E a) = estart E a :=
        flat_u E a (w : Int) Hfl
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      have hb : bv_unsigned (adenot E a) + (w : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hu, Int.natCast_pow]
        omega
      have hap : bv_unsigned (adenot E a) + (w : Int) ≤ lo ∨
          lo + n ≤ bv_unsigned (adenot E a) := by
        rw [hu]
        exact Hap
      rw [RD (adenot E a) w hb hap]
      exact Hrd
  | KZero a nn =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hfl, Hz⟩ := HK
      refine ⟨Hfl, ?_⟩
      intro i Hi0 Hilen
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
        u_small (estart E a + i) ⟨by omega, by omega⟩
      have hap : bv_unsigned (Z_to_bv 64 (estart E a + i)) < lo ∨
          lo + n ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
        rw [hx]
        rcases Hap with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [Hout _ hap]
      exact Hz i Hi0 Hilen
  | KBlob a nn bk =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hfl, Hlen, Hz⟩ := HK
      refine ⟨Hfl, Hlen, ?_⟩
      intro i Hi0 Hilen
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
        u_small (estart E a + i) ⟨by omega, by omega⟩
      have hap : bv_unsigned (Z_to_bv 64 (estart E a + i)) < lo ∨
          lo + n ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
        rw [hx]
        rcases Hap with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [Hout _ hap]
      exact Hz i Hi0 Hilen
  | KImg lo' hi' =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨HB0, HB1, HC⟩ := HK
      refine ⟨HB0, HB1, ?_⟩
      intro i Hi1 Hi2
      have hx : bv_unsigned (Z_to_bv 64 i) = i := u_small i ⟨by omega, by omega⟩
      have hap : bv_unsigned (Z_to_bv 64 i) < lo ∨ lo + n ≤ bv_unsigned (Z_to_bv 64 i) := by
        rw [hx]
        rcases Hap with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [Hout _ hap]
      exact HC i Hi1 Hi2
  | KAlign e m => exact HK
  | KRange e lo' hi' => exact HK
  | KWr a nn =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hfl, Hs⟩ := HK
      refine ⟨Hfl, ?_⟩
      intro d m Hd0 Hdm
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      cases m with
      | zero => rfl
      | succ m' =>
          have hx : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d :=
            u_small (estart E a + d) ⟨by omega, by omega⟩
          have hbnd : bv_unsigned (Z_to_bv 64 (estart E a + d)) + ((m' + 1 : Nat) : Int)
              ≤ ((2 ^ 64 : Nat) : Int) := by
            rw [hx, Int.natCast_pow]
            omega
          refine StoreOk.store_ok_of_all segs M' (m' + 1)
            (Z_to_bv 64 (estart E a + d)) hbnd ?_
          intro x h1 h2
          have h1' : bv_unsigned x ≥ bv_unsigned (Z_to_bv 64 (estart E a + d)) := by
            simpa only [toNat_cast_eq_bv_unsigned] using h1
          have h2' : bv_unsigned x < bv_unsigned (Z_to_bv 64 (estart E a + d))
              + ((m' + 1 : Nat) : Int) := by
            simpa only [toNat_cast_eq_bv_unsigned] using h2
          have hxM : M' x = M x := by
            apply Hout
            rw [hx] at h1' h2'
            rcases Hap with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          rw [wview_congr' segs M M' x hxM]
          exact StoreOk.store_ok_all segs M (m' + 1) (Z_to_bv 64 (estart E a + d))
            (by simpa only [toNat_cast_eq_bv_unsigned] using hbnd)
            (Hs d ((m' : Nat) + 1) Hd0 Hdm) x h1 h2
  | KDisj a1 n1 a2 n2 => exact HK
  | KFill a nn c =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hfl, Hz⟩ := HK
      refine ⟨Hfl, ?_⟩
      intro i Hi0 Hilen
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
        u_small (estart E a + i) ⟨by omega, by omega⟩
      have hap : bv_unsigned (Z_to_bv 64 (estart E a + i)) < lo ∨
          lo + n ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
        rw [hx]
        rcases Hap with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [Hout _ hap]
      exact Hz i Hi0 Hilen
  | KUnk a nn =>
      simp only [kfoot_apart, kfoot] at Hap
      obtain ⟨Hfl, Hz⟩ := HK
      refine ⟨Hfl, ?_⟩
      intro i Hi0 Hilen
      obtain ⟨F1, F2, F3, F4⟩ := Hfl
      have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
        u_small (estart E a + i) ⟨by omega, by omega⟩
      have hap : bv_unsigned (Z_to_bv 64 (estart E a + i)) < lo ∨
          lo + n ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
        rw [hx]
        rcases Hap with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      rw [Hout _ hap]
      exact Hz i Hi0 Hilen


/-- `kentry_apart_b` plus the outside-change hypothesis keeps an entry. -/
theorem kentry_apart_keep (segs : List Segment) (E : env) (M M' : word → Option byte)
    (allkn : List kentry) (K : kentry) (ub : expr) (uk : Int) (un : expr)
    (Hall : know_ok segs E M allkn) (HK : kentry_ok segs E M K)
    (Hb : kentry_apart_b allkn ub uk un K = true)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA ub uk) ∨
      estart E (SA ub uk) + elenZ E un ≤ bv_unsigned x → M' x = M x) :
    kentry_ok segs E M' K :=
  kentry_keep_sem segs E M M' K _ _ HK
    (kentry_apart_b_sem segs E M allkn K ub uk un Hall Hb) Hout

/-- Filtering a knowledge list by a predicate that either proves the entry
    apart or preserves it. -/
theorem know_ok_filter_apart (segs : List Segment) (E : env) (M M' : word → Option byte)
    (k : List kentry) (f : kentry → Bool) (ub : expr) (uk : Int) (un : expr)
    (HK : know_ok segs E M k)
    (Hf : ∀ K, K ∈ k → f K = true →
      kentry_apart_b k ub uk un K = true ∨ kentry_ok segs E M' K)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA ub uk) ∨
      estart E (SA ub uk) + elenZ E un ≤ bv_unsigned x → M' x = M x) :
    know_ok segs E M' (k.filter f) := by
  intro K hK
  obtain ⟨hKk, hKf⟩ := List.mem_filter.mp hK
  rcases Hf K hKk (by simpa using hKf) with h | h
  · exact kentry_apart_keep segs E M M' k K ub uk un HK (HK K hKk) h Hout
  · exact h


/-- The residue fact of `PFresh`. -/
theorem residue_fact_sound (segs : List Segment) (E E' : env)
    (M M' : word → Option byte) (k : List kentry) (e ne : expr)
    (HK : know_ok segs E M k) (Hne : edenot E' ne = edenot E e)
    (Hag : ∀ (e' : expr) (s : Int), AsanPlanCore.deand e = (e', s) →
      edenot E' e' = edenot E e') :
    know_ok segs E' M' (residue_fact k e ne) := by
  obtain ⟨e', s, Hd⟩ : ∃ (e' : expr) (s : Int), AsanPlanCore.deand e = (e', s) :=
    ⟨(AsanPlanCore.deand e).1, (AsanPlanCore.deand e).2, rfl⟩
  intro K hK
  by_cases hs : 0 < s
  · cases h1 : xlo1 k e' with
    | none => simp only [residue_fact, Hd, ite_eq_left hs, h1] at hK; cases hK
    | some lo' =>
        cases h2 : xhi1 k e' with
        | none => simp only [residue_fact, Hd, ite_eq_left hs, h1, h2] at hK; cases hK
        | some hi' =>
            by_cases hsl : s ≤ lo'
            · simp only [residue_fact, Hd, ite_eq_left hs, h1, h2, ite_eq_left hsl,
                List.mem_singleton] at hK
              subst hK
              obtain ⟨hs0, rho, hrho0, hrhos, hE⟩ := deand_sound E e e' s Hd
              have HL : lo' ≤ bv_unsigned (edenot E e') :=
                xlo1_sound segs E M k e' lo' HK h1
              have h1' : 0 ≤ bv_unsigned (edenot E e') - rho := by
                clear hE
                omega
              have h2' : bv_unsigned (edenot E e') - rho < 2 ^ 64 := by
                clear hE
                have hb : bv_unsigned (edenot E e') < 2 ^ 64 := (u64_range (edenot E e')).2
                omega
              have hval : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho := by
                rw [hE, Int.emod_eq_of_lt h1' h2']
              have hsub : bv_unsigned (edenot E' (esub e' ne))
                  = (bv_unsigned (edenot E e') - bv_unsigned (edenot E e)) % 2 ^ 64 := by
                simp only [esub]
                rw [mkAlu_denot]
                rw [show alu64 AluOp.SUB (edenot E' e') (edenot E' ne)
                    = (edenot E' e' - edenot E' ne) from rfl]
                rw [u_sub64, Hag e' s Hd, Hne]
              have hinside : bv_unsigned (edenot E e')
                  - (bv_unsigned (edenot E e') - rho) = rho := by omega
              simp only [kentry_ok]
              rw [hsub, hval, hinside]
              have hrho_lt : rho < 2 ^ 64 := by
                have hb : bv_unsigned (edenot E e') < 2 ^ 64 := (u64_range (edenot E e')).2
                clear hE
                omega
              rw [Int.emod_eq_of_lt hrho0 hrho_lt]
              exact ⟨hrho0, hrhos⟩
            · simp only [residue_fact, Hd, ite_eq_left hs, h1, h2, ite_eq_right hsl] at hK; cases hK
  · simp only [residue_fact, Hd, ite_eq_right hs] at hK; cases hK

/-- A fact the knowledge entails is a knowledge entry. -/
theorem fact_ok_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (K : kentry) (HK : know_ok segs E M k)
    (H : fact_ok k K = true) : kentry_ok segs E M K := by
  cases K with
  | KAlign e m =>
      simp only [fact_ok, Bool.and_eq_true] at H
      obtain ⟨⟨H1, H2⟩, H3⟩ := H
      have hm0 : 0 < m := of_decide_eq_true H1
      have hm_eq : m = zpow 2 (zlog2 m) := beq_iff_eq.mp H2
      have hj : zlog2 m ≤ ealign k e := of_decide_eq_true H3
      refine ⟨hm0, ?_⟩
      obtain ⟨⟨hz0, hz64⟩, Hd⟩ := ealign_sound segs E M k e HK
      rw [hm_eq]
      exact Int.emod_eq_zero_of_dvd
        (Int.dvd_trans (pow2_divide_le (zlog2 m) (ealign k e) ⟨zlog2_nonneg m, hj⟩) Hd)
  | KRange e lo hi =>
      simp only [fact_ok] at H
      cases h1 : xlo2 k e with
      | none => simp only [h1] at H; cases H
      | some l =>
          cases h2 : xhi2 k e with
          | none => simp only [h1, h2] at H; cases H
          | some h =>
              simp only [h1, h2, Bool.and_eq_true] at H
              obtain ⟨H1, H2⟩ := H
              have hl : lo ≤ l := of_decide_eq_true H1
              have hh : h ≤ hi := of_decide_eq_true H2
              exact ⟨by
                have := xlo2_sound segs E M k e l HK h1
                omega, by
                have := xhi2_sound segs E M k e h HK h2
                omega⟩
  | KDisj a1 n1 a2 n2 =>
      obtain ⟨b1, k1⟩ := a1
      obtain ⟨b2, k2⟩ := a2
      simp only [fact_ok] at H
      exact ranges_apart_x_sound segs E M k b1 k1 n1 b2 k2 n2 HK H
  | KWord a w v => simp only [fact_ok] at H; cases H
  | KZero a n => simp only [fact_ok] at H; cases H
  | KBlob a n bk => simp only [fact_ok] at H; cases H
  | KImg lo hi => simp only [fact_ok] at H; cases H
  | KWr a n => simp only [fact_ok] at H; cases H
  | KFill a n c => simp only [fact_ok] at H; cases H
  | KUnk a n => simp only [fact_ok] at H; cases H

/-- Adding a fact the knowledge entails. -/
theorem fact_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (K : kentry) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : fact_ok (kn cs) K = true) :
    cs_ok segs A LIMIT SINV argH FS0 E (add_kn cs [K]) R FULL model := by
  unfold add_kn
  refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
  intro K' hK'
  rcases List.mem_append.mp hK' with h | h
  · simp only [List.mem_singleton] at h
    subst K'
    exact fact_ok_sound segs E (Mr A argH E cs model FULL) (kn cs) K HC.co_know H
  · exact HC.co_know K' h

/-! ### The prepared apartness tests equal the reference ones
     -/
theorem kentry_apart_bp_eq (allkn : List kentry) (ub : expr) (uk : Int) (un : expr)
    (K : kentry) :
    kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K
      = kentry_apart_b allkn ub uk un K := by
  cases K <;> simp only [kentry_apart_bp, kentry_apart_b, ranges_apart_p_eq]
theorem havoc1p_eq (k : List kentry) (ub : expr) (uk : Int) (un : expr) (K : kentry) :
    havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K := by
  unfold havoc1p havoc1
  rw [kentry_apart_bp_eq]
theorem cutout1p_eq (k : List kentry) (ub : expr) (uk : Int) (un : expr) (K : kentry) :
    cutout1p k (mk_sprep k ub uk un) ub uk un K = cutout1 k ub uk un K := by
  unfold cutout1p cutout1
  rw [kentry_apart_bp_eq]

/-! ### `pw_kind` at `KWr`, and the generalized cut -/

/-- A one-byte `store_ok` witnesses that the byte is writable (helper for `pw_kind_wr`): this tree gets this by `destruct`ing the `wview`
    inside `store_ok`'s successor branch. -/
theorem store_ok_one_wview (segs : List Segment) (M : word → Option byte) (a : word)
    (H : store_ok segs M a 1 = true) : wview segs M a ≠ none := by
  intro h
  rw [show store_ok segs M a 1 = false by simp only [store_ok, h]] at H
  cases H
theorem pw_kind_wr (segs : List Segment) :
    pw_kind segs .KWr (fun M x => wview segs M x ≠ none) := by
  intro E M a n
  constructor
  · rintro ⟨hfl, hst⟩
    exact ⟨hfl, fun i Hi => store_ok_one_wview segs M _ (hst i 1 Hi.1 (by omega))⟩
  · rintro ⟨hfl, hall⟩
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hfl
    refine ⟨⟨hf1, hf2, hf3, hf4⟩, ?_⟩
    intro d m hd0 hdm
    cases m with
    | zero => rfl
    | succ m' =>
        have hub : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d :=
          u_small (estart E a + d) ⟨by omega, by omega⟩
        have hm1 : (1 : Int) ≤ ((m' + 1 : Nat) : Int) := by
          rw [Int.natCast_add_one]; omega
        refine StoreOk.store_ok_of_all segs M (m' + 1) (Z_to_bv 64 (estart E a + d)) ?_ ?_
        · show ((Z_to_bv 64 (estart E a + d)).toNat : Int) + ((m' + 1 : Nat) : Int)
            ≤ ((2 ^ 64 : Nat) : Int)
          rw [toNat_cast_eq_bv_unsigned, hub]
          omega
        · intro x Hx1 Hx2
          have hx1 : estart E a + d ≤ bv_unsigned x := by
            rw [toNat_cast_eq_bv_unsigned] at Hx1
            rw [hub] at Hx1
            exact Hx1
          have hx2 : bv_unsigned x < estart E a + d + ((m' + 1 : Nat) : Int) := by
            rw [toNat_cast_eq_bv_unsigned (Z_to_bv 64 (estart E a + d))] at Hx2
            rw [hub] at Hx2
            exact Hx2
          have hxeq : Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a)) = x := by
            have harg : (x.toNat : Int) = estart E a + (bv_unsigned x - estart E a) := by
              rw [toNat_cast_eq_bv_unsigned]
              omega
            rw [← harg]
            exact AxSymExec3Sound.ofInt_toNat x
          rw [← hxeq]
          exact hall (bv_unsigned x - estart E a) ⟨by omega, by omega⟩
theorem know_ok_havoc (segs : List Segment) (E : env) (M M' : word → Option byte)
    (k : List kentry) (b n : expr) (o : Int) (HK : know_ok segs E M k)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b o) ∨
      estart E (SA b o) + elenZ E n ≤ bv_unsigned x → M' x = M x)
    (Hg : StoreOk.mem_grows M M') :
    know_ok segs E M' (kn_havoc k b o n) := by
  intro K hK
  simp only [kn_havoc] at hK
  rw [List.mem_flatMap] at hK
  obtain ⟨K0, hK0, hK1⟩ := hK
  rw [havoc1p_eq] at hK1
  have hK0' : kentry_ok segs E M K0 := HK K0 hK0
  by_cases hf : (kwr_b K0 || kentry_apart_b k b o n K0) = true
  · unfold havoc1 at hK1
    rw [ite_eq_left hf] at hK1
    rw [List.mem_singleton] at hK1
    subst hK1
    rw [Bool.or_eq_true] at hf
    rcases hf with hw | ha
    · cases K with
      | KWr a len =>
          obtain ⟨kb, kk⟩ := a
          obtain ⟨hfl, hst⟩ := hK0'
          refine ⟨hfl, ?_⟩
          intro d m hd0 hdm
          exact StoreOk.store_ok_mono segs m M M' _ Hg (hst d m hd0 hdm)
      | KWord a w v => simp only [kwr_b] at hw; cases hw
      | KZero a nn => simp only [kwr_b] at hw; cases hw
      | KBlob a nn bk => simp only [kwr_b] at hw; cases hw
      | KImg lo hi => simp only [kwr_b] at hw; cases hw
      | KAlign e m => simp only [kwr_b] at hw; cases hw
      | KRange e lo hi => simp only [kwr_b] at hw; cases hw
      | KDisj a1 n1 a2 n2 => simp only [kwr_b] at hw; cases hw
      | KFill a nn c => simp only [kwr_b] at hw; cases hw
      | KUnk a nn => simp only [kwr_b] at hw; cases hw
    · exact kentry_apart_keep segs E M M' k K b o n HK hK0' ha Hout
  · unfold havoc1 at hK1
    rw [ite_eq_right hf] at hK1
    cases K0 with
    | KZero a len =>
        obtain ⟨kb, kk⟩ := a
        exact kzero_cut_sound segs E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KFill a len c =>
        obtain ⟨kb, kk⟩ := a
        exact kfill_cut_sound segs c E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KUnk a len =>
        obtain ⟨kb, kk⟩ := a
        exact kunk_cut_sound segs E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KWord a w v => cases hK1
    | KBlob a nn bk => cases hK1
    | KImg lo hi => cases hK1
    | KAlign e m => cases hK1
    | KRange e lo hi => cases hK1
    | KDisj a1 n1 a2 n2 => cases hK1
    | KWr a nn => cases hK1
theorem droprange_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b n : expr) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 E (node_droprange cs b n) R FULL model := by
  obtain ⟨bb, bk, hsp⟩ : ∃ (bb : expr) (bk : Int), split_lit b = (bb, bk) :=
    ⟨(split_lit b).1, (split_lit b).2, rfl⟩
  have hnode : node_droprange cs b n = set_kn cs (kn_havoc (kn cs) bb bk n) := by
    unfold node_droprange
    rw [hsp]
  rw [hnode]
  refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
  exact know_ok_havoc segs E (Mr A argH E cs model FULL) (Mr A argH E cs model FULL)
    (kn cs) bb n bk HC.co_know (fun _ _ => rfl) (StoreOk.mem_grows_refl _)

/-! ### The generalized cut: `pw_kind` in place of `zf_kind`

    `kcut_sound` in `AxSymExec3Sound` is stated for the `KZero`/`KFill`/`KUnk`
    family (`zf_kind`); `KWR` needs the same argument with the byte predicate
    abstracted to `P`.  The three lemmas below are the `pw_kind` twins of
    `kcut_low_piece` / `kcut_high_piece` / `kcut_high_bounds`; the proofs are
    the `zf_kind` ones with the entry predicate `byteof (M x)` replaced by
    `P M x`. -/

/-- `kcut_low_piece` at `pw_kind`. -/
theorem kcut_low_piece_pw (segs : List Segment) (mk : saddr → expr → kentry)
    (P : (word → Option byte) → word → Prop) (E : env) (M M' : word → Option byte)
    (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hkind : pw_kind segs mk P)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → P M x → P M' x)
    (hB : bv_unsigned (edenot E kb) + kk ≤ bv_unsigned (edenot E wb) + wk)
    (hC : bv_unsigned (edenot E wb) + wk ≤ bv_unsigned (edenot E kb) + kk + elenZ E len) :
    kentry_ok segs E M' (mk (SA kb kk)
      (mkAlu .SUB (mkAlu .ADD wb (.ELit wk)) (mkAlu .ADD kb (.ELit kk)))) := by
  obtain ⟨Hfl, Hz⟩ := (Hkind E M (SA kb kk) len).1 HK
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
  have hk1 : 0 ≤ bv_unsigned (edenot E kb) + kk := Hk1
  have hk2 : bv_unsigned (edenot E kb) + kk < 2 ^ 64 := Hk2
  have hk4 : bv_unsigned (edenot E kb) + kk + elenZ E len ≤ 2 ^ 64 := Hk4
  have hlen_lt : elenZ E len < 2 ^ 64 := (u64_range (edenot E len)).2
  have hX : bv_unsigned (edenot E (mkAlu .ADD wb (.ELit wk)))
      = (bv_unsigned (edenot E wb) + wk) % 2 ^ 64 := by
    rw [mkAlu_denot]
    show bv_unsigned (edenot E wb + edenot E (.ELit wk))
      = (bv_unsigned (edenot E wb) + wk) % 2 ^ 64
    have hl : bv_unsigned (edenot E (.ELit wk)) = wk % 2 ^ 64 := u_lit64 wk
    rw [u_add64, hl, Int.add_emod_emod]
  have hY : bv_unsigned (edenot E (mkAlu .ADD kb (.ELit kk)))
      = (bv_unsigned (edenot E kb) + kk) % 2 ^ 64 := by
    rw [mkAlu_denot]
    show bv_unsigned (edenot E kb + edenot E (.ELit kk))
      = (bv_unsigned (edenot E kb) + kk) % 2 ^ 64
    have hl : bv_unsigned (edenot E (.ELit kk)) = kk % 2 ^ 64 := u_lit64 kk
    rw [u_add64, hl, Int.add_emod_emod]
  have hXr : eqm (bv_unsigned (edenot E (mkAlu .ADD wb (.ELit wk))))
      (bv_unsigned (edenot E wb) + wk) := by rw [hX]; exact eqm_mod _
  have hYr : eqm (bv_unsigned (edenot E (mkAlu .ADD kb (.ELit kk))))
      (bv_unsigned (edenot E kb) + kk) := by rw [hY]; exact eqm_mod _
  have hsub : eqm (bv_unsigned (edenot E (mkAlu .SUB (mkAlu .ADD wb (.ELit wk))
        (mkAlu .ADD kb (.ELit kk)))))
      ((bv_unsigned (edenot E wb) + wk) - (bv_unsigned (edenot E kb) + kk)) := by
    rw [mkAlu_denot]
    show eqm (bv_unsigned (edenot E (mkAlu .ADD wb (.ELit wk))
        - edenot E (mkAlu .ADD kb (.ELit kk)))) _
    have hneg : eqm (- bv_unsigned (edenot E (mkAlu .ADD kb (.ELit kk))))
        (- (bv_unsigned (edenot E kb) + kk)) := by
      obtain ⟨q, hq⟩ := hYr
      exact ⟨-q, by omega⟩
    exact eqm_trans (u_sub_eqm _ _) (eqm_add hXr hneg)
  have hXY0 : 0 ≤ (bv_unsigned (edenot E wb) + wk) - (bv_unsigned (edenot E kb) + kk) := by
    omega
  have hXY1 : (bv_unsigned (edenot E wb) + wk) - (bv_unsigned (edenot E kb) + kk) < 2 ^ 64 := by
    omega
  have HL : elenZ E (mkAlu .SUB (mkAlu .ADD wb (.ELit wk)) (mkAlu .ADD kb (.ELit kk)))
      = (bv_unsigned (edenot E wb) + wk) - (bv_unsigned (edenot E kb) + kk) := by
    show bv_unsigned (edenot E (mkAlu .SUB (mkAlu .ADD wb (.ELit wk))
      (mkAlu .ADD kb (.ELit kk)))) = _
    exact eqm_eq_of_range hsub (u64_range _).1 (u64_range _).2 hXY0 hXY1
  refine (Hkind E M' (SA kb kk)
    (mkAlu .SUB (mkAlu .ADD wb (.ELit wk)) (mkAlu .ADD kb (.ELit kk)))).2 ⟨?_, ?_⟩
  · rw [HL]
    exact ⟨hk1, hk2, hXY0, by omega⟩
  · rintro i ⟨Hi0, HiS⟩
    rw [HL] at HiS
    have hi0 : 0 ≤ bv_unsigned (edenot E kb) + kk + i := by omega
    have hilt : bv_unsigned (edenot E kb) + kk + i < 2 ^ 64 := by omega
    have hxi : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i))
        = bv_unsigned (edenot E kb) + kk + i := u_small (bv_unsigned (edenot E kb) + kk + i) ⟨hi0, hilt⟩
    show P M' (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i))
    have hout : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i))
          < estart E (SA wb wk) ∨
        estart E (SA wb wk) + elenZ E wn
          ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i)) := by
      rw [hxi]
      left
      show bv_unsigned (edenot E kb) + kk + i < bv_unsigned (edenot E wb) + wk
      omega
    exact Hout _ hout (Hz i ⟨Hi0, by omega⟩)

/-- `kcut_high_piece` at `pw_kind`. -/
theorem kcut_high_piece_pw (segs : List Segment) (mk : saddr → expr → kentry)
    (P : (word → Option byte) → word → Prop) (E : env) (M M' : word → Option byte)
    (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (ha : saddr) (L : expr)
    (Hkind : pw_kind segs mk P)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → P M x → P M' x)
    (Hst : estart E ha = estart E (SA wb wk) + elenZ E wn)
    (HL : elenZ E L = estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))
    (HE1 : estart E (SA kb kk) ≤ estart E (SA wb wk) + elenZ E wn)
    (HE2 : estart E (SA wb wk) + elenZ E wn ≤ estart E (SA kb kk) + elenZ E len)
    (HE3 : estart E (SA kb kk) + elenZ E len ≤ 2 ^ 64 - 1) :
    kentry_ok segs E M' (mk ha L) := by
  obtain ⟨Hfl, Hz⟩ := (Hkind E M (SA kb kk) len).1 HK
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
  have hk1 : 0 ≤ bv_unsigned (edenot E kb) + kk := Hk1
  have hW0 : 0 ≤ estart E (SA wb wk) + elenZ E wn := by omega
  have hW1 : estart E (SA wb wk) + elenZ E wn < 2 ^ 64 := by omega
  have hT0 : 0 ≤ estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn) := by
    omega
  have hT1 : estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn) < 2 ^ 64 := by
    omega
  refine (Hkind E M' ha L).2 ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Hst]; exact hW0
    · rw [Hst]; exact hW1
    · rw [HL]; exact hT0
    · rw [HL, Hst]; omega
  · rintro i ⟨Hi0, HiT⟩
    rw [HL] at HiT
    rw [Hst]
    have hi0 : 0 ≤ estart E (SA wb wk) + elenZ E wn + i := by omega
    have hilt : estart E (SA wb wk) + elenZ E wn + i < 2 ^ 64 := by omega
    have hxi : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i))
        = estart E (SA wb wk) + elenZ E wn + i := u_small (estart E (SA wb wk) + elenZ E wn + i) ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i))
          < estart E (SA wb wk) ∨
        estart E (SA wb wk) + elenZ E wn
          ≤ bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i)) := by
      rw [hxi]
      exact Or.inr (by omega)
    refine Hout _ hout ?_
    have hidx : estart E (SA wb wk) + elenZ E wn + i
        = estart E (SA kb kk)
          + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i) := by
      omega
    rw [hidx]
    exact Hz _ ⟨by omega, by omega⟩

/-- `kcut_high_bounds` at `pw_kind`. -/
theorem kcut_high_bounds_pw (segs : List Segment) (mk : saddr → expr → kentry)
    (P : (word → Option byte) → word → Prop) (E : env) (M0 M : word → Option byte)
    (allkn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr)
    (Hkind : pw_kind segs mk P) (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (h1 : lin_ge0 allkn [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)] = true)
    (h2 : lin_ge0 allkn [(wb, wk), (wn, 0)] [(kb, kk)] = true)
    (h3 : lin_ge0 allkn [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)] = true) :
    0 ≤ estart E (SA wb wk) + elenZ E wn ∧
    estart E (SA wb wk) + elenZ E wn < 2 ^ 64 ∧
    (estart E (SA wb wk) + elenZ E wn ≤ estart E (SA kb kk) + elenZ E len ∧
      estart E (SA kb kk) ≤ estart E (SA wb wk) + elenZ E wn ∧
      estart E (SA kb kk) + elenZ E len ≤ 2 ^ 64 - 1) := by
  obtain ⟨Hfl, -⟩ := (Hkind E M (SA kb kk) len).1 HK
  have hk0 : 0 ≤ bv_unsigned (edenot E kb) + kk := Hfl.1
  have A := lin_ge0_sound segs E M0 allkn [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)] Hall h1
  have B := lin_ge0_sound segs E M0 allkn [(wb, wk), (wn, 0)] [(kb, kk)] Hall h2
  have C := lin_ge0_sound segs E M0 allkn [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)] Hall h3
  have hl0 : bv_unsigned (edenot E (.ELit 0)) = 0 := u_lit0
  simp only [xt_den] at A B C
  rw [hl0, two64_eq] at C
  have A1 : bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)
      ≤ bv_unsigned (edenot E kb) + kk + bv_unsigned (edenot E len) := by omega
  have B1 : bv_unsigned (edenot E kb) + kk
      ≤ bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn) := by omega
  have C1 : bv_unsigned (edenot E kb) + kk + bv_unsigned (edenot E len) ≤ 2 ^ 64 - 1 := by omega
  have W0 : 0 ≤ bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn) := by omega
  have W1 : bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn) < 2 ^ 64 := by omega
  exact ⟨W0, W1, A1, B1, C1⟩

/--  :707: the pieces of a `pw_kind` entry survive a write inside it. -/
theorem kcut_pw_sound (segs : List Segment) (mk : saddr → expr → kentry)
    (P : (word → Option byte) → word → Prop) (E : env) (M0 : word → Option byte)
    (M M' : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hkind : pw_kind segs mk P) (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → P M x → P M' x) :
    ∀ K ∈ kcut mk allkn wb wk wn kb kk len, kentry_ok segs E M' K := by
  have LOW : ∀ (h1 : lin_ge0 allkn [(wb, wk)] [(kb, kk)] = true)
      (h2 : lin_ge0 allkn [(kb, kk), (len, 0)] [(wb, wk)] = true),
      kentry_ok segs E M' (mk (SA kb kk)
        (mkAlu .SUB (mkAlu .ADD wb (.ELit wk)) (mkAlu .ADD kb (.ELit kk)))) := by
    intro h1 h2
    have A := lin_ge0_sound segs E M0 allkn [(wb, wk)] [(kb, kk)] Hall h1
    have B := lin_ge0_sound segs E M0 allkn [(kb, kk), (len, 0)] [(wb, wk)] Hall h2
    simp only [xt_den] at A B
    have hA : bv_unsigned (edenot E kb) + kk ≤ bv_unsigned (edenot E wb) + wk := by omega
    have hB : bv_unsigned (edenot E wb) + wk
        ≤ bv_unsigned (edenot E kb) + kk + bv_unsigned (edenot E len) := by omega
    exact kcut_low_piece_pw segs mk P E M M' wb wk wn kb kk len Hkind HK Hout hA hB
  have HIGH : ∀ (h1 : lin_ge0 allkn [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)] = true)
      (h2 : lin_ge0 allkn [(wb, wk), (wn, 0)] [(kb, kk)] = true)
      (h3 : lin_ge0 allkn [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)] = true)
      (ha : saddr) (L : expr),
      estart E ha = estart E (SA wb wk) + elenZ E wn →
      elenZ E L = estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn) →
      kentry_ok segs E M' (mk ha L) := by
    intro h1 h2 h3 ha L hst hl
    obtain ⟨W0, W1, A1, B1, C1⟩ :=
      kcut_high_bounds_pw segs mk P E M0 M allkn wb wk wn kb kk len Hkind Hall HK h1 h2 h3
    exact kcut_high_piece_pw segs mk P E M M' wb wk wn kb kk len ha L Hkind HK Hout
      hst hl B1 A1 C1
  unfold kcut
  dsimp only
  generalize hsp : split_lit (mkAlu .ADD (mkAlu .ADD wb (.ELit wk)) wn) = sp
  obtain ⟨hb, ho⟩ := sp
  intro K hK
  rcases List.mem_append.mp hK with h | h
  · obtain ⟨hc, hK⟩ := mem_ite_single _ _ K h
    obtain ⟨-, h1, h2⟩ := lowc_true hc
    rw [hK]
    exact LOW h1 h2
  · obtain ⟨hc, hK⟩ := mem_ite_single _ _ K h
    obtain ⟨h1, h2, h3⟩ := highc_true hc
    rw [hK]
    obtain ⟨W0, W1, A1, B1, C1⟩ :=
      kcut_high_bounds_pw segs mk P E M0 M allkn wb wk wn kb kk len Hkind Hall HK h1 h2 h3
    have hL := kcut_high_len E wb wk wn kb kk len W0 A1 C1
    refine HIGH h1 h2 h3 _ _ ?_ hL
    by_cases hh : (lin_ge0 allkn [(hb, ho)] [(wb, wk), (wn, 0)]
        && lin_ge0 allkn [(wb, wk), (wn, 0)] [(hb, ho)]) = true
    · rw [ite_eq_left hh]
      obtain ⟨hh1, hh2⟩ := (Bool.and_eq_true ..).mp hh
      have C1' := lin_ge0_sound segs E M0 allkn [(hb, ho)] [(wb, wk), (wn, 0)] Hall hh1
      have C2' := lin_ge0_sound segs E M0 allkn [(wb, wk), (wn, 0)] [(hb, ho)] Hall hh2
      simp only [xt_den] at C1' C2'
      have u1 : bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)
          ≤ bv_unsigned (edenot E hb) + ho := by omega
      have u2 : bv_unsigned (edenot E hb) + ho
          ≤ bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn) := by omega
      show bv_unsigned (edenot E hb) + ho
        = bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)
      omega
    · rw [ite_eq_right hh]
      have hwe : bv_unsigned (edenot E (mkAlu .ADD (mkAlu .ADD wb (.ELit wk)) wn))
          = bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn) :=
        eqm_eq_of_range
          (add_eqm E _ _ _ _ (add_eqm E _ _ _ _ (eqm_refl _) (eqm_u_lit wk)) (eqm_refl _))
          (u64_range _).1 (u64_range _).2 W0 W1
      show bv_unsigned (edenot E (mkAlu .ADD (mkAlu .ADD wb (.ELit wk)) wn)) + 0
        = bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)
      rw [hwe]; omega
theorem kwr_cut_sound (segs : List Segment) (E : env) (M0 M M' : word → Option byte)
    (allkn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr) (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (.KWr (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x) :
    ∀ K ∈ kwr_cut allkn wb wk wn kb kk len, kentry_ok segs E M' K := by
  refine kcut_pw_sound segs .KWr (fun M x => wview segs M x ≠ none) E M0 M M' allkn
    wb wk wn kb kk len (pw_kind_wr segs) Hall HK ?_
  intro x Hx HP
  unfold wview at *
  rw [Hout x Hx]
  exact HP
theorem know_ok_cutout (segs : List Segment) (E : env) (M M' : word → Option byte)
    (k : List kentry) (b n : expr) (o : Int) (HK : know_ok segs E M k)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b o) ∨
      estart E (SA b o) + elenZ E n ≤ bv_unsigned x → M' x = M x) :
    know_ok segs E M' (kn_cutout k b o n) := by
  intro K hK
  simp only [kn_cutout] at hK
  rw [List.mem_flatMap] at hK
  obtain ⟨K0, hK0, hK1⟩ := hK
  rw [cutout1p_eq] at hK1
  have hK0' : kentry_ok segs E M K0 := HK K0 hK0
  by_cases hf : kentry_apart_b k b o n K0 = true
  · unfold cutout1 at hK1
    rw [ite_eq_left hf] at hK1
    rw [List.mem_singleton] at hK1
    subst hK1
    exact kentry_apart_keep segs E M M' k K b o n HK hK0' hf Hout
  · unfold cutout1 at hK1
    rw [ite_eq_right hf] at hK1
    cases K0 with
    | KZero a len =>
        obtain ⟨kb, kk⟩ := a
        exact kzero_cut_sound segs E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KWr a len =>
        obtain ⟨kb, kk⟩ := a
        exact kwr_cut_sound segs E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KFill a len c =>
        obtain ⟨kb, kk⟩ := a
        exact kfill_cut_sound segs c E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KUnk a len =>
        obtain ⟨kb, kk⟩ := a
        exact kunk_cut_sound segs E M M M' k b o n kb kk len HK hK0' Hout K hK1
    | KWord a w v => cases hK1
    | KBlob a nn bk => cases hK1
    | KImg lo hi => cases hK1
    | KAlign e m => cases hK1
    | KRange e lo hi => cases hK1
    | KDisj a1 n1 a2 n2 => cases hK1

/-! ### The fog nodes' ledger lemmas -/
theorem list_set_nth_maps_match (E : env) (ms : List amap) :
    ∀ (l : List (word × word)) (i : Nat) (m : amap) (sz : Int),
      ms[i]? = some m → is_fog m = false → 0 ≤ sz ∧ sz < two64 →
      bv_unsigned (edenot E m.am_len) ≤ sz →
      maps_match E ms l → maps_match E (list_set_nth i (fog_token sz) ms) l := by
  induction ms with
  | nil => intro l i m sz Hn; simp at Hn
  | cons m0 ms ih =>
    intro l i m sz Hn Hf Hsz Hle HM
    have hlit : uE E (fog_token sz).am_len = sz := u_small sz Hsz
    have hfog : is_fog (fog_token sz) = true := by
      simp only [is_fog, fog_token, is_tok_kind]
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hn
        subst Hn
        simp only [list_set_nth]
        rw [maps_match] at HM ⊢
        rw [Hf] at HM
        obtain ⟨l', rfl, HM⟩ := HM
        simp only [hfog, ite_true]
        exact Or.inr ⟨amap_den E m0, l', rfl, by rw [hlit]; exact Hle, HM⟩
    | succ i' =>
        simp only [List.getElem?_cons_succ] at Hn
        simp only [list_set_nth]
        rw [maps_match] at HM ⊢
        by_cases h0 : is_fog m0 = true
        · simp only [h0, ite_true] at HM ⊢
          rcases HM with HM | ⟨iv, l', rfl, Hs, HM⟩
          · exact Or.inl (ih l i' m sz Hn Hf Hsz Hle HM)
          · exact Or.inr ⟨iv, l', rfl, Hs, ih l' i' m sz Hn Hf Hsz Hle HM⟩
        · simp only [h0, ite_false, Bool.not_eq_true] at HM ⊢
          obtain ⟨l', rfl, HM⟩ := HM
          exact ⟨l', rfl, ih l' i' m sz Hn Hf Hsz Hle HM⟩
theorem list_insert_nth_maps_match (E : env) (ms : List amap) :
    ∀ (l : List (word × word)) (i : Nat) (sz : Int),
      maps_match E ms l → maps_match E (list_insert_nth i (fog_token sz) ms) l := by
  induction ms with
  | nil =>
    intro l i sz HM
    have hl : l = [] := HM
    subst hl
    have hfog : is_fog (fog_token sz) = true := by
      simp only [is_fog, fog_token, is_tok_kind]
    cases i with
    | zero =>
        simp only [list_insert_nth, maps_match, hfog, ite_true]
        exact Or.inl trivial
    | succ i' =>
        simp only [list_insert_nth, maps_match, hfog, ite_true]
        exact Or.inl trivial
  | cons m0 ms ih =>
    intro l i sz HM
    have hfog : is_fog (fog_token sz) = true := by
      simp only [is_fog, fog_token, is_tok_kind]
    cases i with
    | zero =>
        simp only [list_insert_nth]
        rw [maps_match]
        simp only [hfog, ite_true]
        exact Or.inl HM
    | succ i' =>
        simp only [list_insert_nth]
        rw [maps_match] at HM ⊢
        by_cases h0 : is_fog m0 = true
        · simp only [h0, ite_true] at HM ⊢
          rcases HM with HM | ⟨iv, l', rfl, Hs, HM⟩
          · exact Or.inl (ih l i' sz HM)
          · exact Or.inr ⟨iv, l', rfl, Hs, ih l' i' sz HM⟩
        · simp only [h0, ite_false, Bool.not_eq_true] at HM ⊢
          obtain ⟨l', rfl, HM⟩ := HM
          exact ⟨l', rfl, ih l' i' sz HM⟩
theorem cs_ok_with_maps (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (ms' : List amap) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (HM : maps_match E ms' (m_vmmaps model).vm_maps)
    (Hsub : ∀ m, m ∈ ms' →
      m = fog_token (match m.am_len with | .ELit z => z | _ => 0) ∨ m ∈ cs.a_maps) :
    cs_ok segs A LIMIT SINV argH FS0 E (with_maps cs ms') R FULL model := by
  refine ⟨HC.co_regs, HC.co_log, HC.co_know, HC.co_halt, HC.co_fds, HC.co_fs, HC.co_tid,
    HC.co_res, HC.co_limit, HM, ?_, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb,
    HC.co_nasub, ?_, ?_, HC.co_totsz, HC.co_split, HC.co_brk, HC.co_sbrk, HC.co_eager,
    HC.co_abytes, HC.co_minv, HC.co_zero, HC.co_sinv⟩
  · intro m hm
    rcases Hsub m hm with h | hm
    · intro hh
      have hf : is_hole m = false := by
        rw [h]
        simp only [is_hole, fog_token, mkind_eqb]
      rw [hf] at hh
      exact absurd hh (by simp)
    · exact HC.co_holes m hm
  · intro m hm hk
    rcases Hsub m hm with h | hm
    · rw [h] at hk
      simp only [fog_token] at hk
      rcases hk with hk | hk <;> cases hk
    · exact HC.co_none m hm hk
  · intro m hm hk a ha
    rcases Hsub m hm with h | hm
    · rw [h] at hk
      simp only [fog_token] at hk
      cases hk
    · exact HC.co_kinds m hm hk a ha
theorem fog_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (i : Nat) (sz : Int) (cs' : acs) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_fog cs i sz = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_fog at H
  cases hn : cs.a_maps[i]? with
  | none => simp only [hn] at H; cases H
  | some m =>
      simp only [hn] at H
      cases hx : xhi (kn cs) m.am_len with
      | none => simp only [hx] at H; simp at H
      | some h =>
          simp only [hx] at H
          split at H
          · rename_i hc
            injection H with hEq
            subst hEq
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true] at hc
            obtain ⟨⟨⟨Hnf, Hs1⟩, Hs2⟩, Hx⟩ := hc
            have hnf : is_fog m = false := by simpa using Hnf
            have hb := xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) m.am_len h
              HC.co_know hx
            refine ⟨?_, rfl⟩
            refine cs_ok_with_maps segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_ ?_
            · exact list_set_nth_maps_match E cs.a_maps (m_vmmaps model).vm_maps i m sz hn hnf
                ⟨Hs1, Hs2⟩ (by omega) HC.co_maps
            · intro m' hm'
              rcases In_list_set_nth cs.a_maps i (fog_token sz) m' hm' with h' | h'
              · subst h'
                exact Or.inl rfl
              · exact Or.inr h'
          · cases H
theorem fognew_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (i : Nat) (sz : Int) (cs' : acs) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_fognew cs i sz = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_fognew at H
  by_cases hc : (i ≤ cs.a_maps.length && 0 ≤ sz && sz < two64) = true
  · rw [ite_eq_left hc] at H
    injection H with hEq
    subst hEq
    refine ⟨?_, rfl⟩
    refine cs_ok_with_maps segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_ ?_
    · exact list_insert_nth_maps_match E cs.a_maps (m_vmmaps model).vm_maps i sz HC.co_maps
    · intro m' hm'
      rcases In_list_insert_nth cs.a_maps i (fog_token sz) m' hm' with h' | h'
      · subst h'
        exact Or.inl rfl
      · exact Or.inr h'
  · rw [ite_eq_right hc] at H
    cases H
theorem entails_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs ch : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : entails cs ch = true) :
    cs_ok segs A LIMIT SINV argH FS0 E ch R FULL model ∧ pc ch = pc cs := by
  simp only [entails, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at H
  obtain ⟨H, Habytes⟩ := H
  obtain ⟨H, Heager⟩ := H
  obtain ⟨H, Hylo⟩ := H
  obtain ⟨H, Htotsz⟩ := H
  obtain ⟨H, Htid⟩ := H
  obtain ⟨H, Hfd⟩ := H
  obtain ⟨H, Hbrk⟩ := H
  obtain ⟨H, Hghost⟩ := H
  obtain ⟨H, Hallow⟩ := H
  obtain ⟨H, Hmaps⟩ := H
  obtain ⟨H, Hkn⟩ := H
  obtain ⟨H, Hregs⟩ := H
  obtain ⟨Hpc, Hlog⟩ := H
  have HregsE : cs.a_ss.s_regs = ch.a_ss.s_regs :=
    list_eqb_eq expr_eqb expr_eqb_eq _ _ Hregs
  have HmapsE : cs.a_maps = ch.a_maps :=
    list_eqb_eq amap_eqb (fun x y h => amap_eqb_eq h) _ _ Hmaps
  have HallowE : cs.a_vis = ch.a_vis :=
    list_eqb_eq pair_eqb (fun x y h => pair_eqb_eq h) _ _ Hallow
  have HghostE : cs.a_ghost = ch.a_ghost :=
    list_eqb_eq pair_eqb (fun x y h => pair_eqb_eq h) _ _ Hghost
  have HbrkE : cs.a_brk = ch.a_brk := expr_eqb_eq _ _ Hbrk
  have HfdE : cs.a_fd = ch.a_fd := afd_eqb_eq _ _ Hfd
  have Hlog' : ch.a_ss.s_log = [] := by
    cases hl : ch.a_ss.s_log with
    | nil => rfl
    | cons x xs =>
        rw [hl] at Hlog
        exact absurd Hlog (by simp)
  have HH : hid A argH E ch model = hid A argH E cs model :=
    hid_ext A argH E cs ch model HallowE.symm
  have HCtotsz := HC.co_totsz
  have HCeager := HC.co_eager
  have HCabytes := HC.co_abytes
  have HA : allowA A E ch = allowA A E cs := by
    unfold allowA
    rw [HallowE, HghostE]
  refine ⟨⟨HregsE ▸ HC.co_regs, Hlog', ?_, HC.co_halt, HfdE ▸ HC.co_fds, HC.co_fs, ?_,
    HC.co_res, HC.co_limit, HmapsE ▸ HC.co_maps, ?_, HC.co_seps, HC.co_wf, HC.co_bounds,
    HC.co_lazyb, HC.co_nasub, ?_, ?_, ?_, ?_, HbrkE ▸ HC.co_brk, HC.co_sbrk, ?_, ?_,
    HA ▸ HC.co_minv, ?_, HC.co_sinv⟩, Hpc.symm⟩
  · -- `co_know`
    have hMr : Mr A argH E ch model FULL = Mr A argH E cs model FULL := by
      unfold Mr
      rw [HH]
    intro K hK
    rw [hMr]
    have h1 := List.all_eq_true.mp Hkn K hK
    obtain ⟨K', hK', heq⟩ := List.any_eq_true.mp h1
    have hKeq : K = K' := kentry_eqb_eq K K' heq
    rw [hKeq]
    exact HC.co_know K' hK'
  · -- `co_tid`
    intro h
    exact HC.co_tid (by rw [Htid]; exact h)
  · -- `co_holes`
    intro m hm hh
    refine holes_mono E cs.a_ylo ch.a_ylo _ ch.a_maps (fun m' hm' => ?_) Hylo m hm hh
    exact HC.co_holes m' (HmapsE ▸ hm')
  · -- `co_none`
    intro m hm hk
    exact HC.co_none m (HmapsE ▸ hm) hk
  · -- `co_kinds`
    intro m hm hk a ha
    exact HC.co_kinds m (HmapsE ▸ hm) hk a ha
  · -- `co_totsz`
    show sum_sizes ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) ≤ ch.a_totsz
    omega
  · -- `co_split`
    obtain ⟨Y, h1, h2, h3, h4⟩ := HC.co_split
    exact ⟨Y, by omega, h2, h3, h4⟩
  · -- `co_eager`
    show eager_used model ≤ ch.a_eager
    omega
  · -- `co_abytes`
    show A_bytes (allowA A E ch) ≤ ch.a_abytes
    rw [HA]
    omega
  · -- `co_zero`
    intro a h1 h2 h3 h4 h5
    refine HC.co_zero a ?_ h2 h3 h4 ?_
    · rw [← HH]; exact h1
    · unfold in_ghost
      rw [HghostE]
      exact h5
theorem hid_cons_sub (A : atable) (argH : env → word → Bool) (E : env) (cs : acs)
    (p : expr × expr) (model : Model) (a : word) (ss : sym_state) (tot ylo eg : Int)
    (gh : List (expr × expr)) (ab : Int) (brk : expr) (fd : afd) (tid : Bool)
    (H : hid A argH E
      (ACS ss cs.a_maps tot ylo eg (p :: cs.a_vis) gh ab brk fd tid) model a = true) :
    hid A argH E cs model a = true := by
  unfold hid at *
  rw [Bool.or_eq_true] at H ⊢
  rcases H with h | h
  · exact Or.inl h
  · have h' : vis A E
        (ACS ss cs.a_maps tot ylo eg (p :: cs.a_vis) gh ab brk fd tid) model a = false := by
      cases hh : vis A E
          (ACS ss cs.a_maps tot ylo eg (p :: cs.a_vis) gh ab brk fd tid) model a <;>
        simp_all
    cases hv : vis A E cs model a with
    | false => exact Or.inr rfl
    | true =>
        rw [vis_mono A E cs
          (ACS ss cs.a_maps tot ylo eg (p :: cs.a_vis) gh ab brk fd tid) model a
          (fun z hz => in_allow_cons A E cs p ss tot ylo eg gh ab brk fd tid z hz) hv] at h'
        exact absurd h' (by simp)
theorem node_havoc_nxt (nx0 : Nat) (cs : acs) (rs : List Nat) (cs1 : acs)
    (H : node_havoc nx0 cs rs = some cs1) :
    nxt cs1 = nxt cs + rs.length ∧ pc cs1 = pc cs := by
  unfold node_havoc at H
  split at H
  · injection H with hEq
    subst hEq
    exact ⟨rfl, rfl⟩
  · cases H
theorem regs_ok_sr_fresh (E : env) (sr : List expr) (R : BvMap word) (rs : List Nat)
    (nx : Nat) (HR : regs_ok E sr R) (Hsr : AsanPlanCore.sr_vars_lt nx sr = true)
    (Hrs : ∀ r ∈ rs, 0 < r ∧ r < 32) :
    regs_ok (ext_list E nx (rs.map (fun r : Nat => getr R (Z_to_bv 5 (r : Int)))))
      (sr_fresh sr rs nx) R := by
  have key : ∀ (rs : List Nat) (E : env) (sr : List expr) (nx : Nat),
      regs_ok E sr R → AsanPlanCore.sr_vars_lt nx sr = true →
      (∀ r ∈ rs, 0 < r ∧ r < 32) →
      regs_ok (ext_list E nx (rs.map (fun r : Nat => getr R (Z_to_bv 5 (r : Int)))))
        (sr_fresh sr rs nx) R := by
    intro rs
    induction rs with
    | nil =>
        intro E sr nx HR Hsr Hrs
        simpa only [List.map_nil, ext_list, sr_fresh] using HR
    | cons r rest ih =>
        intro E sr nx HR Hsr Hrs
        have Hr : 0 < r ∧ r < 32 := Hrs r (by simp)
        have Hrest : ∀ x ∈ rest, 0 < x ∧ x < 32 := fun x hx => Hrs x (by simp [hx])
        simp only [List.map_cons, sr_fresh, ext_list]
        refine ih (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) (sr_upd sr r (.EVar nx))
          (nx + 1) ?_ ?_ Hrest
        · refine regs_ok_respell (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) sr R r
            (.EVar nx) ?_ Hr ?_
          · exact regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) sr R
              (ext1_agree E nx _) Hsr HR
          · have h0 : bv_eqb (Z_to_bv 5 (r : Int)) 0 = false :=
              bv_eqb_neq _ _ (Z_to_bv_five_ne_zero r Hr.1 Hr.2)
            have hg : sr_get sr (Z_to_bv 5 (r : Int)) = sr.getD r (.ELit 0) := by
              simp only [sr_get, h0, Bool.false_eq_true, ite_false, ridx_lit r Hr.2]
            show edenot (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) (.EVar nx)
              = edenot (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) (sr.getD r (.ELit 0))
            rw [show edenot (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) (.EVar nx)
                  = getr R (Z_to_bv 5 (r : Int)) from ext1_at E nx _]
            rw [← hg]
            exact regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (r : Int)))) sr R
              (ext1_agree E nx _) Hsr HR (Z_to_bv 5 (r : Int))
        · refine sr_vars_lt_upd (nx + 1) sr r (.EVar nx) ?_ ?_
          · exact sr_vars_lt_mono nx (nx + 1) sr Hsr (by omega)
          · show decide (nx < nx + 1) = true
            rw [decide_eq_true_eq]
            omega
  exact key rs E sr nx HR Hsr Hrs

/-! ### The `lazy_cover` side condition and `cs_ok_frame`

 :372 and :453.  These are the two boundary facts the block-run
soundness needs on top of the executor's own carry: `lazy_cover_cs` is the
hypothesis `AsanAcctShape.srz_msteps_restricted_T` asks for, and `cs_ok_frame`
re-attaches the post-block state to the memory the block's stores produced. -/

/-- `pagedown` is monotone. -/
theorem pagedown_mono (a b : Int) (H : a ≤ b) : pagedown a ≤ pagedown b := by
  unfold pagedown
  have hq : a / 4096 ≤ b / 4096 := Int.ediv_le_ediv (by decide : (0 : Int) < 4096) H
  exact Int.mul_le_mul_of_nonneg_right hq (by decide : (0 : Int) ≤ 4096)

/-- The page base of a word IS its page-rounded-down value. -/
theorem bv_unsigned_page_base (a : word) :
    bv_unsigned (page_base a) = pagedown (bv_unsigned a) := by
  have hge : 0 ≤ (a.toNat : Int) / 4096 * 4096 := by
    have := Int.emod_nonneg (a.toNat : Int) (by decide : (4096 : Int) ≠ 0); omega
  have hlt : (a.toNat : Int) / 4096 * 4096 < 2 ^ 64 := by omega
  have hu : ((page_base a).toNat : Int) = (a.toNat : Int) / 4096 * 4096 := by
    unfold page_base page_base_of page_size
    exact u64_lit _ ⟨hge, hlt⟩
  simp only [bv_unsigned, pagedown]
  rw [hu]

/-- An aligned `Int` at or below `z` is at most the page-rounded-down `z`. -/
theorem aligned_le_pagedown (a z : Int) (Hm : a % 4096 = 0) (Hz : a ≤ z) :
    a ≤ pagedown z := by
  unfold pagedown
  have hq : a / 4096 ≤ z / 4096 :=
    Int.ediv_le_ediv (by decide : (0 : Int) < 4096) Hz
  have e : a = a / 4096 * 4096 := by
    have h := Int.ediv_mul_add_emod a 4096
    rw [Hm, Int.add_zero] at h
    exact h.symm
  rw [e]
  exact Int.mul_le_mul_of_nonneg_right hq (by decide : (0 : Int) ≤ 4096)

/-- An aligned `Int` above `z` is at least the next page above `z`:
    `pagedown z + 4096` is the least multiple of the page size above `z`. -/
theorem aligned_gt_pagedown (a z : Int) (Hm : a % 4096 = 0) (Hz : z < a) :
    pagedown z + 4096 ≤ a := by
  have hz0 := Int.emod_nonneg z (by decide : (4096 : Int) ≠ 0)
  have e1 : z / 4096 * 4096 + z % 4096 = z := Int.ediv_mul_add_emod z 4096
  have e2 : a / 4096 * 4096 = a := by
    have h := Int.ediv_mul_add_emod a 4096
    rw [Hm, Int.add_zero] at h
    exact h
  have hq : z / 4096 ≤ a / 4096 :=
    Int.ediv_le_ediv (by decide : (0 : Int) < 4096) (by omega)
  have hne : z / 4096 ≠ a / 4096 := by
    intro hEq
    rw [hEq, e2] at e1
    omega
  have hq' : z / 4096 + 1 ≤ a / 4096 := by omega
  have hmul : (z / 4096 + 1) * 4096 = pagedown z + 4096 := by
    unfold pagedown
    rw [Int.add_mul, Int.one_mul]
  rw [← hmul, ← e2]
  exact Int.mul_le_mul_of_nonneg_right hq' (by decide : (0 : Int) ≤ 4096)

/-- The page of an allowed byte is an allowed page: the rounding in `allowA`
    is page-outward, so the containing page fits. -/
theorem in_allow_page (A : atable) (E : env) (cs : acs) (w : word)
    (H : in_allow A E cs (bv_unsigned w) = true) :
    page_allowedb (allowA A E cs) (page_base w) = true := by
  unfold page_allowedb
  rw [List.any_eq_true]
  rw [in_allow, Bool.or_eq_true] at H
  rcases H with hv | hs
  · rw [in_vis, List.any_eq_true] at hv
    obtain ⟨p, hp, hb⟩ := hv
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
    refine ⟨(pagedown (uE E p.1), pageup (uE E p.1 + uE E p.2)), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, List.mem_append_left _ hp, by simp [allow1]⟩
    · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      have hz1 : uE E p.1 ≤ bv_unsigned w := hb.1
      have hz2 : bv_unsigned w < uE E p.1 + uE E p.2 := hb.2
      constructor
      · show pagedown (uE E p.1) ≤ bv_unsigned (page_base w)
        rw [bv_unsigned_page_base]
        exact pagedown_mono _ _ hz1
      · show bv_unsigned (page_base w) + 4096 ≤ pageup (uE E p.1 + uE E p.2)
        rw [bv_unsigned_page_base]
        have hp := pageup_ge (uE E p.1 + uE E p.2)
        exact aligned_gt_pagedown _ _ (pageup_mod _) (by omega)
  · rw [in_sh, List.any_eq_true] at hs
    obtain ⟨p, hp, hb⟩ := hs
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
    refine ⟨(pagedown (sh_lo A E p), pageup (sh_hi A E p)), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨p, List.mem_append_left _ hp, by simp [allow1]⟩
    · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      have hz1 : sh_lo A E p ≤ bv_unsigned w := hb.1
      have hz2 : bv_unsigned w < sh_hi A E p := hb.2
      constructor
      · show pagedown (sh_lo A E p) ≤ bv_unsigned (page_base w)
        rw [bv_unsigned_page_base]
        exact pagedown_mono _ _ hz1
      · show bv_unsigned (page_base w) + 4096 ≤ pageup (sh_hi A E p)
        rw [bv_unsigned_page_base]
        have hp := pageup_ge (sh_hi A E p)
        exact aligned_gt_pagedown _ _ (pageup_mod _) (by omega)
theorem lazy_cover_cs (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HULL_ok : hull_ok A) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    lazy_cover (hid A argH E cs model) (m_vm_lazy model) (allowA A E cs) := by
  intro w Hlz Hh
  have Hlz' : page_in_ranges (page_base w) (m_vm_lazy model) = true := Hlz
  -- `hid` false = not in the argument block and visible
  have hvis : vis A E cs model w = true := by
    have h := Hh
    simp only [hid] at h
    have hn : (!(vis A E cs model w)) = false := or_eq_false_right h
    simpa using hn
  -- the lazy interval holding the page of `w`, and what it says about `w`
  rw [page_in_ranges, List.any_eq_true] at Hlz
  obtain ⟨iv, Hin, Hb⟩ := Hlz
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hb
  obtain ⟨L1, L2⟩ := HC.co_lazyb iv Hin
  obtain ⟨P1, P2, P3⟩ := page_base_le w
  simp only [page_size] at Hb
  have hlo : A.img_hi ≤ bv_unsigned w := Int.le_trans L1 (Int.le_trans Hb.1 P1)
  have hhi : bv_unsigned w < CEIL :=
    Int.lt_of_lt_of_le P2 (Int.le_trans Hb.2 L2)
  -- `vis` is true: in the hull, at/above the ceiling, or allowed — the first
  -- two contradict the lazy interval the page lies in
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

/-- : the fd table's
    denotation only sees `m_fds`/`m_fs`, so it transports along any model
    frame that keeps those two. -/
theorem fds_ok_frame (E : env) (f : afd) (m m' : Model)
    (hf : m_fds m' = m_fds m) (hfs : m_fs m' = m_fs m) (H : fds_ok E f m) :
    fds_ok E f m' := by
  unfold fds_ok at *
  cases f with
  | FdStd => rw [hf]; exact H
  | FdDir => rw [hf]; exact H
  | FdFile k len off =>
      obtain ⟨p, c, h1, h2, h3, h4, h5⟩ := H
      exact ⟨p, c, by rw [hf]; exact h1, by rw [hfs]; exact h2, h3, h4, h5⟩

/--  :453.  Re-attach the block's post-state to the memory its stores
    produced: the symbolic state is replaced wholesale, the model only moves
    along `same_but_materialized`, and every `cs_ok` component that mentions
    the model is transported along that frame. -/
theorem cs_ok_frame (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (ss' : sym_state) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hs : same_but_materialized model model')
    (Hinv : MInv (allowA A E cs) model')
    (HR : regs_ok E ss'.s_regs R') (HL : ss'.s_log = [])
    (HK : know_ok segs E (Mr A argH E cs model FULL') ss'.s_know)
    (Hhid : ∀ a, hid A argH E cs model a = true → FULL' a = FULL a) :
    cs_ok segs A LIMIT SINV argH FS0 E (with_ss cs ss') R' FULL' model' := by
  obtain ⟨-, hvm, hlz, -, -, -, -, -, hfds, -, -, hfs, hha, hti, -, -, heg⟩ :=
    same_but_materialized_frame model model' Hs
  -- `vis`/`hid` do not change: neither the visible ranges nor the model's
  -- mapping part is touched
  have hvis : vis A E (with_ss cs ss') model' = vis A E cs model := by
    rw [vis_same A E (with_ss cs ss') model model' Hs]
    exact vis_ext A E cs (with_ss cs ss') model rfl
  have hhid : ∀ a, hid A argH E (with_ss cs ss') model' a = hid A argH E cs model a := by
    intro a
    simp only [hid, hvis]
  have hmr : Mr A argH E (with_ss cs ss') model' FULL' = Mr A argH E cs model FULL' := by
    unfold Mr
    rw [show (fun a => hid A argH E (with_ss cs ss') model' a)
          = (fun a => hid A argH E cs model a) from funext hhid]
  refine
    { co_regs := HR
      co_log := HL
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
  · rw [hmr]; exact HK
  · rw [hha]; exact HC.co_halt
  · exact fds_ok_frame E cs.a_fd model model' hfds hfs HC.co_fds
  · rw [hfs]; exact HC.co_fs
  · intro Ht
    rw [hti]
    exact HC.co_tid Ht
  · rw [hvm]; exact HC.co_res
  · rw [hvm]; exact HC.co_limit
  · rw [hvm]; exact HC.co_maps
  · rw [hvm]; exact HC.co_holes
  · rw [hvm]; exact HC.co_seps
  · obtain ⟨w1, w2, w3, w4⟩ := HC.co_wf
    exact ⟨by rw [hvm]; exact w1, by rw [hvm]; exact w2,
      by rw [hlz]; exact w3, by rw [hvm]; exact w4⟩
  · rw [hvm]; exact HC.co_bounds
  · rw [hlz]; exact HC.co_lazyb
  · rw [hvm]; exact HC.co_nasub
  · rw [hvm]; exact HC.co_none
  · rw [hvm, hlz]; exact HC.co_kinds
  · rw [hvm]; exact HC.co_totsz
  · rw [hvm]; exact HC.co_split
  · rw [hvm]; exact HC.co_brk
  · rw [hvm]; exact HC.co_sbrk
  · rw [heg]; exact HC.co_eager
  · show A_bytes (allowA A E cs) ≤ cs.a_abytes
    exact HC.co_abytes
  · show MInv (allowA A E cs) model'
    exact Hinv
  · intro a h1 h2 h3 h4 h5
    rw [hhid a] at h1
    rw [hvm] at h2 h3
    rw [hlz] at h4
    rw [Hhid a h1]
    exact HC.co_zero a h1 h2 h3 h4 h5
  · refine SINV_frame E FULL FULL' ?_ HC.co_sinv
    intro a Ha
    exact Hhid a (by simp only [hid, Ha, Bool.true_or])

/--  :2060.  A successful block run simulates the block: the executor's
    `msteps` chain is lifted through `srz_msteps_restricted_T`, the carry
    rebuilds the knowledge about the memory the stores produced, and the
    post-block obligation (hypothesis `Hk`) closes the goal at every model
    that is `same_but_materialized` and stays inside the budget. -/
theorem run_block_sound (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool)
    (FS0 : Fs.Fs) (KC : Nat)
    (IT_ok : itab_sound segs IT) (SEGS_wx : wx_segs_nowrap segs) (HULL_ok : hull_ok A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (gb bfuel : Nat) (stops : List Int) (cs cs' : acs) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (T : TSet)
    (Hgb : nx0 ≤ gb)
    (Hrun : run_block segs IT gb KC bfuel stops cs = some cs')
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hk : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' → env_agree (nxt cs) E E' →
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes segs (cfg_of segs R' (pc cs') FULL' model') T) :
    srealizes segs (cfg_of segs R (pc cs) FULL model) T := by
  rw [run_block_eq] at Hrun
  unfold run_block_ref at Hrun
  cases hf0 : fresh_ok gb cs with
  | false =>
      rw [hf0] at Hrun
      exact absurd Hrun (by simp)
  | true =>
    rw [hf0] at Hrun
    simp only [ite_true] at Hrun
    have Hf : fresh_ok nx0 cs = true := fresh_ok_mono nx0 gb cs Hgb hf0
    obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs Hf
    -- the block's symbolic run, exactly as `run_block_ref` spells it
    let ss' : sym_state := sym_execTX segs IT KC bfuel true stops
      (SS cs.a_ss.s_pc cs.a_ss.s_regs [] cs.a_ss.s_know cs.a_ss.s_next)
    have hss' : sym_execTX segs IT KC bfuel true stops
        (SS cs.a_ss.s_pc cs.a_ss.s_regs [] cs.a_ss.s_know cs.a_ss.s_next) = ss' := rfl
    rw [hss'] at Hrun
    cases hc : carry ss'.s_log ss'.s_know [] with
    | mk kn' rest =>
      obtain ⟨scs, hs⟩ := rest
      cases scs with
      | cons sc rest =>
          rw [hc] at Hrun
          exact absurd Hrun (by simp)
      | nil =>
        rw [hc] at Hrun
        simp only [] at Hrun
        injection Hrun with hcs'
        subst cs'
        -- the executor simulates a machine run, transporting the valuation
        obtain ⟨E', R', Hag, Hle, HR', Hlf, HK', Hms, -⟩ :=
          runTX_sound segs IT KC bfuel stops cs.a_ss.s_pc cs.a_ss.s_regs cs.a_ss.s_know
            (nxt cs) E (Mr A argH E cs model FULL) (seg_rom segs) R IT_ok
            HC.co_regs HC.co_know
            (by rw [← sr_vars_lt_eq]; exact Fsr)
            (by rw [← kn_vars_lt_eq]; exact Fkn)
        have Hagc : env_agree (nxt cs) E E' := Hag
        have HC' : cs_ok segs A LIMIT SINV argH FS0 E' cs R FULL model :=
          cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E E' cs R FULL
            model Hagc Hf HC
        have HH : hid A argH E' cs model = hid A argH E cs model :=
          hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hagc Fle Fallow
        -- the block is a run of the RESTRICTED machine
        show srealizes segs
          (AsanAcct.mkCfg (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)) model) T
        refine AsanAcctShape.srz_msteps_restricted_T segs (hid A argH E cs model)
          (H_off_segments_cs segs A argH E cs model HULL_ok SEGS_in_hull argH_high) SEGS_wx
          (allowA A E cs) (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom segs)) _ model T
          (lazy_cover_cs segs A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC)
          (A_wf_allowA A E cs) HC.co_minv HC.co_halt Hms ?_
        intro model' Hinv' Hsame Hclean
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfsm, -, -, -, -, -⟩ :=
          same_but_materialized_frame model model' Hsame
        -- the carry keeps the knowledge sound against the stored memory
        have HKc : know_ok segs E' (mem_denot E' (Mr A argH E cs model FULL) ss'.s_log)
            kn' :=
          carry_after segs E' (Mr A argH E cs model FULL) ss'.s_log ss'.s_know [] kn' []
            hs hc Hlf HK' (by intro s hmem; simp at hmem)
        let FULL' : word → Option byte :=
          munrestrict (hid A argH E cs model) FULL
            (mem_denot E' (Mr A argH E cs model FULL) ss'.s_log)
        have Hmr' : Mr A argH E' cs model FULL'
            = mem_denot E' (Mr A argH E cs model FULL) ss'.s_log := by
          show mrestrict (hid A argH E' cs model) FULL' = _
          rw [HH]
          exact mrestrict_munrestrict_clean _ _ _ (fun a Ha => Hclean a Ha)
        have hcsok : cs_ok segs A LIMIT SINV argH FS0 E'
            (with_ss cs (mk_ss ss'.s_pc ss'.s_regs kn' ss'.s_next)) R' FULL' model' := by
          refine cs_ok_frame segs A LIMIT SINV argH FS0 SINV_frame E' cs R FULL model
            (mk_ss ss'.s_pc ss'.s_regs kn' ss'.s_next) R' FULL' model' HC' Hsame ?_ HR'
            rfl ?_ ?_
          · rw [allowA_agree A (nxt cs) E E' cs Hagc Fallow]
            exact Hinv'
          · show know_ok segs E' (Mr A argH E' cs model FULL') kn'
            rw [Hmr']
            exact HKc
          · intro a Ha
            have hF : FULL' = munrestrict (hid A argH E cs model) FULL
                (mem_denot E' (Mr A argH E cs model FULL) ss'.s_log) := rfl
            rw [hF]
            rw [HH] at Ha
            simp only [munrestrict, Ha, ite_true]
        exact Hk E' R' FULL' model' (env_agree_le nx0 (nxt cs) E E' Hagc Fle) Hagc hcsok hfsm

/--  :2114.  `run_block_gc_sound` — the GC only forgets knowledge, and
    `cs_gc_ok` says forgetting keeps `cs_ok`; `pc` is unchanged. -/
theorem run_block_gc_sound (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool)
    (FS0 : Fs.Fs) (KC : Nat)
    (IT_ok : itab_sound segs IT) (SEGS_wx : wx_segs_nowrap segs) (HULL_ok : hull_ok A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (gb bfuel : Nat) (stops : List Int) (cs cs' : acs) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (T : TSet)
    (Hgb : nx0 ≤ gb)
    (Hrun : run_block_gc segs IT gb KC bfuel stops cs = some cs')
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hk : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' → env_agree (nxt cs) E E' →
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes segs (cfg_of segs R' (pc cs') FULL' model') T) :
    srealizes segs (cfg_of segs R (pc cs) FULL model) T := by
  unfold run_block_gc at Hrun
  cases hrb : run_block segs IT gb KC bfuel stops cs with
  | none =>
      rw [hrb] at Hrun
      exact absurd Hrun (by simp)
  | some cs1 =>
      rw [hrb] at Hrun
      simp only [] at Hrun
      injection Hrun with hEq
      subst cs'
      refine run_block_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok SEGS_wx HULL_ok
        SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull gb bfuel stops cs cs1 E R
        FULL model T Hgb hrb HC ?_
      intro E' R' FULL' model' Hag1 Hag2 HC1 Hfs
      have hpc : pc (cs_gc gb cs1) = pc cs1 := pc_cs_gc gb cs1
      have hres := Hk E' R' FULL' model' Hag1 Hag2
        (cs_gc_ok segs A LIMIT SINV argH FS0 gb E' cs1 R' FULL' model' HC1) Hfs
      rwa [hpc] at hres

/-! ### `check_all`: every state of the list checks with the returned shape -/

/-- The `check_all` step function's error cases are absorbing: a fold that starts
    from a `CErr` (or any other non-`COk` result) never produces a `COk`.  Needed
    because `check_all_fold_ok` starts its induction at a `COk` accumulator while
    the `shape_eqb` / child-error branches leave a `CErr` accumulator behind. -/
theorem check_all_fold_err (A : atable) (chk : acs → plan → cres) (k : plan) :
    ∀ (l : List acs) (r : cres) (s : shape),
      (∀ s', r ≠ cres.COk s') →
      l.foldl (fun acc cs =>
        match acc with
        | .COk s1 =>
            match chk cs k with
            | .COk s' => if shape_eqb s1 s' then cres.COk s1 else cres.CErr 6 k cs
            | err => err
        | err => err) r ≠ cres.COk s := by
  intro l
  induction l with
  | nil => intro r s hr h; exact hr s h
  | cons c l ih =>
      intro r s hr h
      simp only [List.foldl_cons] at h
      cases hr' : r with
      | COk s1 => exact hr s1 hr'
      | CErr a b d =>
          simp only [hr'] at h
          exact ih (.CErr a b d) s (by intro s' e; exact absurd e.symm (by simp)) h

/-- The `check_all` fold keeps the accumulator `COk`: a successful fold returns
    the very shape the first state produced, and every later state produced it
    too. -/
theorem check_all_fold_ok (A : atable) (chk : acs → plan → cres) (k : plan) (s : shape) :
    ∀ (l : List acs) (s0 : shape),
      l.foldl (fun acc cs =>
        match acc with
        | .COk s1 =>
            match chk cs k with
            | .COk s' => if shape_eqb s1 s' then cres.COk s1 else cres.CErr 6 k cs
            | err => err
        | err => err) (cres.COk s0) = cres.COk s →
      s = s0 ∧ ∀ cs, cs ∈ l → chk cs k = cres.COk s0 := by
  intro l
  induction l with
  | nil =>
      intro s0 h
      refine ⟨?_, by simp⟩
      injection h with h'
      exact h'.symm
  | cons c l ih =>
      intro s0 h
      simp only [List.foldl_cons] at h
      cases hcc : chk c k with
      | COk s' =>
          simp only [hcc] at h
          split at h
          · rename_i hbe
            have hss : s' = s0 := (shape_eqb_eq s0 s' hbe).symm
            rw [hss] at hcc
            obtain ⟨hs, hall⟩ := ih s0 h
            exact ⟨hs, by
              intro cs hcs
              rcases List.mem_cons.mp hcs with rfl | hcs
              · exact hcc
              · exact hall cs hcs⟩
          · exact absurd h (check_all_fold_err A chk k l (.CErr 6 k c) s (by intro s' e; simp at e))
      | CErr a b d =>
          simp only [hcc] at h
          exact absurd h (check_all_fold_err A chk k l (.CErr a b d) s (by intro s' e; simp at e))

/--  :3104.  `check_all` returns `COk s` only if every state of the
    (non-empty) list checks with the same shape `s`; in particular the first
    one does, which is what `check_vars` uses to bound the destroyed-case
    shapes of `PMmapIn`. -/
theorem check_all_ok (A : atable) (chk : acs → plan → cres) (k : plan) (css : List acs)
    (s : shape) (H : check_all A chk k css = .COk s) :
    (∃ cs1, cs1 ∈ css ∧ chk cs1 k = .COk s) ∧ (∀ cs, cs ∈ css → chk cs k = .COk s) := by
  cases css with
  | nil => simp [check_all] at H
  | cons cs0 rest =>
      simp only [check_all] at H
      cases hc0 : chk cs0 k with
      | COk s0 =>
          simp only [hc0] at H
          obtain ⟨hs, hall⟩ := check_all_fold_ok A chk k s rest s0 H
          rw [← hs] at hc0
          refine ⟨⟨cs0, by simp, hc0⟩, ?_⟩
          intro cs hcs
          rcases List.mem_cons.mp hcs with rfl | hcs
          · exact hc0
          · rw [hs]; exact hall cs hcs
      | CErr a b c => simp [hc0] at H

/-- **The fuel-`0` equation at an arbitrary loop context.**

    `AsanPlan.check_zero` states the `fuel = 0` case only at `lc = none`; the
    checker's first equation ignores the loop context, so the statement holds
    verbatim for `some c` too, and that is the form an induction on `fuel`
    needs in its base case .  `rfl`, like
    `check_zero`. -/
theorem check_zero_lc (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC bfuel : Nat) (lc : Option loopctx) (cs : acs) (p : plan) :
    AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 0 lc cs p = .CErr 0 p cs := rfl

/-- **Shapes only mention the initial variables**.

    Every successful `AsanPlan.check` returns a shape that passes
    `shape_vars_lt nx0`: the checker walks its plan from the initial variable
    `nx0` up, and each plan constructor either recurses (the induction
    hypothesis applies to the recursive call at the same `fuel`) or assembles a
    shape from sub-shapes whose bounds are known — `salt2_vars` for the
    two-child `salt2` nodes, `shape_vars_lt` for `SCase`, and `check_all_ok`
    for the destroyed children of `PMmapIn` / `PMmapInH`, whose shape comes
    from a state the fold checked rather than from a plan of its own.

    Proof: induction on `fuel`.  The base case is `check_zero_lc` (the `fuel`
    `0` equation ignores the loop context); at `fuel + 1`, `check_succ`
    unfolds one `check_go` — whose `ck` parameter *is* this induction
    hypothesis — and the goal becomes the plan constructor's own case
    analysis, once per `lc` shape.  The leading `lc_bnd` guard is the only
    place the loop context enters any of the 45 bodies. -/
theorem check_vars (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC : Nat) :
    ∀ (bfuel fuel : Nat) (lc : Option loopctx) (p : plan) (cs : acs) (s : shape),
      AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p = .COk s →
      shape_vars_lt nx0 s = true := by
  intro bfuel fuel
  induction fuel with
  | zero =>
      intro lc p cs s H
      have h0 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 0 lc cs p = .CErr 0 p cs := rfl
      rw [h0] at H
      cases H
  | succ f IH =>
      intro lc p cs s H
      have hstep := AsanPlan.check_succ segs IT A nx0 LIMIT XN XE XB HS KC bfuel f lc cs p
      have H' := hstep.symm.trans H
      clear hstep H
      cases p
      case PRun stops k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : run_block_gc segs IT nx0 KC bfuel (stops ++ STOPS A) cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : run_block_gc segs IT (lc_bnd c) KC bfuel (stops ++ STOPS A) cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PSplit e mid k1 k2 =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hv : AsanPlanCore.expr_vars_lt nx0 e = true
            · rw [ite_eq_left hv] at H'
              revert H'
              generalize hh : erange (kn cs) e = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨lo, hi⟩ := p
                by_cases hc15 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                · rw [ite_eq_left hc15] at H'
                  revert H'
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r
                  cases r with
                  | COk s1 =>
                    intro H'
                    revert H'
                    generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r
                    cases r with
                    | COk s2 =>
                      intro H'
                      cases H'
                      simp only [shape_vars_lt, hv, IH _ _ _ _ h1, IH _ _ _ _ h2]
                      rfl
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                · rw [ite_eq_right hc15] at H'
                  by_cases hc14 : hi ≤ mid
                  · rw [ite_eq_left hc14] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                  · rw [ite_eq_right hc14] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hv] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hv : AsanPlanCore.expr_vars_lt nx0 e = true
            · rw [ite_eq_left hv] at H'
              revert H'
              generalize hh : erange (kn cs) e = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨lo, hi⟩ := p
                by_cases hc15 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                · rw [ite_eq_left hc15] at H'
                  revert H'
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r
                  cases r with
                  | COk s1 =>
                    intro H'
                    revert H'
                    generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r
                    cases r with
                    | COk s2 =>
                      intro H'
                      cases H'
                      simp only [shape_vars_lt, hv, IH _ _ _ _ h1, IH _ _ _ _ h2]
                      rfl
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                · rw [ite_eq_right hc15] at H'
                  by_cases hc14 : hi ≤ mid
                  · rw [ite_eq_left hc14] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                  · rw [ite_eq_right hc14] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hv] at H'
              cases H'
      case PCase2 e mid k1 k2 =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : erange (kn cs) e = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨lo, hi⟩ := p
              by_cases hc20 : (!(decide (lo ≤ mid) && decide (mid < hi))) = true
              · rw [ite_eq_left hc20] at H'
                by_cases hc18 : hi ≤ mid
                · rw [ite_eq_left hc18] at H'
                  first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                · rw [ite_eq_right hc18] at H'
                  first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              · rw [ite_eq_right hc20] at H'
                by_cases hc19 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                · rw [ite_eq_left hc19] at H'
                  by_cases hc17 : kn_contra (kn ((set_kn cs (.KRange e lo mid :: kn cs)))) = true
                  · rw [ite_eq_left hc17] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                  · rw [ite_eq_right hc17] at H'
                    by_cases hc16 : kn_contra (kn ((set_kn cs (.KRange e (mid + 1) hi :: kn cs)))) = true
                    · rw [ite_eq_left hc16] at H'
                      first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                    · rw [ite_eq_right hc16] at H'
                      revert H'
                      generalize h3 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r
                      cases r with
                      | COk s1 =>
                        intro H'
                        revert H'
                        generalize h4 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r
                        cases r with
                        | COk s2 =>
                          intro H'
                          dsimp only at H'
                          by_cases hb : shape_eqb s1 s2 = true
                          · rw [hb] at H'
                            cases H'
                            exact IH _ _ _ _ h3
                          · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                            rw [hbf] at H'
                            cases H'
                        | CErr a b c =>
                          intro H'
                          cases H'
                      | CErr a b c =>
                        intro H'
                        cases H'
                · rw [ite_eq_right hc19] at H'
                  cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : erange (kn cs) e = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨lo, hi⟩ := p
              by_cases hc20 : (!(decide (lo ≤ mid) && decide (mid < hi))) = true
              · rw [ite_eq_left hc20] at H'
                by_cases hc18 : hi ≤ mid
                · rw [ite_eq_left hc18] at H'
                  first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                · rw [ite_eq_right hc18] at H'
                  first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              · rw [ite_eq_right hc20] at H'
                by_cases hc19 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                · rw [ite_eq_left hc19] at H'
                  by_cases hc17 : kn_contra (kn ((set_kn cs (.KRange e lo mid :: kn cs)))) = true
                  · rw [ite_eq_left hc17] at H'
                    first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                  · rw [ite_eq_right hc17] at H'
                    by_cases hc16 : kn_contra (kn ((set_kn cs (.KRange e (mid + 1) hi :: kn cs)))) = true
                    · rw [ite_eq_left hc16] at H'
                      first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                    · rw [ite_eq_right hc16] at H'
                      revert H'
                      generalize h3 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r
                      cases r with
                      | COk s1 =>
                        intro H'
                        revert H'
                        generalize h4 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r
                        cases r with
                        | COk s2 =>
                          intro H'
                          dsimp only at H'
                          by_cases hb : shape_eqb s1 s2 = true
                          · rw [hb] at H'
                            cases H'
                            exact IH _ _ _ _ h3
                          · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                            rw [hbf] at H'
                            cases H'
                        | CErr a b c =>
                          intro H'
                          cases H'
                      | CErr a b c =>
                        intro H'
                        cases H'
                · rw [ite_eq_right hc19] at H'
                  cases H'
            | none =>
              intro H'
              cases H'
      case PCaseDisj b1 b2 k1 k2 =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_casedisj cs b1 b2 = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨csa, csb⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa k1 = r
              cases r with
              | COk s1 =>
                intro H'
                revert H'
                generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb k2 = r
                cases r with
                | COk s2 =>
                  intro H'
                  dsimp only at H'
                  by_cases hc21 : shape_eqb s1 s2 = true
                  · rw [ite_eq_left hc21] at H'
                    cases H'
                    exact IH _ _ _ _ h1
                  · rw [ite_eq_right hc21] at H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_casedisj cs b1 b2 = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨csa, csb⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa k1 = r
              cases r with
              | COk s1 =>
                intro H'
                revert H'
                generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb k2 = r
                cases r with
                | COk s2 =>
                  intro H'
                  dsimp only at H'
                  by_cases hc21 : shape_eqb s1 s2 = true
                  · rw [ite_eq_left hc21] at H'
                    cases H'
                    exact IH _ _ _ _ h1
                  · rw [ite_eq_right hc21] at H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PShDisj b1 n1 b2 n2 k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_shdisj A cs b1 n1 b2 n2 = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_shdisj A cs b1 n1 b2 n2 = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PContra =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc1 : kn_contra (kn cs) = true
            · rw [ite_eq_left hc1] at H'
              cases H'
              simp only [shape_vars_lt]
            · rw [ite_eq_right hc1] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc1 : kn_contra (kn cs) = true
            · rw [ite_eq_left hc1] at H'
              cases H'
              simp only [shape_vars_lt]
            · rw [ite_eq_right hc1] at H'
              cases H'
      case PFact K k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc2 : fact_ok (kn cs) K = true
            · rw [ite_eq_left hc2] at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            · rw [ite_eq_right hc2] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc2 : fact_ok (kn cs) K = true
            · rw [ite_eq_left hc2] at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            · rw [ite_eq_right hc2] at H'
              cases H'
      case PJoin b off n k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_join segs cs b off n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_join segs cs b off n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PForget ixs k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
      case PDropRange b n k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
      case PGcKeep ws k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
      case PBump m k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_bump cs m = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_bump cs m = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PHavoc rs k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havoc nx0 cs rs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havoc nx0 cs rs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PHavocBig K k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocbig nx0 cs K = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocbig nx0 cs K = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PFresh r logc base k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fresh nx0 cs r logc base = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fresh nx0 cs r logc base = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PSys y k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc3 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc3] at H'
              revert H'
              generalize hh : node_sys A nx0 y cs = r
              cases r with
              | some cs' =>
                intro H'
                try dsimp only at H'
                first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc3] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc3 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc3] at H'
              revert H'
              generalize hh : node_sys A nx0 y cs = r
              cases r with
              | some cs' =>
                intro H'
                try dsimp only at H'
                first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc3] at H'
              cases H'
      case PMmap ka kb =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc7 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc7] at H'
              revert H'
              generalize hh : node_mmap2 A nx0 LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc7] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc7 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc7] at H'
              revert H'
              generalize hh : node_mmap2 A nx0 LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc7] at H'
              cases H'
      case PMmapIn ka kb kc =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc10 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc10] at H'
              revert H'
              generalize hh : node_mmapin A nx0 LIMIT false cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb, cscs⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    revert H'
                    generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs = r
                    cases r with
                    | COk sc =>
                      intro H'
                      cases H'
                      obtain ⟨⟨cs1, hin, hck⟩, -⟩ := check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs sc h3
                      exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (salt2_vars nx0 _ _ (IH _ _ _ _ h2) (IH _ _ _ _ hck))
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc10] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc10 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc10] at H'
              revert H'
              generalize hh : node_mmapin A nx0 LIMIT false cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb, cscs⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    revert H'
                    generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs = r
                    cases r with
                    | COk sc =>
                      intro H'
                      cases H'
                      obtain ⟨⟨cs1, hin, hck⟩, -⟩ := check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs sc h3
                      exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (salt2_vars nx0 _ _ (IH _ _ _ _ h2) (IH _ _ _ _ hck))
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc10] at H'
              cases H'
      case PMprotect ka kb =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc8 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc8] at H'
              revert H'
              generalize hh : node_mprotect2 A LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc8] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc8 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc8] at H'
              revert H'
              generalize hh : node_mprotect2 A LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc8] at H'
              cases H'
      case PBrk2 ka kb =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc9 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc9] at H'
              revert H'
              generalize hh : node_brk2 A LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc9] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc9 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc9] at H'
              revert H'
              generalize hh : node_brk2 A LIMIT cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    cases H'
                    exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (IH _ _ _ _ h2)
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc9] at H'
              cases H'
      case PX x args k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_x segs A nx0 x args cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_x segs A nx0 x args cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PExt id args k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XN id args cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XN id args cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PEmit id args k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XE id args cs = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨fd, ps, cs'⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none cs' k = r
              cases r with
              | COk s1 =>
                intro H'
                cases H'
                simp only [shape_vars_lt]
                exact IH _ _ _ _ h1
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XE id args cs = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨fd, ps, cs'⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) cs' k = r
              cases r with
              | COk s1 =>
                intro H'
                cases H'
                simp only [shape_vars_lt]
                exact IH _ _ _ _ h1
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PExt2 id args k1 k2 =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XB id args cs = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨csa, csb⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa k1 = r
              cases r with
              | COk sa =>
                intro H'
                revert H'
                generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb k2 = r
                cases r with
                | COk sb =>
                  intro H'
                  cases H'
                  simp only [shape_vars_lt]
                  rw [IH _ _ _ _ h1, IH _ _ _ _ h2]
                  rfl
                | CErr a b c =>
                  intro H'
                  cases H'
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : XB id args cs = r
            cases r with
            | some p =>
              intro H'
              try dsimp only at H'
              obtain ⟨csa, csb⟩ := p
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa k1 = r
              cases r with
              | COk sa =>
                intro H'
                revert H'
                generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb k2 = r
                cases r with
                | COk sb =>
                  intro H'
                  cases H'
                  simp only [shape_vars_lt]
                  rw [IH _ _ _ _ h1, IH _ _ _ _ h2]
                  rfl
                | CErr a b c =>
                  intro H'
                  cases H'
              | CErr a b c =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PLoop J N inv body k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : loop_ok nx0 cs J N inv = r
            cases r with
            | some nhi =>
              intro H'
              try dsimp only at H'
              by_cases hc13 : (pc inv == pc cs && entails_h A (J + 1) (nxt inv) cs (inst inv J (.ELit 0))) = true
              · rw [ite_eq_left hc13] at H'
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some (loopctx.LC (pc cs) (inst inv J (eaddz (.EVar J) 1)) (J + 1) (nxt inv)) : Option loopctx) (loop_body_state J N nhi inv) body = r
                cases r with
                | COk sb =>
                  intro H'
                  cases sb with
                  | SNext => exact IH _ _ _ _ H'
                  | SNil => cases H'
                  | SExit c => cases H'
                  | SEmitP fd ps sb' => cases H'
                  | SAlt2 x y => cases H'
                  | SCase e m x y => cases H'
                  | SHole h => cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              · rw [ite_eq_right hc13] at H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : loop_ok nx0 cs J N inv = r
            cases r with
            | some nhi =>
              intro H'
              try dsimp only at H'
              by_cases hc13 : (pc inv == pc cs && entails_h A (J + 1) (nxt inv) cs (inst inv J (.ELit 0))) = true
              · rw [ite_eq_left hc13] at H'
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some (loopctx.LC (pc cs) (inst inv J (eaddz (.EVar J) 1)) (J + 1) (nxt inv)) : Option loopctx) (loop_body_state J N nhi inv) body = r
                cases r with
                | COk sb =>
                  intro H'
                  cases sb with
                  | SNext => exact IH _ _ _ _ H'
                  | SNil => cases H'
                  | SExit c => cases H'
                  | SEmitP fd ps sb' => cases H'
                  | SAlt2 x y => cases H'
                  | SCase e m x y => cases H'
                  | SHole h => cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              · rw [ite_eq_right hc13] at H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PNext =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            cases c with
            | LC h nx lo hi =>
              intro H'
              try dsimp only at H'
              by_cases hc : (pc cs == h && entails_h A lo hi cs nx) = true
              · rw [ite_eq_left hc] at H'
                cases H'
                simp only [shape_vars_lt]
              · rw [ite_eq_right hc] at H'
                cases H'
            | JC j js sk b lo => intro H'; cases H'
      case PHandoff h =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : HS h = r
            cases r with
            | some ch =>
              intro H'
              try dsimp only at H'
              by_cases hc4 : entails cs ch
              · rw [ite_eq_left hc4] at H'
                cases H'
                simp only [shape_vars_lt]
              · rw [ite_eq_right hc4] at H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : HS h = r
            cases r with
            | some ch =>
              intro H'
              try dsimp only at H'
              by_cases hc4 : entails cs ch
              · rw [ite_eq_left hc4] at H'
                cases H'
                simp only [shape_vars_lt]
              · rw [ite_eq_right hc4] at H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PExit =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc5 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc5] at H'
              revert H'
              generalize hh : node_exit cs = r
              cases r with
              | some code =>
                intro H'
                try dsimp only at H'
                cases H'
                simp only [shape_vars_lt]
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc5] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc5 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc5] at H'
              revert H'
              generalize hh : node_exit cs = r
              cases r with
              | some code =>
                intro H'
                try dsimp only at H'
                cases H'
                simp only [shape_vars_lt]
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc5] at H'
              cases H'
      case PSpin =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc6 : node_spin segs cs = true
            · rw [ite_eq_left hc6] at H'
              cases H'
              simp only [shape_vars_lt]
            · rw [ite_eq_right hc6] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc6 : node_spin segs cs = true
            · rw [ite_eq_left hc6] at H'
              cases H'
              simp only [shape_vars_lt]
            · rw [ite_eq_right hc6] at H'
              cases H'
      case PFog i sz k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fog cs i sz = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fog cs i sz = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PFogNew i sz k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fognew cs i sz = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_fognew cs i sz = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PGhost b n k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_ghost LIMIT cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_ghost LIMIT cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PUnvis b n k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_unvis A cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_unvis A cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PHavocBrk lo hi k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocbrk nx0 cs lo hi = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocbrk nx0 cs lo hi = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PIntro lo hi k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_intro nx0 cs lo hi = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_intro nx0 cs lo hi = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PDiamond joinpc rs k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : branch_probe IT cs = r
            cases r with
            | some e =>
              intro H'
              try dsimp only at H'
              revert H'
              generalize hh : erange (kn cs) e = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨lo, hi⟩ := p
                by_cases hc23 : (hi < 1 || 0 < lo) = true
                · rw [ite_eq_left hc23] at H'
                  revert H'
                  generalize hh : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A) cs = r
                  cases r with
                  | some cs1 =>
                    intro H'
                    try dsimp only at H'
                    by_cases hc22 : (pc cs1 == joinpc) = true
                    · rw [ite_eq_left hc22] at H'
                      first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                    · rw [ite_eq_right hc22] at H'
                      cases H'
                  | none =>
                    intro H'
                    cases H'
                · rw [ite_eq_right hc23] at H'
                  revert H'
                  generalize hh : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A) (set_kn cs (.KRange e lo 0 :: kn cs)) = r
                  cases r with
                  | some ca =>
                    intro H'
                    try dsimp only at H'
                    revert H'
                    generalize hh : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A) (set_kn cs (.KRange e 1 hi :: kn cs)) = r
                    cases r with
                    | some cb =>
                      intro H'
                      try dsimp only at H'
                      revert H'
                      generalize hh : node_diamond_join A nx0 (nxt cs) joinpc rs ca cb = r
                      cases r with
                      | some csj =>
                        intro H'
                        try dsimp only at H'
                        first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                      | none =>
                        intro H'
                        cases H'
                    | none =>
                      intro H'
                      cases H'
                  | none =>
                    intro H'
                    cases H'
              | none =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : branch_probe IT cs = r
            cases r with
            | some e =>
              intro H'
              try dsimp only at H'
              revert H'
              generalize hh : erange (kn cs) e = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨lo, hi⟩ := p
                by_cases hc23 : (hi < 1 || 0 < lo) = true
                · rw [ite_eq_left hc23] at H'
                  revert H'
                  generalize hh : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A) cs = r
                  cases r with
                  | some cs1 =>
                    intro H'
                    try dsimp only at H'
                    by_cases hc22 : (pc cs1 == joinpc) = true
                    · rw [ite_eq_left hc22] at H'
                      first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                    · rw [ite_eq_right hc22] at H'
                      cases H'
                  | none =>
                    intro H'
                    cases H'
                · rw [ite_eq_right hc23] at H'
                  revert H'
                  generalize hh : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A) (set_kn cs (.KRange e lo 0 :: kn cs)) = r
                  cases r with
                  | some ca =>
                    intro H'
                    try dsimp only at H'
                    revert H'
                    generalize hh : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A) (set_kn cs (.KRange e 1 hi :: kn cs)) = r
                    cases r with
                    | some cb =>
                      intro H'
                      try dsimp only at H'
                      revert H'
                      generalize hh : node_diamond_join A nx0 (nxt cs) joinpc rs ca cb = r
                      cases r with
                      | some csj =>
                        intro H'
                        try dsimp only at H'
                        first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
                      | none =>
                        intro H'
                        cases H'
                    | none =>
                      intro H'
                      cases H'
                  | none =>
                    intro H'
                    cases H'
              | none =>
                intro H'
                cases H'
            | none =>
              intro H'
              cases H'
      case PRename m k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_rename nx0 cs m = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_rename (lc_bnd c) cs m = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PCompact k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_compact nx0 cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_compact (lc_bnd c) cs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PVia j js lo kc k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc12 : via_ok nx0 cs js lo = true
            · rw [ite_eq_left hc12] at H'
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none js k = r
              cases r with
              | COk sk =>
                intro H'
                first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | CErr a b c =>
                intro H'
                cases H'
            · rw [ite_eq_right hc12] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc12 : via_ok nx0 cs js lo = true
            · rw [ite_eq_left hc12] at H'
              revert H'
              generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) js k = r
              cases r with
              | COk sk =>
                intro H'
                first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
              | CErr a b c =>
                intro H'
                cases H'
            · rw [ite_eq_right hc12] at H'
              cases H'
      case PMerge j =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            cases c with
            | JC j' js sk b lo =>
              intro H'
              try dsimp only at H'
              by_cases hg1 : (j == j' && pc cs == pc js && shape_vars_lt nx0 sk && entails_h A lo (nxt js) cs js) = true
              · rw [ite_eq_left hg1] at H'
                cases H'
                have hsv := hg1
                simp only [Bool.and_eq_true, and_assoc] at hsv
                exact hsv.2.2.1
              · rw [ite_eq_right hg1] at H'
                cases H'
            | LC h nx lo hi =>
              intro H'
              try dsimp only at H'
              cases H'
      case PAbstractCell b n k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_abstractcell A cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_abstractcell A cs b n = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PHavocWords bs k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocwords nx0 cs bs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_havocwords nx0 cs bs = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PRespell r e k =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_respell cs r e = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · revert H'
            generalize hh : node_respell cs r e = r
            cases r with
            | some cs' =>
              intro H'
              try dsimp only at H'
              first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm
            | none =>
              intro H'
              cases H'
      case PMmapInH ka kb kc =>
        cases lc with
        | none =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc11 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc11] at H'
              revert H'
              generalize hh : node_mmapin A nx0 LIMIT true cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb, cscs⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    revert H'
                    generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs = r
                    cases r with
                    | COk sc =>
                      intro H'
                      cases H'
                      obtain ⟨⟨cs1, hin, hck⟩, -⟩ := check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs sc h3
                      exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (salt2_vars nx0 _ _ (IH _ _ _ _ h2) (IH _ _ _ _ hck))
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc11] at H'
              cases H'
        | some c =>
          unfold AsanPlan.check_go at H'
          dsimp only at H'
          split at H'
          · cases H'
          · by_cases hc11 : is_ecall_at segs cs = true
            · rw [ite_eq_left hc11] at H'
              revert H'
              generalize hh : node_mmapin A nx0 LIMIT true cs = r
              cases r with
              | some p =>
                intro H'
                try dsimp only at H'
                obtain ⟨csa, csb, cscs⟩ := p
                revert H'
                generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r
                cases r with
                | COk sa =>
                  intro H'
                  revert H'
                  generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r
                  cases r with
                  | COk sb =>
                    intro H'
                    revert H'
                    generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs = r
                    cases r with
                    | COk sc =>
                      intro H'
                      cases H'
                      obtain ⟨⟨cs1, hin, hck⟩, -⟩ := check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs sc h3
                      exact salt2_vars nx0 _ _ (IH _ _ _ _ h1) (salt2_vars nx0 _ _ (IH _ _ _ _ h2) (IH _ _ _ _ hck))
                    | CErr a b c =>
                      intro H'
                      cases H'
                  | CErr a b c =>
                    intro H'
                    cases H'
                | CErr a b c =>
                  intro H'
                  cases H'
              | none =>
                intro H'
                cases H'
            · rw [ite_eq_right hc11] at H'
              cases H'

/-- **Continuation adapter**: the induction hypothesis of
    `check_sound`, which is stated at the *valuation `E` the loop context
    `lc` was frozen at*, gives the shape at any valuation `E'` that agrees with
    it below `nxt cs`.

    Two transports are needed.  On the *shape* side, `sd` only mentions
    variables below `nx0` once `shape_vars_lt nx0 s` holds, which is exactly
    `check_vars` — so `sd D E fs s = sd D E' fs s`.  On the *state* side,
    `LCOK` is stable under `env_agree (nxt cs)` precisely when the state is
    above the loop bound (`lc_guard lc cs`), which is `LCOK_agree`. -/
theorem cont_agree (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat)
    (LIMIT : Int) (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (HS : Nat → Option acs) (KC : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HOLES : Nat → env → Fs.Fs → TSet)
    (HOLES_agree : ∀ (h : Nat) (E E' : env) (fs : Fs.Fs),
      env_agree nx0 E E' → HOLES h E fs = HOLES h E' fs)
    (bfuel fuel : Nat) (lc : Option loopctx) (k : plan) (cs cs' : acs) (s : shape)
    (E : env) (model : Model) (D : TSet)
    (Hc : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs' k = .COk s)
    (HL : LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E (m_fs model))
    (Hg : lc_guard lc cs = true) (HD : D [])
    (Hrec : ∀ (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model),
      cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model →
      LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E (m_fs model) → D [] →
      srealizes segs (cfg_of segs R (pc cs') FULL model) (sd HOLES D E (m_fs model) s))
    (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model)
    (Hag : env_agree nx0 E E' ∧ env_agree (nxt cs) E E')
    (HC' : cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model')
    (Hfs : m_fs model' = m_fs model) :
    srealizes segs (cfg_of segs R' (pc cs') FULL' model') (sd HOLES D E (m_fs model) s) := by
  have hsv : shape_vars_lt nx0 s = true :=
    check_vars segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc k cs' s Hc
  have hsd := sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree Hag.1 s hsv
  rw [hsd, ← Hfs]
  refine Hrec E' R' FULL' model' HC' ?_ HD
  rw [Hfs]
  exact LCOK_agree segs A nx0 LIMIT SINV argH FS0 HOLES lc D E E' (m_fs model) cs HL Hg Hag.2

/--  :1644 — a cheap syntactic contradiction never fires on a state
    whose knowledge is true.  `kn_contra` only inspects `KRange` entries; for
    them the contradiction it detects (`hi < lo`, or a linear form whose
    interval lies wholly outside `[lo, hi]`) is impossible for a value that is
    both in `[lo, hi]` (`kentry_ok`) and in the linear form's interval
    (`lin_range_sound` over `erange_sound`), because a modular equality of two
    values in `[0, 2^64)` is an equality (`eqm_eq_of_range`). -/
theorem kn_contra_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) :
    know_ok segs E M k → kn_contra k = true → False := by
  intro HK H
  unfold kn_contra at H
  obtain ⟨K, Hin, HKb⟩ := List.any_eq_true.mp H
  have HKK := HK K Hin
  dsimp only at HKb
  cases K with
  | KRange e lo hi =>
      dsimp only at HKb
      have hkk : lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := HKK
      have htwo : two64 = 2 ^ 64 := rfl
      have GEN : ∀ (c : Int) (ts : List (Int × expr)), lden E (lin_of e) = c + tden E ts →
          (match lin_range (erange k) c ts with
           | some (a, b) => (decide (0 ≤ a) && decide (b < two64)) &&
                            (decide (b < lo) || decide (hi < a))
           | none => false) = true → False := by
        intro c ts hle Hm
        cases hlr : lin_range (erange k) c ts with
        | none =>
            rw [hlr] at Hm
            exact absurd Hm (by simp)
        | some p =>
            obtain ⟨a, b⟩ := p
            rw [hlr] at Hm
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at Hm
            obtain ⟨⟨ha, hb⟩, hd⟩ := Hm
            have Hbd := lin_range_sound E (erange k)
              (fun a lo hi Ha => erange_sound segs E M k a lo hi HK Ha) c ts a b hlr
            have hq := lin_of_sound E e
            have hq' : eqm (c + tden E ts) (uE E e) := by
              rw [hle] at hq; exact hq
            have hb' : b < 2 ^ 64 := by rw [← htwo]; exact hb
            have heq : c + tden E ts = uE E e :=
              eqm_eq_of_range hq' (by omega) (by omega)
                (u64_range (edenot E e)).1 (u64_range (edenot E e)).2
            have hu : uE E e = bv_unsigned (edenot E e) := rfl
            rw [hu] at heq
            rcases hd with hd | hd
            · omega
            · omega
      by_cases hlt : hi < lo
      · rw [ite_eq_left hlt] at HKb
        omega
      · rw [ite_eq_right hlt] at HKb
        split at HKb
        · simp at HKb
        · revert HKb
          generalize hlin : lin_of e = l
          intro HKb
          cases l with
          | mk c ts =>
            cases ts with
            | nil => simp only [] at HKb; cases HKb
            | cons t ts' =>
              cases ts' with
              | nil => simp only [] at HKb; cases HKb
              | cons t' ts'' =>
                simp only [] at HKb
                refine GEN c (t :: t' :: ts'') ?_ HKb
                rw [hlin]; rfl
  | KWord a w v => simp at HKb
  | KZero a n => simp at HKb
  | KBlob a n kk => simp at HKb
  | KImg lo hi => simp at HKb
  | KAlign e m => simp at HKb
  | KWr a n => simp at HKb
  | KDisj a1 n1 a2 n2 => simp at HKb
  | KFill a n c => simp at HKb
  | KUnk a n => simp at HKb

/--  :3077 — everything `loop_ok` checks, read back off its `some`. -/
theorem loop_ok_facts (nx0 : Nat) (cs : acs) (J : Nat) (N : expr) (inv : acs) (nhi : Int)
    (H : loop_ok nx0 cs J N inv = some nhi) :
    fresh_ok nx0 cs = true ∧ nxt cs ≤ J ∧ J < nxt inv ∧ inv.a_ss.s_log = [] ∧
      inv.a_ss.s_regs.length = 32 ∧ AsanPlanCore.expr_vars_lt (nxt cs) N = true ∧
      xhi (kn cs) N = some nhi ∧ nhi < two64 := by
  unfold loop_ok at H
  dsimp only at H
  cases hs : inv.a_ss.s_log with
  | cons x xs => simp [hs] at H
  | nil =>
    simp only [hs] at H
    split at H
    · rename_i hcond
      simp only [Bool.and_eq_true, and_assoc] at hcond
      obtain ⟨h1, h2, h3, -, h5, h6, h7, -⟩ := hcond
      refine ⟨h1, of_decide_eq_true h2, of_decide_eq_true h3, rfl, ?_, h5, ?_, ?_⟩
      · exact beq_iff_eq.mp h7
      · cases hx : xhi (kn cs) N with
        | none => rw [hx] at H; simp at H
        | some h =>
            rw [hx] at H
            simp only [] at H
            by_cases hlt : h < two64
            · rw [ite_eq_left hlt] at H
              simp only [Option.some.injEq] at H
              subst H
              rfl
            · rw [ite_eq_right hlt] at H
              simp at H
      · cases hx : xhi (kn cs) N with
        | none => rw [hx] at H; simp at H
        | some h =>
            rw [hx] at H
            simp only [] at H
            by_cases hlt : h < two64
            · rw [ite_eq_left hlt] at H
              simp only [Option.some.injEq] at H
              subst H
              exact hlt
            · rw [ite_eq_right hlt] at H
              simp at H
    · simp at H

/-- Integer division: adding a non-negative `y ≤ nhi` to `x ≥ 0` raises the
    quotient by at most `nhi / 8 + 1` .  Local helper for
    `allow1_cost` / `vis_add_sound`. -/
theorem ediv8_add_gap (x y nhi : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (hyn : y ≤ nhi) :
    (x + y) / 8 - x / 8 ≤ nhi / 8 + 1 := by
  have h8 : (0 : Int) < 8 := by decide
  have main : (x + y) / 8 ≤ x / 8 + nhi / 8 + 1 := by
    rw [Int.ediv_le_iff_le_mul h8]
    have hx' : x % 8 + 8 * (x / 8) = x := Int.emod_add_mul_ediv x 8
    have hq' : nhi % 8 + 8 * (nhi / 8) = nhi := Int.emod_add_mul_ediv nhi 8
    have hx0 : 0 ≤ x % 8 := Int.emod_nonneg x (by decide : (8 : Int) ≠ 0)
    have hx1 : x % 8 < 8 := Int.emod_lt_of_pos x h8
    have hq0 : 0 ≤ nhi % 8 := Int.emod_nonneg nhi (by decide : (8 : Int) ≠ 0)
    have hq1 : nhi % 8 < 8 := Int.emod_lt_of_pos nhi h8
    omega
  omega

/--  :3339 — allowing one more visible range costs at most `vis_cost`. -/
theorem allow1_cost (A : atable) (E : env) (b n : expr) (nhi : Int)
    (Hn : bv_unsigned (edenot E n) ≤ nhi) :
    A_bytes (allow1 A E (b, n)) ≤ vis_cost nhi := by
  unfold allow1 vis_cost sh_lo sh_hi
  simp only [A_bytes]
  have hb0 : 0 ≤ uE E b := (u64_range (edenot E b)).1
  have hn0 : 0 ≤ uE E n := (u64_range (edenot E n)).1
  have hun : uE E n = bv_unsigned (edenot E n) := rfl
  have h1 := pageup_pagedown_gap (uE E b) (uE E b + uE E n) (by omega)
  have hlo : A.shadow_off + uE E b / 8 ≤ A.shadow_off + (uE E b + uE E n) / 8 := by
    have h := Int.ediv_le_ediv (by decide : (0 : Int) < 8) (by omega : uE E b ≤ uE E b + uE E n)
    omega
  have h2 := pageup_pagedown_gap (A.shadow_off + uE E b / 8)
    (A.shadow_off + (uE E b + uE E n) / 8) hlo
  have h3 := ediv8_add_gap (uE E b) (uE E n) nhi hb0 hn0 (by omega)
  omega

/--  :2230 — a `KDisj` entry found by `find_disj` really relates the
    two ranges (in one of the two orders `find_disj` tries). -/
theorem find_disj_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b1 b2 : expr) (c1 : expr) (o1 : Int) (n1 : expr)
    (c2 : expr) (o2 : Int) (n2 : expr)
    (HK : know_ok segs E M k) (H : find_disj k b1 b2 = some (c1, o1, n1, c2, o2, n2)) :
    estart E (SA c1 o1) + elenZ E n1 ≤ estart E (SA c2 o2) ∨
      estart E (SA c2 o2) + elenZ E n2 ≤ estart E (SA c1 o1) := by
  revert H
  induction k with
  | nil =>
      intro H
      simp only [find_disj] at H
      exact absurd H (by simp)
  | cons K r ih =>
      intro H
      have HKK : kentry_ok segs E M K := HK K (List.mem_cons_self ..)
      have HKr : know_ok segs E M r := fun x hx => HK x (List.mem_cons_of_mem _ hx)
      cases K with
      | KDisj a1 n1' a2 n2' =>
          obtain ⟨d1, p1⟩ := a1
          obtain ⟨d2, p2⟩ := a2
          dsimp only [find_disj] at H
          by_cases h1 : (expr_eqb d1 b1 && expr_eqb d2 b2) = true
          · rw [ite_eq_left h1] at H
            simp only [Option.some.injEq, Prod.mk.injEq] at H
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := H
            exact HKK
          · rw [ite_eq_right h1] at H
            by_cases h2 : (expr_eqb d1 b2 && expr_eqb d2 b1) = true
            · rw [ite_eq_left h2] at H
              simp only [Option.some.injEq, Prod.mk.injEq] at H
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := H
              have hkk : kentry_ok segs E M (.KDisj ⟨d1, p1⟩ n1' ⟨d2, p2⟩ n2') := HKK
              simp only [kentry_ok] at hkk
              rcases hkk with h | h
              · right; exact h
              · left; exact h
            · rw [ite_eq_right h2] at H
              exact ih HKr H
      | KWord a w v => dsimp only [find_disj] at H; exact ih HKr H
      | KZero a n => dsimp only [find_disj] at H; exact ih HKr H
      | KBlob a n kk => dsimp only [find_disj] at H; exact ih HKr H
      | KImg lo hi => dsimp only [find_disj] at H; exact ih HKr H
      | KAlign e m => dsimp only [find_disj] at H; exact ih HKr H
      | KRange e lo hi => dsimp only [find_disj] at H; exact ih HKr H
      | KWr a n => dsimp only [find_disj] at H; exact ih HKr H
      | KFill a n c => dsimp only [find_disj] at H; exact ih HKr H
      | KUnk a n => dsimp only [find_disj] at H; exact ih HKr H

/--  :3352 — a ghost range only widens `a_ghost` and charges `vis_cost`. -/
theorem ghost_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b n : expr) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_ghost LIMIT cs b n = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_ghost at H
  cases hx : xhi (kn cs) n with
  | none => rw [hx] at H; simp at H
  | some nhi =>
      rw [hx] at H
      simp only [] at H
      by_cases hc : (AsanPlanCore.expr_vars_lt (nxt cs) b && AsanPlanCore.expr_vars_lt (nxt cs) n &&
          decide (cs.a_eager + cs.a_abytes + vis_cost nhi ≤ LIMIT)) = true
      · rw [ite_eq_left hc] at H
        simp only [Option.some.injEq] at H
        obtain rfl : (ACS cs.a_ss cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis
            (cs.a_ghost ++ [(b, n)]) (cs.a_abytes + vis_cost nhi) cs.a_brk cs.a_fd cs.a_tidset) = cs' := H
        have Hb : cs.a_eager + cs.a_abytes + vis_cost nhi ≤ LIMIT := by
          have h := hc; simp only [Bool.and_eq_true, and_assoc] at h
          exact of_decide_eq_true h.2.2
        have Hn : bv_unsigned (edenot E n) ≤ nhi :=
          xhi_sound segs E _ (kn cs) n nhi HC.co_know hx
        have HA : ((cs.a_vis ++ (cs.a_ghost ++ [(b, n)])).flatMap (allow1 A E))
            = allowA A E cs ++ allow1 A E (b, n) := by
          rw [allowA]
          simp only [List.flatMap_append, List.append_assoc, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
        refine ⟨⟨HC.co_regs, HC.co_log, HC.co_know, HC.co_halt, HC.co_fds, HC.co_fs,
          HC.co_tid, HC.co_res, HC.co_limit, HC.co_maps, HC.co_holes, HC.co_seps, HC.co_wf,
          HC.co_bounds, HC.co_lazyb, HC.co_nasub, HC.co_none, HC.co_kinds, HC.co_totsz,
          HC.co_split, HC.co_brk, HC.co_sbrk, HC.co_eager, ?_, ?_, ?_, HC.co_sinv⟩, rfl⟩
        · show A_bytes ((cs.a_vis ++ (cs.a_ghost ++ [(b, n)])).flatMap (allow1 A E))
            ≤ cs.a_abytes + vis_cost nhi
          rw [HA, A_bytes_app]
          have h := allow1_cost A E b n nhi Hn
          have hab := HC.co_abytes
          omega
        · show MInv ((cs.a_vis ++ (cs.a_ghost ++ [(b, n)])).flatMap (allow1 A E)) model
          rw [HA]
          refine MInv_app_r (allowA A E cs) (allow1 A E (b, n)) model HC.co_minv ?_
          have hl : (m_vmmaps model).vm_limit = LIMIT := HC.co_limit
          have he : eager_used model ≤ cs.a_eager := HC.co_eager
          show eager_used model + A_bytes (allowA A E cs ++ allow1 A E (b, n))
            ≤ (m_vmmaps model).vm_limit
          rw [A_bytes_app]
          have h := allow1_cost A E b n nhi Hn
          have hbud := HC.co_minv.minv_budget
          have hab := HC.co_abytes
          omega
        · intro a H1 H2 H3 H4 H5
          refine HC.co_zero a H1 H2 H3 H4 ?_
          unfold in_ghost at H5 ⊢
          rw [List.any_append] at H5
          exact or_eq_false_left H5
      · rw [ite_eq_right hc] at H
        simp at H

/-- Two words whose unsigned difference is `0` mod `2^64` are equal (both are
    in `[0, 2^64)`).  Local helper for `respell_ok_sound`. -/
theorem bv_eq_of_sub_mod (x y : word)
    (h : (bv_unsigned x - bv_unsigned y) % 2 ^ 64 = 0) : x = y := by
  have hx0 : 0 ≤ bv_unsigned x := (u64_range x).1
  have hx1 : bv_unsigned x < 2 ^ 64 := (u64_range x).2
  have hy0 : 0 ≤ bv_unsigned y := (u64_range y).1
  have hy1 : bv_unsigned y < 2 ^ 64 := (u64_range y).2
  have hue : bv_unsigned x = bv_unsigned y := by
    have hq := Int.emod_add_mul_ediv (bv_unsigned x - bv_unsigned y) (2 ^ 64)
    rw [h, Int.zero_add] at hq
    omega
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj hue)

/--  :4024 — `respell_ok` only fires on provably equal spellings. -/
theorem respell_ok_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (a e : expr) (HK : know_ok segs E M k)
    (H : respell_ok k a e = true) : edenot E a = edenot E e := by
  have HINT : (match erange k (mkAlu .SUB a e) with
      | some (lo, hi) => (lo == 0 && hi == 0)
      | none => false) = true → edenot E a = edenot E e := by
    intro Hm
    cases hr : erange k (mkAlu .SUB a e) with
    | none => rw [hr] at Hm; simp at Hm
    | some p =>
        obtain ⟨lo, hi⟩ := p
        rw [hr] at Hm
        simp only [Bool.and_eq_true, beq_iff_eq] at Hm
        obtain ⟨h0, h1⟩ := Hm
        subst h0
        subst h1
        have Hb := erange_sound segs E M k (mkAlu .SUB a e) 0 0 HK hr
        obtain ⟨Hb0, Hb1⟩ := Hb
        have hw : bv_unsigned (edenot E (mkAlu .SUB a e)) = 0 := by omega
        rw [mkAlu_denot] at hw
        simp only [alu64, alu] at hw
        rw [u_sub64] at hw
        exact bv_eq_of_sub_mod (edenot E a) (edenot E e) hw
  unfold respell_ok at H
  cases hd : decide_branch k .EQ a e with
  | none =>
      rw [hd] at H
      simp only [] at H
      exact HINT H
  | some b =>
      cases b with
      | true =>
          rw [hd] at H
          simp only [] at H
          have hb := decide_branch_sound segs E M k .EQ a e true HK hd
          exact beq_iff_eq.mp (by simpa only [branch_taken, bv_eqb] using hb)
      | false =>
          rw [hd] at H
          simp only [] at H
          exact HINT H

/--  :4047 — respelling a register keeps the state sound. -/
theorem respell_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (r : Nat) (e : expr) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_respell cs r e = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_respell at H
  by_cases hc : (0 < r && r < 32 && AsanPlanCore.expr_vars_lt (nxt cs) e &&
      respell_ok (kn cs) (reg cs r) e) = true
  · rw [ite_eq_left hc] at H
    simp only [Option.some.injEq] at H
    obtain rfl : set_reg cs r e = cs' := H
    have hsplit : ((decide (0 < r) && decide (r < 32)) &&
        AsanPlanCore.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e) = true := hc
    have hk : respell_ok (kn cs) (reg cs r) e = true := by
      have h := hsplit; simp only [Bool.and_eq_true, and_assoc] at h
      exact h.2.2.2
    have Heq := respell_ok_sound segs E (Mr A argH E cs model FULL) (kn cs) (reg cs r) e
      HC.co_know hk
    have hreg : edenot E e = edenot E (cs.a_ss.s_regs.getD r (.ELit 0)) := by
      rw [← Heq]
      rfl
    refine ⟨⟨?_, rfl, HC.co_know, HC.co_halt, HC.co_fds, HC.co_fs, HC.co_tid,
      HC.co_res, HC.co_limit, HC.co_maps, HC.co_holes, HC.co_seps, HC.co_wf,
      HC.co_bounds, HC.co_lazyb, HC.co_nasub, HC.co_none, HC.co_kinds, HC.co_totsz,
      HC.co_split, HC.co_brk, HC.co_sbrk, HC.co_eager, HC.co_abytes, HC.co_minv,
      HC.co_zero, HC.co_sinv⟩, rfl⟩
    have hn : 0 < r ∧ r < 32 := by
      have h := hsplit; simp only [Bool.and_eq_true, and_assoc] at h
      exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2.1⟩
    show regs_ok E (set_reg cs r e).a_ss.s_regs R
    show regs_ok E (sr_upd cs.a_ss.s_regs r e) R
    exact regs_ok_respell E cs.a_ss.s_regs R r e HC.co_regs hn hreg
  · rw [ite_eq_right hc] at H
    simp at H

/--  :2424 — havoc of a list of registers is a valuation extension. -/
theorem havoc_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (rs : List Nat) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_havoc nx0 cs rs = some cs') :
    ∃ E', (env_agree nx0 E E' ∧ env_agree (nxt cs) E E') ∧
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_havoc at H
  by_cases hc : (fresh_ok nx0 cs && rs.all (fun r => decide (0 < r) && decide (r < 32))) = true
  · rw [ite_eq_left hc] at H
    simp only [Option.some.injEq] at H
    obtain rfl : with_ss cs (mk_ss cs.a_ss.s_pc (sr_fresh cs.a_ss.s_regs rs cs.a_ss.s_next)
        cs.a_ss.s_know (cs.a_ss.s_next + rs.length)) = cs' := H
    have hf : fresh_ok nx0 cs = true := by
      have h := hc; simp only [Bool.and_eq_true] at h; exact h.1
    have hrs : ∀ r ∈ rs, 0 < r ∧ r < 32 := by
      intro r hr
      have h := hc
      simp only [Bool.and_eq_true] at h
      have hall : ∀ r ∈ rs, (decide (0 < r) && decide (r < 32)) = true :=
        List.all_eq_true.mp h.2
      have hr' := hall r hr
      simp only [Bool.and_eq_true] at hr'
      exact ⟨of_decide_eq_true hr'.1, of_decide_eq_true hr'.2⟩
    obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hf
    have Hag := ext_list_agree E (nxt cs) (rs.map (fun r : Nat => getr R (Z_to_bv 5 (r : Int))))
    have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E
      (ext_list E (nxt cs) (rs.map (fun r : Nat => getr R (Z_to_bv 5 (r : Int)))))
      cs R FULL model Hag hf HC
    refine ⟨ext_list E (nxt cs) (rs.map (fun r : Nat => getr R (Z_to_bv 5 (r : Int)))),
      ⟨env_agree_le nx0 (nxt cs) E _ Hag Fle, Hag⟩, ?_, rfl⟩
    refine ⟨?_, rfl, HC'.co_know, HC'.co_halt, HC'.co_fds, HC'.co_fs, HC'.co_tid,
      HC'.co_res, HC'.co_limit, HC'.co_maps, HC'.co_holes, HC'.co_seps, HC'.co_wf,
      HC'.co_bounds, HC'.co_lazyb, HC'.co_nasub, HC'.co_none, HC'.co_kinds, HC'.co_totsz,
      HC'.co_split, HC'.co_brk, HC'.co_sbrk, HC'.co_eager, HC'.co_abytes, HC'.co_minv,
      HC'.co_zero, HC'.co_sinv⟩
    exact regs_ok_sr_fresh E cs.a_ss.s_regs R rs (nxt cs) HC.co_regs Fsr hrs
  · rw [ite_eq_right hc] at H
    simp at H

/--  :3649 — introducing a fresh variable pinned to `[lo,hi]`. -/
theorem intro_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (lo hi : Int) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_intro nx0 cs lo hi = some cs') :
    ∃ E', (env_agree nx0 E E' ∧ env_agree (nxt cs) E E') ∧
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_intro at H
  by_cases hc : (fresh_ok nx0 cs && decide (0 ≤ lo) && decide (lo ≤ hi) &&
      decide (hi < two64)) = true
  · rw [ite_eq_left hc] at H
    simp only [Option.some.injEq] at H
    obtain rfl : with_ss cs (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs
        (.KRange (.EVar (nxt cs)) lo hi :: cs.a_ss.s_know) (nxt cs + 1)) = cs' := H
    have h := hc
    simp only [Bool.and_eq_true, and_assoc] at h
    obtain ⟨hf, h0, h1, h2⟩ := h
    have h0' : 0 ≤ lo := of_decide_eq_true h0
    have h1' : lo ≤ hi := of_decide_eq_true h1
    have h2' : hi < 2 ^ 64 := by
      have h : two64 = 2 ^ 64 := rfl
      rw [h] at h2
      exact of_decide_eq_true h2
    obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hf
    have Hag : env_agree (nxt cs) E (ext1 E (nxt cs) (Z_to_bv 64 lo)) :=
      ext1_agree E (nxt cs) (Z_to_bv 64 lo)
    have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E
      (ext1 E (nxt cs) (Z_to_bv 64 lo)) cs R FULL model Hag hf HC
    refine ⟨ext1 E (nxt cs) (Z_to_bv 64 lo),
      ⟨env_agree_le nx0 (nxt cs) E _ Hag Fle, Hag⟩, ?_, rfl⟩
    have Hv : bv_unsigned (edenot (ext1 E (nxt cs) (Z_to_bv 64 lo)) (.EVar (nxt cs))) = lo := by
      show bv_unsigned ((ext1 E (nxt cs) (Z_to_bv 64 lo)).ev (nxt cs)) = lo
      rw [ext1_at]
      exact u_small lo ⟨h0', by omega⟩
    refine ⟨HC'.co_regs, rfl, ?_, HC'.co_halt, HC'.co_fds, HC'.co_fs, HC'.co_tid,
      HC'.co_res, HC'.co_limit, HC'.co_maps, HC'.co_holes, HC'.co_seps, HC'.co_wf,
      HC'.co_bounds, HC'.co_lazyb, HC'.co_nasub, HC'.co_none, HC'.co_kinds, HC'.co_totsz,
      HC'.co_split, HC'.co_brk, HC'.co_sbrk, HC'.co_eager, HC'.co_abytes, HC'.co_minv,
      HC'.co_zero, HC'.co_sinv⟩
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · show lo ≤ bv_unsigned (edenot (ext1 E (nxt cs) (Z_to_bv 64 lo)) (.EVar (nxt cs))) ∧
        bv_unsigned (edenot (ext1 E (nxt cs) (Z_to_bv 64 lo)) (.EVar (nxt cs))) ≤ hi
      rw [Hv]
      exact ⟨Int.le_refl lo, h1'⟩
    · exact HC'.co_know K hK
  · rw [ite_eq_right hc] at H
    simp at H

/--  :3619 — havoc the break expression inside its known interval. -/
theorem havocbrk_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (lo hi : Int) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_havocbrk nx0 cs lo hi = some cs') :
    ∃ E', (env_agree nx0 E E' ∧ env_agree (nxt cs) E E') ∧
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_havocbrk at H
  cases hl : xlo (kn cs) cs.a_brk with
  | none => rw [hl] at H; simp at H
  | some l =>
    cases hh : xhi (kn cs) cs.a_brk with
    | none => rw [hl, hh] at H; simp at H
    | some h =>
      rw [hl, hh] at H
      simp only [] at H
      by_cases hc : (fresh_ok nx0 cs && decide (lo ≤ l) && decide (h ≤ hi)) = true
      · rw [ite_eq_left hc] at H
        simp only [Option.some.injEq] at H
        obtain rfl : ACS (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs
            (.KRange (.EVar (nxt cs)) lo hi :: cs.a_ss.s_know) (nxt cs + 1))
            cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
            (.EVar (nxt cs)) cs.a_fd cs.a_tidset = cs' := H
        have h := hc
        simp only [Bool.and_eq_true, and_assoc] at h
        obtain ⟨hf, h1, h2⟩ := h
        have h1' : lo ≤ l := of_decide_eq_true h1
        have h2' : h ≤ hi := of_decide_eq_true h2
        have L1 : l ≤ bv_unsigned (edenot E cs.a_brk) :=
          xlo_sound segs E _ (kn cs) cs.a_brk l HC.co_know hl
        have L2 : bv_unsigned (edenot E cs.a_brk) ≤ h :=
          xhi_sound segs E _ (kn cs) cs.a_brk h HC.co_know hh
        obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hf
        have Hag : env_agree (nxt cs) E
            (ext1 E (nxt cs) ((m_vmmaps model).vm_brk)) :=
          ext1_agree E (nxt cs) _
        have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E
          (ext1 E (nxt cs) ((m_vmmaps model).vm_brk)) cs R FULL model Hag hf HC
        refine ⟨ext1 E (nxt cs) ((m_vmmaps model).vm_brk),
          ⟨env_agree_le nx0 (nxt cs) E _ Hag Fle, Hag⟩, ?_, rfl⟩
        have Hv : edenot (ext1 E (nxt cs) ((m_vmmaps model).vm_brk)) (.EVar (nxt cs))
            = (m_vmmaps model).vm_brk := by
          show (ext1 E (nxt cs) ((m_vmmaps model).vm_brk)).ev (nxt cs) = _
          exact ext1_at E (nxt cs) _
        have HB0 : (m_vmmaps model).vm_brk = edenot E cs.a_brk := HC.co_brk
        refine ⟨HC'.co_regs, rfl, ?_, HC'.co_halt, HC'.co_fds, HC'.co_fs, HC'.co_tid,
          HC'.co_res, HC'.co_limit, HC'.co_maps, HC'.co_holes, HC'.co_seps, HC'.co_wf,
          HC'.co_bounds, HC'.co_lazyb, HC'.co_nasub, HC'.co_none, HC'.co_kinds,
          HC'.co_totsz, HC'.co_split, ?_, HC'.co_sbrk, HC'.co_eager, HC'.co_abytes,
          HC'.co_minv, HC'.co_zero, HC'.co_sinv⟩
        · intro K hK
          rcases List.mem_cons.mp hK with rfl | hK
          · show lo ≤ bv_unsigned (edenot (ext1 E (nxt cs) ((m_vmmaps model).vm_brk))
              (.EVar (nxt cs))) ∧
              bv_unsigned (edenot (ext1 E (nxt cs) ((m_vmmaps model).vm_brk))
                (.EVar (nxt cs))) ≤ hi
            rw [Hv, HB0]
            exact ⟨by omega, by omega⟩
          · exact HC'.co_know K hK
        · show (m_vmmaps model).vm_brk
            = edenot (ext1 E (nxt cs) ((m_vmmaps model).vm_brk)) (.EVar (nxt cs))
          rw [Hv]
      · rw [ite_eq_right hc] at H
        simp at H

/--  :2754 — outside the image hull the loaded segments read as
    `none` (`SEGS_in_hull` in `H_off_segments` form). -/
theorem seg_rom_off_hull (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (a : word) (Ha : in_hull A (bv_unsigned a) = false) :
    seg_rom segs a = none := by
  simp only [seg_rom, memory_read1_hidden segs (fun x => !(in_hull A (bv_unsigned x)))
    (by intro x hx; exact SEGS_in_hull x (by simpa using hx)) a (by simpa using Ha)]

/--  :1033 — the split of a literal addend denotes the same address.

    The proof: `to_saddr` is `split_lit` plus the addend, and
    `to_saddr_denot` already carries the (long) case analysis that
    `split_lit` needs; running it at addend `0` gives the statement. -/
theorem split_lit_denot (E : env) (e b : expr) (k : Int) (H : split_lit e = (b, k)) :
    edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k) := by
  have h := to_saddr_denot E e 0
  simp only [to_saddr, H, Int.add_zero] at h
  rw [show Z_to_bv 64 (bv_unsigned (edenot E b) + k) = adenot E (SA b k) from rfl]
  rw [h]
  show edenot E e = Z_to_bv 64 (bv_unsigned (edenot E e) + 0)
  rw [Int.add_zero]
  exact (Z_to_bv_unsigned _).symm

/--  :1063 — `split_lit` preserves the unsigned value, given that the
    split address is in range. -/
theorem u_of_split (E : env) (e b : expr) (k : Int) (Hs : split_lit e = (b, k))
    (Hr : 0 ≤ estart E (SA b k) ∧ estart E (SA b k) < 2 ^ 64) :
    bv_unsigned (edenot E e) = estart E (SA b k) := by
  have h := split_lit_denot E e b k Hs
  unfold estart at *
  rw [h, u_lit64a, Int.emod_eq_of_lt Hr.1 Hr.2]

/--  :2244 — the `KRange` fact `disj_side_fact` builds is sound. -/
theorem disj_side_fact_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (cA : expr) (oA : Int) (nA : expr) (cB : expr) (oB : Int)
    (K : kentry) (HK : know_ok segs E M k)
    (H : disj_side_fact k cA oA nA cB oB = some K)
    (HA : 0 ≤ estart E (SA cA oA)) (HB : estart E (SA cB oB) < 2 ^ 64)
    (Hle : estart E (SA cA oA) + elenZ E nA ≤ estart E (SA cB oB)) :
    kentry_ok segs E M K := by
  unfold disj_side_fact at H
  split at H
  · rename_i n blo bhi hn hb
    by_cases hc : (decide (0 ≤ n) && decide (n ≤ bhi + oB)) = true
    · rw [ite_eq_left hc] at H
      simp only [Option.some.injEq] at H
      subst H
      have hc' : 0 ≤ n ∧ n ≤ bhi + oB := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
      have Hn := xlo2_sound segs E M k nA n HK hn
      have Hbr := base_range_sound segs E M k cB blo bhi HK hb
      obtain ⟨hA0, hAlt⟩ := u64_range (edenot E cA)
      obtain ⟨hB0, hBlt⟩ := u64_range (edenot E cB)
      dsimp only [estart, elenZ] at *
      have hX0 : 0 ≤ bv_unsigned (edenot E cB) + oB := by omega
      have hXlt : bv_unsigned (edenot E cB) + oB < 2 ^ 64 := HB
      have hYlt : bv_unsigned (edenot E cA) + oA < 2 ^ 64 := by omega
      have hval : bv_unsigned (edenot E (esub (eaddz cB oB) (eaddz cA oA)))
          = (bv_unsigned (edenot E cB) + oB) - (bv_unsigned (edenot E cA) + oA) := by
        show bv_unsigned (edenot E (mkAlu .SUB (mkAlu .ADD cB (.ELit oB))
          (mkAlu .ADD cA (.ELit oA)))) = _
        rw [mkAlu_denot, mkAlu_denot, mkAlu_denot]
        show bv_unsigned ((edenot E cB + Z_to_bv 64 oB)
          - (edenot E cA + Z_to_bv 64 oA)) = _
        rw [u_sub64, u_add64, u_add64, u_lit64, u_lit64]
        simp only [two64]
        rw [show (bv_unsigned (edenot E cB) + oB % 2 ^ 64) % 2 ^ 64
              = bv_unsigned (edenot E cB) + oB from by
          rw [Int.add_comm (bv_unsigned (edenot E cB)) (oB % 2 ^ 64),
            emod_add_mod oB (bv_unsigned (edenot E cB)),
            Int.add_comm oB (bv_unsigned (edenot E cB)),
            Int.emod_eq_of_lt hX0 hXlt]]
        rw [show (bv_unsigned (edenot E cA) + oA % 2 ^ 64) % 2 ^ 64
              = bv_unsigned (edenot E cA) + oA from by
          rw [Int.add_comm (bv_unsigned (edenot E cA)) (oA % 2 ^ 64),
            emod_add_mod oA (bv_unsigned (edenot E cA)),
            Int.add_comm oA (bv_unsigned (edenot E cA)),
            Int.emod_eq_of_lt HA hYlt]]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      simp only [kentry_ok]
      rw [hval]
      exact ⟨by omega, by omega⟩
    · rw [ite_eq_right hc] at H
      cases H
  · cases H

/--  :1050 — `flat_x`'s three side conditions, denotationally. -/
theorem flat_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b : expr) (off : Int) (n : expr) (HK : know_ok segs E M k)
    (H : flat_x k b off n = true) :
    0 ≤ estart E (SA b off) ∧ estart E (SA b off) + bv_unsigned (edenot E n) ≤ 2 ^ 64 ∧
      0 < bv_unsigned (edenot E n) := by
  unfold flat_x at H
  split at H
  · rename_i lo hi nl nh hbr hxl hxh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨⟨h0, h2⟩, h1⟩ := H
    have hb := base_range_sound segs E M k b lo hi HK hbr
    have hn1 := xlo_sound segs E M k n nl HK hxl
    have hn2 := xhi_sound segs E M k n nh HK hxh
    have h2' : hi + off + nh ≤ 2 ^ 64 := h2
    dsimp only [estart] at *
    exact ⟨by omega, by omega, by omega⟩
  · cases H

/--  :2270 — `PCaseDisj`: one of the two branches is sound
    (whichever side of the apartness the `KDisj` fact lands on). -/
theorem casedisj_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (b1 b2 : expr) (csa csb : acs)
    (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_casedisj cs b1 b2 = some (csa, csb)) :
    (cs_ok segs A LIMIT SINV argH FS0 E csa R FULL model ∧ pc csa = pc cs) ∨
      (cs_ok segs A LIMIT SINV argH FS0 E csb R FULL model ∧ pc csb = pc cs) := by
  unfold node_casedisj at H
  dsimp only at H
  split at H
  · rename_i _ c1 o1 n1 c2 o2 n2 hf
    split at H
    · rename_i K1 K2 h1 h2 d1 d2
      simp only [Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      have HK := HC.co_know
      have Hf := find_disj_sound segs E (Mr A argH E cs model FULL) (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK hf
      have F1 := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs) c1 o1 n1 HK h1
      have F2 := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs) c2 o2 n2 HK h2
      dsimp only [elenZ] at Hf F1 F2
      have hkn : ∀ (Kk : kentry) (r : List kentry), know_ok segs E (Mr A argH E cs model FULL) r →
          kentry_ok segs E (Mr A argH E cs model FULL) Kk →
          know_ok segs E (Mr A argH E cs model FULL) (Kk :: r) := by
        intro Kk r hr hk K' hK'
        rcases List.mem_cons.mp hK' with h | h
        · subst h; exact hk
        · exact hr K' h
      rcases Hf with hd | hd
      · left
        have hK1 : kentry_ok segs E (Mr A argH E cs model FULL) K1 :=
          disj_side_fact_sound segs E _ (kn cs) c1 o1 n1 c2 o2 K1 HK d1 F1.1
            (by omega) hd
        refine ⟨cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _
          HC (hkn K1 (kn cs) HK hK1), rfl⟩
      · right
        have hK2 : kentry_ok segs E (Mr A argH E cs model FULL) K2 :=
          disj_side_fact_sound segs E _ (kn cs) c2 o2 n2 c1 o1 K2 HK d2 F2.1
            (by omega) hd
        refine ⟨cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _
          HC (hkn K2 (kn cs) HK hK2), rfl⟩
    · cases H
  · cases H

/--  :3379 — a `KZero` entry (or one contained in it) proves a whole
    range zero.  The argument of `APSX.kzero_x_sound` (this file's own copy). -/
theorem kzero_x_sound0 (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) (k : List kentry) (b : expr) (off : Int) (n : expr)
    (Hall : know_ok segs E M allkn) (HK : know_ok segs E M k)
    (H : kzero_x allkn k b off n = true) :
    (∀ i, 0 ≤ i → i < elenZ E n →
      M (Z_to_bv 64 (estart E (SA b off) + i)) = some (Z_to_bv 8 0)) ∧
    0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 := by
  revert H
  induction k with
  | nil =>
      intro H
      simp only [kzero_x] at H
      cases H
  | cons K rest ih =>
      intro H
      have HKr : know_ok segs E M rest := fun x hx => HK x (List.mem_cons_of_mem _ hx)
      have HKK : kentry_ok segs E M K := HK K (List.mem_cons_self ..)
      cases K with
      | KZero a zn =>
          obtain ⟨zb, zk⟩ := a
          dsimp only [kzero_x] at H
          have H2w : ∀ c1 c2 : Bool,
              (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true →
              (c1 || c2) = true ∨ kzero_x allkn rest b off n = true := by
            intro c1 c2 h
            cases c1 with
            | true => exact Or.inl (by simp)
            | false =>
                cases c2 with
                | true => exact Or.inl (by simp)
                | false => exact Or.inr (by simpa using h)
          have CORE : ∀ (zb : expr) (zk : Int) (zn : expr),
              kentry_ok segs E M (.KZero ⟨zb, zk⟩ zn) →
              bv_unsigned (edenot E zb) + zk ≤ bv_unsigned (edenot E b) + off →
              bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) ≤
                bv_unsigned (edenot E zb) + zk + bv_unsigned (edenot E zn) →
              (∀ i, 0 ≤ i → i < bv_unsigned (edenot E n) →
                M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) =
                  some (Z_to_bv 8 0)) ∧
              0 ≤ bv_unsigned (edenot E b) + off ∧
              bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) ≤ 2 ^ 64 := by
            intro zb zk zn hkk A0 B0
            obtain ⟨hfl, Hz⟩ := hkk
            obtain ⟨F1, F2, F3, F4⟩ := hfl
            dsimp only [estart, elenZ] at *
            refine ⟨?_, by omega, by omega⟩
            intro i hi1 hi2
            have h1 : 0 ≤ bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i := by
              omega
            have h2 : bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i <
                bv_unsigned (edenot E zn) := by omega
            have he := Hz _ h1 h2
            rw [show bv_unsigned (edenot E zb) + zk +
                  (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)
                = bv_unsigned (edenot E b) + off + i from by omega] at he
            exact he
          rcases H2w _ _ H with H | H
          · rw [Bool.or_eq_true] at H
            rcases H with H1 | H2
            · by_cases hc : (expr_eqb b zb && decide (zk ≤ off)) = true
              · rw [ite_eq_left hc] at H1
                split at H1
                · rename_i nh zl hxh hxl
                  simp only [decide_eq_true_eq] at H1
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                  obtain ⟨heb, hzo⟩ := hc
                  have hbz : b = zb := expr_eqb_eq b zb heb
                  have hbe : bv_unsigned (edenot E zb) = bv_unsigned (edenot E b) := by
                    rw [hbz]
                  have h1 := xhi_sound segs E M allkn n nh Hall hxh
                  have h2 := xlo_sound segs E M allkn zn zl Hall hxl
                  dsimp only [elenZ] at h1 h2 ⊢
                  exact CORE zb zk zn HKK (by omega) (by omega)
                · cases H1
              · rw [ite_eq_right hc] at H1
                cases H1
            · have hxi := xinside_sound segs E M allkn b off n zb zk zn Hall H2
              exact CORE zb zk zn HKK hxi.1 hxi.2
          · exact ih HKr H
      | KWord a w v => dsimp only [kzero_x] at H; exact ih HKr H
      | KBlob a n' kk => dsimp only [kzero_x] at H; exact ih HKr H
      | KImg lo hi => dsimp only [kzero_x] at H; exact ih HKr H
      | KAlign e m => dsimp only [kzero_x] at H; exact ih HKr H
      | KRange e lo hi => dsimp only [kzero_x] at H; exact ih HKr H
      | KWr a n' => dsimp only [kzero_x] at H; exact ih HKr H
      | KDisj a1 n1 a2 n2 => dsimp only [kzero_x] at H; exact ih HKr H
      | KFill a n' c => dsimp only [kzero_x] at H; exact ih HKr H
      | KUnk a n' => dsimp only [kzero_x] at H; exact ih HKr H

/--  :2952 — the valuation `henv` reads a havoc'd register's ORIGINAL
    value (the first occurrence of that variable in `ts`). -/
theorem henv_havoc (lo hi : Nat) (E : env) (rs ts : List expr) (i v : Nat)
    (Hlen : rs.length = ts.length) (Hi : i < ts.length)
    (Hv : is_havoc lo hi (ts.getD i (.ELit 0)) = some v)
    (Hbefore : ∀ i', i' < i → is_havoc lo hi (ts.getD i' (.ELit 0)) ≠ some v) :
    (henv lo hi E rs ts).ev v = edenot E (rs.getD i (.ELit 0)) := by
  induction rs generalizing ts i v with
  | nil =>
      cases ts with
      | nil => simp at Hi
      | cons t ts => simp at Hlen
  | cons r rs ih =>
      cases ts with
      | nil => simp at Hlen
      | cons t ts =>
          have hlen' : rs.length = ts.length := by simpa using Hlen
          cases i with
          | zero =>
              rw [List.getD_cons_zero] at Hv
              simp only [henv]
              rw [Hv]
              simp only []
              rw [upd_at]
              rw [List.getD_cons_zero]
          | succ i =>
              simp only [henv]
              have hv' : is_havoc lo hi (ts.getD i (.ELit 0)) = some v := by
                simpa only [List.getD_cons_succ] using Hv
              have hi' : i < ts.length := by simpa using Hi
              have hb' : ∀ i', i' < i → is_havoc lo hi (ts.getD i' (.ELit 0)) ≠ some v :=
                fun i' hi'' => by
                  simpa only [List.getD_cons_succ] using Hbefore (i' + 1) (by omega)
              have hrec := ih ts i v hlen' hi' hv' hb'
              cases hh : is_havoc lo hi t with
              | none =>
                  simp only []
                  simpa only [List.getD_cons_succ] using hrec
              | some v' =>
                  simp only []
                  have hne : v' ≠ v := by
                    intro he
                    exact Hbefore 0 (by omega) (by rw [List.getD_cons_zero, hh, he])
                  have hne2 : v ≠ v' := fun he => hne he.symm
                  have hstep : (upd (henv lo hi E rs ts) v' (edenot E r)).ev v
                      = (henv lo hi E rs ts).ev v := by
                    simp only [upd]
                    simp [hne2]
                  rw [hstep]
                  simpa only [List.getD_cons_succ] using hrec


/-- Counterpart of , restated for this tree's `node_spin`
    (which tests `bv_unsigned w == SPIN_WORD` instead of `is_self_jump`). -/
theorem self_jump_word (segs : List Segment) (ms : machine_state)
    (Hs : ms.ms_svc_pending = none)
    (Hf : fetch_word segs (ms_pc ms) = some (Z_to_bv 32 SPIN_WORD)) :
    DivergeSim.is_self_jump segs ms = true := by
  unfold DivergeSim.is_self_jump
  rw [Hs, Hf]
  decide

/--  :4065 — the spin node realizes the empty trace. -/
theorem node_spin_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_spin segs cs = true) :
    srealizes segs (cfg_of segs R (pc cs) FULL model) t_nil := by
  unfold node_spin at H
  rw [Bool.and_eq_true, Bool.and_eq_true] at H
  obtain ⟨⟨-, -⟩, Hw⟩ := H
  cases hf : fetch_word segs (Z_to_bv 64 (pc cs)) with
  | none => rw [hf] at Hw; simp at Hw
  | some w =>
      rw [hf] at Hw
      have hbv : bv_unsigned w = SPIN_WORD := by simpa using Hw
      have hw : w = Z_to_bv 32 SPIN_WORD := by
        apply BitVec.eq_of_toNat_eq
        have h1 : (w.toNat : Int) = SPIN_WORD := hbv
        have h2 : ((Z_to_bv 32 SPIN_WORD).toNat : Int) = SPIN_WORD := by
          unfold SPIN_WORD
          decide
        omega
      subst hw
      exact srealizes.srz_spin _ (DivergeSim.is_self_jump_to_spin segs _ model
        (self_jump_word segs _ rfl hf)) HC.co_halt

/-! ### `PShDisj`: the shadow interval's denotation -/

/--  :2292 — the shadow interval `shadow_of` builds denotes the
    shadow of `b, b+n`: its start is `b/8 + shadow_off` and its length is
    `n/8` (in the `mod 2^64` / truncated form `estart`/`elenZ` read). -/
theorem shadow_of_val (segs : List Segment) (A : atable) (E : env)
    (M : word → Option byte) (k : List kentry) (b n sb sn : expr) (sk : Int)
    (Hsh : shadow_ok A) (HK : know_ok segs E M k)
    (Hs : shadow_of A k b n = (sb, sk, sn)) (Hf : flat_x k sb sk sn = true) :
    estart E (SA sb sk) = (bv_unsigned (edenot E b) / 8 + A.shadow_off) % 2 ^ 64 ∧
      elenZ E sn = bv_unsigned (edenot E n) / 8 := by
  have hsh : 0 ≤ A.shadow_off ∧ A.shadow_off < 2 ^ 64 :=
    ⟨Hsh.1, Int.lt_of_le_of_lt Hsh.2 (by decide : (2 : Int) ^ 47 < 2 ^ 64)⟩
  unfold shadow_of at Hs
  split at Hs
  rename_i sb' sk' hsp
  obtain ⟨hsb, hsk, hsn⟩ : sb' = sb ∧ sk' = sk ∧ mkSrl k n 3 = sn := by
    simpa only [Prod.mk.injEq] using Hs
  subst hsb
  subst hsk
  subst hsn
  clear Hs
  have S3 : ∀ x : expr,
      bv_unsigned (edenot E (mkSrl k x 3)) = bv_unsigned (edenot E x) / 8 := by
    intro x
    rw [mkSrl_denot segs E M k x 3 (Z_to_bv 64 3) HK (by decide), u_srl64,
      show (bv_unsigned (Z_to_bv 64 3) % 64).toNat = 3 from by decide,
      show (2 : Int) ^ 3 = 8 from by decide]
  have F := flat_x_sound segs E M k sb' sk' (mkSrl k n 3) HK Hf
  obtain ⟨F1, F2, F3⟩ := F
  have hd := split_lit_denot E (eadd (mkSrl k b 3) (.ELit A.shadow_off)) sb' sk' hsp
  have hu : bv_unsigned (edenot E (eadd (mkSrl k b 3) (.ELit A.shadow_off)))
      = (bv_unsigned (edenot E b) / 8 + A.shadow_off) % 2 ^ 64 := by
    simp only [eadd]
    rw [mkAlu_denot]
    show bv_unsigned (edenot E (mkSrl k b 3) + Z_to_bv 64 A.shadow_off) = _
    rw [u_add64, u_lit64a, S3, Int.emod_eq_of_lt hsh.1 hsh.2]
  have h1 : bv_unsigned (edenot E sb') + sk'
      = bv_unsigned (edenot E (eadd (mkSrl k b 3) (.ELit A.shadow_off))) := by
    have h := congrArg bv_unsigned hd
    rw [u_lit64a] at h
    dsimp only [estart] at F1 F2
    rw [Int.emod_eq_of_lt F1 (by omega)] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · show bv_unsigned (edenot E sb') + sk' = _
    rw [h1, hu]
  · unfold elenZ
    exact S3 n

/--  :2316 — `PShDisj`: the shadow facts of two apart application
    ranges are apart (so a memset of one shadow keeps the other's facts).

    NB the guard of `AsanPlanCore.node_shdisj` must parenthesise its `match`
    (see the `DEFERRED` prose and the there): with Lean's
    match-swallows-`&&` parse the apartness test would only reach the dead
    `false && …` branch and this statement would be FALSE. -/
theorem shdisj_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (b1 n1 b2 n2 : expr) (cs' : acs) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (Hsh : shadow_ok A)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_shdisj A cs b1 n1 b2 n2 = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  rw [node_shdisj_eq] at H
  unfold node_shdisj_ref at H
  dsimp only at H
  split at H
  · rename_i hb1 hn1 hb2 hn2 he1 he2 he3 he4
    split at H
    · rename_i hcond
      simp only [Option.some.injEq] at H
      subst H
      have HK : know_ok segs E (Mr A argH E cs model FULL) (kn cs) := HC.co_know
      have hc := hcond
      simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hc
      obtain ⟨hLb1, hLn1, hLb2, hLn2, hF1, hF2, hFs1, hFs2, hhi1, hhi2, hAp⟩ := hc
      -- the four 8-divisibilities, from the alignment domains
      have HD1 := ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) b1 HK
      have HD2 := ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) n1 HK
      have HD3 := ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) b2 HK
      have HD4 := ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) n2 HK
      have h8 : (8 : Int) = zpow 2 3 := by decide
      have hd1 : (8 : Int) ∣ bv_unsigned (edenot E b1) := by
        rw [h8]; exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, hLb1⟩) HD1.2
      have hd2 : (8 : Int) ∣ bv_unsigned (edenot E n1) := by
        rw [h8]; exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, hLn1⟩) HD2.2
      have hd3 : (8 : Int) ∣ bv_unsigned (edenot E b2) := by
        rw [h8]; exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, hLb2⟩) HD3.2
      have hd4 : (8 : Int) ∣ bv_unsigned (edenot E n2) := by
        rw [h8]; exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, hLn2⟩) HD4.2
      obtain ⟨q1, hq1⟩ := hd1
      obtain ⟨q2, hq2⟩ := hd2
      obtain ⟨q3, hq3⟩ := hd3
      obtain ⟨q4, hq4⟩ := hd4
      have e1 : bv_unsigned (edenot E b1) / 8 = q1 := by
        rw [hq1]
        exact Int.mul_ediv_cancel_left q1 (by decide : (8 : Int) ≠ 0)
      have e2 : bv_unsigned (edenot E n1) / 8 = q2 := by
        rw [hq2]
        exact Int.mul_ediv_cancel_left q2 (by decide : (8 : Int) ≠ 0)
      have e3 : bv_unsigned (edenot E b2) / 8 = q3 := by
        rw [hq3]
        exact Int.mul_ediv_cancel_left q3 (by decide : (8 : Int) ≠ 0)
      have e4 : bv_unsigned (edenot E n2) / 8 = q4 := by
        rw [hq4]
        exact Int.mul_ediv_cancel_left q4 (by decide : (8 : Int) ≠ 0)
      -- flatness and the split addresses
      have F1 := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
        (split_lit b1).fst (split_lit b1).snd n1 HK hF1
      have F2 := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
        (split_lit b2).fst (split_lit b2).snd n2 HK hF2
      obtain ⟨F11, F12, F13⟩ := F1
      obtain ⟨F21, F22, F23⟩ := F2
      have U1 : bv_unsigned (edenot E b1) = estart E (SA (split_lit b1).fst (split_lit b1).snd) :=
        u_of_split E b1 _ _ rfl ⟨F11, by omega⟩
      have U2 : bv_unsigned (edenot E b2) = estart E (SA (split_lit b2).fst (split_lit b2).snd) :=
        u_of_split E b2 _ _ rfl ⟨F21, by omega⟩
      have AP := ranges_apart_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
        (split_lit b1).fst (split_lit b1).snd n1 (split_lit b2).fst (split_lit b2).snd n2 HK hAp
      -- the shadow facts
      have HS1 := shadow_of_val segs A E (Mr A argH E cs model FULL) (kn cs) b1 n1
        (shadow_of A (kn cs) b1 n1).fst (shadow_of A (kn cs) b1 n1).2.snd
        (shadow_of A (kn cs) b1 n1).2.fst Hsh HK rfl hFs1
      have HS2 := shadow_of_val segs A E (Mr A argH E cs model FULL) (kn cs) b2 n2
        (shadow_of A (kn cs) b2 n2).fst (shadow_of A (kn cs) b2 n2).2.snd
        (shadow_of A (kn cs) b2 n2).2.fst Hsh HK rfl hFs2
      obtain ⟨HV1, HL1⟩ := HS1
      obtain ⟨HV2, HL2⟩ := HS2
      -- the `KDisj` obligation
      have hkey : kentry_ok segs E (Mr A argH E cs model FULL)
          (.KDisj (SA (shadow_of A (kn cs) b1 n1).fst (shadow_of A (kn cs) b1 n1).2.fst)
            (shadow_of A (kn cs) b1 n1).2.snd
            (SA (shadow_of A (kn cs) b2 n2).fst (shadow_of A (kn cs) b2 n2).2.fst)
            (shadow_of A (kn cs) b2 n2).2.snd) := by
        dsimp only [kentry_ok]
        rw [HV1, HV2, HL1, HL2, e1, e2, e3, e4]
        have hb1 := u64_range (edenot E b1)
        have hb2 := u64_range (edenot E n1)
        have hb3 := u64_range (edenot E b2)
        have hb4 := u64_range (edenot E n2)
        have hs1 : 0 ≤ A.shadow_off := Hsh.1
        have hs2 : A.shadow_off ≤ 2 ^ 47 := Hsh.2
        have HM1 : (q1 + A.shadow_off) % 2 ^ 64 = q1 + A.shadow_off :=
          Int.emod_eq_of_lt (by omega) (by omega)
        have HM3 : (q3 + A.shadow_off) % 2 ^ 64 = q3 + A.shadow_off :=
          Int.emod_eq_of_lt (by omega) (by omega)
        rw [HM1, HM3]
        dsimp only [elenZ] at AP
        rw [← U1, ← U2] at AP
        rw [hq1, hq2, hq3, hq4] at AP
        omega
      have hkn : know_ok segs E (Mr A argH E cs model FULL)
          ([.KDisj (SA (shadow_of A (kn cs) b1 n1).fst (shadow_of A (kn cs) b1 n1).2.fst)
              (shadow_of A (kn cs) b1 n1).2.snd
              (SA (shadow_of A (kn cs) b2 n2).fst (shadow_of A (kn cs) b2 n2).2.fst)
              (shadow_of A (kn cs) b2 n2).2.snd] ++ kn cs) := by
        intro K hK
        rcases List.mem_append.mp hK with h | h
        · rw [List.mem_singleton] at h
          subst h
          exact hkey
        · exact HK K h
      exact ⟨cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC hkn, rfl⟩
    · simp at H
  · simp at H

theorem regs_match_h_char (lo hi : Nat) (seen : List Nat) (rs ts : List expr)
    (H0 : regs_match_h lo hi seen rs ts = true) :
    rs.length = ts.length ∧
      ∀ i, i < ts.length →
        (∃ v, is_havoc lo hi (ts.getD i (.ELit 0)) = some v ∧ v ∉ seen ∧
            ∀ i', i' < i → is_havoc lo hi (ts.getD i' (.ELit 0)) ≠ some v) ∨
        (is_havoc lo hi (ts.getD i (.ELit 0)) = none ∧
          ts.getD i (.ELit 0) = rs.getD i (.ELit 0) ∧
          AsanPlanCore.expr_vars_lt lo (ts.getD i (.ELit 0)) = true) := by
  revert seen ts
  induction rs with
  | nil =>
      intro seen ts H
      cases ts with
      | nil => exact ⟨rfl, fun i hilen => absurd hilen (by simp)⟩
      | cons t ts =>
          simp only [regs_match_h] at H
          exact absurd H (by simp)
  | cons r rs ih =>
      intro seen ts H
      cases ts with
      | nil =>
          simp only [regs_match_h] at H
          exact absurd H (by simp)
      | cons t ts =>
          -- every position of `t :: ts` except the first, via the induction hypothesis
          have STEP : ∀ (seen' : List Nat), regs_match_h lo hi seen' rs ts = true →
              (∀ u, u ∈ seen → u ∈ seen') →
              (∀ u, is_havoc lo hi t = some u → u ∈ seen') →
              rs.length = ts.length ∧
              ∀ i, i < ts.length →
                (∃ v, is_havoc lo hi ((t :: ts).getD (i + 1) (.ELit 0)) = some v ∧ v ∉ seen ∧
                    ∀ i', i' < i + 1 → is_havoc lo hi ((t :: ts).getD i' (.ELit 0)) ≠ some v) ∨
                (is_havoc lo hi ((t :: ts).getD (i + 1) (.ELit 0)) = none ∧
                  (t :: ts).getD (i + 1) (.ELit 0) = (r :: rs).getD (i + 1) (.ELit 0) ∧
                  AsanPlanCore.expr_vars_lt lo ((t :: ts).getD (i + 1) (.ELit 0)) = true) := by
            intro seen' Hm Hsub Ht
            obtain ⟨Hlen, Hc⟩ := ih seen' ts Hm
            refine ⟨Hlen, fun i hilen => ?_⟩
            rcases Hc i hilen with ⟨v, hv, hns, hb⟩ | ⟨hn, heq, hvl⟩
            · refine Or.inl ⟨v, ?_, ?_, ?_⟩
              · simpa only [List.getD_cons_succ] using hv
              · exact fun hin => hns (Hsub v hin)
              · intro i' hi' heq2
                cases i' with
                | zero =>
                    have h0 : is_havoc lo hi t = some v := by
                      simpa only [List.getD_cons_zero] using heq2
                    exact hns (Ht v h0)
                | succ j =>
                    exact hb j (by omega) (by simpa only [List.getD_cons_succ] using heq2)
            · exact Or.inr ⟨by simpa only [List.getD_cons_succ] using hn,
                by simpa only [List.getD_cons_succ] using heq,
                by simpa only [List.getD_cons_succ] using hvl⟩
          cases hv : is_havoc lo hi t with
          | some v =>
              obtain ⟨htv, hvlo, hvhi⟩ := is_havoc_range lo hi t v hv
              subst htv
              have hc : (decide (lo ≤ v) && decide (v < hi)) = true := by
                rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
                exact ⟨hvlo, hvhi⟩
              simp only [regs_match_h] at H
              rw [ite_eq_left hc] at H
              rw [Bool.and_eq_true] at H
              obtain ⟨hnew, Hm⟩ := H
              have hnsv : v ∉ seen := by
                intro hin
                have hany : (seen.any (fun x => v == x)) = true :=
                  List.any_eq_true.mpr ⟨v, hin, by simp⟩
                rw [hany] at hnew
                exact absurd hnew (by simp)
              obtain ⟨Hlen, Hc1⟩ := STEP (v :: seen) Hm
                (fun u hu => List.mem_cons_of_mem _ hu)
                (fun u hu' => by
                  rw [hv] at hu'
                  injection hu' with h
                  subst h
                  exact List.mem_cons_self ..)
              refine ⟨?_, fun i hilen => ?_⟩
              · simp only [List.length_cons]
                rw [Hlen]
              · cases i with
                | zero =>
                    refine Or.inl ⟨v, ?_, hnsv, ?_⟩
                    · simp only [List.getD_cons_zero]
                      exact hv
                    · intro i' hi'
                      exact absurd hi' (by omega)
                | succ j =>
                    exact Hc1 j (by simpa using hilen)
          | none =>
              have Hm : (expr_eqb r t && AsanPlanCore.expr_vars_lt lo t
                  && regs_match_h lo hi seen rs ts) = true := by
                cases t with
                | EVar n =>
                    simp only [is_havoc] at hv
                    split at hv
                    · cases hv
                    · rename_i hcf
                      have H' := H
                      simp only [regs_match_h] at H'
                      rw [ite_eq_right hcf] at H'
                      exact H'
                | ELit z => simpa only [regs_match_h] using H
                | EAlu op a b => simpa only [regs_match_h] using H
                | EAluw op a b => simpa only [regs_match_h] using H
                | EMd op a b => simpa only [regs_match_h] using H
                | EMdw op a b => simpa only [regs_match_h] using H
                | EExt sx l n e => simpa only [regs_match_h] using H
                | EBlob sx k i n => simpa only [regs_match_h] using H
              rw [Bool.and_eq_true] at Hm
              obtain ⟨h1, Hm'⟩ := Hm
              rw [Bool.and_eq_true] at h1
              obtain ⟨he, hvl⟩ := h1
              have hrt : r = t := expr_eqb_eq r t he
              obtain ⟨Hlen, Hc1⟩ := STEP seen Hm' (fun u hu => hu)
                (fun u hu' => by rw [hv] at hu'; cases hu')
              refine ⟨?_, fun i hilen => ?_⟩
              · simp only [List.length_cons]
                rw [Hlen]
              · cases i with
                | zero =>
                    refine Or.inr ⟨?_, ?_, ?_⟩
                    · simpa only [List.getD_cons_zero] using hv
                    · simp only [List.getD_cons_zero]
                      exact hrt.symm
                    · simpa only [List.getD_cons_zero] using hvl
                | succ j =>
                    exact Hc1 j (by simpa using hilen)

/--  :2968 — the havoc substitution reads every register back as the
    concrete register file does. -/
theorem regs_match_h_sound (lo hi : Nat) (E : env) (rs ts : List expr) (R : BvMap word)
    (H : regs_match_h lo hi [] rs ts = true) (Hlen : ts.length = 32)
    (HR : regs_ok E rs R) : regs_ok (henv lo hi E rs ts) ts R := by
  obtain ⟨Hl, Hc⟩ := regs_match_h_char lo hi [] rs ts H
  intro r
  show getr R r = edenot (henv lo hi E rs ts) (sr_get ts r)
  by_cases hr0 : (bv_eqb r 0) = true
  · have h1 : sr_get ts r = .ELit 0 := by simp only [sr_get]; rw [ite_eq_left hr0]
    have h2 : sr_get rs r = .ELit 0 := by simp only [sr_get]; rw [ite_eq_left hr0]
    have HRr := HR r
    rw [h2] at HRr
    rw [h1, HRr]
    rfl
  · have h1 : sr_get ts r = ts.getD (ridx r) (.ELit 0) := by
      simp only [sr_get]; rw [ite_eq_right hr0]
    have h2 : sr_get rs r = rs.getD (ridx r) (.ELit 0) := by
      simp only [sr_get]; rw [ite_eq_right hr0]
    have HRr : getr R r = edenot E (rs.getD (ridx r) (.ELit 0)) := by
      have h := HR r
      rw [h2] at h
      exact h
    have Hlt : ridx r < ts.length := by rw [Hlen]; exact ridx_range r
    rw [h1, HRr]
    rcases Hc (ridx r) Hlt with ⟨v, Hv, -, Hbefore⟩ | ⟨-, Heq, Hvl⟩
    · obtain ⟨htv, -, -⟩ := is_havoc_range lo hi (ts.getD (ridx r) (.ELit 0)) v Hv
      rw [htv]
      show edenot E (rs.getD (ridx r) (.ELit 0)) = (henv lo hi E rs ts).ev v
      exact (henv_havoc lo hi E rs ts (ridx r) v Hl Hlt Hv Hbefore).symm
    · rw [Heq] at Hvl ⊢
      exact edenot_agree' lo E (henv lo hi E rs ts) (rs.getD (ridx r) (.ELit 0))
        (henv_agree lo hi E rs ts) Hvl

/--  :2980 — states agreeing on every denotation have the same
    `cs_ok` (the register file is supplied separately). -/
theorem cs_ok_reenv (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (b : Nat) (E E' : env) (cs : acs) (sr' : List expr)
    (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hag : env_agree b E E') (Hb : nx0 ≤ b)
    (Hkn : AsanPlanCore.kn_vars_lt b (kn cs) = true)
    (Hmaps : maps_vars_lt b cs.a_maps = true)
    (Hallow : pairs_vars_lt b (cs.a_vis ++ cs.a_ghost) = true)
    (Hbrk : AsanPlanCore.expr_vars_lt b cs.a_brk = true)
    (Hfd : fd_vars_lt b cs.a_fd = true)
    (HR : regs_ok E' sr' R) :
    cs_ok segs A LIMIT SINV argH FS0 E' (set_regs cs sr') R FULL model := by
  have HH : hid A argH E' (set_regs cs sr') model = hid A argH E' cs model :=
    hid_ext A argH E' cs (set_regs cs sr') model rfl
  have HH' : hid A argH E' cs model = hid A argH E cs model :=
    hid_agree A nx0 argH argH_agree b E E' cs model Hag Hb Hallow
  have HA : allowA A E' (set_regs cs sr') = allowA A E cs := by
    rw [show allowA A E' (set_regs cs sr') = allowA A E' cs from rfl]
    exact allowA_agree A b E E' cs Hag Hallow
  have hden : ∀ m ∈ cs.a_maps, amap_den E' m = amap_den E m := by
    intro m hm
    obtain ⟨h1, h2⟩ := maps_vars_lt_elem b cs.a_maps m hm Hmaps
    simp only [amap_den, Prod.mk.injEq]
    exact ⟨(edenot_agree' b E E' m.am_base Hag h1).symm,
      (edenot_agree' b E E' m.am_len Hag h2).symm⟩
  refine
    { co_regs := HR
      co_log := rfl
      co_know := ?_
      co_halt := HC.co_halt
      co_fds := ?_
      co_fs := HC.co_fs
      co_tid := HC.co_tid
      co_res := HC.co_res
      co_limit := HC.co_limit
      co_maps := ?_
      co_holes := ?_
      co_seps := HC.co_seps
      co_wf := HC.co_wf
      co_bounds := HC.co_bounds
      co_lazyb := HC.co_lazyb
      co_nasub := HC.co_nasub
      co_none := ?_
      co_kinds := ?_
      co_totsz := HC.co_totsz
      co_split := HC.co_split
      co_brk := ?_
      co_sbrk := HC.co_sbrk
      co_eager := HC.co_eager
      co_abytes := ?_
      co_minv := ?_
      co_zero := ?_
      co_sinv := ?_ }
  · show know_ok segs E' (mrestrict (fun a => hid A argH E' (set_regs cs sr') model a) FULL)
      (kn cs)
    rw [HH, HH']
    exact know_ok_agree' segs b E E' _ (kn cs) Hag Hkn HC.co_know
  · exact fds_ok_agree b E E' cs.a_fd model Hag Hfd HC.co_fds
  · exact maps_match_agree b E E' cs.a_maps Hag Hmaps _ HC.co_maps
  · exact holes_agree b E E' cs.a_ylo _ cs.a_maps Hag Hmaps HC.co_holes
  · intro m hm hk
    show amap_den E' m ∈ (m_vmmaps model).vm_noaccess
    rw [hden m hm]
    exact HC.co_none m hm hk
  · intro m hm hk a Ha
    obtain ⟨hb, hl⟩ := maps_vars_lt_elem b cs.a_maps m hm Hmaps
    have hd1 : edenot E' m.am_base = edenot E m.am_base :=
      (edenot_agree' b E E' m.am_base Hag hb).symm
    have hd2 : edenot E' m.am_len = edenot E m.am_len :=
      (edenot_agree' b E E' m.am_len Hag hl).symm
    rw [hd1, hd2] at Ha
    exact HC.co_kinds m hm hk a Ha
  · rw [HC.co_brk]
    exact edenot_agree' b E E' cs.a_brk Hag Hbrk
  · rw [HA]; exact HC.co_abytes
  · rw [HA]; exact HC.co_minv
  · intro a hh hm1 hm2 hm3 hm4
    rw [HH, HH'] at hh
    have h4 : in_ghost E' (set_regs cs sr') = in_ghost E' cs := rfl
    rw [h4] at hm4
    rw [in_ghost_agree b E E' cs Hag Hallow] at hm4
    exact HC.co_zero a hh hm1 hm2 hm3 hm4
  · exact SINV_agree E E' FULL (env_agree_le nx0 b E E' Hag Hb) HC.co_sinv

/-- `estart` determines the denotation of the address . -/
theorem adenot_eq_of_estart (E : env) (a a' : saddr) (H : estart E a' = estart E a) :
    adenot E a' = adenot E a := by
  obtain ⟨b, o⟩ := a
  obtain ⟨b', o'⟩ := a'
  simp only [estart, adenot, v_addi] at H ⊢
  rw [H]

/--  :2713 — a template knowledge entry that only RE-SPLITS the address
    of an entry that already holds holds too, provided the template side is
    flat against the state's knowledge. -/
theorem kentry_eqb_h_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (X K : kentry) (HK : know_ok segs E M k)
    (HX : kentry_ok segs E M X) (Heq : kentry_eqb_h X K = true)
    (Hfl : kflat_h k K = true) :
    kentry_ok segs E M K := by
  -- the shared address fact: a re-split of a flat range starts where it started
  have SAD : ∀ (a a' : saddr) (n : Int) (ne : expr),
      saddr_eqb_h a a' = true → flat E a n → flat_x k a'.a_base a'.a_off ne = true →
      estart E a' = estart E a := by
    intro a a' n ne Hs Hf Hfx
    obtain ⟨b, o⟩ := a
    obtain ⟨b', o'⟩ := a'
    unfold saddr_eqb_h at Hs
    rw [Bool.or_eq_true] at Hs
    rcases Hs with Hs | Hs
    · exact congrArg (estart E) (saddr_eqb_eq Hs).symm
    · have h := congrArg (fun e => bv_unsigned (edenot E e)) (expr_eqb_eq _ _ Hs)
      have ho : bv_unsigned (edenot E (.ELit o)) = o % 2 ^ 64 := by
        show bv_unsigned (Z_to_bv 64 o) = o % 2 ^ 64
        simpa only [two64] using u_lit64 o
      have ho' : bv_unsigned (edenot E (.ELit o')) = o' % 2 ^ 64 := by
        show bv_unsigned (Z_to_bv 64 o') = o' % 2 ^ 64
        simpa only [two64] using u_lit64 o'
      have h2 : (bv_unsigned (edenot E b) + o % 2 ^ 64) % 2 ^ 64
          = (bv_unsigned (edenot E b') + o' % 2 ^ 64) % 2 ^ 64 := by
        have h' := h
        simp only [eaddz] at h'
        rw [mkAlu_denot, mkAlu_denot] at h'
        rw [SymExec.alu64_add_eq, SymExec.alu64_add_eq] at h'
        rw [u_add64, u_add64, ho, ho'] at h'
        simpa only [two64] using h'
      unfold flat at Hf
      obtain ⟨h0, hlt, -, -⟩ := Hf
      obtain ⟨h0', hle', hpos⟩ := flat_x_sound segs E M k b' o' ne HK Hfx
      dsimp only [estart] at h0 hlt h0' hle'
      have hlt' : bv_unsigned (edenot E b') + o' < 2 ^ 64 := by omega
      have e1 : (bv_unsigned (edenot E b) + o % 2 ^ 64) % 2 ^ 64
          = bv_unsigned (edenot E b) + o := by
        rw [Int.add_comm (bv_unsigned (edenot E b)) (o % 2 ^ 64),
          emod_add_mod o (bv_unsigned (edenot E b)),
          Int.add_comm o (bv_unsigned (edenot E b)),
          Int.emod_eq_of_lt h0 hlt]
      have e2 : (bv_unsigned (edenot E b') + o' % 2 ^ 64) % 2 ^ 64
          = bv_unsigned (edenot E b') + o' := by
        rw [Int.add_comm (bv_unsigned (edenot E b')) (o' % 2 ^ 64),
          emod_add_mod o' (bv_unsigned (edenot E b')),
          Int.add_comm o' (bv_unsigned (edenot E b')),
          Int.emod_eq_of_lt h0' hlt']
      rw [e1, e2] at h2
      dsimp only [estart]
      exact h2.symm
  have AD : ∀ (a a' : saddr), estart E a' = estart E a → adenot E a' = adenot E a :=
    fun a a' He => adenot_eq_of_estart E a a' He
  simp only [kentry_eqb_h] at Heq
  rw [Bool.or_eq_true] at Heq
  rcases Heq with Heq | Heq
  · rw [← kentry_eqb_eq _ _ Heq]
    exact HX
  · cases X with
    | KWord a w v =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' w' v'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hw, hv⟩ := Heq
          subst hw
          have hv' := expr_eqb_eq _ _ hv
          subst hv'
          obtain ⟨hm1, hm2, hm3⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (w : Int) (.ELit (w : Int)) hsad hm2 Hfl
          have hAd := AD (SA b o) (SA b' o') ES
          refine ⟨hm1, ?_, ?_⟩
          · unfold flat at hm2 ⊢
            rw [ES]
            exact hm2
          · rw [hAd]
            exact hm3
        all_goals exact Heq.elim
    | KZero a n =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' n'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hn⟩ := Heq
          have hn' := expr_eqb_eq _ _ hn
          subst hn'
          obtain ⟨hm1, hm2⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (elenZ E n) n hsad hm1 Hfl
          refine ⟨?_, ?_⟩
          · unfold flat at hm1 ⊢
            rw [ES]
            exact hm1
          · intro i hi0 hilt
            rw [ES]
            exact hm2 i hi0 hilt
        all_goals exact Heq.elim
    | KBlob a n kk =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' n' kk'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hn, hk⟩ := Heq
          have hn' := expr_eqb_eq _ _ hn
          subst hn'
          subst hk
          obtain ⟨hm1, hm2, hm3⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (elenZ E n) n hsad hm1 Hfl
          refine ⟨?_, ?_, ?_⟩
          · unfold flat at hm1 ⊢
            rw [ES]
            exact hm1
          · exact hm2
          · intro i hi0 hilt
            rw [ES]
            exact hm3 i hi0 hilt
        all_goals exact Heq.elim
    | KImg lo hi =>
        simp only [Bool.false_eq_true] at Heq
    | KAlign e m =>
        simp only [Bool.false_eq_true] at Heq
    | KRange e lo hi =>
        simp only [Bool.false_eq_true] at Heq
    | KWr a n =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' n'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hn⟩ := Heq
          have hn' := expr_eqb_eq _ _ hn
          subst hn'
          obtain ⟨hm1, hm2⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (elenZ E n) n hsad hm1 Hfl
          refine ⟨?_, ?_⟩
          · unfold flat at hm1 ⊢
            rw [ES]
            exact hm1
          · intro d m hd hm
            rw [ES]
            exact hm2 d m hd hm
        all_goals exact Heq.elim
    | KDisj a1 n1 a2 n2 =>
        simp only [Bool.false_eq_true] at Heq
    | KFill a n c =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' n' c'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hn, hc⟩ := Heq
          have hn' := expr_eqb_eq _ _ hn
          subst hn'
          subst hc
          obtain ⟨hm1, hm2⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (elenZ E n) n hsad hm1 Hfl
          refine ⟨?_, ?_⟩
          · unfold flat at hm1 ⊢
            rw [ES]
            exact hm1
          · intro i hi0 hilt
            rw [ES]
            exact hm2 i hi0 hilt
        all_goals exact Heq.elim
    | KUnk a n =>
        obtain ⟨b, o⟩ := a
        cases K <;>
          simp only [Bool.and_eq_true, and_assoc, Bool.false_eq_true] at Heq
        · rename_i a' n'
          obtain ⟨b', o'⟩ := a'
          obtain ⟨hsad, hn⟩ := Heq
          have hn' := expr_eqb_eq _ _ hn
          subst hn'
          obtain ⟨hm1, hm2⟩ := HX
          have ES := SAD (SA b o) (SA b' o') (elenZ E n) n hsad hm1 Hfl
          refine ⟨?_, ?_⟩
          · unfold flat at hm1 ⊢
            rw [ES]
            exact hm1
          · intro i hi0 hilt
            rw [ES]
            exact hm2 i hi0 hilt
        all_goals exact Heq.elim



/-! ### `PHavocWords` -/

/--  :3954 — replacing the first `KWord` value at `a` by the fresh
    variable `EVar x` keeps the knowledge sound (under the valuation that reads
    the old value at `x`) and keeps the variable bound. -/
theorem hw_apply_ok (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (a : saddr) (x : Nat) (HK : know_ok segs E M k)
    (Hv : AsanPlanCore.kn_vars_lt x k = true) :
    know_ok segs (upd E x (edenot E (hw_val k a))) M (hw_apply k a x false)
    ∧ AsanPlanCore.kn_vars_lt (x + 1) (hw_apply k a x false) = true := by
  induction k with
  | nil =>
      refine ⟨?_, rfl⟩
      intro K hK
      cases hK
  | cons X r ih =>
      have HX : kentry_ok segs E M X := HK X List.mem_cons_self
      have Hr : know_ok segs E M r := fun K hK => HK K (List.mem_cons_of_mem _ hK)
      have Hv' := Hv
      simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at Hv'
      obtain ⟨HvX, Hvr⟩ := Hv'
      -- the untouched entries survive every `upd` at `x`
      have KEEP : ∀ e : word, kentry_ok segs (upd E x e) M X := by
        intro e
        have h : know_ok segs (upd E x e) M [X] :=
          know_ok_agree' segs x E (upd E x e) M [X] (upd_agree E x e)
            (by simp only [AsanPlanCore.kn_vars_lt, HvX, Bool.and_true])
            (by
              intro K hK
              rcases List.mem_cons.mp hK with rfl | h
              · exact HX
              · cases h)
        exact h X List.mem_cons_self
      have KEEPV : AsanPlanCore.kentry_vars_lt (x + 1) X = true :=
        kentry_vars_lt_mono x (x + 1) X HvX (by omega)
      have UNIFORM : know_ok segs (upd E x (edenot E (hw_val r a))) M
            (X :: hw_apply r a x false)
          ∧ AsanPlanCore.kn_vars_lt (x + 1) (X :: hw_apply r a x false) = true := by
        have ih' := ih Hr Hvr
        refine ⟨?_, ?_⟩
        · intro K hK
          rcases List.mem_cons.mp hK with rfl | hK
          · exact KEEP _
          · exact ih'.1 K hK
        · simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
          exact ⟨KEEPV, ih'.2⟩
      cases X
      · rename_i a' w v
        cases hsb : saddr_eqb a' a with
        | true =>
            -- the replaced entry
            simp only [hw_apply, hw_val, hsb, ite_true, ite_false, Bool.false_eq_true]
            have Hva : AsanPlanCore.expr_vars_lt x a'.a_base = true := by
              have h := HvX
              simp only [AsanPlanCore.kentry_vars_lt, AsanPlanCore.saddr_vars_lt,
                Bool.and_eq_true] at h
              exact h.1
            have hAG : env_agree x E (upd E x (edenot E v)) := upd_agree E x (edenot E v)
            have hden : edenot E a'.a_base = edenot (upd E x (edenot E v)) a'.a_base :=
              edenot_agree' x E (upd E x (edenot E v)) a'.a_base hAG Hva
            have hEa : adenot (upd E x (edenot E v)) a' = adenot E a' := by
              simp only [adenot]
              rw [← hden]
            have hEs : estart (upd E x (edenot E v)) a' = estart E a' := by
              simp only [estart]
              rw [← hden]
            have hU : edenot (upd E x (edenot E v)) (.EVar x) = edenot E v := by
              show (upd E x (edenot E v)).ev x = edenot E v
              exact upd_at E x (edenot E v)
            have hHD : kentry_ok segs (upd E x (edenot E v)) M (kentry.KWord a' w (.EVar x)) := by
              obtain ⟨hw1, hf1, hr1⟩ := HX
              refine ⟨hw1, ?_, ?_⟩
              · unfold flat at hf1 ⊢
                rw [hEs]
                exact hf1
              · rw [hEa, hU]
                exact hr1
            have hTL : know_ok segs (upd E x (edenot E v)) M (hw_apply r a x true) :=
              know_ok_agree' segs x E (upd E x (edenot E v)) M (hw_apply r a x true) hAG
                (hw_apply_true_vars r a x x Hvr)
                (fun K hK => Hr K (hw_apply_true_incl r a x K hK))
            refine ⟨?_, ?_⟩
            · intro K hK
              rcases List.mem_cons.mp hK with rfl | hK
              · exact hHD
              · exact hTL K hK
            · have h1 : AsanPlanCore.kentry_vars_lt (x + 1) (kentry.KWord a' w (.EVar x))
                  = true := by
                simp only [AsanPlanCore.kentry_vars_lt, AsanPlanCore.saddr_vars_lt,
                  AsanPlanCore.expr_vars_lt, Bool.and_eq_true]
                exact ⟨expr_vars_lt_mono x (x + 1) a'.a_base Hva (by omega), by simp⟩
              simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true]
              exact ⟨h1, kn_vars_lt_mono' x (x + 1) (hw_apply r a x true)
                  (hw_apply_true_vars r a x x Hvr) (by omega)⟩
        | false =>
            simp only [hw_apply, hw_val, hsb, ite_false, Bool.false_eq_true]
            exact UNIFORM
      all_goals
        simp only [hw_apply, hw_val]
        exact UNIFORM

/--  :3991 — walking the address list keeps the knowledge sound under a
    valuation that agrees below the start of the havoc range. -/
theorem hw_go_ok (segs : List Segment) (bs : List expr) (E : env) (M : word → Option byte)
    (k : List kentry) (x : Nat) (HK : know_ok segs E M k)
    (Hv : AsanPlanCore.kn_vars_lt x k = true) :
    ∃ E', env_agree x E E' ∧ know_ok segs E' M (hw_go k bs x)
      ∧ AsanPlanCore.kn_vars_lt (x + bs.length) (hw_go k bs x) = true := by
  induction bs generalizing E M k x with
  | nil =>
      exact ⟨E, env_agree_refl x E, HK,
        by simpa only [hw_go, List.length_nil, Nat.add_zero] using Hv⟩
  | cons b r ih =>
      simp only [hw_go, List.length_cons]
      obtain ⟨H1, H2⟩ := hw_apply_ok segs E M k (sa_of b) x HK Hv
      obtain ⟨E', Hag, HK', Hv'⟩ :=
        ih (upd E x (edenot E (hw_val k (sa_of b)))) M (hw_apply k (sa_of b) x false)
          (x + 1) H1 H2
      refine ⟨E', ?_, HK', ?_⟩
      · exact env_agree_trans x E (upd E x (edenot E (hw_val k (sa_of b)))) E'
          (upd_agree E x (edenot E (hw_val k (sa_of b))))
          (env_agree_le x (x + 1) _ _ Hag (by omega))
      · have hl : x + (r.length + 1) = (x + 1) + r.length := by omega
        rw [hl]
        exact Hv'

/--  :4003 — `PHavocWords`: the listed addresses' first `KWord` values
    become fresh variables. -/
theorem havocwords_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (bs : List expr) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_havocwords nx0 cs bs = some cs') :
    ∃ E', (env_agree nx0 E E' ∧ env_agree (nxt cs) E E') ∧
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_havocwords at H
  dsimp only at H
  by_cases hf : fresh_ok nx0 cs = true
  · rw [ite_eq_left hf] at H
    simp only [Option.some.injEq] at H
    obtain rfl : with_ss cs (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs
        (hw_go cs.a_ss.s_know bs cs.a_ss.s_next) (cs.a_ss.s_next + bs.length)) = cs' := H
    obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hf
    obtain ⟨E', Hag, HK', Hv'⟩ :=
      hw_go_ok segs bs E (Mr A argH E cs model FULL) (kn cs) (nxt cs) HC.co_know Fkn
    have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E E' cs
      R FULL model Hag hf HC
    have hMr : Mr A argH E' cs model FULL = Mr A argH E cs model FULL := by
      simp only [Mr, hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow]
    have hMr2 : Mr A argH E' (bump cs bs.length) model FULL = Mr A argH E' cs model FULL := rfl
    have HKb : know_ok segs E' (Mr A argH E' (bump cs bs.length) model FULL)
        (kn (bump cs bs.length)) := by
      rw [hMr2]
      exact HC'.co_know
    have HK'' : know_ok segs E' (Mr A argH E' (bump cs bs.length) model FULL)
        (hw_go (kn cs) bs (nxt cs)) := by
      rw [hMr2, hMr]
      exact HK'
    have HCb : cs_ok segs A LIMIT SINV argH FS0 E' (bump cs bs.length) R FULL model :=
      { co_regs := HC'.co_regs
        co_log := rfl
        co_know := HKb
        co_halt := HC'.co_halt
        co_fds := HC'.co_fds
        co_fs := HC'.co_fs
        co_tid := HC'.co_tid
        co_res := HC'.co_res
        co_limit := HC'.co_limit
        co_maps := HC'.co_maps
        co_holes := HC'.co_holes
        co_seps := HC'.co_seps
        co_wf := HC'.co_wf
        co_bounds := HC'.co_bounds
        co_lazyb := HC'.co_lazyb
        co_nasub := HC'.co_nasub
        co_none := HC'.co_none
        co_kinds := HC'.co_kinds
        co_totsz := HC'.co_totsz
        co_split := HC'.co_split
        co_brk := HC'.co_brk
        co_sbrk := HC'.co_sbrk
        co_eager := HC'.co_eager
        co_abytes := HC'.co_abytes
        co_minv := HC'.co_minv
        co_zero := HC'.co_zero
        co_sinv := HC'.co_sinv }
    have hfin : cs_ok segs A LIMIT SINV argH FS0 E'
        (with_ss cs (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs
          (hw_go cs.a_ss.s_know bs cs.a_ss.s_next) (cs.a_ss.s_next + bs.length)))
        R FULL model :=
      cs_ok_set_kn segs A LIMIT SINV argH FS0 E' (bump cs bs.length) R FULL model _
        HCb HK''
    exact ⟨E', ⟨env_agree_le nx0 (nxt cs) E E' Hag Fle, Hag⟩, hfin, rfl⟩
  · rw [ite_eq_right hf] at H
    simp only [reduceCtorEq] at H


/--  :2762 — inside a successful `rdn` the base overlay is DEFINED
    (else the read would fall back to the image, which is hidden off the hull). -/
theorem rdn_bytes_some (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (M : word → Option byte) :
    ∀ (a : word) (w : Nat) (bs : List byte), rdn segs M a w = some bs →
      ∀ (x : word), bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (w : Int) →
        in_hull A (bv_unsigned x) = false → M x ≠ none := by
  intro a w
  revert a
  induction w with
  | zero =>
      intro a bs Hr x Hx Hh
      have h := Hx.2
      have hz : ((0 : Nat) : Int) = 0 := rfl
      rw [hz] at h
      omega
  | succ w ih =>
      intro a bs Hr x Hx Hh
      simp only [rdn] at Hr
      by_cases heq : bv_unsigned x = bv_unsigned a
      · have hxa : x = a := by
          apply BitVec.eq_of_toNat_eq
          exact_mod_cast heq
        rw [hxa] at Hh ⊢
        cases hMa : M a with
        | some b => simp
        | none =>
            rw [hMa] at Hr
            dsimp only at Hr
            rw [seg_rom_off_hull segs A SEGS_in_hull a Hh] at Hr
            simp at Hr
      · have hx1 : bv_unsigned a < bv_unsigned x := by omega
        have hx64 := x.isLt
        have han : a.toNat < x.toNat := by exact_mod_cast hx1
        have hlt : bv_unsigned a + 1 < (2 : Int) ^ 64 := by
          have h1 : a.toNat + 1 < 2 ^ 64 := by omega
          have h2 : ((a.toNat : Int) + 1) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast h1
          exact h2
        have hsucc : bv_unsigned (a + 1) = bv_unsigned a + 1 := PropExec.u_add1 a hlt
        have h1 : bv_unsigned a + 1 ≤ bv_unsigned x := by
          have h := hx1
          clear hlt hsucc Hx hx64
          omega
        have Hx' : bv_unsigned (a + 1) ≤ bv_unsigned x ∧
            bv_unsigned x < bv_unsigned (a + 1) + (w : Int) := by
          rw [hsucc]
          refine ⟨h1, ?_⟩
          rw [Int.add_right_comm]
          have hh := Hx.2
          push_cast at hh
          exact hh
        cases hMa : M a with
        | some b =>
            rw [hMa] at Hr
            dsimp only at Hr
            cases hr2 : rdn segs M (a + 1) w with
            | none => rw [hr2] at Hr; simp at Hr
            | some rest => exact ih (a + 1) rest hr2 x Hx' Hh
        | none =>
            rw [hMa] at Hr
            dsimp only at Hr
            cases hs : seg_rom segs a with
            | none => rw [hs] at Hr; simp at Hr
            | some b =>
                rw [hs] at Hr
                cases hr2 : rdn segs M (a + 1) w with
                | none => rw [hr2] at Hr; simp at Hr
                | some rest => exact ih (a + 1) rest hr2 x Hx' Hh

/--  :2779 — inside a successful `cover1` every byte of `[i, e)` is
    overlay-DEFINED (and `e` really is above `i`): the entry it lands in is
    flat, so its own bytes read back from the base memory.
-/
theorem cover1_sound (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (E : env) (M : word → Option byte) (k : List kentry) (b : expr) (i e : Int)
    (HK : know_ok segs E M k) (H : cover1 k b i = some e) :
    i < e ∧ ∀ j, i ≤ j → j < e → in_hull A (uE E b + j) = false →
      (0 ≤ uE E b + j ∧ uE E b + j < 2 ^ 64) ∧
        M (Z_to_bv 64 (uE E b + j)) ≠ none := by
  revert HK
  induction k with
  | nil => cases H
  | cons K rest ih =>
    have ZF : ∀ (kb : expr) (kk l : Int) (P : Option byte → Prop),
        (flat E (SA kb kk) (elenZ E (.ELit l)) ∧
          ∀ i0, 0 ≤ i0 → i0 < elenZ E (.ELit l) →
            P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) →
        (∀ x, P x → x ≠ none) →
        (if (expr_eqb b kb && decide (0 ≤ l) && decide (l < two64) && decide (kk ≤ i)
            && decide (i < kk + l)) then some (kk + l) else none) = some e →
        i < e ∧ ∀ j, i ≤ j → j < e → in_hull A (uE E b + j) = false →
          (0 ≤ uE E b + j ∧ uE E b + j < 2 ^ 64) ∧
            M (Z_to_bv 64 (uE E b + j)) ≠ none := by
      intro kb kk l P hfl hP hc
      split at hc
      · rename_i hg
        simp only [Option.some.injEq] at hc
        have he : e = kk + l := hc.symm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        obtain ⟨⟨⟨⟨hb, hl0⟩, hlt⟩, hki⟩, hie⟩ := hg
        have hbk : b = kb := expr_eqb_eq b kb hb
        rw [hbk] at ⊢
        have hlz : elenZ E (.ELit l) = l :=
          elenZ_lit E l ⟨hl0, by simpa only [two64] using hlt⟩
        rw [hlz] at hfl
        obtain ⟨hf, hfall⟩ := hfl
        obtain ⟨hf0, hf1, -, hf3⟩ := hf
        dsimp only [uE, estart] at *
        refine ⟨by omega, ?_⟩
        intro j hj1 hj2 hh
        have hj3 : j < kk + l := by omega
        have hjeq : bv_unsigned (edenot E kb) + j
            = bv_unsigned (edenot E kb) + kk + (j - kk) := by omega
        have hr1 : 0 ≤ bv_unsigned (edenot E kb) + j := by omega
        have hr2 : bv_unsigned (edenot E kb) + j < 2 ^ 64 := by omega
        refine ⟨⟨hr1, hr2⟩, ?_⟩
        rw [hjeq]
        exact hP _ (hfall (j - kk) (by omega) (by omega))
      · cases hc
    simp only [cover1] at H
    split at H
    · rename_i o e1 heq
      split at heq
      · -- `KWord`
        rename_i Kx kb kk w v
        intro HK
        have HKK : kentry_ok segs E M (kentry.KWord (SA kb kk) w v) := HK _ (by simp)
        split at heq
        · rename_i hg
          simp only [Option.some.injEq] at heq H
          have he : e = kk + (w : Int) := by omega
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          obtain ⟨⟨hb, hki⟩, hie⟩ := hg
          have hbk : b = kb := expr_eqb_eq b kb hb
          rw [hbk] at ⊢
          obtain ⟨- , hfl, hrd⟩ := HKK
          have hu : bv_unsigned (adenot E (SA kb kk)) = estart E (SA kb kk) :=
            flat_u E (SA kb kk) (w : Int) hfl
          obtain ⟨hf0, hf1, -, hf3⟩ := hfl
          dsimp only [uE, estart] at *
          refine ⟨by omega, ?_⟩
          intro j hj1 hj2 hh
          have hj3 : j < kk + (w : Int) := by omega
          have hr1 : 0 ≤ bv_unsigned (edenot E kb) + j := by omega
          have hr2 : bv_unsigned (edenot E kb) + j < 2 ^ 64 := by omega
          have hxs : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + j))
              = bv_unsigned (edenot E kb) + j :=
            u_small (z := bv_unsigned (edenot E kb) + j) ⟨hr1, hr2⟩
          refine ⟨⟨hr1, hr2⟩, ?_⟩
          have hh' : in_hull A (bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + j)))
              = false := by rw [hxs]; exact hh
          refine rdn_bytes_some segs A SEGS_in_hull M (adenot E (SA kb kk)) w
            (word_to_le_bytes w (edenot E v)) hrd
            (Z_to_bv 64 (bv_unsigned (edenot E kb) + j)) ?_ hh'
          rw [hxs, hu]
          omega
        · cases heq
      · -- `KZero`
        rename_i Kx kb kk l
        intro HK
        refine ZF kb kk l (fun x => x = some (Z_to_bv 8 0)) ?_
          (fun x hx => by rw [hx]; simp) (heq.trans H)
        exact HK (kentry.KZero (SA kb kk) (.ELit l)) (by simp)
      · -- `KFill`
        rename_i Kx kb kk l c
        intro HK
        refine ZF kb kk l (fun x => x = some (Z_to_bv 8 c)) ?_
          (fun x hx => by rw [hx]; simp) (heq.trans H)
        exact HK (kentry.KFill (SA kb kk) (.ELit l) c) (by simp)
      · -- `KBlob`
        rename_i Kx kb kk l b0
        intro HK
        have HKK : kentry_ok segs E M (kentry.KBlob (SA kb kk) (.ELit l) b0) := HK _ (by simp)
        obtain ⟨h1, -, h2⟩ := HKK
        refine ZF kb kk l (fun x => ∃ y, x = some y) ⟨h1, ?_⟩
          (fun x hx => by obtain ⟨y, hy⟩ := hx; rw [hy]; simp) (heq.trans H)
        exact fun i0 h0 h1 => ⟨_, h2 i0 h0 h1⟩
      · -- `KUnk`
        rename_i Kx kb kk l
        intro HK
        refine ZF kb kk l (fun x => x ≠ none) ?_ (fun x hx => hx) (heq.trans H)
        exact HK (kentry.KUnk (SA kb kk) (.ELit l)) (by simp)
      · cases heq
    · rename_i o heq
      intro HK
      exact ih H (fun X hX => HK X (by simp [hX]))

/--  :2822 — walking `i, stop` with `cover1` keeps the coverage of
    every byte of `[i, stop)`. -/
theorem cover_x_sound (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (fuel : Nat) (E : env) (M : word → Option byte) (k : List kentry) (b : expr)
    (i stop : Int) (HK : know_ok segs E M k) (H : cover_x fuel k b i stop = true) :
    ∀ j, i ≤ j → j < stop → in_hull A (uE E b + j) = false →
      (0 ≤ uE E b + j ∧ uE E b + j < 2 ^ 64) ∧
        M (Z_to_bv 64 (uE E b + j)) ≠ none := by
  induction fuel generalizing i with
  | zero => simp only [cover_x] at H; cases H
  | succ f ih =>
    simp only [cover_x] at H
    by_cases hle : stop ≤ i
    · rw [ite_eq_left hle] at H
      intro j hj1 hj2 _
      omega
    · rw [ite_eq_right hle] at H
      split at H
      · rename_i e hc
        by_cases hlt : i < e
        · rw [ite_eq_left hlt] at H
          intro j hj1 hj2 hh
          have hcov := cover1_sound segs A SEGS_in_hull E M k b i e HK hc
          by_cases hje : j < e
          · exact hcov.2 j hj1 hje hh
          · exact ih e H j (by omega) hj2 hh
        · rw [ite_eq_right hlt] at H
          cases H
      · cases H


/--  :2837 — a `KUnk` entry that `kunk_covered` accepts really holds:
    flat (from `flat_x`), and every byte of `b+o, +n` off the hull is
    overlay-defined (the `cover_x` walk, each step of which is `cover1_sound`;
    the hull apartness comes from `off_image_x`). -/
theorem kunk_covered_sound (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (E : env) (M : word → Option byte) (k : List kentry) (K : kentry)
    (HK : know_ok segs E M k) (H : kunk_covered A k K = true) :
    kentry_ok segs E M K := by
  unfold kunk_covered at H
  split at H
  · rename_i Kx b o n
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    obtain ⟨⟨⟨⟨⟨h0, h40⟩, himg⟩, hflat⟩, hoff⟩, hcov⟩ := H
    have hn0 : 0 ≤ n := by omega
    have hn64 : n < (2 : Int) ^ 64 := by
      have h1 : zpow 2 40 < (2 : Int) ^ 64 := by decide
      omega
    have hlen : elenZ E (.ELit n) = n := elenZ_lit E n ⟨hn0, hn64⟩
    have hbn : bv_unsigned (edenot E (.ELit n)) = n := hlen
    have hF := flat_x_sound segs E M k b o (.ELit n) HK hflat
    rw [hbn] at hF
    obtain ⟨hF0, hF2, hF3⟩ := hF
    -- the hull apartness: `[b+o, +n)` misses `[img_lo, img_hi)`
    have hKHI : KHI < (2 : Int) ^ 64 := by decide
    have hhi : A.img_hi ≤ KHI := HULL_ok.2.2.2
    have hlo : 0 ≤ A.img_lo := HULL_ok.1
    have hlen2 : elenZ E (.ELit (A.img_hi - A.img_lo)) = A.img_hi - A.img_lo :=
      elenZ_lit E (A.img_hi - A.img_lo) ⟨by omega, by omega⟩
    have hAP := ranges_apart_x_sound segs E M k b o (.ELit n) (.ELit 0) A.img_lo
      (.ELit (A.img_hi - A.img_lo)) HK hoff
    rw [hlen, hlen2] at hAP
    dsimp only [estart] at hAP
    rw [edenot_lit, u_lit0, Int.zero_add] at hAP
    have hAP' : bv_unsigned (edenot E b) + o + n ≤ A.img_lo ∨
        A.img_hi ≤ bv_unsigned (edenot E b) + o := by
      rcases hAP with h | h
      · exact Or.inl h
      · right
        omega
    have hzeq : ∀ i : Int, uE E b + (o + i) = bv_unsigned (edenot E b) + o + i := by
      intro i
      dsimp only [uE]
      omega
    refine ⟨?_, ?_⟩
    · -- flat
      show flat E (SA b o) (elenZ E (.ELit n))
      rw [hlen]
      exact ⟨hF0, by omega, by omega, by omega⟩
    · intro i hi0 hin
      rw [hlen] at hin
      have hIn : in_hull A (uE E b + (o + i)) = false := by
        simp only [in_hull]
        have hz := hzeq i
        rcases hAP' with h | h
        · rw [show decide (A.img_lo ≤ uE E b + (o + i)) = false from
              decide_eq_false (by rw [hz]; omega)]
          simp
        · rw [show decide (uE E b + (o + i) < A.img_hi) = false from
              decide_eq_false (by rw [hz]; omega)]
          simp
      have hcov' := cover_x_sound segs A SEGS_in_hull (k.length + 1) E M k b o (o + n)
        HK hcov (o + i) (by omega) (by omega) hIn
      rw [hzeq i] at hcov'
      exact hcov'.2
  · cases H


/--  :2858 — every entry of the template's knowledge is entailed by the
    state's, byte for byte: either verbatim (`kentry_eqb`), as a re-splitting of
    a flat entry (`kentry_eqb_h` at `kflat_h`), as an image sub-range
    (`kimg_sub_covered`), or by coverage (`kunk_covered`). -/
theorem kn_incl_h_sound (segs : List Segment) (A : atable)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (E : env) (M : word → Option byte) (k tk : List kentry)
    (HK : know_ok segs E M k) (H : kn_incl_h A k tk = true) :
    know_ok segs E M tk := by
  intro K Hin
  have HK1 : kn_incl1_h A k K = true := List.all_eq_true.mp H K Hin
  -- the `KImg` sub-range arm
  have IMG : kimg_sub_covered k K = true → kentry_ok segs E M K := by
    intro himg
    unfold kimg_sub_covered at himg
    cases K with
    | KImg lo hi =>
        obtain ⟨X, hX, hXc⟩ := List.any_eq_true.mp himg
        cases X with
        | KImg lo' hi' =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hXc
            obtain ⟨h1, h2⟩ := hXc
            obtain ⟨ha, hb, hc⟩ := HK _ hX
            exact ⟨by omega, by omega, fun i hi1 hi2 => hc i (by omega) (by omega)⟩
        | _ => simp at hXc
    | _ => cases himg
  unfold kn_incl1_h at HK1
  split at HK1
  · rename_i hex
    obtain ⟨X, hX, heq⟩ := List.any_eq_true.mp hex
    have hXK : X = K := kentry_eqb_eq X K heq
    rw [← hXK]
    exact HK X hX
  · split at HK1
    · rename_i hc1 hfl
      split at HK1
      · rename_i hexh
        obtain ⟨X, hX, heq⟩ := List.any_eq_true.mp hexh
        exact kentry_eqb_h_sound segs E M k X K HK (HK X hX) heq hfl
      · split at HK1
        · rename_i himg
          exact IMG himg
        · exact kunk_covered_sound segs A SEGS_in_hull HULL_ok E M k K HK HK1
    · rename_i hx1 hx2
      rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at HK1
      split at HK1
      · rename_i himg
        exact IMG himg
      · exact kunk_covered_sound segs A SEGS_in_hull HULL_ok E M k K HK HK1

/--  :3011 — the havoc-aware entailment `entails_h` is sound: if `T`'s
    template is entailed by `cs`, then some valuation (the havoc `henv`) makes
    `T` a `cs_ok` state, agreeing with `E` below `lo` and above `hi`.
-/
theorem entails_h_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (lo hi : Nat) (E : env) (cs T : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : entails_h A lo hi cs T = true) (Hlo : nx0 ≤ lo)
    (Hlen : T.a_ss.s_regs.length = 32) :
    ∃ E', env_agree lo E E' ∧ (∀ n, hi ≤ n → E'.ev n = E.ev n) ∧
      cs_ok segs A LIMIT SINV argH FS0 E' T R FULL model ∧ pc T = pc cs := by
  simp only [entails_h, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at H
  obtain ⟨H, Habytes⟩ := H
  obtain ⟨H, Heager⟩ := H
  obtain ⟨H, Hylo⟩ := H
  obtain ⟨H, Htotsz⟩ := H
  obtain ⟨H, Htid⟩ := H
  obtain ⟨H, Hfd⟩ := H
  obtain ⟨H, Hbrk⟩ := H
  obtain ⟨H, HghostL⟩ := H
  obtain ⟨H, HvisL⟩ := H
  obtain ⟨H, HmapsL⟩ := H
  obtain ⟨H, Hfdv⟩ := H
  obtain ⟨H, Hbrkv⟩ := H
  obtain ⟨H, Hghostv⟩ := H
  obtain ⟨H, Hvisv⟩ := H
  obtain ⟨H, Hmapsv⟩ := H
  obtain ⟨H, Hknv⟩ := H
  obtain ⟨H, Hkn⟩ := H
  obtain ⟨H, Hregs⟩ := H
  obtain ⟨H, Hresv⟩ := H
  obtain ⟨H, Hlog⟩ := H
  have Hlog' : T.a_ss.s_log = [] := by
    cases hl : T.a_ss.s_log with
    | nil => rfl
    | cons x xs =>
        rw [hl] at Hlog
        exact absurd Hlog (by simp)
  have Hresv' : T.a_ss.s_resv = none := by
    cases hr : T.a_ss.s_resv with
    | none => rfl
    | some a =>
        rw [hr] at Hresv
        exact absurd Hresv (by simp)
  have HmapsE : cs.a_maps = T.a_maps :=
    list_eqb_eq amap_eqb (fun x y h => amap_eqb_eq h) _ _ HmapsL
  have HvisE : cs.a_vis = T.a_vis :=
    list_eqb_eq pair_eqb (fun x y h => pair_eqb_eq h) _ _ HvisL
  have HghostE : cs.a_ghost = T.a_ghost :=
    list_eqb_eq pair_eqb (fun x y h => pair_eqb_eq h) _ _ HghostL
  have HbrkE : cs.a_brk = T.a_brk := expr_eqb_eq _ _ Hbrk
  have HfdE : cs.a_fd = T.a_fd := afd_eqb_eq _ _ Hfd
  refine ⟨henv lo hi E cs.a_ss.s_regs T.a_ss.s_regs, henv_agree lo hi E _ _,
    fun n hn => henv_high lo hi E _ _ n hn, ?_, H.symm⟩
  -- `Tc`: `T` with `cs`'s registers
  have Evis : (set_regs T cs.a_ss.s_regs).a_vis = cs.a_vis := HvisE.symm
  have Eghost : (set_regs T cs.a_ss.s_regs).a_ghost = cs.a_ghost := HghostE.symm
  have HH : hid A argH E (set_regs T cs.a_ss.s_regs) model = hid A argH E cs model :=
    hid_ext A argH E cs (set_regs T cs.a_ss.s_regs) model Evis
  have HA : allowA A E (set_regs T cs.a_ss.s_regs) = allowA A E cs := by
    unfold allowA
    rw [Evis, Eghost]
  have HMr : Mr A argH E (set_regs T cs.a_ss.s_regs) model FULL
      = Mr A argH E cs model FULL := by
    unfold Mr
    rw [HH]
  have HCtotsz := HC.co_totsz
  have HCeager := HC.co_eager
  have HCabytes := HC.co_abytes
  have hgE : in_ghost E (set_regs T cs.a_ss.s_regs) = in_ghost E cs := by
    unfold in_ghost
    rw [Eghost]
  have HC1 : cs_ok segs A LIMIT SINV argH FS0 E (set_regs T cs.a_ss.s_regs) R FULL model := by
    refine
      { co_regs := HC.co_regs
        co_log := rfl
        co_know := ?_
        co_halt := HC.co_halt
        co_fds := ?_
        co_fs := HC.co_fs
        co_tid := ?_
        co_res := HC.co_res
        co_limit := HC.co_limit
        co_maps := ?_
        co_holes := ?_
        co_seps := HC.co_seps
        co_wf := HC.co_wf
        co_bounds := HC.co_bounds
        co_lazyb := HC.co_lazyb
        co_nasub := HC.co_nasub
        co_none := ?_
        co_kinds := ?_
        co_totsz := ?_
        co_split := ?_
        co_brk := ?_
        co_sbrk := HC.co_sbrk
        co_eager := ?_
        co_abytes := ?_
        co_minv := ?_
        co_zero := ?_
        co_sinv := HC.co_sinv }
    · rw [HMr]
      exact kn_incl_h_sound segs A SEGS_in_hull HULL_ok E _ (kn cs) (kn T) HC.co_know Hkn
    · rw [show (set_regs T cs.a_ss.s_regs).a_fd = cs.a_fd from HfdE.symm]
      exact HC.co_fds
    · intro h
      exact HC.co_tid (by rw [Htid]; exact h)
    · rw [show (set_regs T cs.a_ss.s_regs).a_maps = cs.a_maps from HmapsE.symm]
      exact HC.co_maps
    · intro m hm
      rw [show (set_regs T cs.a_ss.s_regs).a_maps = cs.a_maps from HmapsE.symm] at hm
      exact holes_mono E cs.a_ylo T.a_ylo _ cs.a_maps (fun m' hm' => HC.co_holes m' hm') Hylo m hm
    · intro m hm hk
      rw [show (set_regs T cs.a_ss.s_regs).a_maps = cs.a_maps from HmapsE.symm] at hm
      exact HC.co_none m hm hk
    · intro m hm hk a Ha
      rw [show (set_regs T cs.a_ss.s_regs).a_maps = cs.a_maps from HmapsE.symm] at hm
      exact HC.co_kinds m hm hk a Ha
    · show sum_sizes _ ≤ T.a_totsz
      omega
    · obtain ⟨Y, h1, h2, h3, h4⟩ := HC.co_split
      exact ⟨Y, by show T.a_ylo ≤ Y; omega, h2, h3, h4⟩
    · rw [show (set_regs T cs.a_ss.s_regs).a_brk = cs.a_brk from HbrkE.symm]
      exact HC.co_brk
    · show eager_used model ≤ T.a_eager
      omega
    · show A_bytes (allowA A E (set_regs T cs.a_ss.s_regs)) ≤ T.a_abytes
      rw [HA]
      omega
    · rw [HA]
      exact HC.co_minv
    · intro a h1 h2 h3 h4 h5
      refine HC.co_zero a ?_ h2 h3 h4 ?_
      · rw [← HH]; exact h1
      · rw [← hgE]; exact h5
  -- `T` really is `Tc` with its own registers put back
  have hT1 : T = set_regs T T.a_ss.s_regs := by
    obtain ⟨⟨p, sr, lg, k, nx, rv⟩, m, t, y, eg, v, g, ab, br, f, ti⟩ := T
    dsimp only at Hlog' Hresv' ⊢
    subst Hlog'
    subst Hresv'
    rfl
  have ET : T = set_regs (set_regs T cs.a_ss.s_regs) T.a_ss.s_regs := by
    rw [show set_regs (set_regs T cs.a_ss.s_regs) T.a_ss.s_regs = set_regs T T.a_ss.s_regs
      from rfl, ← hT1]
  rw [ET]
  have hpairs : pairs_vars_lt lo
      ((set_regs T cs.a_ss.s_regs).a_vis ++ (set_regs T cs.a_ss.s_regs).a_ghost) = true := by
    show pairs_vars_lt lo (T.a_vis ++ T.a_ghost) = true
    have h1 : pairs_vars_lt lo T.a_vis = true := Hvisv
    have h2 : pairs_vars_lt lo T.a_ghost = true := Hghostv
    simp only [pairs_vars_lt, List.all_append] at h1 h2 ⊢
    rw [h1, h2]
    rfl
  exact cs_ok_reenv segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 lo E
    (henv lo hi E cs.a_ss.s_regs T.a_ss.s_regs) (set_regs T cs.a_ss.s_regs) T.a_ss.s_regs
    R FULL model HC1 (henv_agree lo hi E _ _) Hlo Hknv Hmapsv hpairs Hbrkv Hfdv
    (regs_match_h_sound lo hi E cs.a_ss.s_regs T.a_ss.s_regs R Hregs Hlen HC.co_regs)


/--  :3055 — `PDiamond`: the joined state is entailed by both arm end
    states, so either arm's `cs_ok` lifts to it (with a valuation agreeing
    below `nx0` and below the branch's `nx`). -/
theorem diamond_join_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (nx : Nat) (joinpc : Int) (rs : List Nat) (ca cb csj : acs)
    (H : node_diamond_join A nx0 nx joinpc rs ca cb = some csj) :
    (∀ (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model),
      cs_ok segs A LIMIT SINV argH FS0 E ca R FULL model →
      ∃ E', (env_agree nx0 E E' ∧ env_agree nx E E') ∧
        cs_ok segs A LIMIT SINV argH FS0 E' csj R FULL model ∧ pc csj = pc ca)
    ∧ (∀ (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model),
      cs_ok segs A LIMIT SINV argH FS0 E cb R FULL model →
      ∃ E', (env_agree nx0 E E' ∧ env_agree nx E E') ∧
        cs_ok segs A LIMIT SINV argH FS0 E' csj R FULL model ∧ pc csj = pc cb) := by
  unfold node_diamond_join at H
  dsimp only at H
  split at H
  · rename_i hg
    simp only [Option.some.injEq] at H
    subst H
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
    obtain ⟨⟨⟨⟨⟨⟨hpa, hpb⟩, hvlt⟩, hlen⟩, hn0⟩, hea⟩, heb⟩ := hg
    have hnx : nx ≤ max nx (max (nxt ca) (nxt cb)) := Nat.le_max_left nx _
    constructor
    · intro E R FULL model HC
      obtain ⟨E', Hag, -, HC', Hpc⟩ := entails_h_sound segs A LIMIT nx0 SEGS_in_hull
        HULL_ok SINV SINV_agree argH argH_agree FS0 _ _ E ca _ R FULL model HC hea hn0 hlen
      exact ⟨E', ⟨env_agree_le nx0 _ E E' Hag hn0, env_agree_le nx _ E E' Hag hnx⟩, HC', Hpc⟩
    · intro E R FULL model HC
      obtain ⟨E', Hag, -, HC', Hpc⟩ := entails_h_sound segs A LIMIT nx0 SEGS_in_hull
        HULL_ok SINV SINV_agree argH argH_agree FS0 _ _ E cb _ R FULL model HC heb hn0 hlen
      exact ⟨E', ⟨env_agree_le nx0 _ E E' Hag hn0, env_agree_le nx _ E E' Hag hnx⟩, HC', Hpc⟩
  · cases H


/--  :3926 — `PAbstractCell`: the off-image byte range `b, b+n` becomes
    one `KUnk` entry.  Pure weakening: `kunk_covered` (the cover chain) makes
    the new entry true, and `kn_cutout` removes everything else about the
    range. -/
theorem abstractcell_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs cs' : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b : expr) (n : Int)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_abstractcell A cs b n = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_abstractcell at H
  dsimp only at H
  split at H
  · rename_i hcov
    simp only [Option.some.injEq] at H
    subst H
    refine ⟨?_, pc_set_kn cs _⟩
    refine cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _ HC ?_
    intro K' hK'
    rw [List.mem_cons] at hK'
    rcases hK' with rfl | hK'
    · exact kunk_covered_sound segs A SEGS_in_hull HULL_ok E _ (kn cs) _ HC.co_know hcov
    · exact know_ok_cutout segs E _ _ (kn cs) (split_lit b).fst (.ELit n)
        (split_lit b).snd HC.co_know (fun x _ => rfl) K' hK'
  · cases H


/--  :2477 — re-spelling the big `KWord` values as the fresh variables
    that the valuation gives them keeps the knowledge true. -/
theorem kn_bigsubst_sound (segs : List Segment) (K : Nat) (k : List kentry) (nx : Nat)
    (E2 : env) (M : word → Option byte)
    (HK : know_ok segs E2 M k) (Hv : AsanPlanCore.kn_vars_lt nx k = true)
    (Hvals : ∀ i, i < (kn_bigexprs K k).length →
      E2.ev (nx + i) = edenot E2 ((kn_bigexprs K k).getD i (.ELit 0))) :
    know_ok segs E2 M (kn_bigsubst K k nx).1 := by
  revert Hvals Hv HK
  induction k generalizing nx with
  | nil => intro HK Hv Hvals X hX; cases hX
  | cons x r ih =>
      intro HK Hv Hvals
      have Hx : kentry_ok segs E2 M x := HK x (by simp)
      have Hr : know_ok segs E2 M r := fun X hX => HK X (by simp [hX])
      simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at Hv
      obtain ⟨Hvx, Hvr⟩ := Hv
      have TAIL : ∀ (y : kentry) (r' : List kentry),
          know_ok segs E2 M r' → kentry_ok segs E2 M y →
          know_ok segs E2 M (y :: r') := by
        intro y r' Hr' Hy K' hK'
        rw [List.mem_cons] at hK'
        rcases hK' with rfl | hK'
        · exact Hy
        · exact Hr' K' hK'
      cases x with
      | KWord a w v =>
          by_cases hb : bigb K v = true
          · -- the substituted case
            have hge : kn_bigexprs K (kentry.KWord a w v :: r) = v :: kn_bigexprs K r := by
              simp only [kn_bigexprs, hb, ite_true]
            have hl : (kn_bigexprs K (kentry.KWord a w v :: r)).length
                = (kn_bigexprs K r).length + 1 := by
              rw [hge]
              simp
            have Hvr' : AsanPlanCore.kn_vars_lt (nx + 1) r = true :=
              kn_vars_lt_mono' nx (nx + 1) r Hvr (by omega)
            have Hvals' : ∀ i, i < (kn_bigexprs K r).length →
                E2.ev (nx + 1 + i) = edenot E2 ((kn_bigexprs K r).getD i (.ELit 0)) := by
              intro i hi
              have h := Hvals (i + 1) (by rw [hl]; omega)
              rw [hge] at h
              rw [show nx + (i + 1) = nx + 1 + i from by omega] at h
              simpa using h
            have Hih := ih (nx + 1) Hr Hvr' Hvals'
            simp only [kn_bigsubst, hb, ite_true]
            intro K' hK'
            rw [List.mem_cons] at hK'
            rcases hK' with rfl | hK'
            · obtain ⟨H1, H2, H3⟩ := Hx
              refine ⟨H1, H2, ?_⟩
              have h0 := Hvals 0 (by rw [hl]; omega)
              have h0' : edenot E2 (.EVar nx) = edenot E2 v := by
                have h1 : E2.ev (nx + 0) = edenot E2 v := by
                  rw [hge] at h0
                  simpa using h0
                show E2.ev nx = edenot E2 v
                rwa [Nat.add_zero] at h1
              rw [H3, h0']
            · exact Hih K' hK'
          · -- `bigb` false: the entry is kept verbatim
            have hbf : bigb K v = false := by
              cases hh : bigb K v with
              | false => rfl
              | true => exact absurd hh hb
            have hge : kn_bigexprs K (kentry.KWord a w v :: r) = kn_bigexprs K r := by
              simp only [kn_bigexprs, hbf, Bool.false_eq_true, ite_false]
            have HvalsR : ∀ i, i < (kn_bigexprs K r).length →
                E2.ev (nx + i) = edenot E2 ((kn_bigexprs K r).getD i (.ELit 0)) := by
              intro i hi
              have h := Hvals i (by rw [hge]; exact hi)
              rwa [hge] at h
            simp only [kn_bigsubst, hbf, Bool.false_eq_true, ite_false]
            exact TAIL _ _ (ih nx Hr Hvr HvalsR) Hx
      | KZero a n =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KBlob a n kb =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KImg lo hi =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KAlign e m =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KRange e lo hi =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KWr a n =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KDisj a1 n1 a2 n2 =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KFill a n c =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx
      | KUnk a n =>
          simp only [kn_bigsubst, ite_true]
          exact TAIL _ _ (ih nx Hr Hvr Hvals) Hx

/--  :919 — a read that succeeds on the RESTRICTED overlay only
    touches bytes that are NOT hidden (`H_off_segments` is what rules out the
    fall-back to the image: a hidden byte off every segment reads back as
    `none`, so the run would have stopped there). -/
theorem rdn_visible (segs : List Segment) (H : word → Bool) (FULL : word → Option byte) :
    ∀ (a : word) (w : Nat) (bs : List byte),
      H_off_segments segs H → rdn segs (mrestrict H FULL) a w = some bs →
      ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + (w : Int) →
        H x = false := by
  intro a w
  revert a
  induction w with
  | zero =>
      intro a bs HH Hr x Hx
      have h2 := Hx.2
      push_cast at h2
      omega
  | succ w ih =>
      intro a bs HH Hr x Hx
      simp only [rdn] at Hr
      cases hHa : H a with
      | true =>
          -- the first byte is hidden: the overlay says `none` and the image
          -- says `none` too, so the read cannot have succeeded
          have hmem : mrestrict H FULL a = none := by
            simp [mrestrict, hHa]
          rw [hmem] at Hr
          dsimp only at Hr
          have hs : seg_rom segs a = none := by
            simp only [seg_rom, memory_read1_hidden segs H HH a hHa]
          rw [hs] at Hr
          simp at Hr
      | false =>
          have hmem : mrestrict H FULL a = FULL a := by
            simp [mrestrict, hHa]
          rw [hmem] at Hr
          by_cases hx : bv_unsigned x = bv_unsigned a
          · have hxa : x = a := by
              apply BitVec.eq_of_toNat_eq
              exact_mod_cast hx
            rw [hxa]
            exact hHa
          · have hx1 : bv_unsigned a < bv_unsigned x := by omega
            have hx64 := x.isLt
            have han : a.toNat < x.toNat := by exact_mod_cast hx1
            have hlt : bv_unsigned a + 1 < (2 : Int) ^ 64 := by
              have h1 : a.toNat + 1 < 2 ^ 64 := by omega
              have h2 : ((a.toNat : Int) + 1) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast h1
              exact h2
            have hsucc : bv_unsigned (a + 1) = bv_unsigned a + 1 := PropExec.u_add1 a hlt
            have Hx' : bv_unsigned (a + 1) ≤ bv_unsigned x ∧
                bv_unsigned x < bv_unsigned (a + 1) + (w : Int) := by
              rw [hsucc]
              refine ⟨by omega, ?_⟩
              rw [Int.add_right_comm]
              have hh := Hx.2
              push_cast at hh
              exact hh
            cases hF : FULL a with
            | some b =>
                rw [hF] at Hr
                dsimp only at Hr
                cases hr2 : rdn segs (mrestrict H FULL) (a + 1) w with
                | none => rw [hr2] at Hr; simp at Hr
                | some rest => exact ih (a + 1) rest HH hr2 x Hx'
            | none =>
                rw [hF] at Hr
                dsimp only at Hr
                cases hs : seg_rom segs a with
                | none => rw [hs] at Hr; simp at Hr
                | some b =>
                    rw [hs] at Hr
                    cases hr2 : rdn segs (mrestrict H FULL) (a + 1) w with
                    | none => rw [hr2] at Hr; simp at Hr
                    | some rest => exact ih (a + 1) rest HH hr2 x Hx'

/--  :943 — knowledge survives making MORE bytes visible
    (`H2 ⊆ H1`), provided its `KImg` facts lie in the hull: at a byte that
    `H1` hides, the two restricted memories agree (a byte hidden by `H1` but
    visible in `H2` would have to be a hull byte, which `H1` never hides),
    and the bytes a `KWord` reads are never hidden by `H1` (`rdn_visible`). -/
theorem know_ok_unhide (segs : List Segment) (A : atable) (E : env)
    (H1 H2 : word → Bool) (FULL : word → Option byte) (k : List kentry)
    (HH1 : H_off_segments segs H1) (Hki : kimg_in_hull A k)
    (Hsub : ∀ a, H2 a = true → H1 a = true)
    (Hhull : ∀ a : word, in_hull A (bv_unsigned a) = true → H1 a = false)
    (HK : know_ok segs E (mrestrict H1 FULL) k) :
    know_ok segs E (mrestrict H2 FULL) k := by
  -- at a byte `H1` does not hide, restricting by `H2` changes nothing
  have AG : ∀ a, H1 a = false → mrestrict H2 FULL a = mrestrict H1 FULL a := by
    intro a Ha
    cases h2 : H2 a with
    | true =>
        rw [Hsub a h2] at Ha
        simp at Ha
    | false => simp [mrestrict, Ha, h2]
  -- the definedness order used by `KWr`
  have GR : StoreOk.mem_grows (mrestrict H1 FULL) (mrestrict H2 FULL) := by
    intro x Hx
    by_cases h1 : H1 x = true
    · simp [mrestrict, h1] at Hx
    · by_cases h2 : H2 x = true
      · exact absurd (Hsub x h2) h1
      · have h1f : H1 x = false := by
          cases h : H1 x with
          | false => rfl
          | true => exact absurd h h1
        have h2f : H2 x = false := by
          cases h : H2 x with
          | false => rfl
          | true => exact absurd h h2
        rw [show mrestrict H1 FULL x = FULL x from by simp [mrestrict, h1f]] at Hx
        simp [mrestrict, h2f]
        exact Hx
  -- a byte that the `H1`-restricted memory has defined is not hidden by `H1`
  have H1false : ∀ a : word, mrestrict H1 FULL a ≠ none → H1 a = false := by
    intro a h
    cases hh : H1 a with
    | false => rfl
    | true => exact absurd (by simp [mrestrict, hh]) h
  intro K hK
  have HKK := HK K hK
  have HKi := Hki K hK
  cases K with
  | KWord a w v =>
      obtain ⟨Hw, Hfl, Hrd⟩ := HKK
      refine ⟨Hw, Hfl, ?_⟩
      have heq : rdn segs (mrestrict H2 FULL) (adenot E a) w
          = rdn segs (mrestrict H1 FULL) (adenot E a) w := by
        refine PropExec.rdn_ext segs w (mrestrict H2 FULL) (mrestrict H1 FULL)
          (adenot E a) ?_ ?_
        · have hfu := flat_u E a (w : Int) Hfl
          obtain ⟨_, _, _, h4⟩ := Hfl
          show bv_unsigned (adenot E a) + (w : Int) ≤ ((2 ^ 64 : Nat) : Int)
          rw [hfu]
          exact h4
        · intro x Hx
          exact AG _ (rdn_visible segs H1 FULL (adenot E a) w _ HH1 Hrd x Hx)
      rw [heq]
      exact Hrd
  | KZero a n =>
      obtain ⟨Hfl, Hz⟩ := HKK
      refine ⟨Hfl, ?_⟩
      intro i Hi1 Hi2
      have hz := Hz i Hi1 Hi2
      rw [AG _ (H1false _ (by rw [hz]; simp))]
      exact hz
  | KBlob a n kb =>
      obtain ⟨Hfl, Hlen, Hz⟩ := HKK
      refine ⟨Hfl, Hlen, ?_⟩
      intro i Hi1 Hi2
      have hz := Hz i Hi1 Hi2
      rw [AG _ (H1false _ (by rw [hz]; simp))]
      exact hz
  | KImg lo hi =>
      obtain ⟨HA, HB, HC⟩ := HKK
      obtain ⟨Ki1, Ki2⟩ := HKi
      refine ⟨HA, HB, ?_⟩
      intro i Hi1 Hi2
      have Hh : in_hull A (bv_unsigned (Z_to_bv 64 i)) = true := by
        have hi2 : i < 2 ^ 64 := by
          have h : i < hi := Hi2
          have h' : hi ≤ 2 ^ 64 := HB
          omega
        unfold in_hull
        rw [u_small (z := i) ⟨by omega, hi2⟩]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by omega⟩
      rw [AG _ (Hhull _ Hh)]
      exact HC i Hi1 Hi2
  | KAlign e m => exact HKK
  | KRange e lo hi => exact HKK
  | KWr a n =>
      obtain ⟨Hfl, Hs⟩ := HKK
      refine ⟨Hfl, ?_⟩
      intro d m Hd Hdm
      exact StoreOk.store_ok_mono segs m (mrestrict H1 FULL) (mrestrict H2 FULL)
        (BitVec.ofInt 64 (estart E a + d)) GR (Hs d m Hd Hdm)
  | KDisj a1 n1 a2 n2 => exact HKK
  | KFill a n c =>
      obtain ⟨Hfl, Hz⟩ := HKK
      refine ⟨Hfl, ?_⟩
      intro i Hi1 Hi2
      have hz := Hz i Hi1 Hi2
      rw [AG _ (H1false _ (by rw [hz]; simp))]
      exact hz
  | KUnk a n =>
      obtain ⟨Hfl, Hz⟩ := HKK
      refine ⟨Hfl, ?_⟩
      intro i Hi1 Hi2
      have hz := Hz i Hi1 Hi2
      rw [AG _ (H1false _ hz)]
      exact hz

/-- `map_remove` of a pair whose base is the removed address (the
    `RefNodes` twins `map_remove_head` / `map_remove_skip` are NOT in this
    file's import cone, so they are restated here). -/
theorem map_remove_head' (a n : word) (l : List (word × word)) :
    map_remove ((a, n) :: l) a = map_remove l a := by
  simp [map_remove]

/-- `map_remove` keeps a pair whose base differs from the removed address. -/
theorem map_remove_skip' (p : word × word) (a : word) (l : List (word × word))
    (H : p.1 ≠ a) : map_remove (p :: l) a = p :: map_remove l a := by
  obtain ⟨b, s⟩ := p
  have h' : (b == a) = false := beq_eq_false_iff_ne.mpr H
  simp [map_remove, h']

/--  :3495 — the engine behind `unvis_sound`'s `HK1`/`HK2`: the
    entries `kn_unfill` keeps are still valid in a memory that (a) agrees with
    the old one OUTSIDE the unfilled range and (b) defines nothing the old one
    did not. -/
theorem kn_unfill_keep (segs : List Segment) (E : env) (M M' : word → Option byte)
    (k : List kentry) (b : expr) (off : Int) (n : expr)
    (HK : know_ok segs E M k)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
      estart E (SA b off) + elenZ E n ≤ bv_unsigned x → M' x = M x)
    (Hnone : ∀ x : word, M x = none → M' x = none) :
    know_ok segs E M' (kn_unfill k b off n) := by
  intro K hK
  simp only [kn_unfill] at hK
  obtain ⟨hKk, hkeep⟩ := List.mem_filter.mp hK
  rw [Bool.or_eq_true] at hkeep
  have HKK := HK K hKk
  rcases hkeep with himg | hap
  · -- `KImg`: it only says the overlay is undefined, and `M'` defines no more
    cases K with
    | KImg lo hi =>
        obtain ⟨I1, I2, I3⟩ := HKK
        refine ⟨I1, I2, ?_⟩
        intro i Hi1 Hi2
        exact Hnone _ (I3 i Hi1 Hi2)
    | _ => exact absurd himg (by simp [kimg_b])
  · -- apart from the range: the entry survives `kentry_apart_keep`
    rw [kentry_apart_bp_eq] at hap
    exact kentry_apart_keep segs E M M' k K b off n HK HKK hap Hout

/--  :1184 — dropping a tracked entry from the ledger is the same as
    dropping its `amap` from the tracked list.  The `Nodup` and uniqueness
    hypotheses are what make the ledger's matching element the entry's OWN
    interval: they rule out a second ledger element with the same base. -/
theorem maps_match_remove (E : env) (ms : List amap) :
    ∀ (l : List (word × word)) (m : amap), maps_match E ms l → m ∈ ms →
      is_fog m = false → l.Nodup →
      (∀ iv, iv ∈ l → iv.1 = edenot E m.am_base → iv = amap_den E m) →
      maps_match E (ms.filter (fun m' => !(amap_eqb m' m)))
        (map_remove l (edenot E m.am_base)) := by
  induction ms with
  | nil => intro l m _ Hin; simp at Hin
  | cons m0 ms ih =>
      intro l m HM Hin Hf Hnd Huniq
      rw [maps_match] at HM
      by_cases heq : amap_eqb m0 m = true
      · -- the head IS `m`
        have hm0 : m = m0 := (amap_eqb_eq heq).symm
        subst hm0
        rw [Hf] at HM
        obtain ⟨l', rfl, HM⟩ := HM
        rw [show (m :: ms).filter (fun m' => !(amap_eqb m' m))
              = ms.filter (fun m' => !(amap_eqb m' m)) from by
              rw [List.filter_cons_of_neg (by simp [heq])]]
        rw [show map_remove (amap_den E m :: l') (edenot E m.am_base)
              = map_remove l' (edenot E m.am_base) from map_remove_head' _ _ _]
        rw [List.nodup_cons] at Hnd
        obtain ⟨Hnotin, Hnd'⟩ := Hnd
        have hnotin' : m ∉ ms := by
          intro hm
          exact Hnotin (maps_match_In E ms l' m HM hm Hf)
        have hall : ∀ x, x ∈ ms → Bool.not (amap_eqb x m) = true := by
          intro x hx
          have hne : amap_eqb x m = false := by
            cases h : amap_eqb x m with
            | false => rfl
            | true => exact absurd (by rw [← amap_eqb_eq h]; exact hx) hnotin'
          rw [hne]; rfl
        rw [filter_all_true (fun m' => Bool.not (amap_eqb m' m)) ms hall]
        have hnin : ∀ b sz, (b, sz) ∈ l' → b ≠ edenot E m.am_base := by
          intro b sz hbs hb
          have h1 : (b, sz) = amap_den E m :=
            Huniq (b, sz) (List.mem_cons_of_mem _ hbs) hb
          exact Hnotin (by rw [← h1]; exact hbs)
        rw [map_remove_notin' l' (edenot E m.am_base) hnin]
        exact HM
      · -- the head is NOT `m`
        have hf0 : amap_eqb m0 m = false := by
          cases h : amap_eqb m0 m with
          | false => rfl
          | true => exact absurd h heq
        rcases List.mem_cons.mp Hin with rfl | Hin
        · rw [amap_eqb_refl'] at hf0
          exact absurd hf0 (by simp)
        · rw [show (m0 :: ms).filter (fun m' => !(amap_eqb m' m))
                = m0 :: ms.filter (fun m' => !(amap_eqb m' m)) from by
                rw [List.filter_cons_of_pos (by simp [hf0])]]
          cases hfog : is_fog m0 with
          | true =>
              rw [hfog] at HM
              rw [maps_match]
              simp only [hfog, ite_true]
              rcases HM with HM | ⟨iv, l', rfl, Hsz, HM⟩
              · exact Or.inl (ih l m HM Hin Hf Hnd Huniq)
              · rw [List.nodup_cons] at Hnd
                obtain ⟨Hnotin, Hnd'⟩ := Hnd
                have Hne : iv.1 ≠ edenot E m.am_base := by
                  intro hb
                  refine Hnotin ?_
                  rw [Huniq iv (List.mem_cons_self ..) hb]
                  exact maps_match_In E ms l' m HM Hin Hf
                rw [map_remove_skip' iv _ l' Hne]
                exact Or.inr ⟨iv, map_remove l' (edenot E m.am_base), rfl, Hsz,
                  ih l' m HM Hin Hf Hnd'
                    (fun x hx => Huniq x (List.mem_cons_of_mem _ hx))⟩
          | false =>
              rw [hfog] at HM
              rw [maps_match]
              simp only [hfog, Bool.false_eq_true, ite_false]
              obtain ⟨l', rfl, HM⟩ := HM
              rw [List.nodup_cons] at Hnd
              obtain ⟨Hnotin, Hnd'⟩ := Hnd
              have Hne : (amap_den E m0).1 ≠ edenot E m.am_base := by
                intro hb
                refine Hnotin ?_
                rw [Huniq (amap_den E m0) (List.mem_cons_self ..) hb]
                exact maps_match_In E ms l' m HM Hin Hf
              rw [map_remove_skip' (amap_den E m0) _ l' Hne]
              exact ⟨map_remove l' (edenot E m.am_base), rfl,
                ih l' m HM Hin Hf Hnd'
                  (fun x hx => Huniq x (List.mem_cons_of_mem _ hx))⟩

/-- The values `kn_bigexprs` keeps only mention variables below the counter. -/
theorem kn_bigexprs_vars_lt (K b : Nat) (k : List kentry)
    (Hk : AsanPlanCore.kn_vars_lt b k = true) :
    ∀ i, i < (kn_bigexprs K k).length →
      AsanPlanCore.expr_vars_lt b ((kn_bigexprs K k).getD i (.ELit 0)) = true := by
  induction k with
  | nil =>
      intro i hi
      simp [kn_bigexprs] at hi
  | cons x r ih =>
      have Hx : AsanPlanCore.kentry_vars_lt b x = true := by
        have h := Hk
        simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at h
        exact h.1
      have Hr : AsanPlanCore.kn_vars_lt b r = true := by
        have h := Hk
        simp only [AsanPlanCore.kn_vars_lt, Bool.and_eq_true] at h
        exact h.2
      cases x with
      | KWord a w v =>
          by_cases hb : bigb K v = true
          · -- `bigb` fires: the value itself is kept (and later substituted)
            have hge : kn_bigexprs K (kentry.KWord a w v :: r)
                = v :: kn_bigexprs K r := by
              simp only [kn_bigexprs, hb, ite_true]
            intro i hi
            rw [hge] at hi ⊢
            cases i with
            | zero =>
                simp only [List.getD_cons_zero]
                have hx := Hx
                simp only [AsanPlanCore.kentry_vars_lt, Bool.and_eq_true] at hx
                exact hx.2
            | succ j =>
                simp only [List.getD_cons_succ]
                exact ih Hr j (by simpa using hi)
          · -- `bigb` does not fire: the entry is kept but contributes no value
            have hbf : bigb K v = false := by
              cases hh : bigb K v with
              | false => rfl
              | true => exact absurd hh hb
            have hge : kn_bigexprs K (kentry.KWord a w v :: r)
                = kn_bigexprs K r := by
              simp only [kn_bigexprs, hbf, Bool.false_eq_true, ite_false]
            intro i hi
            rw [hge] at hi ⊢
            exact ih Hr i hi
      | KZero a n =>
          intro i hi
          exact ih Hr i hi
      | KBlob a n kb =>
          intro i hi
          exact ih Hr i hi
      | KImg lo hi =>
          intro i hi
          exact ih Hr i hi
      | KAlign e m =>
          intro i hi
          exact ih Hr i hi
      | KRange e lo hi =>
          intro i hi
          exact ih Hr i hi
      | KWr a n =>
          intro i hi
          exact ih Hr i hi
      | KDisj a1 n1 a2 n2 =>
          intro i hi
          exact ih Hr i hi
      | KFill a n c =>
          intro i hi
          exact ih Hr i hi
      | KUnk a n =>
          intro i hi
          exact ih Hr i hi

/--  :2504 — `PHavocBig`: every register and every `KWord` value whose
    expression is bigger than `K` nodes is re-spelled as a fresh variable.
    Registers are `havoc_sound`'s job; the knowledge is re-valued by extending
    the valuation with the denotations of `kn_bigexprs` (`ext_list`), which is
    a pure weakening (`co_know` only has to survive the *restricted* memory,
    which the extension does not touch) plus the valuation extension. -/
theorem havocbig_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (K : Nat) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_havocbig nx0 cs K = some cs') :
    ∃ E', (env_agree nx0 E E' ∧ env_agree (nxt cs) E E') ∧
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧ pc cs' = pc cs := by
  unfold node_havocbig at H
  dsimp only at H
  -- The two `Option`/`Prod` scrutinees: revert, generalize, then `cases` (a
  -- direct `split` would destructure the `Prod` into its `Nat` components).
  revert H
  generalize hh : node_havoc nx0 cs ((List.range' 1 31).filter (fun r => bigb K (reg cs r))) = r0
  cases r0 with
  | none =>
      intro H
      cases H
  | some cs1 =>
      intro H
      dsimp only at H
      by_cases hf : (fresh_ok nx0 cs1) = true
      · rw [ite_eq_left hf] at H
        revert H
        generalize hs : kn_bigsubst K (kn cs1) (nxt cs1) = pp
        cases pp with
        | mk k' c =>
            intro H
            dsimp only at H
            simp only [Option.some.injEq] at H
            obtain rfl : cs' = with_ss cs1
                (mk_ss (pc cs1) cs1.a_ss.s_regs k' (nxt cs1 + c)) := H.symm
            obtain ⟨E1, ⟨Hag0, Hag1⟩, HC1, Hpc1⟩ :=
              havoc_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL
                model _ cs1 HC hh
            obtain ⟨_, Fkn, _, _, _, _, Fle⟩ := fresh_ok_parts nx0 cs1 hf
            have hnx : nxt cs ≤ nxt cs1 := by
              have h1 := (node_havoc_nxt nx0 cs _ cs1 hh).1
              omega
            let vals : List word := (kn_bigexprs K (kn cs1)).map (edenot E1)
            let E2 : env := ext_list E1 (nxt cs1) vals
            have Hag2 : env_agree (nxt cs1) E1 E2 := ext_list_agree E1 (nxt cs1) vals
            have Hvals : ∀ i, i < (kn_bigexprs K (kn cs1)).length →
                E2.ev (nxt cs1 + i)
                  = edenot E2 ((kn_bigexprs K (kn cs1)).getD i (.ELit 0)) := by
              intro i hi
              have hlen : i < vals.length := by
                rw [show vals = (kn_bigexprs K (kn cs1)).map (edenot E1) from rfl,
                  List.length_map]
                exact hi
              refine (ext_list_at E1 (nxt cs1) vals i hlen).trans ?_
              have h2 : vals.getD i (Z_to_bv 64 0)
                  = edenot E1 ((kn_bigexprs K (kn cs1)).getD i (.ELit 0)) :=
                getD_map' (edenot E1) (kn_bigexprs K (kn cs1)) i (Z_to_bv 64 0)
                  (.ELit 0) rfl
              rw [h2]
              exact edenot_agree' (nxt cs1) E1 E2 _ Hag2
                (kn_bigexprs_vars_lt K (nxt cs1) (kn cs1) Fkn i hi)
            refine ⟨E2, ⟨?_, ?_⟩, ?_, ?_⟩
            · exact env_agree_trans nx0 E E1 E2 Hag0
                (env_agree_le nx0 (nxt cs1) E1 E2 Hag2 Fle)
            · exact env_agree_trans (nxt cs) E E1 E2 Hag1
                (env_agree_le (nxt cs) (nxt cs1) E1 E2 Hag2 hnx)
            · have HC2 := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                E1 E2 cs1 R FULL model Hag2 hf HC1
              have hk' : (kn_bigsubst K (kn cs1) (nxt cs1)).1 = k' := by rw [hs]
              have HK' : know_ok segs E2 (Mr A argH E2 cs1 model FULL) k' := by
                have h := kn_bigsubst_sound segs K (kn cs1) (nxt cs1) E2
                  (Mr A argH E2 cs1 model FULL) HC2.co_know Fkn Hvals
                rwa [hk'] at h
              have hset : set_kn (bump cs1 c) k'
                  = with_ss cs1 (mk_ss (pc cs1) cs1.a_ss.s_regs k' (nxt cs1 + c)) := rfl
              rw [← hset]
              have HCb : cs_ok segs A LIMIT SINV argH FS0 E2 (bump cs1 c) R FULL model :=
                { HC2 with co_log := rfl }
              exact cs_ok_set_kn segs A LIMIT SINV argH FS0 E2 (bump cs1 c) R FULL model k'
                HCb HK'
            · exact Hpc1
      · rw [ite_eq_right hf] at H
        simp at H


/-- `HAB`: forgetting a visible range into the ghost list does
    not grow the allowed set's byte total.  The `(b, n)` entry leaves
    `a_vis` (dropping its TWO intervals, range and shadow) and re-enters at
    the END of `a_ghost` (adding the same two back, as `allow1 (b, n)`);
    since `(b, n)` was visible, `vis.filter (vis_here b n)` holds it at least
    once, so the total loses `(k - 1) * A_bytes (allow1 (b, n))` for some
    `k >= 1`.  The entries left in `a_vis` are untouched, so the only
    arithmetic is `1 <= #(vis.filter (vis_here b n))` (the `Hin` witness)
    plus `A_bytes_allow1_nonneg`. -/
theorem A_bytes_unvis_le (A : atable) (E : env) (ss : sym_state) (ms : List amap)
    (totsz ylo eager abytes : Int) (vis ghost : List (expr × expr))
    (brk : expr) (fd : afd) (tid : Bool) (b n : expr)
    (Hin : vis.any (vis_here b n) = true) :
    A_bytes (allowA A E (ACS ss ms totsz ylo eager
        (vis.filter (fun p => !vis_here b n p)) (ghost ++ [(b, n)]) abytes brk fd tid))
      ≤ A_bytes (allowA A E (ACS ss ms totsz ylo eager vis ghost abytes brk fd tid)) := by
  have HA : allowA A E (ACS ss ms totsz ylo eager
      (vis.filter (fun p => !vis_here b n p)) (ghost ++ [(b, n)]) abytes brk fd tid)
      = (vis.filter (fun p => !vis_here b n p)).flatMap (allow1 A E)
        ++ (ghost.flatMap (allow1 A E) ++ allow1 A E (b, n)) := by
    simp only [allowA, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  have HA0 : allowA A E (ACS ss ms totsz ylo eager vis ghost abytes brk fd tid)
      = vis.flatMap (allow1 A E) ++ ghost.flatMap (allow1 A E) := by
    simp only [allowA, List.flatMap_append]
  have hFF : vis.filter (fun p => !(!vis_here b n p)) = vis.filter (vis_here b n) := by
    congr 1
    funext p
    cases vis_here b n p <;> rfl
  have GONE : ∀ p ∈ vis.filter (vis_here b n), p = (b, n) := by
    intro p hp
    exact vis_here_eq b n p (List.mem_filter.mp hp).2
  obtain ⟨q, hq, hf⟩ := List.any_eq_true.mp Hin
  have hlen : 1 ≤ ((vis.filter (vis_here b n)).length : Int) := by
    have hmem : q ∈ vis.filter (vis_here b n) := List.mem_filter.mpr ⟨hq, hf⟩
    have hpos : 0 < (vis.filter (vis_here b n)).length :=
      List.length_pos_iff.mpr (fun h => by rw [h] at hmem; simp at hmem)
    omega
  have hnn : 0 ≤ A_bytes (allow1 A E (b, n)) := A_bytes_allow1_nonneg A E (b, n)
  rw [HA, HA0, A_bytes_app, A_bytes_app, A_bytes_app,
    A_bytes_fm_split A E (fun p => !vis_here b n p) vis, hFF,
    A_bytes_fm_here A E b n _ GONE]
  have hmul : A_bytes (allow1 A E (b, n))
      ≤ ((vis.filter (vis_here b n)).length : Int) * A_bytes (allow1 A E (b, n)) := by
    have hk : ((vis.filter (vis_here b n)).length : Int)
        = 1 + (((vis.filter (vis_here b n)).length - 1 : Nat) : Int) := by omega
    rw [hk, Int.add_mul, Int.one_mul]
    exact Int.le_add_of_nonneg_right
      (Int.mul_nonneg (Int.natCast_nonneg _) hnn)
  omega

/--  :3447 — `PUnvis b n`: turning the visible range `(b, n)` into a
    GHOST range keeps every `cs_ok` field.

    The state changes in exactly four places: `s_know` (two `kn_unfill`s:
    first the range `[b, b+n)`, then its shadow `[shadow_off + b/8, +n/8)`),
    `a_vis` (the pair is filtered out) and `a_ghost` (it is appended).  So of
    `cs_ok`'s 27 fields, 23 are the old ones verbatim; the four that need
    work are `co_know` (the knowledge about the restricted memory moves from
    `Mr cs` to `Mr cs'`, bridged by the `Mmid` memory that agrees with `Mmid`
    on the two dropped ranges and with `Mr cs` outside them), `co_abytes`
    (`A_bytes_unvis_le`), `co_minv` (`page_allowedb` is monotone because the
    allowed set only GROWS: every `a_vis` pair is either kept or re-added as
    `(b, n)`) and `co_zero` (a hidden lazy byte that was a shadow byte of
    `(b, n)` read zero while visible, by `kzero_x`).

    the extra hypothesis `(Hsh : shadow_ok A)` is explicit here,
    exactly as in `shdisj_sound` / `shadow_of_val`; `check_sound` threads
    `SHADOW_ok` into its `PUnvis` arm.
-/
theorem unvis_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b n : expr) (cs' : acs) (Hsh : shadow_ok A)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_unvis A cs b n = some cs') :
    cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model ∧ pc cs' = pc cs := by
  rw [node_unvis_eq] at H
  unfold node_unvis_ref at H
  dsimp only at H
  cases hb : xhi (kn cs) b with
  | none => rw [hb] at H; simp at H
  | some bh =>
    cases hn : xhi (kn cs) n with
    | none => rw [hb, hn] at H; simp at H
    | some nh =>
      rw [hb, hn] at H
      dsimp only at H
      split at H
      · rename_i hg
        simp only [Option.some.injEq] at H
        -- the guard's seven facts
        have hc := hg
        simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hc
        obtain ⟨Hany, He1, He2, Hfl, Hceil, Hfls, Hkz⟩ := hc
        have HK : know_ok segs E (Mr A argH E cs model FULL) (kn cs) := HC.co_know
        have Hbh : bv_unsigned (edenot E b) ≤ bh :=
          xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) b bh HK hb
        have Hnh : bv_unsigned (edenot E n) ≤ nh :=
          xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) n nh HK hn
        obtain ⟨F1a, F1b, F1c⟩ := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
          (split_lit b).fst (split_lit b).snd n HK Hfl
        generalize hub : bv_unsigned (edenot E b) = ub at *
        generalize hun : bv_unsigned (edenot E n) = un at *
        have hub0 : 0 ≤ ub := by rw [← hub]; exact bv_unsigned_nonneg _
        have hun0 : 0 ≤ un := by rw [← hun]; exact bv_unsigned_nonneg _
        have hubE : uE E b = ub := hub
        have hunE : uE E n = un := hun
        have hlenZ : elenZ E n = un := hun
        obtain ⟨HS0, HSn⟩ := shadow_of_val segs A E (Mr A argH E cs model FULL) (kn cs) b n
          (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.snd
          (shadow_of A (kn cs) b n).2.fst Hsh HK rfl Hfls
        rw [hub] at HS0
        rw [hun] at HSn
        have hlenSN : elenZ E (shadow_of A (kn cs) b n).2.snd = un / 8 := HSn
        have HB : estart E (SA (split_lit b).fst (split_lit b).snd) = ub :=
          ((u_of_split E b (split_lit b).fst (split_lit b).snd rfl ⟨F1a, by omega⟩).symm).trans hub
        have HSS : estart E (SA (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.fst)
            = A.shadow_off + ub / 8 := by
          rw [HS0]
          have h1 : 0 ≤ ub / 8 + A.shadow_off := by
            have h2 := Int.ediv_nonneg hub0 (by decide : (0 : Int) ≤ 8)
            have h3 : 0 ≤ A.shadow_off := Hsh.1
            omega
          have hdivb : ub / 8 ≤ ub := Int.ediv_le_self 8 hub0
          have h2 : ub / 8 + A.shadow_off < 2 ^ 64 := by
            have hs47 : A.shadow_off ≤ 2 ^ 47 := Hsh.2
            have hCeil : CEIL < 2 ^ 47 := by decide
            omega
          rw [Int.emod_eq_of_lt h1 h2]
          omega
        generalize hS : A.shadow_off + ub / 8 = S at *
        have Hshhi : A.shadow_off + (ub + un) / 8 = S + un / 8 := by
          obtain ⟨qb, hqb⟩ : ∃ qb : Int, ub = 8 * qb := by
            refine ⟨ub / 8, ?_⟩
            have hd : (8 : Int) ∣ ub := by
              have h8 : (8 : Int) = zpow 2 3 := by decide
              rw [h8]
              exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, He1⟩)
                (hub ▸ (ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) b HK).2)
            obtain ⟨q, hq⟩ := hd
            rw [hq, Int.mul_ediv_cancel_left q (by decide : (8 : Int) ≠ 0)]
          obtain ⟨qn, hqn⟩ : ∃ qn : Int, un = 8 * qn := by
            refine ⟨un / 8, ?_⟩
            have hd : (8 : Int) ∣ un := by
              have h8 : (8 : Int) = zpow 2 3 := by decide
              rw [h8]
              exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, He2⟩)
                (hun ▸ (ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) n HK).2)
            obtain ⟨q, hq⟩ := hd
            rw [hq, Int.mul_ediv_cancel_left q (by decide : (8 : Int) ≠ 0)]
          rw [hqb, hqn, Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0),
            ← Int.mul_add, Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0)]
          omega
        have Hzero : ∀ i : Int, 0 ≤ i → i < un / 8 →
            Mr A argH E cs model FULL (Z_to_bv 64 (S + i)) = some (Z_to_bv 8 0) := by
          intro i h1 h2
          have h := (kzero_x_sound0 segs E (Mr A argH E cs model FULL) (kn cs) (kn cs)
            (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.fst
            (shadow_of A (kn cs) b n).2.snd HK HK Hkz).1
          rw [HSS] at h
          exact h i h1 (by rw [hlenSN]; exact h2)
        -- the pairs removed from `a_vis` are all `(b, n)`
        have GONE : ∀ p ∈ cs.a_vis.filter (vis_here b n), p = (b, n) := by
          intro p hp
          exact vis_here_eq b n p (List.mem_filter.mp hp).2
        -- the result state
        let K1 : List kentry := kn_unfill (kn cs) (split_lit b).fst (split_lit b).snd n
        let K2 : List kentry :=
          kn_unfill K1 (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.fst
            (shadow_of A (kn cs) b n).2.snd
        let CS : acs := ACS (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs K2 cs.a_ss.s_next)
          cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager
          (cs.a_vis.filter (fun p => !vis_here b n p)) (cs.a_ghost ++ [(b, n)])
          cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
        have hcs' : cs' = CS := H.symm
        rw [hcs']
        refine ⟨?_, rfl⟩
        have hvis : CS.a_vis = cs.a_vis.filter (fun p => !vis_here b n p) := rfl
        have hgh : CS.a_ghost = cs.a_ghost ++ [(b, n)] := rfl
        have hknCS : kn CS = K2 := rfl
        -- allowed set: only shrinks when read backwards
        have ALLOW_sub : ∀ z : Int, in_allow A E CS z = true → in_allow A E cs z = true := by
          intro z Hz
          simp only [in_allow, in_vis, in_sh] at Hz ⊢
          rw [Bool.or_eq_true] at Hz ⊢
          rw [hvis] at Hz
          rcases Hz with hz | hz
          · left
            obtain ⟨q, hq, hzq⟩ := List.any_eq_true.mp hz
            obtain ⟨hq, -⟩ := List.mem_filter.mp hq
            exact List.any_eq_true.mpr ⟨q, hq, hzq⟩
          · right
            obtain ⟨q, hq, hzq⟩ := List.any_eq_true.mp hz
            obtain ⟨hq, -⟩ := List.mem_filter.mp hq
            exact List.any_eq_true.mpr ⟨q, hq, hzq⟩
        have hshlo : sh_lo A E (b, n) = S := by
          show A.shadow_off + uE E b / 8 = S
          rw [hubE]
          exact hS
        have hshhi : sh_hi A E (b, n) = S + un / 8 := by
          show A.shadow_off + (uE E b + uE E n) / 8 = S + un / 8
          rw [hubE, hunE]
          exact Hshhi
        have ALLOW_eq : ∀ z : Int, ¬ (ub ≤ z ∧ z < ub + un) → ¬ (S ≤ z ∧ z < S + un / 8) →
            in_allow A E CS z = in_allow A E cs z := by
          intro z H1 H2
          by_cases h' : in_allow A E CS z = true
          · exact h'.trans (ALLOW_sub z h').symm
          · rw [Bool.not_eq_true] at h'
            by_cases h : in_allow A E cs z = true
            · exfalso
              simp only [in_allow, in_vis, in_sh] at h h'
              rw [hvis] at h'
              rw [Bool.or_eq_true] at h
              rw [Bool.or_eq_false_iff] at h'
              obtain ⟨hv', hs'⟩ := h'
              have Q : ∀ q ∈ cs.a_vis, vis_here b n q = false →
                  q ∈ cs.a_vis.filter (fun p => !vis_here b n p) := by
                intro q hq hh
                exact List.mem_filter.mpr ⟨hq, by rw [hh]; rfl⟩
              rcases h with h | h
              · obtain ⟨q, hq, hzq⟩ := List.any_eq_true.mp h
                by_cases hh : vis_here b n q = true
                · rw [vis_here_eq b n q hh] at hzq
                  try dsimp only at hzq
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hzq
                  rw [hubE, hunE] at hzq
                  exact H1 ⟨hzq.1, hzq.2⟩
                · have hh' : vis_here b n q = false := by
                    cases hq' : vis_here b n q <;> simp_all
                  have hX : (cs.a_vis.filter (fun p => !vis_here b n p)).any
                      (fun p => (uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2)) = true :=
                    List.any_eq_true.mpr ⟨q, Q q hq hh', hzq⟩
                  rw [hX] at hv'
                  exact absurd hv' (by simp)
              · obtain ⟨q, hq, hzq⟩ := List.any_eq_true.mp h
                by_cases hh : vis_here b n q = true
                · rw [vis_here_eq b n q hh] at hzq
                  try dsimp only at hzq
                  simp only [hshlo, hshhi] at hzq
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hzq
                  exact H2 ⟨hzq.1, hzq.2⟩
                · have hh' : vis_here b n q = false := by
                    cases hq' : vis_here b n q <;> simp_all
                  have hX : (cs.a_vis.filter (fun p => !vis_here b n p)).any
                      (fun p => (sh_lo A E p ≤ z) && (z < sh_hi A E p)) = true :=
                    List.any_eq_true.mpr ⟨q, Q q hq hh', hzq⟩
                  rw [hX] at hs'
                  exact absurd hs' (by simp)
            · rw [Bool.not_eq_true] at h
              rw [h', h]
        -- visibility only shrinks (in the hidden direction it only grows)
        have HID_mono : ∀ a : word, hid A argH E cs model a = true →
            hid A argH E CS model a = true := by
          intro a Ha
          unfold hid at *
          rw [Bool.or_eq_true] at Ha ⊢
          rcases Ha with ha | ha
          · exact Or.inl ha
          · right
            rw [Bool.not_eq_true'] at ha ⊢
            by_cases hv : vis A E CS model a = true
            · rw [vis_mono A E CS cs model a ALLOW_sub hv] at ha
              exact absurd ha (by simp)
            · rw [Bool.not_eq_true] at hv
              rw [hv]
        have HID_eq : ∀ a : word, ¬ (ub ≤ bv_unsigned a ∧ bv_unsigned a < ub + un) →
            ¬ (S ≤ bv_unsigned a ∧ bv_unsigned a < S + un / 8) →
            hid A argH E CS model a = hid A argH E cs model a := by
          intro a H1 H2
          unfold hid vis
          dsimp only
          rw [ALLOW_eq (bv_unsigned a) H1 H2]
        have M_none : ∀ x : word, Mr A argH E cs model FULL x = none →
            Mr A argH E CS model FULL x = none := by
          intro x Hx
          simp only [Mr, mrestrict] at Hx ⊢
          by_cases hh : hid A argH E cs model x = true
          · rw [ite_eq_left hh] at Hx
            rw [ite_eq_left (HID_mono x hh)]
          · rw [ite_eq_right hh] at Hx
            by_cases hh2 : hid A argH E CS model x = true
            · rw [ite_eq_left hh2]
            · rw [ite_eq_right hh2]
              exact Hx
        have M_eq : ∀ x : word, ¬ (ub ≤ bv_unsigned x ∧ bv_unsigned x < ub + un) →
            ¬ (S ≤ bv_unsigned x ∧ bv_unsigned x < S + un / 8) →
            Mr A argH E CS model FULL x = Mr A argH E cs model FULL x := by
          intro x H1 H2
          have he : hid A argH E CS model x = hid A argH E cs model x := HID_eq x H1 H2
          simp only [Mr, mrestrict]
          by_cases hh : hid A argH E cs model x = true
          · rw [ite_eq_left hh, ite_eq_left (by rw [he]; exact hh)]
          · rw [ite_eq_right hh, ite_eq_right (by rw [he]; exact hh)]
        -- `Mmid`: the memory between the two unfills
        let Mmid : word → Option byte := fun x =>
          if decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un) then
            Mr A argH E CS model FULL x else Mr A argH E cs model FULL x
        have Mmid_app : ∀ x : word, Mmid x =
            (if decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un) then
              Mr A argH E CS model FULL x else Mr A argH E cs model FULL x) := fun x => rfl
        have Mmid_out : ∀ x : word, bv_unsigned x < ub ∨ ub + un ≤ bv_unsigned x →
            Mmid x = Mr A argH E cs model FULL x := by
          intro x Hx
          show (if decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un) then
            Mr A argH E CS model FULL x else Mr A argH E cs model FULL x) = _
          by_cases hc : (decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un)) = true
          · rw [ite_eq_left hc]
            exfalso
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            omega
          · rw [ite_eq_right hc]
        have Mmid_none : ∀ x : word, Mr A argH E cs model FULL x = none → Mmid x = none := by
          intro x Hx
          show (if decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un) then
            Mr A argH E CS model FULL x else Mr A argH E cs model FULL x) = _
          by_cases hc : (decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un)) = true
          · rw [ite_eq_left hc]
            exact M_none x Hx
          · rw [ite_eq_right hc]
            exact Hx
        have HK1 : know_ok segs E Mmid K1 := by
          refine kn_unfill_keep segs E (Mr A argH E cs model FULL) Mmid (kn cs)
            (split_lit b).fst (split_lit b).snd n HK ?_ Mmid_none
          intro x Hx
          rw [HB, hlenZ] at Hx
          exact Mmid_out x Hx
        have HK2 : know_ok segs E (Mr A argH E CS model FULL)
            (kn_unfill K1 (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.fst
              (shadow_of A (kn cs) b n).2.snd) := by
          refine kn_unfill_keep segs E Mmid (Mr A argH E CS model FULL) K1
            (shadow_of A (kn cs) b n).fst (shadow_of A (kn cs) b n).2.fst
            (shadow_of A (kn cs) b n).2.snd HK1 ?_ ?_
          · intro x Hx
            rw [HSS, hlenSN] at Hx
            rw [Mmid_app x]
            by_cases hc : (decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un)) = true
            · rw [ite_eq_left hc]
            · rw [ite_eq_right hc]
              exact M_eq x (fun Hcon => hc (by
                rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
                exact ⟨Hcon.1, Hcon.2⟩)) (by omega)
          · intro x Hx
            rw [Mmid_app x] at Hx
            by_cases hc : (decide (ub ≤ bv_unsigned x) && decide (bv_unsigned x < ub + un)) = true
            · rw [ite_eq_left hc] at Hx
              exact Hx
            · rw [ite_eq_right hc] at Hx
              exact M_none x Hx
        -- the allowed-set byte budget
        have HAB : A_bytes (allowA A E CS) ≤ A_bytes (allowA A E cs) :=
          A_bytes_unvis_le A E (mk_ss cs.a_ss.s_pc cs.a_ss.s_regs K2 cs.a_ss.s_next)
            cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_abytes cs.a_vis cs.a_ghost
            cs.a_brk cs.a_fd cs.a_tidset b n Hany
        -- the allowed set only GROWS, so `page_allowedb` is preserved
        have HA' : allowA A E CS = (cs.a_vis.filter (fun p => !vis_here b n p)).flatMap (allow1 A E)
            ++ (cs.a_ghost.flatMap (allow1 A E) ++ allow1 A E (b, n)) := by
          simp only [allowA, hvis, hgh, List.flatMap_append, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
        have HA0' : allowA A E cs = cs.a_vis.flatMap (allow1 A E)
            ++ cs.a_ghost.flatMap (allow1 A E) := by
          simp only [allowA, List.flatMap_append]
        have HPG : ∀ pg : word, page_allowedb (allowA A E cs) pg = true →
            page_allowedb (allowA A E CS) pg = true := by
          intro pg Hp
          unfold page_allowedb at Hp ⊢
          obtain ⟨iv, hiv, hpg⟩ := List.any_eq_true.mp Hp
          rw [HA0'] at hiv
          refine List.any_eq_true.mpr ⟨iv, ?_, hpg⟩
          rw [HA', List.mem_append, List.mem_append]
          rcases List.mem_append.mp hiv with h | h
          · obtain ⟨q, hq, hiq⟩ := List.mem_flatMap.mp h
            by_cases hh : vis_here b n q = true
            · rw [vis_here_eq b n q hh] at hiq
              exact Or.inr (Or.inr hiq)
            · have hh' : vis_here b n q = false := by
                cases hq' : vis_here b n q <;> simp_all
              exact Or.inl (List.mem_flatMap.mpr
                ⟨q, List.mem_filter.mpr ⟨hq, by rw [hh']; rfl⟩, hiq⟩)
          · exact Or.inr (Or.inl h)
        -- `co_zero`: no hidden lazy shadow byte is non-zero
        have HZ : ∀ a : word, hid A argH E CS model a = true →
            in_ivs (bv_unsigned a) (m_vmmaps model).vm_maps = true →
            in_ivs (bv_unsigned a) (m_vmmaps model).vm_noaccess = false →
            page_in_ranges (page_base a) (m_vm_lazy model) = true →
            in_ghost E CS (bv_unsigned a) = false → FULL a = some (Z_to_bv 8 0) := by
          intro a H1 H2 H3 H4 H5
          simp only [in_ghost] at H5
          rw [hgh] at H5
          rw [List.any_append] at H5
          rw [Bool.or_eq_false_iff] at H5
          obtain ⟨H5, H6⟩ := H5
          simp only [List.any_cons, List.any_nil, Bool.or_false] at H6
          have NA : ¬ (ub ≤ bv_unsigned a ∧ bv_unsigned a < ub + un) := by
            intro Hin
            have hX : (decide (uE E b ≤ (bv_unsigned a : Int)) &&
                decide ((bv_unsigned a : Int) < uE E b + uE E n)) = true := by
              rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hubE, hunE]
              exact ⟨Hin.1, Hin.2⟩
            rw [hX] at H6
            exact absurd H6 (by simp)
          by_cases Hh : hid A argH E cs model a = true
          · exact HC.co_zero a Hh H2 H3 H4 H5
          · rw [Bool.not_eq_true] at Hh
            by_cases L1 : S ≤ bv_unsigned a
            · by_cases L2 : bv_unsigned a < S + un / 8
              · have hz0 := Hzero (bv_unsigned a - S) (by omega) (by omega)
                rw [show S + (bv_unsigned a - S) = bv_unsigned a by omega] at hz0
                rw [show Z_to_bv 64 (bv_unsigned a) = a from AxSymExec3Sound.ofInt_toNat a] at hz0
                simp only [Mr, mrestrict] at hz0
                rw [ite_eq_right (by rw [Hh]; simp)] at hz0
                exact hz0
              · rw [HID_eq a NA (by omega)] at H1
                rw [Hh] at H1
                exact absurd H1 (by simp)
            · rw [HID_eq a NA (by omega)] at H1
              rw [Hh] at H1
              exact absurd H1 (by simp)
        -- THE RECORD
        refine
          { co_regs := HC.co_regs
            co_log := rfl
            co_know := HK2
            co_halt := HC.co_halt
            co_fds := HC.co_fds
            co_fs := HC.co_fs
            co_tid := HC.co_tid
            co_res := HC.co_res
            co_limit := HC.co_limit
            co_maps := HC.co_maps
            co_holes := HC.co_holes
            co_seps := HC.co_seps
            co_wf := HC.co_wf
            co_bounds := HC.co_bounds
            co_lazyb := HC.co_lazyb
            co_nasub := HC.co_nasub
            co_none := HC.co_none
            co_kinds := HC.co_kinds
            co_totsz := HC.co_totsz
            co_split := HC.co_split
            co_brk := HC.co_brk
            co_sbrk := HC.co_sbrk
            co_eager := HC.co_eager
            co_abytes := by
              show A_bytes (allowA A E CS) ≤ cs.a_abytes
              have h := HC.co_abytes
              omega
            co_minv := by
              refine ⟨HC.co_minv.minv_nodup, HC.co_minv.minv_aligned, ?_,
                HC.co_minv.minv_lazy, ?_⟩
              · intro p hp
                exact HPG p (HC.co_minv.minv_allowed p hp)
              · have h := HC.co_minv.minv_budget
                have h2 := HAB
                omega
            co_zero := HZ
            co_sinv := HC.co_sinv }
      · simp at H


/--  :1245 — the shared obligation discharge for every node that calls
    `vis_add`: from `cs_ok` of the state BEFORE the range was declared visible
    (knowledge `kn cs` valid at the OLD visibility) and the caller's facts `k`
    valid at the NEW visibility, conclude `cs_ok` of the result.
    * The shadow's symbolic flatness `flat_x k sb sk sn = true` comes from
      `vis_add_ref`'s guard (its fourth conjunct, peeled below as `Hfls`), not
      from a hypothesis. with
      bounds on `split_lit`'s literal offset, which `split_lit` alone does not
      supply (`split_lit (ELit z) = (ELit 0, z)` for ANY `z`).  So the guard of
      `vis_add_ref` / `vis_add` carries that conjunct as a it only rejects more plans; `node_unvis_ref` already checks the same fact),
      so this theorem now has NO shadow-flatness hypothesis and `check_sound`'s
      `PVis` arm can discharge the obligation from the guard, as `PUnvis` does
      with `SHADOW_ok`.
-/
theorem vis_add_sound (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (b n : expr) (k : List kentry) (cs2 : acs)
    (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (Hsh : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (Hv : vis_add A LIMIT cs b n k = some cs2)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (HKk : know_ok segs E (Mr A argH E cs2 model FULL) k) :
    cs_ok segs A LIMIT SINV argH FS0 E cs2 R FULL model := by
  rw [vis_add_eq] at Hv
  unfold vis_add_ref at Hv
  dsimp only at Hv
  cases hn : xhi (kn cs) n with
  | none => rw [hn] at Hv; exact absurd Hv (by simp)
  | some nhi =>
    rw [hn] at Hv
    dsimp only [] at Hv
    split at Hv
    · rename_i hg
      have hc := hg
      simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hc
      obtain ⟨He1, He2, Hfl, Hfls, Hvb, Hvn, Hvis, Hgh, Hbud⟩ := hc
      simp only [Option.some.injEq] at Hv
      -- name the shadow triple
      obtain ⟨sb, sk, sn, hsb⟩ :
          ∃ (sb : expr) (sk : Int) (sn : expr), shadow_of A (kn cs) b n = (sb, sk, sn) := ⟨_, _, _, rfl⟩
      rw [hsb] at Hfls Hvis Hgh
      dsimp only at Hfls Hvis Hgh
      -- the result state
      let CS : acs := ACS (mk_ss (pc cs) cs.a_ss.s_regs
        (shadow_facts A (kn cs) cs.a_maps b n ++ k) (nxt cs))
        cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager ((b, n) :: cs.a_vis) cs.a_ghost
        (cs.a_abytes + vis_cost nhi) cs.a_brk cs.a_fd cs.a_tidset
      have hCS : cs2 = CS := Hv.symm
      rw [hCS] at HKk ⊢
      -- ## 1. numeric setup
      have Hnle : bv_unsigned (edenot E n) ≤ nhi :=
        xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) n nhi HC.co_know hn
      have Hcost := allow1_cost A E b n nhi Hnle
      obtain ⟨Fb1, Fb2, Fb3⟩ := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
        (split_lit b).fst (split_lit b).snd n HC.co_know Hfl
      obtain ⟨HS0, HSn⟩ := shadow_of_val segs A E (Mr A argH E cs model FULL) (kn cs) b n
        sb sn sk Hsh HC.co_know hsb Hfls
      have hub0 : 0 ≤ bv_unsigned (edenot E b) := bv_unsigned_nonneg _
      have hub64 : bv_unsigned (edenot E b) < 2 ^ 64 := (u64_range (edenot E b)).2
      have hun0 : 0 ≤ bv_unsigned (edenot E n) := bv_unsigned_nonneg _
      have hun64 : bv_unsigned (edenot E n) < 2 ^ 64 := (u64_range (edenot E n)).2
      generalize hub : bv_unsigned (edenot E b) = ub at *
      generalize hun : bv_unsigned (edenot E n) = un at *
      have hubE : uE E b = ub := hub
      have hunE : uE E n = un := hun
      have hlenZ : elenZ E n = un := hun
      have hlenSN : elenZ E sn = un / 8 := HSn
      have HSS : estart E (SA sb sk) = A.shadow_off + ub / 8 := by
        rw [HS0]
        have h1 : 0 ≤ ub / 8 + A.shadow_off := by
          have h2 := Int.ediv_nonneg hub0 (by decide : (0 : Int) ≤ 8)
          have h3 : 0 ≤ A.shadow_off := Hsh.1
          omega
        have h2 : ub / 8 + A.shadow_off < 2 ^ 64 := by
          have e := Int.emod_add_mul_ediv ub 8
          have e0 : 0 ≤ ub % 8 := Int.emod_nonneg ub (by decide)
          have e1 : ub % 8 < 8 := Int.emod_lt_of_pos ub (by decide)
          have h47 : A.shadow_off ≤ 2 ^ 47 := Hsh.2
          omega
        rw [Int.emod_eq_of_lt h1 h2]
        omega
      have Hshhi : A.shadow_off + (ub + un) / 8 = (A.shadow_off + ub / 8) + un / 8 := by
        obtain ⟨qb, hqb⟩ : ∃ qb : Int, ub = 8 * qb := by
          refine ⟨ub / 8, ?_⟩
          have hd : (8 : Int) ∣ ub := by
            have h8 : (8 : Int) = zpow 2 3 := by decide
            rw [h8]
            exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, He1⟩)
              (hub ▸ (ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) b HC.co_know).2)
          obtain ⟨q, hq⟩ := hd
          rw [hq, Int.mul_ediv_cancel_left q (by decide : (8 : Int) ≠ 0)]
        obtain ⟨qn, hqn⟩ : ∃ qn : Int, un = 8 * qn := by
          refine ⟨un / 8, ?_⟩
          have hd : (8 : Int) ∣ un := by
            have h8 : (8 : Int) = zpow 2 3 := by decide
            rw [h8]
            exact Int.dvd_trans (pow2_divide_le 3 _ ⟨by decide, He2⟩)
              (hun ▸ (ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) n HC.co_know).2)
          obtain ⟨q, hq⟩ := hd
          rw [hq, Int.mul_ediv_cancel_left q (by decide : (8 : Int) ≠ 0)]
        rw [hqb, hqn, Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0),
          ← Int.mul_add, Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0)]
        omega
      generalize hS : A.shadow_off + ub / 8 = S at *
      have HSS' : estart E (SA sb sk) = S := HSS
      have HSSr : bv_unsigned (edenot E sb) + sk = S := HSS'
      have Hshhi' : A.shadow_off + (ub + un) / 8 = S + un / 8 := Hshhi
      have hS0 : 0 ≤ S := by
        rw [← hS]
        have h1 := Int.ediv_nonneg hub0 (by decide : (0 : Int) ≤ 8)
        have h2 : 0 ≤ A.shadow_off := Hsh.1
        omega
      have HB : estart E (SA (split_lit b).fst (split_lit b).snd) = ub :=
        (u_of_split E b (split_lit b).fst (split_lit b).snd rfl ⟨Fb1, by omega⟩).symm.trans hub
      have HBS : bv_unsigned (edenot E (split_lit b).fst) + (split_lit b).snd = ub := HB
      -- strict upper bound on the shadow window
      have hS64s : S + un / 8 < 2 ^ 64 := by
        rw [← Hshhi']
        have e := Int.emod_add_mul_ediv (ub + un) 8
        have e0 : 0 ≤ (ub + un) % 8 := Int.emod_nonneg _ (by decide)
        have h47 : A.shadow_off ≤ 2 ^ 47 := Hsh.2
        have hFb2 := Fb2
        dsimp only [estart, SA, saddr.a_base, saddr.a_off] at hFb2
        rw [HBS] at hFb2
        omega
      -- ## 2. the allowed set
      have hvisCS : CS.a_vis = (b, n) :: cs.a_vis := rfl
      have hghCS : CS.a_ghost = cs.a_ghost := rfl
      have hknCS : kn CS = shadow_facts A (kn cs) cs.a_maps b n ++ k := rfl
      have habCS : CS.a_abytes = cs.a_abytes + vis_cost nhi := rfl
      have HA : allowA A E CS = allow1 A E (b, n) ++ allowA A E cs := by
        simp only [allowA, hvisCS, hghCS, List.cons_append, List.flatMap_cons,
          List.flatMap_append, List.flatMap_nil, List.append_nil]
      have hshlo : sh_lo A E (b, n) = S := by
        show A.shadow_off + uE E b / 8 = S
        rw [hubE]
        exact hS
      have hshhi : sh_hi A E (b, n) = S + un / 8 := by
        show A.shadow_off + (uE E b + uE E n) / 8 = S + un / 8
        rw [hubE, hunE]
        exact Hshhi'
      -- ## 3. the shadow facts (co_know's first half)
      have HKsh : know_ok segs E (Mr A argH E CS model FULL)
          (shadow_facts A (kn cs) cs.a_maps b n) := by
        cases hf : find_containing (kn cs) cs.a_maps [.KRWLAZY] sb sk sn with
        | none =>
            have hz : shadow_facts A (kn cs) cs.a_maps b n = [] := by
              unfold shadow_facts
              dsimp only
              rw [hsb]
              dsimp only
              rw [hf]
            rw [hz]
            intro K hK
            cases hK
        | some m =>
          have hz : shadow_facts A (kn cs) cs.a_maps b n
              = [.KWr (SA sb sk) sn, .KZero (SA sb sk) sn] := by
            unfold shadow_facts
            dsimp only
            rw [hsb]
            dsimp only
            rw [hf]
          rw [hz]
          -- the containing tracked entry
          have Hmin : m ∈ cs.a_maps := List.mem_of_find?_eq_some hf
          have Hmb := List.find?_some hf
          unfold find_containing at Hmb
          rw [Bool.and_eq_true] at Hmb
          obtain ⟨Hmb, Hins⟩ := Hmb
          rw [Bool.and_eq_true] at Hmb
          obtain ⟨Hnf, Hkind⟩ := Hmb
          have Hnf' : is_fog m = false := by
            cases h : is_fog m <;> simp_all
          have Hkind' : m.am_kind = .KRWLAZY := mkind_eqb_eq (by simpa using Hkind)
          have Hmv : amap_den E m ∈ (m_vmmaps model).vm_maps :=
            maps_match_In E cs.a_maps (m_vmmaps model).vm_maps m HC.co_maps Hmin Hnf'
          obtain ⟨B1, B2, B3, B4, B5⟩ := HC.co_bounds (amap_den E m) Hmv
          dsimp only [amap_den, Prod.fst, Prod.snd] at B1 B2 B3 B4 B5
          obtain ⟨I1, I2⟩ := xinside_sound segs E (Mr A argH E cs model FULL) (kn cs)
            sb sk sn m.am_base 0 m.am_len HC.co_know Hins
          have I1' : bv_unsigned (edenot E m.am_base) ≤ S := by
            have h := I1
            rw [HSS'] at h
            simpa only [estart, SA, saddr.a_base, saddr.a_off, Int.add_zero] using h
          have I2' : S + un / 8 ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
            have h := I2
            rw [HSS', hlenSN] at h
            simpa only [estart, SA, saddr.a_base, saddr.a_off, Int.add_zero, elenZ] using h
          have HRmb : 0 ≤ bv_unsigned (edenot E m.am_base) := bv_unsigned_nonneg _
          have HCeil : CEIL < 2 ^ 64 := by decide
          have hzr : ∀ i : Int, 0 ≤ i → i < un / 8 →
              bv_unsigned (edenot E m.am_base) ≤ S + i ∧
              S + i < bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
            intro i hi0 hilt; constructor <;> omega
          -- a GHOST range is not entered either
          have Hghostp : ∀ p ∈ cs.a_ghost, ∀ z : Int, S ≤ z → z < S + un / 8 →
              ((uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2)) = false := by
            intro p hp z hSz hzi
            have hpp := List.all_eq_true.mp Hgh p hp
            rw [Bool.and_eq_true] at hpp
            obtain ⟨hpf, hap2⟩ := hpp
            have Fp := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
              (split_lit p.1).fst (split_lit p.1).snd p.2 HC.co_know hpf
            have Up := u_of_split E p.1 (split_lit p.1).fst (split_lit p.1).snd rfl
              ⟨Fp.1, by omega⟩
            have A2 := ranges_apart_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
              sb sk sn (split_lit p.1).fst (split_lit p.1).snd p.2 HC.co_know hap2
            rw [HSS', hlenSN] at A2
            simp only [elenZ] at A2
            dsimp only [uE]
            rw [Bool.and_eq_false_iff]
            rcases A2 with A2 | A2
            /- `simp only`, not `rw`: the `decide … = false` sits under an
               instance that `rw` will not rewrite through. -/
            · left; simp only [decide_eq_false_iff_not, Up]; omega
            · right; simp only [decide_eq_false_iff_not, Up]; omega
          -- the two facts every OLD VISIBLE range satisfies
          have Hvisp : ∀ p ∈ cs.a_vis, ∀ z : Int, S ≤ z → z < S + un / 8 →
              (((uE E p.1 ≤ z) && (z < uE E p.1 + uE E p.2)) = false ∧
               ((sh_lo A E p ≤ z) && (z < sh_hi A E p)) = false) := by
            intro p hp z hSz hzi
            have hpp := List.all_eq_true.mp Hvis p hp
            rw [Bool.and_eq_true] at hpp
            obtain ⟨hpp, hap2⟩ := hpp
            rw [Bool.and_eq_true] at hpp
            obtain ⟨hpf, hap1⟩ := hpp
            have Fp := flat_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
              (split_lit p.1).fst (split_lit p.1).snd p.2 HC.co_know hpf
            have Up := u_of_split E p.1 (split_lit p.1).fst (split_lit p.1).snd rfl
              ⟨Fp.1, by omega⟩
            have A2 := ranges_apart_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
              sb sk sn (split_lit p.1).fst (split_lit p.1).snd p.2 HC.co_know hap2
            have A1 := ranges_apart_x_sound segs E (Mr A argH E cs model FULL) (kn cs)
              (split_lit b).fst (split_lit b).snd n (split_lit p.1).fst (split_lit p.1).snd p.2
              HC.co_know hap1
            rw [HSS', hlenSN] at A2
            rw [hlenZ, HB] at A1
            simp only [elenZ] at A1 A2
            constructor
            · dsimp only [uE]
              rw [Bool.and_eq_false_iff]
              rcases A2 with A2 | A2
              · left; simp only [decide_eq_false_iff_not, Up]; omega
              · right; simp only [decide_eq_false_iff_not, Up]; omega
            · dsimp only [sh_lo, sh_hi, uE]
              rw [Bool.and_eq_false_iff]
              have hd : ub / 8 + un / 8 ≤ (ub + un) / 8 := by
                have e := Int.emod_add_mul_ediv (ub + un) 8
                have e0 : 0 ≤ (ub + un) % 8 := Int.emod_nonneg _ (by decide)
                have f := Int.emod_add_mul_ediv ub 8
                have f0 : 0 ≤ ub % 8 := Int.emod_nonneg ub (by decide)
                have f1 : ub % 8 < 8 := Int.emod_lt_of_pos ub (by decide)
                have g := Int.emod_add_mul_ediv un 8
                have g0 : 0 ≤ un % 8 := Int.emod_nonneg un (by decide)
                have g1 : un % 8 < 8 := Int.emod_lt_of_pos un (by decide)
                have h2 : (ub + un) % 8 ≤ ub % 8 + un % 8 := by
                  rw [Int.add_emod]
                  omega
                omega
              rcases A1 with A1 | A1
              · left
                simp only [decide_eq_false_iff_not, Up]
                have h1 : ub / 8 + un / 8
                    ≤ estart E (SA (split_lit p.1).fst (split_lit p.1).snd) / 8 :=
                  Int.le_trans hd (Int.ediv_le_ediv (by decide : (0 : Int) < 8) A1)
                omega
              · right
                simp only [decide_eq_false_iff_not, Up]
                have h1 : A.shadow_off + (estart E (SA (split_lit p.1).fst (split_lit p.1).snd)
                    + bv_unsigned (edenot E p.2)) / 8 ≤ S := by
                  rw [← hS]
                  have h2 := Int.ediv_le_ediv (by decide : (0 : Int) < 8) A1
                  omega
                omega
          -- every byte of the shadow window reads zero
          have BYTE : ∀ i : Int, 0 ≤ i → i < un / 8 →
              Mr A argH E CS model FULL (Z_to_bv 64 (S + i)) = some (Z_to_bv 8 0) := by
            intro i hi0 hilt
            obtain ⟨hlo, hhi⟩ := hzr i hi0 hilt
            have hz0 : 0 ≤ S + i := by omega
            have hzlt : S + i < 2 ^ 64 := by omega
            have Ua : bv_unsigned (Z_to_bv 64 (S + i)) = S + i := by
              show bv_unsigned (Z_to_bv 64 (S + i)) = S + i
              rw [u_lit64a, Int.emod_eq_of_lt hz0 hzlt]
            have HB1 : S ≤ bv_unsigned (Z_to_bv 64 (S + i)) := by omega
            have HB2 : bv_unsigned (Z_to_bv 64 (S + i)) < S + un / 8 := by omega
            have Hm1 : in_ivs (bv_unsigned (Z_to_bv 64 (S + i))) (m_vmmaps model).vm_maps = true :=
              in_ivs_maps_match E cs.a_maps (m_vmmaps model).vm_maps m _ HC.co_maps Hmin Hnf'
                ⟨by omega, by omega⟩
            obtain ⟨Hna, Hlz⟩ := HC.co_kinds m Hmin Hkind' (Z_to_bv 64 (S + i))
              ⟨by omega, by omega⟩
            have HCEILb : bv_unsigned (Z_to_bv 64 (S + i)) < CEIL := by omega
            have Hargh : argH E (Z_to_bv 64 (S + i)) = false := by
              cases ha : argH E (Z_to_bv 64 (S + i)) with
              | false => rfl
              | true =>
                  exfalso
                  have h1 := argH_high E _ ha
                  omega
            have Hallow : in_allow A E CS (bv_unsigned (Z_to_bv 64 (S + i))) = true := by
              have hsh : in_sh A E CS (bv_unsigned (Z_to_bv 64 (S + i))) = true := by
                unfold in_sh
                rw [hvisCS, List.any_cons]
                rw [show ((sh_lo A E (b, n) ≤ bv_unsigned (Z_to_bv 64 (S + i))) &&
                    (bv_unsigned (Z_to_bv 64 (S + i)) < sh_hi A E (b, n))) = true from by
                  rw [Bool.and_eq_true]
                  exact ⟨by rw [decide_eq_true_eq, hshlo]; omega,
                    by rw [decide_eq_true_eq, hshhi]; omega⟩]
                exact Bool.true_or _
              simp only [in_allow, hsh, Bool.or_true]
            have Hvis2 : hid A argH E CS model (Z_to_bv 64 (S + i)) = false := by
              unfold hid
              rw [Hargh]
              have hv : vis A E CS model (Z_to_bv 64 (S + i)) = true := by
                simp only [vis, Hm1, Hna, Hallow, Bool.not_false, Bool.not_true, Bool.and_true,
                  Bool.true_and, Bool.or_true, Bool.false_or, Bool.true_or]
              rw [hv]; rfl
            have hghost : in_ghost E cs (bv_unsigned (Z_to_bv 64 (S + i))) = false := by
              unfold in_ghost
              exact existsb_false_forall _ _ (fun p hp => Hghostp p hp _ HB1 HB2)
            have Hhid1 : hid A argH E cs model (Z_to_bv 64 (S + i)) = true := by
              unfold hid
              rw [Hargh]
              have hhull : in_hull A (bv_unsigned (Z_to_bv 64 (S + i))) = false := by
                unfold in_hull
                rw [Bool.and_eq_false_iff]
                right
                rw [decide_eq_false_iff_not]
                omega
              have hceil : decide (CEIL ≤ bv_unsigned (Z_to_bv 64 (S + i))) = false := by
                rw [decide_eq_false_iff_not]; omega
              have hallow' : in_allow A E cs (bv_unsigned (Z_to_bv 64 (S + i))) = false := by
                unfold in_allow
                rw [Bool.or_eq_false_iff]
                refine ⟨?_, ?_⟩
                · unfold in_vis
                  exact existsb_false_forall _ _ (fun p hp => (Hvisp p hp _ HB1 HB2).1)
                · unfold in_sh
                  exact existsb_false_forall _ _ (fun p hp => (Hvisp p hp _ HB1 HB2).2)
              simp only [vis, hhull, hceil, Hna, Hlz, hallow', hghost, Bool.and_false,
                Bool.false_and, Bool.false_or, Bool.not_false, Bool.and_true, Bool.true_and,
                Bool.not_true]
            simp only [Mr, mrestrict]
            rw [ite_eq_right (by rw [Hvis2]; simp)]
            exact HC.co_zero (Z_to_bv 64 (S + i)) Hhid1 Hm1 Hna Hlz hghost
          -- the two shadow facts are sound
          have HF : flat E (SA sb sk) (elenZ E sn) := by
            unfold flat
            rw [hlenSN, HSS']
            exact ⟨hS0, by omega, by omega, by omega⟩
          intro K hK
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
          rcases hK with rfl | rfl
          · -- KWr
            simp only [kentry_ok]
            refine ⟨HF, ?_⟩
            intro d w hd hdw
            have hdw' : d + (w : Int) ≤ un / 8 := by rw [← hlenSN]; exact hdw
            have hUbd : bv_unsigned (Z_to_bv 64 (S + d)) = S + d := by
              show bv_unsigned (Z_to_bv 64 (S + d)) = S + d
              rw [u_lit64a, Int.emod_eq_of_lt] <;> omega
            have ht1 : ((Z_to_bv 64 (S + d)).toNat : Int) = S + d := by
              rw [toNat_cast_eq_bv_unsigned]; exact hUbd
            rw [HSS']
            refine StoreOk.store_ok_of_all segs (Mr A argH E CS model FULL) w (Z_to_bv 64 (S + d)) ?_ ?_
            · show ((Z_to_bv 64 (S + d)).toNat : Int) + (w : Int) ≤ ((2 ^ 64 : Nat) : Int)
              have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by decide
              rw [ht1, h64]
              omega
            · intro x hx1 hx2
              rw [ht1] at hx1 hx2
              rw [toNat_cast_eq_bv_unsigned] at hx1 hx2
              have hb := BYTE (bv_unsigned x - S) (by omega) (by omega)
              have hx' : Z_to_bv 64 (S + (bv_unsigned x - S)) = x := by
                rw [show S + (bv_unsigned x - S) = bv_unsigned x from by omega]
                exact Z_to_bv_unsigned x
              rw [← hx']
              simp only [wview, hb]
              simp
          · -- KZero
            simp only [kentry_ok]
            refine ⟨HF, ?_⟩
            intro i hi0 hil
            rw [hlenSN] at hil
            rw [HSS']
            exact BYTE i hi0 hil
      -- ## 4. the record
      refine ⟨HC.co_regs, rfl, ?_, HC.co_halt, HC.co_fds, HC.co_fs, HC.co_tid, HC.co_res,
        HC.co_limit, HC.co_maps, HC.co_holes, HC.co_seps, HC.co_wf, HC.co_bounds, HC.co_lazyb,
        HC.co_nasub, HC.co_none, HC.co_kinds, HC.co_totsz, HC.co_split, HC.co_brk, HC.co_sbrk,
        HC.co_eager, ?_, ?_, ?_, HC.co_sinv⟩
      · -- co_know
        show know_ok segs E (Mr A argH E CS model FULL) (kn CS)
        rw [hknCS]
        intro K hK
        rw [List.mem_append] at hK
        rcases hK with h | h
        · exact HKsh K h
        · exact HKk K h
      · -- co_abytes
        show A_bytes (allowA A E CS) ≤ CS.a_abytes
        rw [HA, A_bytes_app, habCS]
        have h := HC.co_abytes
        omega
      · -- co_minv
        show MInv (allowA A E CS) model
        rw [HA]
        refine MInv_app (allow1 A E (b, n)) (allowA A E cs) model HC.co_minv ?_
        show eager_used model + A_bytes (allow1 A E (b, n) ++ allowA A E cs)
          ≤ (m_vmmaps model).vm_limit
        rw [A_bytes_app, HC.co_limit]
        have h1 := HC.co_eager
        have h2 := HC.co_abytes
        omega
      · -- co_zero
        intro a h1 h2 h3 h4 h5
        refine HC.co_zero a ?_ h2 h3 h4 ?_
        · exact hid_cons_sub A argH E cs (b, n) model a (mk_ss (pc cs) cs.a_ss.s_regs
            (shadow_facts A (kn cs) cs.a_maps b n ++ k) (nxt cs)) cs.a_totsz cs.a_ylo
            cs.a_eager cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset h1
        · exact h5
    · exact absurd Hv (by simp)

/-- Local helper for `PFresh`: the three knowledge entries `node_fresh`
    appends are sound once the address's bounds and its divisibility by
    `c = 2^logc` are known. -/
theorem fresh_entries_ok (segs : List Segment) (E E' : env) (M M' : word → Option byte)
    (k : List kentry) (e ne : expr) (v : Nat) (c lo hi q : Int)
    (HK : know_ok segs E M k) (Hne : edenot E' ne = edenot E e)
    (Hd : ∀ (e' : expr) (s : Int), AsanPlanCore.deand e = (e', s) → edenot E' e' = edenot E e')
    (Hv : bv_unsigned (E'.ev v) = q) (Hc : 0 < c)
    (Hlo : lo ≤ bv_unsigned (edenot E e)) (Hhi : bv_unsigned (edenot E e) ≤ hi)
    (Hq : bv_unsigned (edenot E e) = c * q) (Hev : edenot E' e = edenot E e) :
    know_ok segs E' M' (.KRange (.EVar v) ((lo + c - 1) / c) (hi / c) ::
      .KRange (esub e ne) 0 0 :: residue_fact k e ne) := by
  intro K hK
  rcases List.mem_cons.mp hK with rfl | hK
  · show ((lo + c - 1) / c ≤ bv_unsigned (E'.ev v)) ∧ bv_unsigned (E'.ev v) ≤ hi / c
    rw [Hv]
    constructor
    · have h1 : lo + c - 1 < (q + 1) * c := by
        have hexp : (q + 1) * c = q * c + 1 * c := Int.add_mul q 1 c
        rw [hexp, Int.one_mul, Int.mul_comm q c]
        omega
      have h2 : (lo + c - 1) / c < q + 1 := (Int.ediv_lt_iff_lt_mul Hc).mpr h1
      omega
    · have h3 : q * c ≤ hi := by rw [Int.mul_comm q c]; omega
      exact (Int.le_ediv_iff_mul_le Hc).mpr h3
  · rcases List.mem_cons.mp hK with rfl | hK
    · show 0 ≤ bv_unsigned (edenot E' (esub e ne)) ∧ bv_unsigned (edenot E' (esub e ne)) ≤ 0
      have hz : bv_unsigned (edenot E' (esub e ne)) = 0 := by
        rw [esub, mkAlu_denot, SymExec.alu64_sub_eq, u_sub64, Hev, Hne]
        simp
      rw [hz]
      exact ⟨Int.le_refl 0, Int.le_refl 0⟩
    · exact residue_fact_sound segs E E' M M' k e ne HK Hne Hd K hK

/--  :2138, the body of `PFresh` for an already-resolved base
    expression: the guard, the two `xlo2`/`xhi2` bounds and the state it
    builds.  `node_fresh_sound_pf` only has to eliminate the `Option` match on
    `base` (`node_fresh` compiles it to a shared auxiliary match function,
    which no `rw`/`generalize` can see through) and hand the hypothesis here. -/
theorem node_fresh_step (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (T : TSet) (r : Nat) (logc : Int) (b : expr) (cs' : acs)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (Hk : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' → m_fs model' = m_fs model →
      srealizes segs (cfg_of segs R' (pc cs') FULL' model') T)
    (Hn : (if (decide (0 < r) && decide (r < 32) && decide (0 ≤ logc) && decide (logc ≤ 40) &&
        decide (logc ≤ ealign (kn cs) (esub (reg cs r) b)) &&
        AsanPlanCore.expr_vars_lt (nxt cs) b &&
        AsanPlanCore.expr_vars_lt (nxt cs) (esub (reg cs r) b) && fresh_ok nx0 cs) = true then
      (match xlo2 (kn cs) (esub (reg cs r) b), xhi2 (kn cs) (esub (reg cs r) b) with
       | some lo, some hi =>
          some (bump (set_reg (add_kn cs (.KRange (.EVar (nxt cs))
              ((lo + zpow 2 logc - 1) / zpow 2 logc) (hi / zpow 2 logc) ::
              .KRange (esub (esub (reg cs r) b) (escale (zpow 2 logc) (.EVar (nxt cs)))) 0 0 ::
              residue_fact (kn cs) (esub (reg cs r) b) (escale (zpow 2 logc) (.EVar (nxt cs)))))
            r (eadd b (escale (zpow 2 logc) (.EVar (nxt cs))))) 1)
       | _, _ => none) else none) = some cs') :
    srealizes segs (cfg_of segs R (pc cs) FULL model) T := by
  by_cases hc : (decide (0 < r) && decide (r < 32) && decide (0 ≤ logc) &&
      decide (logc ≤ 40) && decide (logc ≤ ealign (kn cs) (esub (reg cs r) b)) &&
      AsanPlanCore.expr_vars_lt (nxt cs) b &&
      AsanPlanCore.expr_vars_lt (nxt cs) (esub (reg cs r) b) && fresh_ok nx0 cs) = true
  · rw [ite_eq_left hc] at Hn
    have hg := hc
    simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hg
    obtain ⟨h0r, hr32, h0l, hl40, hal, hvb, hve, hf⟩ := hg
    revert Hn
    generalize hh1 : xlo2 (kn cs) (esub (reg cs r) b) = o1
    generalize hh2 : xhi2 (kn cs) (esub (reg cs r) b) = o2
    cases o1 with
    | none =>
        intro Hn
        simp at Hn
    | some lo =>
      cases o2 with
      | none =>
          intro Hn
          simp at Hn
      | some hi =>
          intro Hn
          simp only [Option.some.injEq] at Hn
          subst Hn
          let ne : expr := escale (zpow 2 logc) (.EVar (nxt cs))
          let kf : List kentry :=
            .KRange (.EVar (nxt cs)) ((lo + zpow 2 logc - 1) / zpow 2 logc) (hi / zpow 2 logc) ::
              .KRange (esub (esub (reg cs r) b) ne) 0 0 ::
              residue_fact (kn cs) (esub (reg cs r) b) ne
          obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs hf
          have HK := HC.co_know
          have Hlo := xlo2_sound segs E (Mr A argH E cs model FULL) (kn cs)
            (esub (reg cs r) b) lo HK hh1
          have Hhi := xhi2_sound segs E (Mr A argH E cs model FULL) (kn cs)
            (esub (reg cs r) b) hi HK hh2
          obtain ⟨Hea0, Hdiv⟩ :=
            ealign_sound segs E (Mr A argH E cs model FULL) (kn cs) (esub (reg cs r) b) HK
          have Hcpos : 0 < zpow 2 logc := by
            show 0 < (2 : Int) ^ logc.toNat
            exact two_pow_pos_int _
          have Hcnat : logc.toNat ≤ 40 := by
            have h : (40 : Int).toNat = 40 := by decide
            rw [← h]
            exact Int.toNat_le_toNat hl40
          have Hc40 : zpow 2 logc ≤ 2 ^ 40 := by
            show (2 : Int) ^ logc.toNat ≤ (2 : Int) ^ 40
            exact int_pow_le_pow _ _ Hcnat
          have Hclt : zpow 2 logc < 2 ^ 64 := by
            have h : (2 : Int) ^ 40 < 2 ^ 64 := by decide
            omega
          have Hcd : zpow 2 logc ∣ bv_unsigned (edenot E (esub (reg cs r) b)) :=
            Int.dvd_trans (pow2_divide_le logc (ealign (kn cs) (esub (reg cs r) b))
              ⟨h0l, hal⟩) Hdiv
          obtain ⟨q, Hq⟩ := Hcd
          have Hue : 0 ≤ bv_unsigned (edenot E (esub (reg cs r) b)) ∧
              bv_unsigned (edenot E (esub (reg cs r) b)) < 2 ^ 64 := u64_range _
          have Hq0 : 0 ≤ q := by
            by_cases h : 0 ≤ q
            · exact h
            · have hneg : zpow 2 logc * q < 0 := Int.mul_neg_of_pos_of_neg Hcpos (by omega)
              omega
          have Hq64 : q < 2 ^ 64 := by
            have hc1 : (1 : Int) ≤ zpow 2 logc := Hcpos
            have hle : 1 * q ≤ zpow 2 logc * q := Int.mul_le_mul_of_nonneg_right hc1 Hq0
            rw [Int.one_mul] at hle
            omega
          let E' : env := ext1 E (nxt cs) (Z_to_bv 64 q)
          have HagE : env_agree (nxt cs) E E' := ext1_agree E (nxt cs) (Z_to_bv 64 q)
          have HC' := cs_ok_agree segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
            E E' cs R FULL model HagE hf HC
          have Hvb : edenot E' b = edenot E b :=
            (edenot_agree' (nxt cs) E E' b HagE hvb).symm
          have Hve : edenot E' (esub (reg cs r) b) = edenot E (esub (reg cs r) b) :=
            (edenot_agree' (nxt cs) E E' _ HagE hve).symm
          have Hrv : edenot E' (reg cs r) = edenot E (reg cs r) := by
            have hr : AsanPlanCore.expr_vars_lt (nxt cs) (reg cs r) = true :=
              nth_sr_vars_lt (nxt cs) cs.a_ss.s_regs r Fsr hr32
            exact (edenot_agree' (nxt cs) E E' _ HagE hr).symm
          have He_sem : edenot E (esub (reg cs r) b)
              = edenot E (reg cs r) - edenot E b := by
            rw [esub, mkAlu_denot, SymExec.alu64_sub_eq]
          have Hne : edenot E' ne = edenot E (esub (reg cs r) b) := by
            show edenot E' (escale (zpow 2 logc) (.EVar (nxt cs))) = _
            rw [escale, mkMd_denot]
            show mul_div MulOp.MUL (Z_to_bv 64 (zpow 2 logc)) (E'.ev (nxt cs)) = _
            rw [show E'.ev (nxt cs) = Z_to_bv 64 q from ext1_at E (nxt cs) (Z_to_bv 64 q)]
            have key : bv_unsigned (mul_div MulOp.MUL (Z_to_bv 64 (zpow 2 logc)) (Z_to_bv 64 q))
                = bv_unsigned (edenot E (esub (reg cs r) b)) := by
              show bv_unsigned ((Z_to_bv 64 (zpow 2 logc)) * (Z_to_bv 64 q)) = _
              rw [u_mul64, u_small (zpow 2 logc) ⟨by omega, Hclt⟩, u_small q ⟨Hq0, Hq64⟩, ← Hq]
              exact Int.emod_eq_of_lt (by omega) (by omega)
            exact BitVec.eq_of_toNat_eq (Int.ofNat.inj key)
          refine Hk E' R FULL model
            ⟨env_agree_le nx0 (nxt cs) E E' HagE Fle, HagE⟩ ?_ rfl
          refine ⟨?_, rfl, ?_, HC'.co_halt, HC'.co_fds, HC'.co_fs, HC'.co_tid, HC'.co_res,
            HC'.co_limit, HC'.co_maps, HC'.co_holes, HC'.co_seps, HC'.co_wf, HC'.co_bounds,
            HC'.co_lazyb, HC'.co_nasub, HC'.co_none, HC'.co_kinds, HC'.co_totsz, HC'.co_split,
            HC'.co_brk, HC'.co_sbrk, HC'.co_eager, HC'.co_abytes, HC'.co_minv, HC'.co_zero,
            HC'.co_sinv⟩
          · show regs_ok E' (sr_upd cs.a_ss.s_regs r (eadd b ne)) R
            refine regs_ok_respell E' cs.a_ss.s_regs R r (eadd b ne) HC'.co_regs
              ⟨h0r, hr32⟩ ?_
            show edenot E' (eadd b ne) = edenot E' (reg cs r)
            rw [eadd, mkAlu_denot, SymExec.alu64_add_eq, Hvb, Hne, He_sem, Hrv]
            rw [BitVec.add_comm, BitVec.sub_add_cancel]
          · show know_ok segs E' (Mr A argH E' cs model FULL) (kf ++ kn cs)
            have hkf := fresh_entries_ok segs E E' (Mr A argH E cs model FULL)
              (Mr A argH E' cs model FULL) (kn cs) (esub (reg cs r) b) ne (nxt cs)
              (zpow 2 logc) lo hi q HK Hne
              (fun e' s hd => (edenot_agree' (nxt cs) E E' e' HagE
                (deand_vars (nxt cs) (esub (reg cs r) b) e' s hd hve)).symm)
              (by rw [show E'.ev (nxt cs) = Z_to_bv 64 q from ext1_at E (nxt cs) (Z_to_bv 64 q)]
                  exact u_small q ⟨Hq0, Hq64⟩)
              Hcpos Hlo Hhi Hq Hve
            intro K hK
            rcases List.mem_append.mp hK with hK | hK
            · exact hkf K hK
            · exact HC'.co_know K hK
  · rw [ite_eq_right hc] at Hn
    simp at Hn

/--  :2138 — the `PFresh` node: a fresh variable pinned to a residue
    class.  `node_fresh` compiles its `match base with` into a shared auxiliary
    match function, which neither `rw` nor `generalize` can see through; the
    two `cases base` arms therefore name the resulting expression themselves
    and hand the hypothesis to `node_fresh_step`. -/
theorem node_fresh_sound_pf (segs : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) : fresh_stmt segs A nx0 LIMIT SINV argH FS0 := by
  intro r logc base cs cs' E R FULL model T HC _ Hn Hk
  unfold node_fresh at Hn
  dsimp only at Hn
  cases base with
  | none =>
      dsimp only at Hn
      generalize hb : (expr.ELit 0) = bb at Hn
      exact node_fresh_step segs A nx0 LIMIT SINV SINV_agree argH argH_agree FS0 E cs R FULL
        model T r logc bb cs' HC Hk Hn
  | some b0 =>
      dsimp only at Hn
      generalize hb : b0 = bb at Hn
      exact node_fresh_step segs A nx0 LIMIT SINV SINV_agree argH argH_agree FS0 E cs R FULL
        model T r logc bb cs' HC Hk Hn


/-!
Local helpers : `getD_map_erename`,
`estart_rename`, `elenZ_rename`, `adenot_rename`, `flat_rename`,
`allow1_rename`, `amap_den_mrename`.
MEASURED (this pass):
  * `node_rename`'s body holds `let ok (v) := match nt_get fw v with …` and
    `match mk_fwd m, mk_bwd m with`, and BOTH compile to shared auxiliary
    match functions (`node_rename.match_1`).  `rw`, `generalize` and `cases`
    on `mk_fwd m` / `nt_get fw v` therefore do NOT reach them, and
    `dsimp only at H` cannot reduce the auxiliary while the scrutinee is
    still a variable.  The recipe that works in `rename_sound` is:
    `unfold node_rename at H`, `by_cases` + `rw [ite_eq_left …]` for the outer
    `if`, then `revert H` -> `cases hfw : mk_fwd m` -> `cases hbw : mk_bwd m`
    -> `intro H` -> `dsimp only at H` (now a redex, so it iota-reduces).  The
    `s_log` component of the inner guard is best discharged by rewriting
    `HC.co_log` into `H` FIRST (`simp only [Bool.and_true]`), which avoids a
    hypothesis-level split of `match cs.a_ss.s_log`.
  * `show`/`change` to `rename_cs fw cs nx` must keep the SAME `nx` the
    definition puts into `mk_ss` (`max gb (csmaxv (rename_cs fw cs 0))`):
    `with_ss` only overwrites `s_next`, the `s_regs`/`kn` fields are already
    the renamed ones, so any `nx` that matches the goal's `mk_ss` reduces.
-/

/-- The renamed valuation: a target reads its source's value. -/
def ren_env (bw : List (Option Nat)) (E : env) : env :=
  { ev := fun w => match nt_get bw w with | some s => E.ev s | none => E.ev w
    eb := E.eb }

/-- `v` may keep its own value after the renaming. -/
def ren_ok (fw bw : List (Option Nat)) (v : Nat) : Bool :=
  match nt_get fw v with
  | some _ => true
  | none => match nt_get bw v with | some _ => false | none => true

/-- The forward table reads exactly the pairs of `m`. -/
theorem mk_fwd_spec_gen (m0 : List (Nat × Nat)) :
    ∀ (t : List (Option Nat)), mk_fwd m0 = some t → ∀ s d, nt_get t s = some d ↔ (s, d) ∈ m0 := by
  induction m0 with
  | nil =>
      intro t H s d
      simp only [mk_fwd, Option.some.injEq] at H
      subst H
      simp only [nt_get, List.getD_nil, List.not_mem_nil, iff_false]
      intro h
      cases h
  | cons p rest ih =>
      intro t H s d
      obtain ⟨s0, d0⟩ := p
      simp only [mk_fwd] at H
      cases hr : mk_fwd rest with
      | none => rw [hr] at H; simp at H
      | some t0 =>
          rw [hr] at H
          dsimp only at H
          cases hg : nt_get t0 s0 with
          | some x => rw [hg] at H; simp at H
          | none =>
              rw [hg] at H
              dsimp only at H
              simp only [Option.some.injEq] at H
              subst H
              rw [nt_get_set]
              by_cases hseq : s = s0
              · subst hseq
                simp only [beq_self_eq_true, ite_true, Option.some.injEq, List.mem_cons,
                  Prod.mk.injEq, true_and]
                have hn : ¬ (s, d) ∈ rest := by
                  intro hmem
                  have hsome : nt_get t0 s = some d := (ih t0 hr s d).mpr hmem
                  rw [hg] at hsome
                  exact absurd hsome (by simp)
                constructor
                · intro h; exact Or.inl h.symm
                · intro h
                  rcases h with h | h
                  · exact h.symm
                  · exact absurd h hn
              · have hbeq : (s == s0) = false := by simp [hseq]
                rw [hbeq]
                simp only [Bool.false_eq_true, ite_false]
                rw [ih t0 hr s d]
                rw [List.mem_cons]
                constructor
                · exact Or.inr
                · intro h
                  rcases h with h | h
                  · exact absurd (Prod.mk.injEq .. ▸ h) (by simp [hseq])
                  · exact h

/-- The backward table reads exactly the pairs of `m`, transposed. -/
theorem mk_bwd_spec_gen (m0 : List (Nat × Nat)) :
    ∀ (t : List (Option Nat)), mk_bwd m0 = some t → ∀ s d, nt_get t d = some s ↔ (s, d) ∈ m0 := by
  induction m0 with
  | nil =>
      intro t H s d
      simp only [mk_bwd, Option.some.injEq] at H
      subst H
      simp only [nt_get, List.getD_nil, List.not_mem_nil, iff_false]
      intro h
      cases h
  | cons p rest ih =>
      intro t H s d
      obtain ⟨s0, d0⟩ := p
      simp only [mk_bwd] at H
      cases hr : mk_bwd rest with
      | none => rw [hr] at H; simp at H
      | some t0 =>
          rw [hr] at H
          dsimp only at H
          cases hg : nt_get t0 d0 with
          | some x => rw [hg] at H; simp at H
          | none =>
              rw [hg] at H
              dsimp only at H
              simp only [Option.some.injEq] at H
              subst H
              rw [nt_get_set]
              by_cases hdeq : d = d0
              · subst hdeq
                simp only [beq_self_eq_true, ite_true, Option.some.injEq, List.mem_cons,
                  Prod.mk.injEq, true_and, and_true]
                have hn : ¬ (s, d) ∈ rest := by
                  intro hmem
                  have hsome : nt_get t0 d = some s := (ih t0 hr s d).mpr hmem
                  rw [hg] at hsome
                  exact absurd hsome (by simp)
                constructor
                · intro h; exact Or.inl h.symm
                · intro h
                  rcases h with h | h
                  · exact h.symm
                  · exact absurd h hn
              · have hbeq : (d == d0) = false := by simp [hdeq]
                rw [hbeq]
                simp only [Bool.false_eq_true, ite_false]
                rw [ih t0 hr s d]
                rw [List.mem_cons]
                constructor
                · exact Or.inr
                · intro h
                  rcases h with h | h
                  · exact absurd (Prod.mk.injEq .. ▸ h) (by simp [hdeq])
                  · exact h

/-- `fw_in`: the forward table at `fw`. -/
theorem fw_in (m : List (Nat × Nat)) (fw : List (Option Nat)) (Hfw : mk_fwd m = some fw)
    (s d : Nat) : nt_get fw s = some d ↔ (s, d) ∈ m :=
  mk_fwd_spec_gen m fw Hfw s d

/-- `bw_in`: the backward table at `bw`. -/
theorem bw_in (m : List (Nat × Nat)) (bw : List (Option Nat)) (Hbw : mk_bwd m = some bw)
    (s d : Nat) : nt_get bw d = some s ↔ (s, d) ∈ m :=
  mk_bwd_spec_gen m bw Hbw s d

theorem edenot_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) :
    ∀ (E : env) (e : expr), evars_all (ren_ok fw bw) e = true →
      edenot (ren_env bw E) (erename fw e) = edenot E e := by
  intro E e
  induction e with
  | ELit z => intro _; rfl
  | EVar v =>
      intro H
      simp only [evars_all] at H
      simp only [erename]
      cases h : nt_get fw v with
      | some d =>
          have hm : (v, d) ∈ m := (fw_in m fw Hfw v d).mp h
          have hbd : nt_get bw d = some v := (bw_in m bw Hbw v d).mpr hm
          show (ren_env bw E).ev d = E.ev v
          show (match nt_get bw d with | some s => E.ev s | none => E.ev d) = E.ev v
          rw [hbd]
      | none =>
          rw [ren_ok, h] at H
          dsimp only at H
          cases hb : nt_get bw v with
          | some x => rw [hb] at H; simp at H
          | none =>
              show (ren_env bw E).ev v = E.ev v
              show (match nt_get bw v with | some s => E.ev s | none => E.ev v) = E.ev v
              rw [hb]
  | EAlu op x y ihx ihy =>
      intro H
      simp only [evars_all, Bool.and_eq_true] at H
      simp only [erename]
      show alu64 op (edenot (ren_env bw E) (erename fw x))
          (edenot (ren_env bw E) (erename fw y)) = alu64 op (edenot E x) (edenot E y)
      rw [ihx H.1, ihy H.2]
  | EAluw op x y ihx ihy =>
      intro H
      simp only [evars_all, Bool.and_eq_true] at H
      simp only [erename]
      show sext 64 (alu32 op (low32 (edenot (ren_env bw E) (erename fw x)))
          (low32 (edenot (ren_env bw E) (erename fw y))))
        = sext 64 (alu32 op (low32 (edenot E x)) (low32 (edenot E y)))
      rw [ihx H.1, ihy H.2]
  | EMd op x y ihx ihy =>
      intro H
      simp only [evars_all, Bool.and_eq_true] at H
      simp only [erename]
      show mul_div op (edenot (ren_env bw E) (erename fw x))
          (edenot (ren_env bw E) (erename fw y)) = mul_div op (edenot E x) (edenot E y)
      rw [ihx H.1, ihy H.2]
  | EMdw op x y ihx ihy =>
      intro H
      simp only [evars_all, Bool.and_eq_true] at H
      simp only [erename]
      show sext 64 (mul_div op (low32 (edenot (ren_env bw E) (erename fw x)))
          (low32 (edenot (ren_env bw E) (erename fw y))))
        = sext 64 (mul_div op (low32 (edenot E x)) (low32 (edenot E y)))
      rw [ihx H.1, ihy H.2]
  | EExt sx lo n a iha =>
      intro H
      simp only [evars_all] at H
      simp only [erename]
      show ext_val sx lo n (edenot (ren_env bw E) (erename fw a))
        = ext_val sx lo n (edenot E a)
      rw [iha H]
  | EBlob sx k i n => intro _; rfl

/-- The renamed valuation keeps the byte strings. -/
theorem eb_ren (bw : List (Option Nat)) (E : env) : (ren_env bw E).eb = E.eb := rfl

/-- Under a good renaming the valuation agrees below `gb`. -/
theorem ren_agree (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (gb : Nat)
    (Hm : m.all (fun p => gb ≤ p.1 && gb ≤ p.2) = true) (E : env) :
    env_agree gb E (ren_env bw E) := by
  refine ⟨?_, rfl⟩
  intro n _
  cases hb : nt_get bw n with
  | none =>
      show E.ev n = (ren_env bw E).ev n
      show E.ev n = (match nt_get bw n with | some s => E.ev s | none => E.ev n)
      rw [hb]
  | some s =>
      exfalso
      have hm : (s, n) ∈ m := (bw_in m bw Hbw s n).mp hb
      have hall := (List.all_eq_true.mp Hm) (s, n) hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
      omega

/-- `uE` is invariant under the renaming. -/
theorem uE_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (e : expr)
    (H : evars_all (ren_ok fw bw) e = true) : uE (ren_env bw E) (erename fw e) = uE E e := by
  simp only [uE, edenot_rename m fw bw Hfw Hbw E e H]

/-- `getD` commutes with the renaming (the default is a
    literal). -/
theorem getD_map_erename (fw : List (Option Nat)) :
    ∀ (sr : List expr) (i : Nat),
      (sr.map (erename fw)).getD i (.ELit 0) = erename fw (sr.getD i (.ELit 0)) := by
  intro sr
  induction sr with
  | nil => intro i; rfl
  | cons e t ih =>
      intro i
      cases i with
      | zero => rfl
      | succ j => simp only [List.getD_cons_succ]; exact ih j

/-- The register file is renamed consistently. -/
theorem regs_ok_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env)
    (sr : List expr) (R : BvMap word) (Hsr : sr.all (evars_all (ren_ok fw bw)) = true)
    (HR : regs_ok E sr R) : regs_ok (ren_env bw E) (sr.map (erename fw)) R := by
  intro r
  rw [HR r]
  simp only [sr_get]
  cases hz : bv_eqb r 0 with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      revert Hsr
      generalize ridx r = i
      clear HR
      induction sr generalizing i with
      | nil => intro _; rfl
      | cons e t ih =>
          intro Hsr
          simp only [List.all_cons, Bool.and_eq_true] at Hsr
          cases i with
          | zero => exact (edenot_rename m fw bw Hfw Hbw E e Hsr.1).symm
          | succ j => simp only [List.getD_cons_succ]; exact ih j Hsr.2

/-- `estart` is invariant under the renaming. -/
theorem estart_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (a : saddr)
    (H : evars_all (ren_ok fw bw) a.a_base = true) :
    estart (ren_env bw E) (arename fw a) = estart E a := by
  simp only [estart, arename, edenot_rename m fw bw Hfw Hbw E a.a_base H]

/-- `elenZ` is invariant under the renaming. -/
theorem elenZ_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (n : expr)
    (H : evars_all (ren_ok fw bw) n = true) :
    elenZ (ren_env bw E) (erename fw n) = elenZ E n := by
  simp only [elenZ, edenot_rename m fw bw Hfw Hbw E n H]

/-- `adenot` is invariant under the renaming. -/
theorem adenot_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (a : saddr)
    (H : evars_all (ren_ok fw bw) a.a_base = true) :
    adenot (ren_env bw E) (arename fw a) = adenot E a := by
  simp only [adenot, arename, edenot_rename m fw bw Hfw Hbw E a.a_base H]

/-- `flat` is invariant under the renaming. -/
theorem flat_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (a : saddr) (n : Int)
    (H : evars_all (ren_ok fw bw) a.a_base = true) :
    flat (ren_env bw E) (arename fw a) n ↔ flat E a n := by
  unfold flat
  rw [estart_rename m fw bw Hfw Hbw E a H]

/-- Every knowledge entry keeps its meaning under the renaming. -/
theorem kentry_ok_rename (segs : List Segment) (m : List (Nat × Nat))
    (fw bw : List (Option Nat)) (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw)
    (E : env) (base : word → Option byte) (K : kentry)
    (HK : kvars_all (ren_ok fw bw) K = true) (Hk : kentry_ok segs E base K) :
    kentry_ok segs (ren_env bw E) base (krename fw K) := by
  cases K with
  | KWord a w v =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2, h3⟩ := Hk
      exact ⟨h1, (flat_rename m fw bw Hfw Hbw E a (w : Int) HK.1).mpr h2,
        by rw [adenot_rename m fw bw Hfw Hbw E a HK.1,
              edenot_rename m fw bw Hfw Hbw E v HK.2]; exact h3⟩
  | KZero a n =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      refine ⟨?_, ?_⟩
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]
        exact (flat_rename m fw bw Hfw Hbw E a (elenZ E n) HK.1).mpr h1
      · intro i hi1 hi2
        rw [elenZ_rename m fw bw Hfw Hbw E n HK.2] at hi2
        rw [estart_rename m fw bw Hfw Hbw E a HK.1]
        exact h2 i hi1 hi2
  | KBlob a n k =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok, eb_ren] at Hk ⊢
      obtain ⟨h1, h2, h3⟩ := Hk
      refine ⟨?_, ?_, ?_⟩
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]
        exact (flat_rename m fw bw Hfw Hbw E a (elenZ E n) HK.1).mpr h1
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]; exact h2
      · intro i hi1 hi2
        rw [elenZ_rename m fw bw Hfw Hbw E n HK.2] at hi2
        rw [estart_rename m fw bw Hfw Hbw E a HK.1]
        exact h3 i hi1 hi2
  | KImg lo hi => simpa only [krename, kentry_ok] using Hk
  | KAlign x mm =>
      simp only [kvars_all] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      exact ⟨h1, by rw [edenot_rename m fw bw Hfw Hbw E x HK]; exact h2⟩
  | KRange x lo hi =>
      simp only [kvars_all] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      exact ⟨by rw [edenot_rename m fw bw Hfw Hbw E x HK]; exact h1,
        by rw [edenot_rename m fw bw Hfw Hbw E x HK]; exact h2⟩
  | KWr a n =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      refine ⟨?_, ?_⟩
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]
        exact (flat_rename m fw bw Hfw Hbw E a (elenZ E n) HK.1).mpr h1
      · intro d mm hd hm
        rw [elenZ_rename m fw bw Hfw Hbw E n HK.2] at hm
        rw [estart_rename m fw bw Hfw Hbw E a HK.1]
        exact h2 d mm hd hm
  | KDisj a1 n1 a2 n2 =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := HK
      simp only [krename, kentry_ok] at Hk ⊢
      rw [estart_rename m fw bw Hfw Hbw E a1 h1, elenZ_rename m fw bw Hfw Hbw E n1 h2,
        estart_rename m fw bw Hfw Hbw E a2 h3, elenZ_rename m fw bw Hfw Hbw E n2 h4]
      exact Hk
  | KFill a n c =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      refine ⟨?_, ?_⟩
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]
        exact (flat_rename m fw bw Hfw Hbw E a (elenZ E n) HK.1).mpr h1
      · intro i hi1 hi2
        rw [elenZ_rename m fw bw Hfw Hbw E n HK.2] at hi2
        rw [estart_rename m fw bw Hfw Hbw E a HK.1]
        exact h2 i hi1 hi2
  | KUnk a n =>
      simp only [kvars_all, Bool.and_eq_true] at HK
      simp only [krename, kentry_ok] at Hk ⊢
      obtain ⟨h1, h2⟩ := Hk
      refine ⟨?_, ?_⟩
      · rw [elenZ_rename m fw bw Hfw Hbw E n HK.2]
        exact (flat_rename m fw bw Hfw Hbw E a (elenZ E n) HK.1).mpr h1
      · intro i hi1 hi2
        rw [elenZ_rename m fw bw Hfw Hbw E n HK.2] at hi2
        rw [estart_rename m fw bw Hfw Hbw E a HK.1]
        exact h2 i hi1 hi2

/-- A whole knowledge list keeps its meaning under the renaming. -/
theorem know_ok_rename (segs : List Segment) (m : List (Nat × Nat))
    (fw bw : List (Option Nat)) (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw)
    (E : env) (M : word → Option byte) :
    ∀ (k : List kentry), k.all (kvars_all (ren_ok fw bw)) = true →
      know_ok segs E M k → know_ok segs (ren_env bw E) M (k.map (krename fw)) := by
  intro k
  induction k with
  | nil => intro _ _ K hK'; exact absurd hK' (by simp)
  | cons K rest ih =>
      intro Hv Hk K' hK'
      simp only [List.all_cons, Bool.and_eq_true] at Hv
      rcases List.mem_cons.mp hK' with rfl | hK'
      · exact kentry_ok_rename segs m fw bw Hfw Hbw E M K Hv.1 (Hk K (List.mem_cons_self ..))
      · exact ih Hv.2 (fun K0 hK0 => Hk K0 (List.mem_cons_of_mem _ hK0)) K' hK'

/-- Every variable of every visible/ghost range is legal . -/
def pvars_all (fw bw : List (Option Nat)) (l : List (expr × expr)) : Bool :=
  l.all (fun p => evars_all (ren_ok fw bw) p.1 && evars_all (ren_ok fw bw) p.2)

/-- one allowed interval is unchanged by the renaming . -/
theorem allow1_rename (A : atable) (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (p : expr × expr)
    (H1 : evars_all (ren_ok fw bw) p.1 = true) (H2 : evars_all (ren_ok fw bw) p.2 = true) :
    allow1 A (ren_env bw E) (prename fw p) = allow1 A E p := by
  simp only [allow1, prename, sh_lo, sh_hi, uE_rename m fw bw Hfw Hbw E p.1 H1,
    uE_rename m fw bw Hfw Hbw E p.2 H2]

/-- The allowed set is unchanged by the renaming. -/
theorem allowA_rename (A : atable) (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (cs : acs) (nx : Nat)
    (Hv : pvars_all fw bw cs.a_vis = true) (Hg : pvars_all fw bw cs.a_ghost = true) :
    allowA A (ren_env bw E) (rename_cs fw cs nx) = allowA A E cs := by
  simp only [allowA, rename_cs, pvars_all] at Hv Hg ⊢
  rw [← List.map_append, List.flatMap_map]
  apply flatMap_congr_mem
  intro p hp
  have hpp : (evars_all (ren_ok fw bw) p.1 && evars_all (ren_ok fw bw) p.2) = true := by
    rcases List.mem_append.mp hp with h | h
    · exact (List.all_eq_true.mp Hv) p h
    · exact (List.all_eq_true.mp Hg) p h
  simp only [Bool.and_eq_true] at hpp
  exact allow1_rename A m fw bw Hfw Hbw E p hpp.1 hpp.2

/-- The visible-range predicate is unchanged by the renaming. -/
theorem in_allow_rename (A : atable) (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (cs : acs) (nx : Nat)
    (Hv : pvars_all fw bw cs.a_vis = true) :
    in_allow A (ren_env bw E) (rename_cs fw cs nx) = in_allow A E cs := by
  funext z
  simp only [in_allow, in_vis, in_sh, rename_cs, existsb_map', pvars_all] at Hv ⊢
  congr 1
  · apply any_congr_mem
    intro p hp
    have hpp := (List.all_eq_true.mp Hv) p hp
    simp only [Bool.and_eq_true] at hpp
    simp only [prename, uE_rename m fw bw Hfw Hbw E p.1 hpp.1,
      uE_rename m fw bw Hfw Hbw E p.2 hpp.2]
  · apply any_congr_mem
    intro p hp
    have hpp := (List.all_eq_true.mp Hv) p hp
    simp only [Bool.and_eq_true] at hpp
    simp only [prename, sh_lo, sh_hi, uE_rename m fw bw Hfw Hbw E p.1 hpp.1,
      uE_rename m fw bw Hfw Hbw E p.2 hpp.2]
    rfl

/-- The ghost-range predicate is unchanged by the renaming. -/
theorem in_ghost_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (cs : acs) (nx : Nat)
    (Hg : pvars_all fw bw cs.a_ghost = true) :
    in_ghost (ren_env bw E) (rename_cs fw cs nx) = in_ghost E cs := by
  funext z
  simp only [in_ghost, rename_cs, existsb_map', pvars_all] at Hg ⊢
  apply any_congr_mem
  intro p hp
  have hpp := (List.all_eq_true.mp Hg) p hp
  simp only [Bool.and_eq_true] at hpp
  simp only [prename, uE_rename m fw bw Hfw Hbw E p.1 hpp.1,
    uE_rename m fw bw Hfw Hbw E p.2 hpp.2]

/-- Visibility is unchanged by the renaming, up to the valuation agreement. -/
theorem hid_rename (A : atable) (nx0 : Nat) (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (gb : Nat) (Hgb : nx0 ≤ gb)
    (Hm : m.all (fun p => gb ≤ p.1 && gb ≤ p.2) = true)
    (E : env) (cs : acs) (nx : Nat) (model : Model)
    (Hv : pvars_all fw bw cs.a_vis = true) :
    hid A argH (ren_env bw E) (rename_cs fw cs nx) model = hid A argH E cs model := by
  funext a
  have hAG : env_agree nx0 E (ren_env bw E) := env_agree_le nx0 gb E _ (ren_agree m fw bw Hfw Hbw gb Hm E) Hgb
  simp only [hid, vis, in_allow_rename A m fw bw Hfw Hbw E cs nx Hv,
    argH_agree E (ren_env bw E) a hAG]

/-- The tracked ledger keeps matching the model's. -/
theorem maps_match_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) :
    ∀ (ms : List amap) (l : List (word × word)),
      ms.all (fun m0 => evars_all (ren_ok fw bw) m0.am_base
        && evars_all (ren_ok fw bw) m0.am_len) = true →
      maps_match E ms l → maps_match (ren_env bw E) (ms.map (mrename fw)) l := by
  intro ms
  induction ms with
  | nil => intro l _ H; exact H
  | cons mm ms ih =>
      intro l H HM
      simp only [List.all_cons, Bool.and_eq_true] at H
      obtain ⟨⟨h1a, h1b⟩, h2⟩ := H
      have hbase : uE (ren_env bw E) (erename fw mm.am_base) = uE E mm.am_base :=
        uE_rename m fw bw Hfw Hbw E mm.am_base h1a
      have hlen : uE (ren_env bw E) (erename fw mm.am_len) = uE E mm.am_len :=
        uE_rename m fw bw Hfw Hbw E mm.am_len h1b
      cases hf : is_tok_kind mm.am_kind with
      | true =>
          simp only [List.map_cons, maps_match, mrename, is_fog, hf] at HM ⊢
          rcases HM with HM | ⟨iv, l', rfl, Hsz, HM⟩
          · exact Or.inl (ih l h2 HM)
          · refine Or.inr ⟨iv, l', rfl, ?_, ih l' h2 HM⟩
            simp only [mrename, hlen]
            exact Hsz
      | false =>
          simp only [List.map_cons, maps_match, mrename, is_fog, hf] at HM ⊢
          obtain ⟨l', rfl, HM⟩ := HM
          refine ⟨l', ?_, ih l' h2 HM⟩
          simp only [amap_den, mrename, edenot_rename m fw bw Hfw Hbw E mm.am_base h1a,
            edenot_rename m fw bw Hfw Hbw E mm.am_len h1b]

/-- Every hole token stays free. -/
theorem holes_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (y : Int)
    (l : List (word × word)) (ms : List amap)
    (H : ms.all (fun m0 => evars_all (ren_ok fw bw) m0.am_base
        && evars_all (ren_ok fw bw) m0.am_len) = true)
    (HF : ∀ m0 ∈ ms, hole_ok E y l m0) :
    ∀ m0 ∈ ms.map (mrename fw), hole_ok (ren_env bw E) y l m0 := by
  intro m0 hm0
  obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hm0
  have h1 := (List.all_eq_true.mp H) m1 hm1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h1a, h1b⟩ := h1
  have hbase : uE (ren_env bw E) (erename fw m1.am_base) = uE E m1.am_base :=
    uE_rename m fw bw Hfw Hbw E m1.am_base h1a
  have hlen : uE (ren_env bw E) (erename fw m1.am_len) = uE E m1.am_len :=
    uE_rename m fw bw Hfw Hbw E m1.am_len h1b
  have hok := HF m1 hm1
  simp only [hole_ok, mrename, is_hole, hbase, hlen] at hok ⊢
  exact hok

/-- The fd state keeps its meaning under the renaming. -/
theorem fds_ok_rename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (f : afd)
    (model : Model)
    (Hv : (match f with
        | .FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o
        | _ => true) = true)
    (H : fds_ok E f model) : fds_ok (ren_env bw E) (frename fw f) model := by
  cases f with
  | FdStd => simpa only [frename, fds_ok] using H
  | FdDir => simpa only [frename, fds_ok] using H
  | FdFile k len off =>
      simp only [Bool.and_eq_true] at Hv
      simp only [frename, fds_ok, eb_ren] at H ⊢
      obtain ⟨p, c, h1, h2, h3, h4, h5⟩ := H
      refine ⟨p, c, ?_, h2, ?_, ?_, ?_⟩
      · rw [h1, edenot_rename m fw bw Hfw Hbw E off Hv.2]
      · rw [uE_rename m fw bw Hfw Hbw E len Hv.1]; exact h3
      · rw [uE_rename m fw bw Hfw Hbw E off Hv.2, uE_rename m fw bw Hfw Hbw E len Hv.1]
        exact h4
      · intro j hj; exact h5 j hj

/-- the ledger entry's interval is unchanged by the renaming
    (`amap_den` of `mrename`). -/
theorem amap_den_mrename (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (E : env) (mm : amap)
    (H1 : evars_all (ren_ok fw bw) mm.am_base = true)
    (H2 : evars_all (ren_ok fw bw) mm.am_len = true) :
    amap_den (ren_env bw E) (mrename fw mm) = amap_den E mm := by
  simp only [amap_den, mrename, edenot_rename m fw bw Hfw Hbw E mm.am_base H1,
    edenot_rename m fw bw Hfw Hbw E mm.am_len H2]

/-- The whole checker state keeps its meaning under the renaming. -/
theorem cs_ok_rename (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (m : List (Nat × Nat)) (fw bw : List (Option Nat))
    (Hfw : mk_fwd m = some fw) (Hbw : mk_bwd m = some bw) (gb : Nat) (Hgb : nx0 ≤ gb)
    (Hm : m.all (fun p => gb ≤ p.1 && gb ≤ p.2) = true)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (nx : Nat) (Hv : csvars_all (ren_ok fw bw) cs = true)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 (ren_env bw E) (rename_cs fw cs nx) R FULL model := by
  simp only [csvars_all, Bool.and_eq_true] at Hv
  obtain ⟨⟨⟨⟨⟨⟨hregs, hkn⟩, hmaps⟩, hvis⟩, hghost⟩, hbrk⟩, hfd⟩ := Hv
  have hAG : env_agree nx0 E (ren_env bw E) :=
    env_agree_le nx0 gb E _ (ren_agree m fw bw Hfw Hbw gb Hm E) Hgb
  have HH : hid A argH (ren_env bw E) (rename_cs fw cs nx) model = hid A argH E cs model :=
    hid_rename A nx0 argH argH_agree m fw bw Hfw Hbw gb Hgb Hm E cs nx model hvis
  have HA : allowA A (ren_env bw E) (rename_cs fw cs nx) = allowA A E cs :=
    allowA_rename A m fw bw Hfw Hbw E cs nx hvis hghost
  have HMr : Mr A argH (ren_env bw E) (rename_cs fw cs nx) model FULL
      = Mr A argH E cs model FULL := by simp only [Mr, HH]
  refine
    { co_regs := ?_, co_log := ?_, co_know := ?_, co_halt := ?_, co_fds := ?_, co_fs := ?_
      co_tid := ?_, co_res := ?_, co_limit := ?_, co_maps := ?_, co_holes := ?_, co_seps := ?_
      co_wf := ?_, co_bounds := ?_, co_lazyb := ?_, co_nasub := ?_, co_none := ?_, co_kinds := ?_
      co_totsz := ?_, co_split := ?_, co_brk := ?_, co_sbrk := ?_, co_eager := ?_
      co_abytes := ?_, co_minv := ?_, co_zero := ?_, co_sinv := ?_ }
  · exact regs_ok_rename m fw bw Hfw Hbw E cs.a_ss.s_regs R hregs HC.co_regs
  · rfl
  · rw [HMr]
    exact know_ok_rename segs m fw bw Hfw Hbw E (Mr A argH E cs model FULL) (kn cs) hkn HC.co_know
  · exact HC.co_halt
  · exact fds_ok_rename m fw bw Hfw Hbw E cs.a_fd model hfd HC.co_fds
  · exact HC.co_fs
  · exact HC.co_tid
  · exact HC.co_res
  · exact HC.co_limit
  · exact maps_match_rename m fw bw Hfw Hbw E cs.a_maps (m_vmmaps model).vm_maps hmaps HC.co_maps
  · exact holes_rename m fw bw Hfw Hbw E cs.a_ylo _ cs.a_maps hmaps HC.co_holes
  · exact HC.co_seps
  · exact HC.co_wf
  · exact HC.co_bounds
  · exact HC.co_lazyb
  · exact HC.co_nasub
  · intro m0 hm0 hk
    obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hm0
    have h1 := (List.all_eq_true.mp hmaps) m1 hm1
    simp only [Bool.and_eq_true] at h1
    rw [amap_den_mrename m fw bw Hfw Hbw E m1 h1.1 h1.2]
    exact HC.co_none m1 hm1 hk
  · intro m0 hm0 hk a Ha
    obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hm0
    have h1 := (List.all_eq_true.mp hmaps) m1 hm1
    simp only [Bool.and_eq_true] at h1
    have hb := edenot_rename m fw bw Hfw Hbw E m1.am_base h1.1
    have hl := edenot_rename m fw bw Hfw Hbw E m1.am_len h1.2
    simp only [mrename] at Ha
    rw [hb, hl] at Ha
    exact HC.co_kinds m1 hm1 hk a Ha
  · exact HC.co_totsz
  · exact HC.co_split
  · show (m_vmmaps model).vm_brk = edenot (ren_env bw E) (erename fw cs.a_brk)
    rw [edenot_rename m fw bw Hfw Hbw E cs.a_brk hbrk]
    exact HC.co_brk
  · exact HC.co_sbrk
  · exact HC.co_eager
  · rw [HA]; exact HC.co_abytes
  · rw [HA]; exact HC.co_minv
  · intro a hh hm1 hm2 hm3 hm4
    rw [HH] at hh
    rw [in_ghost_rename m fw bw Hfw Hbw E cs nx hghost] at hm4
    exact HC.co_zero a hh hm1 hm2 hm3 hm4
  · exact SINV_agree E (ren_env bw E) FULL hAG HC.co_sinv

/-- `PRename` is sound: the renamed state denotes the same shape under a
    valuation agreeing below the GC bound. -/
theorem rename_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (gb : Nat) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (m : List (Nat × Nat)) (cs' : acs)
    (Hgb : nx0 ≤ gb) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_rename gb cs m = some cs') :
    ∃ E', env_agree gb E E' ∧ cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧
      pc cs' = pc cs := by
  unfold node_rename at H
  by_cases Hm : (m.all (fun p => gb ≤ p.1 && gb ≤ p.2)) = true
  · rw [ite_eq_left Hm] at H
    revert H
    cases hfw : mk_fwd m with
    | none =>
        intro H
        dsimp only at H
        exact absurd H (by simp)
    | some fw =>
        cases hbw : mk_bwd m with
        | none =>
            intro H
            dsimp only at H
            exact absurd H (by simp)
        | some bw =>
            intro H
            dsimp only at H
            rw [HC.co_log] at H
            simp only [Bool.and_true] at H
            split at H
            · rename_i Hv
              simp only [Option.some.injEq] at H
              subst cs'
              refine ⟨ren_env bw E, ren_agree m fw bw hfw hbw gb Hm E, ?_, rfl⟩
              show cs_ok segs A LIMIT SINV argH FS0 (ren_env bw E)
                (rename_cs fw cs (max gb (csmaxv (rename_cs fw cs 0)))) R FULL model
              exact cs_ok_rename segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 m fw bw
                hfw hbw gb Hgb Hm E cs R FULL model _ Hv HC
            · exact absurd H (by simp)
  · rw [ite_eq_right Hm] at H
    exact absurd H (by simp)

/-- `PCompact` is sound: it is `PRename` at the compaction map . -/
theorem compact_sound (segs : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (gb : Nat) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (cs' : acs)
    (Hgb : nx0 ≤ gb) (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model)
    (H : node_compact gb cs = some cs') :
    ∃ E', env_agree gb E E' ∧ cs_ok segs A LIMIT SINV argH FS0 E' cs' R FULL model ∧
      pc cs' = pc cs := by
  unfold node_compact at H
  exact rename_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 gb E cs R FULL model
    (compact_map gb cs) cs' Hgb HC H
/-! ## 10+++. `check_sound`

    The summit of the tower: **the plan checker accepts only plans whose
    execution conforms to the shape specification.**

    `AsanPlan.check` is `Nat.rec`-shaped and `AsanPlan.check_go` takes the
    recursive call as a *parameter*, so `AsanPlan.check_succ` unfolds exactly
    one step (`rfl`).  The proof is therefore: induction on the fuel; at
    `fuel + 1`, one case analysis per plan constructor over the body of
    `check_go`, in which

    * the leading `lc_bnd` guard is discharged from the hypothesis itself (its
      `CErr 9` branch is not `COk s`), yielding `lc_guard lc cs = true`;
    * `CONT` is the continuation adapter (`cont_agree` at the induction
      hypothesis, which transports the shape across a valuation that agrees
      below the state's counter and the loop-context guard), and `SAME` is its
      special case at the unchanged valuation;
    * each node decision is taken by `revert`ing the goal, `generalize`ing the
      scrutinee and `cases`ing it on the goal (a hypothesis-level `split` on an
      `Option` match destructures the payload into `Nat`/`Int` cases; see the
      MEASURED notes below), after which the arm is one call to the node lemma
      of section 10 — `fog_sound`, `bump_sound`, …, `rename_sound`,
      `compact_sound`, and the twelve `*_stmt` parameters for the node families
      discharged in the `AsanNodes*` files.
    * the `PRename` / `PCompact` / `PVia` / `PLoop` / `PDiamond` arms recurse
      into the induction hypothesis (the last two through the join frame and
      the loop context they build). -/

/-- **`check_sound`**: **the plan checker accepts only plans
    whose execution conforms to the shape specification.**

    If `AsanPlan.check` returns the shape `s` from the state `cs`, then — for
    every valuation `E`, register file `R`, memory `FULL` and model that realize
    the checker state, and every set `D` the enclosing loop body may realize —
    the configuration at `pc cs` realizes the denotation `sd D E (m_fs model) s`.
    This is the statement the whole tower exists for: the eleven `AsanNodes*`
    files discharge the per-node `*_stmt` obligations it takes as parameters,
    and every node lemma of section 10 is one of its arms. -/
theorem check_sound (segs : List Segment) (IT : itab) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (HS : Nat → Option acs)
    (XN : Nat → List expr → acs → Option acs)
    (XE : Nat → List expr → acs → Option (Int × List spiece × acs))
    (XB : Nat → List expr → acs → Option (acs × acs))
    (IT_ok : itab_sound segs IT) (SEGS_wx : wx_segs_nowrap segs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment segs (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (HOLES : Nat → env → Fs.Fs → TSet)
    (HOLES_agree : ∀ (h : Nat) (E E' : env) (fs : Fs.Fs), env_agree nx0 E E' →
      HOLES h E fs = HOLES h E' fs)
    (HOLES_nil : ∀ (h : Nat) (E : env) (fs : Fs.Fs), HOLES h E fs [])
    (KC : Nat)
    (Hsys : ∀ y, sys_stmt segs A nx0 LIMIT SINV argH FS0 y)
    (Hx : ∀ x, x_stmt segs A nx0 LIMIT SINV argH FS0 x)
    (Hfresh : fresh_stmt segs A nx0 LIMIT SINV argH FS0)
    (Hjoin : join_stmt segs A nx0 LIMIT SINV argH FS0)
    (Hbrk2 : brk2_stmt segs A nx0 LIMIT SINV argH FS0)
    (Hexit : exit_stmt segs A nx0 LIMIT SINV argH FS0)
    (Hext : ext_stmt segs A nx0 LIMIT SINV argH FS0 XN)
    (Hext2 : ext2_stmt segs A nx0 LIMIT SINV argH FS0 XB)
    (Hmmap2 : mm2_stmt segs A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT))
    (Hmprotect2 : mm2_stmt segs A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT))
    (Hmmapin : mm3_stmt segs A nx0 LIMIT SINV argH FS0 (node_mmapin A nx0 LIMIT false))
    (HmmapinH : mm3_stmt segs A nx0 LIMIT SINV argH FS0 (node_mmapin A nx0 LIMIT true))
    (Hemit : emit_stmt segs A nx0 LIMIT SINV argH FS0 XE)
    (Hholes : holes_stmt segs A LIMIT SINV argH FS0 HS HOLES) :
    ∀ (bfuel fuel : Nat) (lc : Option loopctx) (p : plan) (cs : acs) (s : shape),
      AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p = .COk s →
      ∀ (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model) (D : TSet),
        cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model →
        LCOK segs A nx0 LIMIT SINV argH FS0 HOLES lc D E (m_fs model) → D [] →
        srealizes segs (cfg_of segs R (pc cs) FULL model) (sd HOLES D E (m_fs model) s) := by
  intro bfuel fuel
  revert bfuel
  induction fuel with
  | zero =>
      intro bfuel lc p cs s Hc E R FULL model D HC HL HD
      have h0 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel 0 lc cs p
          = .CErr 0 p cs := rfl
      rw [h0] at Hc
      cases Hc
  | succ f IH =>
      intro bfuel lc p cs s Hc E R FULL model D HC HL HD
      have hstep := AsanPlan.check_succ segs IT A nx0 LIMIT XN XE XB HS KC bfuel f lc cs p
      have H : AsanPlan.check_go segs IT A nx0 LIMIT XN XE XB HS KC bfuel
          (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f) lc cs p = .COk s := by
        rw [← hstep]; exact Hc
      -- the `lc_bnd` guard of `check_go`: `CErr 9` is not `COk s`, so it holds
      have Hg : lc_guard lc cs = true := by
        have Hne := H
        cases lc with
        | none => rfl
        | some c =>
            unfold AsanPlan.check_go at Hne
            dsimp only at Hne
            split at Hne
            · cases Hne
            · rename_i hgc
              simpa [lc_guard] using hgc
      have hsv : shape_vars_lt nx0 s = true :=
        check_vars segs IT A nx0 LIMIT XN XE XB HS KC bfuel (f + 1) lc p cs s Hc
      have CONT : ∀ (k : plan) (cs' : acs) (s' : shape),
          AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f lc cs' k = .COk s' →
          ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
            env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
            cs_ok segs A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
            m_fs model' = m_fs model →
            srealizes segs (cfg_of segs R' (pc cs') FULL' model')
              (sd HOLES D E (m_fs model) s') := by
        intro k cs' s' Hk E' R' FULL' model' Hag HC' Hfs
        exact cont_agree segs IT A nx0 LIMIT XN XE XB HS KC SINV argH FS0 HOLES HOLES_agree
          bfuel f lc k cs cs' s' E model D Hk HL Hg HD
          (fun E R FULL model HC'' HL'' HD'' =>
            IH bfuel lc k cs' s' Hk E R FULL model D HC'' HL'' HD'')
          E' R' FULL' model' Hag HC' Hfs
      have SAME : ∀ (k : plan) (cs' : acs) (s' : shape),
          AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f lc cs' k = .COk s' →
          cs_ok segs A LIMIT SINV argH FS0 E cs' R FULL model →
          srealizes segs (cfg_of segs R (pc cs') FULL model)
            (sd HOLES D E (m_fs model) s') := by
        intro k cs' s' Hk HC'
        exact CONT k cs' s' Hk E R FULL model
          ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ HC' rfl
      cases p with
      | PRun stops k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : run_block_gc segs IT nx0 KC bfuel (stops ++ STOPS A) cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok SEGS_wx HULL_ok
                    SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull nx0 bfuel
                    (stops ++ STOPS A) cs cs' E R FULL model _ (by omega) hh HC
                    (fun E' R' FULL' model' h1 h2 h3 h4 =>
                      CONT k cs' s H E' R' FULL' model' ⟨h1, h2⟩ h3 h4)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : run_block_gc segs IT (lc_bnd c) KC bfuel (stops ++ STOPS A) cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok SEGS_wx HULL_ok
                    SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull (lc_bnd c) bfuel
                    (stops ++ STOPS A) cs cs' E R FULL model _
                    (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL)
                    hh HC (fun E' R' FULL' model' h1 h2 h3 h4 =>
                      CONT k cs' s H E' R' FULL' model' ⟨h1, h2⟩ h3 h4)
      | PSplit e mid k1 k2 =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hv : AsanPlanCore.expr_vars_lt nx0 e = true
              · rw [ite_eq_left hv] at H
                revert H
                generalize hr : erange (kn cs) e = r0
                cases r0 with
                | none => intro H; cases H
                | some pr =>
                    intro H
                    try dsimp only at H
                    obtain ⟨lo, hi⟩ := pr
                    by_cases hc : (decide (lo ≤ mid) && decide (mid < hi)) = true
                    · rw [ite_eq_left hc] at H
                      revert H
                      generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r1
                      cases r1 with
                      | COk s1 =>
                          intro H
                          revert H
                          generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r2
                          cases r2 with
                          | COk s2 =>
                              intro H
                              try dsimp only at H
                              cases H
                              obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hr
                              dsimp only [sd]
                              by_cases hle : bv_unsigned (edenot E e) ≤ mid
                              · rw [ite_eq_left hle]
                                exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) _ h1 (HCl hle)
                              · rw [ite_eq_right hle]
                                exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) _ h2 (HCr (by omega))
                          | CErr a b c => intro H; cases H
                      | CErr a b c => intro H; cases H
                    · rw [ite_eq_right hc] at H
                      by_cases hle : hi ≤ mid
                      · rw [ite_eq_left hle] at H
                        exact SAME k1 cs s H HC
                      · rw [ite_eq_right hle] at H
                        exact SAME k2 cs s H HC
              · rw [ite_eq_right hv] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hv : AsanPlanCore.expr_vars_lt nx0 e = true
              · rw [ite_eq_left hv] at H
                revert H
                generalize hr : erange (kn cs) e = r0
                cases r0 with
                | none => intro H; cases H
                | some pr =>
                    intro H
                    try dsimp only at H
                    obtain ⟨lo, hi⟩ := pr
                    by_cases hc : (decide (lo ≤ mid) && decide (mid < hi)) = true
                    · rw [ite_eq_left hc] at H
                      revert H
                      generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r1
                      cases r1 with
                      | COk s1 =>
                          intro H
                          revert H
                          generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r2
                          cases r2 with
                          | COk s2 =>
                              intro H
                              try dsimp only at H
                              cases H
                              obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hr
                              dsimp only [sd]
                              by_cases hle : bv_unsigned (edenot E e) ≤ mid
                              · rw [ite_eq_left hle]
                                exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) _ h1 (HCl hle)
                              · rw [ite_eq_right hle]
                                exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) _ h2 (HCr (by omega))
                          | CErr a b c => intro H; cases H
                      | CErr a b c => intro H; cases H
                    · rw [ite_eq_right hc] at H
                      by_cases hle : hi ≤ mid
                      · rw [ite_eq_left hle] at H
                        exact SAME k1 cs s H HC
                      · rw [ite_eq_right hle] at H
                        exact SAME k2 cs s H HC
              · rw [ite_eq_right hv] at H
                cases H
      | PCase2 e mid k1 k2 =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : erange (kn cs) e = r0
              cases r0 with
              | none => intro H; cases H
              | some pr =>
                  intro H
                  try dsimp only at H
                  obtain ⟨lo, hi⟩ := pr
                  by_cases hc20 : (!(decide (lo ≤ mid) && decide (mid < hi))) = true
                  · rw [ite_eq_left hc20] at H
                    by_cases hc18 : hi ≤ mid
                    · rw [ite_eq_left hc18] at H
                      exact SAME k1 cs s H HC
                    · rw [ite_eq_right hc18] at H
                      exact SAME k2 cs s H HC
                  · rw [ite_eq_right hc20] at H
                    by_cases hc19 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                    · rw [ite_eq_left hc19] at H
                      by_cases hc17 : kn_contra (kn (set_kn cs (.KRange e lo mid :: kn cs))) = true
                      · rw [ite_eq_left hc17] at H
                        obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                        by_cases hle : bv_unsigned (edenot E e) ≤ mid
                        · exact (kn_contra_sound segs E _ _ (HCl hle).co_know hc17).elim
                        · exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) s H (HCr (by omega))
                      · rw [ite_eq_right hc17] at H
                        by_cases hc16 : kn_contra (kn (set_kn cs (.KRange e (mid + 1) hi :: kn cs))) = true
                        · rw [ite_eq_left hc16] at H
                          obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                          by_cases hle : bv_unsigned (edenot E e) ≤ mid
                          · exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) s H (HCl hle)
                          · exact (kn_contra_sound segs E _ _ (HCr (by omega)).co_know hc16).elim
                        · rw [ite_eq_right hc16] at H
                          revert H
                          generalize h3 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r3
                          cases r3 with
                          | COk s1 =>
                              intro H
                              revert H
                              generalize h4 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r4
                              cases r4 with
                              | COk s2 =>
                                  intro H
                                  try dsimp only at H
                                  by_cases hb : shape_eqb s1 s2 = true
                                  · have hse : s1 = s2 := shape_eqb_eq s1 s2 hb
                                    rw [hb] at H
                                    cases H
                                    rw [← hse] at h4
                                    obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                                    by_cases hle : bv_unsigned (edenot E e) ≤ mid
                                    · exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) _ h3 (HCl hle)
                                    · exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) _ h4 (HCr (by omega))
                                  · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                                    rw [hbf] at H
                                    cases H
                              | CErr a b c => intro H; cases H
                          | CErr a b c => intro H; cases H
                    · rw [ite_eq_right hc19] at H
                      cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : erange (kn cs) e = r0
              cases r0 with
              | none => intro H; cases H
              | some pr =>
                  intro H
                  try dsimp only at H
                  obtain ⟨lo, hi⟩ := pr
                  by_cases hc20 : (!(decide (lo ≤ mid) && decide (mid < hi))) = true
                  · rw [ite_eq_left hc20] at H
                    by_cases hc18 : hi ≤ mid
                    · rw [ite_eq_left hc18] at H
                      exact SAME k1 cs s H HC
                    · rw [ite_eq_right hc18] at H
                      exact SAME k2 cs s H HC
                  · rw [ite_eq_right hc20] at H
                    by_cases hc19 : (decide (lo ≤ mid) && decide (mid < hi)) = true
                    · rw [ite_eq_left hc19] at H
                      by_cases hc17 : kn_contra (kn (set_kn cs (.KRange e lo mid :: kn cs))) = true
                      · rw [ite_eq_left hc17] at H
                        obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                        by_cases hle : bv_unsigned (edenot E e) ≤ mid
                        · exact (kn_contra_sound segs E _ _ (HCl hle).co_know hc17).elim
                        · exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) s H (HCr (by omega))
                      · rw [ite_eq_right hc17] at H
                        by_cases hc16 : kn_contra (kn (set_kn cs (.KRange e (mid + 1) hi :: kn cs))) = true
                        · rw [ite_eq_left hc16] at H
                          obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                          by_cases hle : bv_unsigned (edenot E e) ≤ mid
                          · exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) s H (HCl hle)
                          · exact (kn_contra_sound segs E _ _ (HCr (by omega)).co_know hc16).elim
                        · rw [ite_eq_right hc16] at H
                          revert H
                          generalize h3 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e lo mid :: kn cs)) k1 = r3
                          cases r3 with
                          | COk s1 =>
                              intro H
                              revert H
                              generalize h4 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) k2 = r4
                              cases r4 with
                              | COk s2 =>
                                  intro H
                                  try dsimp only at H
                                  by_cases hb : shape_eqb s1 s2 = true
                                  · have hse : s1 = s2 := shape_eqb_eq s1 s2 hb
                                    rw [hb] at H
                                    cases H
                                    rw [← hse] at h4
                                    obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e mid lo hi E R FULL model HC hh
                                    by_cases hle : bv_unsigned (edenot E e) ≤ mid
                                    · exact SAME k1 (set_kn cs (.KRange e lo mid :: kn cs)) _ h3 (HCl hle)
                                    · exact SAME k2 (set_kn cs (.KRange e (mid + 1) hi :: kn cs)) _ h4 (HCr (by omega))
                                  · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                                    rw [hbf] at H
                                    cases H
                              | CErr a b c => intro H; cases H
                          | CErr a b c => intro H; cases H
                    · rw [ite_eq_right hc19] at H
                      cases H
      | PCaseDisj b1 b2 k1 k2 =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_casedisj cs b1 b2 = r0
              cases r0 with
              | none => intro H; cases H
              | some pr =>
                  intro H
                  try dsimp only at H
                  obtain ⟨csa, csb⟩ := pr
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa k1 = r1
                  cases r1 with
                  | COk s1 =>
                      intro H
                      revert H
                      generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb k2 = r2
                      cases r2 with
                      | COk s2 =>
                          intro H
                          try dsimp only at H
                          by_cases hb : shape_eqb s1 s2 = true
                          · have hse : s1 = s2 := shape_eqb_eq s1 s2 hb
                            rw [hb] at H
                            cases H
                            rw [← hse] at h2
                            rcases casedisj_sound segs A LIMIT SINV argH FS0 E cs b1 b2 csa csb R FULL model HC hh
                              with ⟨HC1, Hpc⟩ | ⟨HC1, Hpc⟩
                            · rw [← Hpc]
                              exact SAME k1 csa _ h1 HC1
                            · rw [← Hpc]
                              exact SAME k2 csb _ h2 HC1
                          · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                            rw [hbf] at H
                            cases H
                      | CErr a b c => intro H; cases H
                  | CErr a b c => intro H; cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_casedisj cs b1 b2 = r0
              cases r0 with
              | none => intro H; cases H
              | some pr =>
                  intro H
                  try dsimp only at H
                  obtain ⟨csa, csb⟩ := pr
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa k1 = r1
                  cases r1 with
                  | COk s1 =>
                      intro H
                      revert H
                      generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb k2 = r2
                      cases r2 with
                      | COk s2 =>
                          intro H
                          try dsimp only at H
                          by_cases hb : shape_eqb s1 s2 = true
                          · have hse : s1 = s2 := shape_eqb_eq s1 s2 hb
                            rw [hb] at H
                            cases H
                            rw [← hse] at h2
                            rcases casedisj_sound segs A LIMIT SINV argH FS0 E cs b1 b2 csa csb R FULL model HC hh
                              with ⟨HC1, Hpc⟩ | ⟨HC1, Hpc⟩
                            · rw [← Hpc]
                              exact SAME k1 csa _ h1 HC1
                            · rw [← Hpc]
                              exact SAME k2 csb _ h2 HC1
                          · have hbf : shape_eqb s1 s2 = false := by simpa using hb
                            rw [hbf] at H
                            cases H
                      | CErr a b c => intro H; cases H
                  | CErr a b c => intro H; cases H
      | PShDisj b1 n1 b2 n2 k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_shdisj A cs b1 n1 b2 n2 = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := shdisj_sound segs A LIMIT SINV argH FS0 cs b1 n1 b2 n2 cs'
                    E R FULL model SHADOW_ok HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_shdisj A cs b1 n1 b2 n2 = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := shdisj_sound segs A LIMIT SINV argH FS0 cs b1 n1 b2 n2 cs'
                    E R FULL model SHADOW_ok HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PContra =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · by_cases hk : (kn_contra (kn cs)) = true
              · rw [ite_eq_left hk] at H
                cases H
                exact (kn_contra_sound segs E (Mr A argH E cs model FULL) (kn cs) HC.co_know hk).elim
              · rw [ite_eq_right hk] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · by_cases hk : (kn_contra (kn cs)) = true
              · rw [ite_eq_left hk] at H
                cases H
                exact (kn_contra_sound segs E (Mr A argH E cs model FULL) (kn cs) HC.co_know hk).elim
              · rw [ite_eq_right hk] at H
                cases H
      | PFact K k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · by_cases hf : fact_ok (kn cs) K = true
              · rw [ite_eq_left hf] at H
                exact SAME k (add_kn cs [K]) s H
                  (fact_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model K HC hf)
              · rw [ite_eq_right hf] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · by_cases hf : fact_ok (kn cs) K = true
              · rw [ite_eq_left hf] at H
                exact SAME k (add_kn cs [K]) s H
                  (fact_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model K HC hf)
              · rw [ite_eq_right hf] at H
                cases H
      | PJoin b off n k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_join segs cs b off n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hjoin b off n cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' FULL' model' hag h3 h4 =>
                      CONT k cs' s H E' R' FULL' model' hag h3 h4)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_join segs cs b off n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hjoin b off n cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' FULL' model' hag h3 h4 =>
                      CONT k cs' s H E' R' FULL' model' hag h3 h4)
      | PForget ixs k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (set_kn cs (drop_ixs ixs 0 (kn cs))) s H
                (forget_sound segs A LIMIT SINV argH FS0 E cs R FULL model ixs HC)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (set_kn cs (drop_ixs ixs 0 (kn cs))) s H
                (forget_sound segs A LIMIT SINV argH FS0 E cs R FULL model ixs HC)
      | PDropRange b n k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (node_droprange cs b n) s H
                (droprange_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n HC)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (node_droprange cs b n) s H
                (droprange_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n HC)
      | PGcKeep ws k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (set_kn cs (kn_keep (kn cs) ws)) s H
                (cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _
                  HC (know_ok_filter segs E (Mr A argH E cs model FULL) _ (kn cs) HC.co_know))
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · exact SAME k (set_kn cs (kn_keep (kn cs) ws)) s H
                (cs_ok_set_kn segs A LIMIT SINV argH FS0 E cs R FULL model _
                  HC (know_ok_filter segs E (Mr A argH E cs model FULL) _ (kn cs) HC.co_know))
      | PBump m k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_bump cs m = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := bump_sound segs A LIMIT SINV argH FS0 E cs R FULL model m cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · revert H
              generalize hh : node_bump cs m = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := bump_sound segs A LIMIT SINV argH FS0 E cs R FULL model m cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PHavoc rs k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havoc nx0 cs rs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havoc_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model rs cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havoc nx0 cs rs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havoc_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model rs cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
      | PHavocBig K k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocbig nx0 cs K = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocbig_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model K cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocbig nx0 cs K = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocbig_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model K cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
      | PFresh r logc base k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fresh nx0 cs r logc base = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hfresh r logc base cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' FULL' model' hag h3 h4 => CONT k cs' s H E' R' FULL' model' hag h3 h4)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fresh nx0 cs r logc base = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hfresh r logc base cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' FULL' model' hag h3 h4 => CONT k cs' s H E' R' FULL' model' hag h3 h4)
      | PSys y k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_sys A nx0 y cs = r0
                cases r0 with
                | none => intro H; cases H
                | some cs' =>
                    intro H
                    try dsimp only at H
                    exact Hsys y cs cs' E R FULL model _ HC hec hh
                      (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_sys A nx0 y cs = r0
                cases r0 with
                | none => intro H; cases H
                | some cs' =>
                    intro H
                    try dsimp only at H
                    exact Hsys y cs cs' E R FULL model _ HC hec hh
                      (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
              · rw [ite_eq_right hec] at H
                cases H
      | PBrk2 ka kb =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_brk2 A LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hbrk2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_brk2 A LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hbrk2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
      | PMmap ka kb =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmap2 A nx0 LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hmmap2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmap2 A nx0 LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hmmap2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
      | PMmapIn ka kb kc =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmapin A nx0 LIMIT false cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb, cscs⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            revert H
                            generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs = r3
                            cases r3 with
                            | COk sc =>
                                intro H
                                try dsimp only at H
                                cases H
                                have Hall : ∀ cs ∈ cscs, AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none cs kc = .COk sc :=
                                  (check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs sc h3).2
                                refine srz_conseq segs _ _ _
                                  (Hmmapin cs csa csb cscs E R FULL model _ _ _ HC hec hh
                                    (fun E' R' F' m' hag h3' h4 => CONT ka csa sa h1 E' R' F' m' hag h3' h4)
                                    (fun E' R' F' m' hag h3' h4 => CONT kb csb sb h2 E' R' F' m' hag h3' h4)
                                    (fun csc hin E' R' F' m' hag h3' h4 =>
                                      CONT kc csc sc (Hall csc hin) E' R' F' m' hag h3' h4)) ?_
                                exact t_eq_trans
                                  (t_eq_alt2 _ _ _ _ (t_eq_refl' _) (sd_salt2 HOLES D E (m_fs model) HOLES_nil sb sc HD))
                                  (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa (salt2 sb sc) HD)
                            | CErr a b c => intro H; cases H
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmapin A nx0 LIMIT false cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb, cscs⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            revert H
                            generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs = r3
                            cases r3 with
                            | COk sc =>
                                intro H
                                try dsimp only at H
                                cases H
                                have Hall : ∀ cs ∈ cscs, AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) cs kc = .COk sc :=
                                  (check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs sc h3).2
                                refine srz_conseq segs _ _ _
                                  (Hmmapin cs csa csb cscs E R FULL model _ _ _ HC hec hh
                                    (fun E' R' F' m' hag h3' h4 => CONT ka csa sa h1 E' R' F' m' hag h3' h4)
                                    (fun E' R' F' m' hag h3' h4 => CONT kb csb sb h2 E' R' F' m' hag h3' h4)
                                    (fun csc hin E' R' F' m' hag h3' h4 =>
                                      CONT kc csc sc (Hall csc hin) E' R' F' m' hag h3' h4)) ?_
                                exact t_eq_trans
                                  (t_eq_alt2 _ _ _ _ (t_eq_refl' _) (sd_salt2 HOLES D E (m_fs model) HOLES_nil sb sc HD))
                                  (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa (salt2 sb sc) HD)
                            | CErr a b c => intro H; cases H
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
      | PMmapInH ka kb kc =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmapin A nx0 LIMIT true cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb, cscs⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            revert H
                            generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs = r3
                            cases r3 with
                            | COk sc =>
                                intro H
                                try dsimp only at H
                                cases H
                                have Hall : ∀ cs ∈ cscs, AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none cs kc = .COk sc :=
                                  (check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none) kc cscs sc h3).2
                                refine srz_conseq segs _ _ _
                                  (HmmapinH cs csa csb cscs E R FULL model _ _ _ HC hec hh
                                    (fun E' R' F' m' hag h3' h4 => CONT ka csa sa h1 E' R' F' m' hag h3' h4)
                                    (fun E' R' F' m' hag h3' h4 => CONT kb csb sb h2 E' R' F' m' hag h3' h4)
                                    (fun csc hin E' R' F' m' hag h3' h4 =>
                                      CONT kc csc sc (Hall csc hin) E' R' F' m' hag h3' h4)) ?_
                                exact t_eq_trans
                                  (t_eq_alt2 _ _ _ _ (t_eq_refl' _) (sd_salt2 HOLES D E (m_fs model) HOLES_nil sb sc HD))
                                  (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa (salt2 sb sc) HD)
                            | CErr a b c => intro H; cases H
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mmapin A nx0 LIMIT true cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb, cscs⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            revert H
                            generalize h3 : check_all A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs = r3
                            cases r3 with
                            | COk sc =>
                                intro H
                                try dsimp only at H
                                cases H
                                have Hall : ∀ cs ∈ cscs, AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) cs kc = .COk sc :=
                                  (check_all_ok A (AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c)) kc cscs sc h3).2
                                refine srz_conseq segs _ _ _
                                  (HmmapinH cs csa csb cscs E R FULL model _ _ _ HC hec hh
                                    (fun E' R' F' m' hag h3' h4 => CONT ka csa sa h1 E' R' F' m' hag h3' h4)
                                    (fun E' R' F' m' hag h3' h4 => CONT kb csb sb h2 E' R' F' m' hag h3' h4)
                                    (fun csc hin E' R' F' m' hag h3' h4 =>
                                      CONT kc csc sc (Hall csc hin) E' R' F' m' hag h3' h4)) ?_
                                exact t_eq_trans
                                  (t_eq_alt2 _ _ _ _ (t_eq_refl' _) (sd_salt2 HOLES D E (m_fs model) HOLES_nil sb sc HD))
                                  (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa (salt2 sb sc) HD)
                            | CErr a b c => intro H; cases H
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
      | PMprotect ka kb =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mprotect2 A LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hmprotect2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_mprotect2 A LIMIT cs = r0
                cases r0 with
                | none => intro H; cases H
                | some p =>
                    intro H
                    try dsimp only at H
                    obtain ⟨csa, csb⟩ := p
                    revert H
                    generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa ka = r1
                    cases r1 with
                    | COk sa =>
                        intro H
                        revert H
                        generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb kb = r2
                        cases r2 with
                        | COk sb =>
                            intro H
                            try dsimp only at H
                            cases H
                            exact srz_conseq segs _ _ _
                              (Hmprotect2 cs csa csb E R FULL model _ _ HC hec hh
                                (fun E' R' F' m' hag h3 h4 => CONT ka csa sa h1 E' R' F' m' hag h3 h4)
                                (fun E' R' F' m' hag h3 h4 => CONT kb csb sb h2 E' R' F' m' hag h3 h4))
                              (sd_salt2 HOLES D E (m_fs model) HOLES_nil sa sb HD)
                        | CErr a b c => intro H; cases H
                    | CErr a b c => intro H; cases H
              · rw [ite_eq_right hec] at H
                cases H
      | PX x args k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_x segs A nx0 x args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hx x args cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_x segs A nx0 x args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hx x args cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
      | PExt id args k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XN id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hext id args cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XN id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  exact Hext id args cs cs' E R FULL model _ HC rfl hh
                    (fun E' R' F' m' hag h3 h4 => CONT k cs' s H E' R' F' m' hag h3 h4)
      | PEmit id args k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XE id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some p =>
                  intro H
                  try dsimp only at H
                  obtain ⟨fd, ps, cs'⟩ := p
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none cs' k = r1
                  cases r1 with
                  | COk s1 =>
                      intro H
                      try dsimp only at H
                      cases H
                      exact Hemit id args cs fd ps cs' E R FULL model _ HC hh
                        (sd_has_nil HOLES D E (m_fs model) HOLES_nil s1 HD)
                        (fun E' R' F' m' hag h3 h4 => CONT k cs' s1 h1 E' R' F' m' hag h3 h4)
                  | CErr a b c => intro H; cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XE id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some p =>
                  intro H
                  try dsimp only at H
                  obtain ⟨fd, ps, cs'⟩ := p
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) cs' k = r1
                  cases r1 with
                  | COk s1 =>
                      intro H
                      try dsimp only at H
                      cases H
                      exact Hemit id args cs fd ps cs' E R FULL model _ HC hh
                        (sd_has_nil HOLES D E (m_fs model) HOLES_nil s1 HD)
                        (fun E' R' F' m' hag h3 h4 => CONT k cs' s1 h1 E' R' F' m' hag h3 h4)
                  | CErr a b c => intro H; cases H
      | PExt2 id args k1 k2 =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XB id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some p =>
                  intro H
                  try dsimp only at H
                  obtain ⟨csa, csb⟩ := p
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csa k1 = r1
                  cases r1 with
                  | COk sa =>
                      intro H
                      revert H
                      generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none csb k2 = r2
                      cases r2 with
                      | COk sb =>
                          intro H
                          try dsimp only at H
                          cases H
                          exact Hext2 id args cs csa csb E R FULL model _ _ HC hh
                            (fun E' R' F' m' hag h3 h4 => CONT k1 csa sa h1 E' R' F' m' hag h3 h4)
                            (fun E' R' F' m' hag h3 h4 => CONT k2 csb sb h2 E' R' F' m' hag h3 h4)
                      | CErr a b c => intro H; cases H
                  | CErr a b c => intro H; cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : XB id args cs = r0
              cases r0 with
              | none => intro H; cases H
              | some p =>
                  intro H
                  try dsimp only at H
                  obtain ⟨csa, csb⟩ := p
                  revert H
                  generalize h1 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csa k1 = r1
                  cases r1 with
                  | COk sa =>
                      intro H
                      revert H
                      generalize h2 : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) csb k2 = r2
                      cases r2 with
                      | COk sb =>
                          intro H
                          try dsimp only at H
                          cases H
                          exact Hext2 id args cs csa csb E R FULL model _ _ HC hh
                            (fun E' R' F' m' hag h3 h4 => CONT k1 csa sa h1 E' R' F' m' hag h3 h4)
                            (fun E' R' F' m' hag h3 h4 => CONT k2 csb sb h2 E' R' F' m' hag h3 h4)
                      | CErr a b c => intro H; cases H
                  | CErr a b c => intro H; cases H
      | PLoop J N inv body k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
                revert H
                generalize hlo : loop_ok nx0 cs J N inv = r0
                cases r0 with
                | none => intro H; cases H
                | some nhi =>
                    intro H
                    try dsimp only at H
                    by_cases ht : ((pc inv == pc cs) && entails_h A (J + 1) (nxt inv) cs (inst inv J (.ELit 0))) = true
                    · rw [ite_eq_left ht] at H
                      simp only [Bool.and_eq_true, beq_iff_eq] at ht
                      obtain ⟨Hpc, Hent⟩ := ht
                      revert H
                      generalize hbody : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f
                        (some (.LC (pc cs) (inst inv J (eaddz (.EVar J) 1)) (J + 1) (nxt inv)))
                        (loop_body_state J N nhi inv) body = r1
                      cases r1 with
                      | CErr a b c => intro H; cases H
                      | COk sb =>
                          intro H
                          try dsimp only at H
                          cases sb with
                          | SNil => cases H
                          | SExit c => cases H
                          | SEmitP fd ps s' => cases H
                          | SAlt2 a b => cases H
                          | SCase e mid s1 s2 => cases H
                          | SHole hh => cases H
                          | SNext =>
                              obtain ⟨Ffr, FJ, FJh, Flog, Flen, FvN, FxN, Fnhi⟩ :=
                                loop_ok_facts nx0 cs J N inv nhi hlo
                              obtain ⟨-, -, -, -, -, -, Fle⟩ := fresh_ok_parts nx0 cs Ffr
                              have HNv : bv_unsigned (edenot E N) ≤ nhi :=
                                xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) N nhi HC.co_know FxN
                              have htwo : (two64 : Int) = 2 ^ 64 := rfl
                              have Hnil : sd HOLES D E (m_fs model) s [] :=
                                sd_has_nil HOLES D E (m_fs model) HOLES_nil s HD
                              have Q : ∀ (m : Nat) (j : Int) (E' : env) (R' : BvMap word)
                                  (F' : word → Option byte) (m' : Model),
                                  j = bv_unsigned (edenot E N) - (m : Int) → 0 ≤ j →
                                  env_agree (nxt cs) E E' →
                                  cs_ok segs A LIMIT SINV argH FS0 E' (inst inv J (.ELit j)) R' F' m' →
                                  m_fs m' = m_fs model →
                                  srealizes segs (cfg_of segs R' (pc cs) F' m')
                                    (sd HOLES D E (m_fs model) s) := by
                                intro m
                                induction m with
                                | zero =>
                                    intro j E' R' F' m' Hj Hj0 Hag HCj Hfs
                                    have hj64 : j < 2 ^ 64 := by
                                      have := Fnhi; omega
                                    have hbv : bv_unsigned (edenot E' N) = bv_unsigned (edenot E' (.ELit j)) := by
                                      rw [← edenot_agree' (nxt cs) E E' N Hag FvN]
                                      show bv_unsigned (edenot E N) = bv_unsigned (Z_to_bv 64 j)
                                      rw [u_small j ⟨Hj0, hj64⟩]
                                      omega
                                    have HNe : edenot E' N = edenot E' (.ELit j) :=
                                      BitVec.eq_of_toNat_eq (by exact_mod_cast hbv)
                                    have HCN : cs_ok segs A LIMIT SINV argH FS0 E' (inst inv J N) R' F' m' := by
                                      refine (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J N inv R' F' m' (by omega) Flog).2 ?_
                                      rw [HNe]
                                      exact (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J (.ELit j) inv R' F' m' (by omega) Flog).1 HCj
                                    rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                                      (env_agree_le nx0 (nxt cs) E E' Hag Fle) s hsv]
                                    rw [← Hfs]
                                    rw [show pc cs = pc (inst inv J N) from by rw [pc_inst]; exact Hpc.symm]
                                    exact IH bfuel none k (inst inv J N) s H E' R' F' m' D HCN
                                      (Hfs ▸ LCOK_agree segs A nx0 LIMIT SINV argH FS0 HOLES none D E E'
                                        (m_fs model) cs HL Hg Hag) HD
                                | succ m IHm =>
                                    intro j E' R' F' m' Hj Hj0 Hag HCj Hfs
                                    have hj64 : j < 2 ^ 64 := by
                                      have := Fnhi; omega
                                    have Hjlt : j < bv_unsigned (edenot E N) := by omega
                                    have HCinv : cs_ok segs A LIMIT SINV argH FS0
                                        (upd E' J (Z_to_bv 64 j)) inv R' F' m' :=
                                      (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J (.ELit j) inv R' F' m' (by omega) Flog).1 HCj
                                    have Hag'' : env_agree (nxt cs) E (upd E' J (Z_to_bv 64 j)) := by
                                      refine env_agree_trans (nxt cs) E E' (upd E' J (Z_to_bv 64 j)) Hag ?_
                                      exact env_agree_le (nxt cs) J E' (upd E' J (Z_to_bv 64 j))
                                        (upd_agree E' J (Z_to_bv 64 j)) FJ
                                    have HNE'' : edenot (upd E' J (Z_to_bv 64 j)) N = edenot E N := by
                                      rw [← edenot_agree' (nxt cs) E (upd E' J (Z_to_bv 64 j)) N Hag'' FvN]
                                    have HJ'' : (upd E' J (Z_to_bv 64 j)).ev J = Z_to_bv 64 j :=
                                      upd_at E' J (Z_to_bv 64 j)
                                    have hEv : edenot (upd E' J (Z_to_bv 64 j)) (.EVar J) = Z_to_bv 64 j := HJ''
                                    have hsub : bv_unsigned (edenot (upd E' J (Z_to_bv 64 j)) (esub N (.EVar J)))
                                        = bv_unsigned (edenot E N) - j := by
                                      rw [show edenot (upd E' J (Z_to_bv 64 j)) (esub N (.EVar J))
                                          = edenot (upd E' J (Z_to_bv 64 j)) N
                                            - edenot (upd E' J (Z_to_bv 64 j)) (.EVar J) from by
                                        rw [esub, mkAlu_denot, SymExec.alu64_sub_eq]]
                                      rw [HNE'', hEv, u_sub64, u_small j ⟨Hj0, hj64⟩,
                                        Int.emod_eq_of_lt (by omega) (by omega)]
                                    have HCb : cs_ok segs A LIMIT SINV argH FS0 (upd E' J (Z_to_bv 64 j))
                                        (loop_body_state J N nhi inv) R' F' m' := by
                                      have HKb : know_ok segs (upd E' J (Z_to_bv 64 j))
                                          (Mr A argH (upd E' J (Z_to_bv 64 j))
                                            (loop_body_state J N nhi inv) m' F')
                                          (kn (loop_body_state J N nhi inv)) := by
                                        intro K hK
                                        have hKn : kn (loop_body_state J N nhi inv)
                                            = [.KRange (.EVar J) 0 (nhi - 1),
                                               .KRange (esub N (.EVar J)) 1 nhi] ++ kn inv := rfl
                                        rw [hKn, List.mem_append] at hK
                                        rcases hK with hK | hK
                                        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
                                          rcases hK with rfl | rfl
                                          · refine ⟨?_, ?_⟩
                                            · rw [hEv, u_small j ⟨Hj0, hj64⟩]; exact Hj0
                                            · rw [hEv, u_small j ⟨Hj0, hj64⟩]; omega
                                          · refine ⟨?_, ?_⟩
                                            · rw [hsub]; omega
                                            · rw [hsub]; omega
                                        · exact HCinv.co_know K hK
                                      exact cs_ok_set_kn segs A LIMIT SINV argH FS0
                                        (upd E' J (Z_to_bv 64 j)) inv R' F' m'
                                        (kn (loop_body_state J N nhi inv)) HCinv HKb
                                    rw [show pc cs = pc (loop_body_state J N nhi inv) from Hpc.symm]
                                    refine IH bfuel (some (.LC (pc cs) (inst inv J (eaddz (.EVar J) 1))
                                        (J + 1) (nxt inv))) body (loop_body_state J N nhi inv) shape.SNext hbody
                                      (upd E' J (Z_to_bv 64 j)) R' F' m'
                                      (sd HOLES D E (m_fs model) s) HCb ?_ Hnil
                                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                                    · omega
                                    · omega
                                    · show (inst inv J (eaddz (.EVar J) 1)).a_ss.s_regs.length = 32
                                      rw [show (inst inv J (eaddz (.EVar J) 1)).a_ss.s_regs
                                          = inv.a_ss.s_regs.map (esubst J (eaddz (.EVar J) 1)) from rfl,
                                        List.length_map]
                                      exact Flen
                                    · intro E3 R3 F3 m3 Hag3 HC3 Hfs3
                                      have HJ3 : E3.ev J = Z_to_bv 64 j := by
                                        rw [← HJ'']
                                        exact (Hag3.1 J (by omega)).symm
                                      have Hnext : edenot E3 (eaddz (.EVar J) 1) = Z_to_bv 64 (j + 1) := by
                                        have hbv2 : bv_unsigned (edenot E3 (eaddz (.EVar J) 1))
                                            = bv_unsigned (Z_to_bv 64 (j + 1)) := by
                                          rw [show edenot E3 (eaddz (.EVar J) 1)
                                              = edenot E3 (.EVar J) + edenot E3 (.ELit 1) from by
                                            rw [eaddz, mkAlu_denot, SymExec.alu64_add_eq]]
                                          rw [show edenot E3 (.EVar J) = Z_to_bv 64 j from HJ3,
                                            show edenot E3 (.ELit 1) = Z_to_bv 64 1 from rfl,
                                            u_add64, u_small j ⟨Hj0, hj64⟩, u_small 1 (by decide),
                                            u_small (j + 1) ⟨by omega, by omega⟩]
                                          omega
                                        exact BitVec.eq_of_toNat_eq (by exact_mod_cast hbv2)
                                      have HE4 : env_agree (nxt cs) E
                                          (upd E3 J (Z_to_bv 64 (j + 1))) := by
                                        refine env_agree_trans (nxt cs) E (upd E' J (Z_to_bv 64 j))
                                          (upd E3 J (Z_to_bv 64 (j + 1))) Hag'' ?_
                                        refine env_agree_trans (nxt cs) (upd E' J (Z_to_bv 64 j)) E3
                                          (upd E3 J (Z_to_bv 64 (j + 1))) ?_ ?_
                                        · exact env_agree_le (nxt cs) (J + 1) _ _ Hag3 (by omega)
                                        · exact env_agree_le (nxt cs) J _ _
                                            (upd_agree E3 J (Z_to_bv 64 (j + 1))) FJ
                                      have HCs4 : cs_ok segs A LIMIT SINV argH FS0
                                          (upd E3 J (Z_to_bv 64 (j + 1))) (inst inv J (.ELit (j + 1)))
                                          R3 F3 m3 := by
                                        refine (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                                          FS0 (upd E3 J (Z_to_bv 64 (j + 1))) J (.ELit (j + 1)) inv R3 F3 m3
                                          (by omega) Flog).2 ?_
                                        rw [show edenot (upd E3 J (Z_to_bv 64 (j + 1))) (.ELit (j + 1))
                                            = Z_to_bv 64 (j + 1) from rfl, upd_upd, ← Hnext]
                                        exact (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                                          FS0 E3 J (eaddz (.EVar J) 1) inv R3 F3 m3 (by omega) Flog).1 HC3
                                      exact IHm (j + 1) (upd E3 J (Z_to_bv 64 (j + 1))) R3 F3 m3
                                        (by omega) (by omega) HE4 HCs4 (by rw [Hfs3, Hfs])
                              obtain ⟨E1, Hag1, -, HC1, -⟩ :=
                                entails_h_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok SINV SINV_agree
                                  argH argH_agree FS0 (J + 1) (nxt inv) E cs (inst inv J (.ELit 0))
                                  R FULL model HC Hent (by omega)
                                  (by show (inst inv J (.ELit 0)).a_ss.s_regs.length = 32
                                      rw [show (inst inv J (.ELit 0)).a_ss.s_regs
                                          = inv.a_ss.s_regs.map (esubst J (.ELit 0)) from rfl,
                                        List.length_map]
                                      exact Flen)
                              have hcast : (((bv_unsigned (edenot E N)).toNat : Nat) : Int)
                                  = bv_unsigned (edenot E N) :=
                                Int.toNat_of_nonneg (by have := bv_unsigned_nonneg (edenot E N); omega)
                              refine Q (bv_unsigned (edenot E N)).toNat 0 E1 R FULL model ?_ (by omega)
                                (env_agree_le (nxt cs) (J + 1) E E1 Hag1 (by omega)) HC1 rfl
                              omega
                    · rw [ite_eq_right ht] at H
                      cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
                revert H
                generalize hlo : loop_ok nx0 cs J N inv = r0
                cases r0 with
                | none => intro H; cases H
                | some nhi =>
                    intro H
                    try dsimp only at H
                    by_cases ht : ((pc inv == pc cs) && entails_h A (J + 1) (nxt inv) cs (inst inv J (.ELit 0))) = true
                    · rw [ite_eq_left ht] at H
                      simp only [Bool.and_eq_true, beq_iff_eq] at ht
                      obtain ⟨Hpc, Hent⟩ := ht
                      revert H
                      generalize hbody : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f
                        (some (.LC (pc cs) (inst inv J (eaddz (.EVar J) 1)) (J + 1) (nxt inv)))
                        (loop_body_state J N nhi inv) body = r1
                      cases r1 with
                      | CErr a b c => intro H; cases H
                      | COk sb =>
                          intro H
                          try dsimp only at H
                          cases sb with
                          | SNil => cases H
                          | SExit c => cases H
                          | SEmitP fd ps s' => cases H
                          | SAlt2 a b => cases H
                          | SCase e mid s1 s2 => cases H
                          | SHole hh => cases H
                          | SNext =>
                              obtain ⟨Ffr, FJ, FJh, Flog, Flen, FvN, FxN, Fnhi⟩ :=
                                loop_ok_facts nx0 cs J N inv nhi hlo
                              obtain ⟨-, -, -, -, -, -, Fle⟩ := fresh_ok_parts nx0 cs Ffr
                              have HNv : bv_unsigned (edenot E N) ≤ nhi :=
                                xhi_sound segs E (Mr A argH E cs model FULL) (kn cs) N nhi HC.co_know FxN
                              have htwo : (two64 : Int) = 2 ^ 64 := rfl
                              have Hnil : sd HOLES D E (m_fs model) s [] :=
                                sd_has_nil HOLES D E (m_fs model) HOLES_nil s HD
                              have Q : ∀ (m : Nat) (j : Int) (E' : env) (R' : BvMap word)
                                  (F' : word → Option byte) (m' : Model),
                                  j = bv_unsigned (edenot E N) - (m : Int) → 0 ≤ j →
                                  env_agree (nxt cs) E E' →
                                  cs_ok segs A LIMIT SINV argH FS0 E' (inst inv J (.ELit j)) R' F' m' →
                                  m_fs m' = m_fs model →
                                  srealizes segs (cfg_of segs R' (pc cs) F' m')
                                    (sd HOLES D E (m_fs model) s) := by
                                intro m
                                induction m with
                                | zero =>
                                    intro j E' R' F' m' Hj Hj0 Hag HCj Hfs
                                    have hj64 : j < 2 ^ 64 := by
                                      have := Fnhi; omega
                                    have hbv : bv_unsigned (edenot E' N) = bv_unsigned (edenot E' (.ELit j)) := by
                                      rw [← edenot_agree' (nxt cs) E E' N Hag FvN]
                                      show bv_unsigned (edenot E N) = bv_unsigned (Z_to_bv 64 j)
                                      rw [u_small j ⟨Hj0, hj64⟩]
                                      omega
                                    have HNe : edenot E' N = edenot E' (.ELit j) :=
                                      BitVec.eq_of_toNat_eq (by exact_mod_cast hbv)
                                    have HCN : cs_ok segs A LIMIT SINV argH FS0 E' (inst inv J N) R' F' m' := by
                                      refine (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J N inv R' F' m' (by omega) Flog).2 ?_
                                      rw [HNe]
                                      exact (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J (.ELit j) inv R' F' m' (by omega) Flog).1 HCj
                                    rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                                      (env_agree_le nx0 (nxt cs) E E' Hag Fle) s hsv]
                                    rw [← Hfs]
                                    rw [show pc cs = pc (inst inv J N) from by rw [pc_inst]; exact Hpc.symm]
                                    exact IH bfuel (some c) k (inst inv J N) s H E' R' F' m' D HCN
                                      (Hfs ▸ LCOK_agree segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E E'
                                        (m_fs model) cs HL Hg Hag) HD
                                | succ m IHm =>
                                    intro j E' R' F' m' Hj Hj0 Hag HCj Hfs
                                    have hj64 : j < 2 ^ 64 := by
                                      have := Fnhi; omega
                                    have Hjlt : j < bv_unsigned (edenot E N) := by omega
                                    have HCinv : cs_ok segs A LIMIT SINV argH FS0
                                        (upd E' J (Z_to_bv 64 j)) inv R' F' m' :=
                                      (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0
                                        E' J (.ELit j) inv R' F' m' (by omega) Flog).1 HCj
                                    have Hag'' : env_agree (nxt cs) E (upd E' J (Z_to_bv 64 j)) := by
                                      refine env_agree_trans (nxt cs) E E' (upd E' J (Z_to_bv 64 j)) Hag ?_
                                      exact env_agree_le (nxt cs) J E' (upd E' J (Z_to_bv 64 j))
                                        (upd_agree E' J (Z_to_bv 64 j)) FJ
                                    have HNE'' : edenot (upd E' J (Z_to_bv 64 j)) N = edenot E N := by
                                      rw [← edenot_agree' (nxt cs) E (upd E' J (Z_to_bv 64 j)) N Hag'' FvN]
                                    have HJ'' : (upd E' J (Z_to_bv 64 j)).ev J = Z_to_bv 64 j :=
                                      upd_at E' J (Z_to_bv 64 j)
                                    have hEv : edenot (upd E' J (Z_to_bv 64 j)) (.EVar J) = Z_to_bv 64 j := HJ''
                                    have hsub : bv_unsigned (edenot (upd E' J (Z_to_bv 64 j)) (esub N (.EVar J)))
                                        = bv_unsigned (edenot E N) - j := by
                                      rw [show edenot (upd E' J (Z_to_bv 64 j)) (esub N (.EVar J))
                                          = edenot (upd E' J (Z_to_bv 64 j)) N
                                            - edenot (upd E' J (Z_to_bv 64 j)) (.EVar J) from by
                                        rw [esub, mkAlu_denot, SymExec.alu64_sub_eq]]
                                      rw [HNE'', hEv, u_sub64, u_small j ⟨Hj0, hj64⟩,
                                        Int.emod_eq_of_lt (by omega) (by omega)]
                                    have HCb : cs_ok segs A LIMIT SINV argH FS0 (upd E' J (Z_to_bv 64 j))
                                        (loop_body_state J N nhi inv) R' F' m' := by
                                      have HKb : know_ok segs (upd E' J (Z_to_bv 64 j))
                                          (Mr A argH (upd E' J (Z_to_bv 64 j))
                                            (loop_body_state J N nhi inv) m' F')
                                          (kn (loop_body_state J N nhi inv)) := by
                                        intro K hK
                                        have hKn : kn (loop_body_state J N nhi inv)
                                            = [.KRange (.EVar J) 0 (nhi - 1),
                                               .KRange (esub N (.EVar J)) 1 nhi] ++ kn inv := rfl
                                        rw [hKn, List.mem_append] at hK
                                        rcases hK with hK | hK
                                        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
                                          rcases hK with rfl | rfl
                                          · refine ⟨?_, ?_⟩
                                            · rw [hEv, u_small j ⟨Hj0, hj64⟩]; exact Hj0
                                            · rw [hEv, u_small j ⟨Hj0, hj64⟩]; omega
                                          · refine ⟨?_, ?_⟩
                                            · rw [hsub]; omega
                                            · rw [hsub]; omega
                                        · exact HCinv.co_know K hK
                                      exact cs_ok_set_kn segs A LIMIT SINV argH FS0
                                        (upd E' J (Z_to_bv 64 j)) inv R' F' m'
                                        (kn (loop_body_state J N nhi inv)) HCinv HKb
                                    rw [show pc cs = pc (loop_body_state J N nhi inv) from Hpc.symm]
                                    refine IH bfuel (some (.LC (pc cs) (inst inv J (eaddz (.EVar J) 1))
                                        (J + 1) (nxt inv))) body (loop_body_state J N nhi inv) shape.SNext hbody
                                      (upd E' J (Z_to_bv 64 j)) R' F' m'
                                      (sd HOLES D E (m_fs model) s) HCb ?_ Hnil
                                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                                    · omega
                                    · omega
                                    · show (inst inv J (eaddz (.EVar J) 1)).a_ss.s_regs.length = 32
                                      rw [show (inst inv J (eaddz (.EVar J) 1)).a_ss.s_regs
                                          = inv.a_ss.s_regs.map (esubst J (eaddz (.EVar J) 1)) from rfl,
                                        List.length_map]
                                      exact Flen
                                    · intro E3 R3 F3 m3 Hag3 HC3 Hfs3
                                      have HJ3 : E3.ev J = Z_to_bv 64 j := by
                                        rw [← HJ'']
                                        exact (Hag3.1 J (by omega)).symm
                                      have Hnext : edenot E3 (eaddz (.EVar J) 1) = Z_to_bv 64 (j + 1) := by
                                        have hbv2 : bv_unsigned (edenot E3 (eaddz (.EVar J) 1))
                                            = bv_unsigned (Z_to_bv 64 (j + 1)) := by
                                          rw [show edenot E3 (eaddz (.EVar J) 1)
                                              = edenot E3 (.EVar J) + edenot E3 (.ELit 1) from by
                                            rw [eaddz, mkAlu_denot, SymExec.alu64_add_eq]]
                                          rw [show edenot E3 (.EVar J) = Z_to_bv 64 j from HJ3,
                                            show edenot E3 (.ELit 1) = Z_to_bv 64 1 from rfl,
                                            u_add64, u_small j ⟨Hj0, hj64⟩, u_small 1 (by decide),
                                            u_small (j + 1) ⟨by omega, by omega⟩]
                                          omega
                                        exact BitVec.eq_of_toNat_eq (by exact_mod_cast hbv2)
                                      have HE4 : env_agree (nxt cs) E
                                          (upd E3 J (Z_to_bv 64 (j + 1))) := by
                                        refine env_agree_trans (nxt cs) E (upd E' J (Z_to_bv 64 j))
                                          (upd E3 J (Z_to_bv 64 (j + 1))) Hag'' ?_
                                        refine env_agree_trans (nxt cs) (upd E' J (Z_to_bv 64 j)) E3
                                          (upd E3 J (Z_to_bv 64 (j + 1))) ?_ ?_
                                        · exact env_agree_le (nxt cs) (J + 1) _ _ Hag3 (by omega)
                                        · exact env_agree_le (nxt cs) J _ _
                                            (upd_agree E3 J (Z_to_bv 64 (j + 1))) FJ
                                      have HCs4 : cs_ok segs A LIMIT SINV argH FS0
                                          (upd E3 J (Z_to_bv 64 (j + 1))) (inst inv J (.ELit (j + 1)))
                                          R3 F3 m3 := by
                                        refine (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                                          FS0 (upd E3 J (Z_to_bv 64 (j + 1))) J (.ELit (j + 1)) inv R3 F3 m3
                                          (by omega) Flog).2 ?_
                                        rw [show edenot (upd E3 J (Z_to_bv 64 (j + 1))) (.ELit (j + 1))
                                            = Z_to_bv 64 (j + 1) from rfl, upd_upd, ← Hnext]
                                        exact (cs_ok_inst segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                                          FS0 E3 J (eaddz (.EVar J) 1) inv R3 F3 m3 (by omega) Flog).1 HC3
                                      exact IHm (j + 1) (upd E3 J (Z_to_bv 64 (j + 1))) R3 F3 m3
                                        (by omega) (by omega) HE4 HCs4 (by rw [Hfs3, Hfs])
                              obtain ⟨E1, Hag1, -, HC1, -⟩ :=
                                entails_h_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok SINV SINV_agree
                                  argH argH_agree FS0 (J + 1) (nxt inv) E cs (inst inv J (.ELit 0))
                                  R FULL model HC Hent (by omega)
                                  (by show (inst inv J (.ELit 0)).a_ss.s_regs.length = 32
                                      rw [show (inst inv J (.ELit 0)).a_ss.s_regs
                                          = inv.a_ss.s_regs.map (esubst J (.ELit 0)) from rfl,
                                        List.length_map]
                                      exact Flen)
                              have hcast : (((bv_unsigned (edenot E N)).toNat : Nat) : Int)
                                  = bv_unsigned (edenot E N) :=
                                Int.toNat_of_nonneg (by have := bv_unsigned_nonneg (edenot E N); omega)
                              refine Q (bv_unsigned (edenot E N)).toNat 0 E1 R FULL model ?_ (by omega)
                                (env_agree_le (nxt cs) (J + 1) E E1 Hag1 (by omega)) HC1 rfl
                              omega
                    · rw [ite_eq_right ht] at H
                      cases H
      | PNext =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · cases H
        | some c =>
            cases c with
            | JC j js sk b lo =>
                unfold AsanPlan.check_go at H
                dsimp only at H
                split at H
                · cases H
                · cases H
            | LC u nx lo hi =>
                unfold AsanPlan.check_go at H
                dsimp only at H
                split at H
                · cases H
                · by_cases ht : ((pc cs == u) && entails_h A lo hi cs nx) = true
                  · rw [ite_eq_left ht] at H
                    cases H
                    simp only [Bool.and_eq_true, beq_iff_eq] at ht
                    obtain ⟨Hpc, Hent⟩ := ht
                    obtain ⟨⟨Hn0, Hlh, Hlen⟩, HL2⟩ := HL
                    obtain ⟨E', Hag, -, HC1, -⟩ := entails_h_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok
                      SINV SINV_agree argH argH_agree FS0 lo hi E cs nx R FULL model HC Hent Hn0 Hlen
                    rw [Hpc]
                    exact HL2 E' R FULL model Hag HC1 rfl
                  · rw [ite_eq_right ht] at H
                    cases H
      | PHandoff h =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hs : HS h = r0
              cases r0 with
              | none => intro H; cases H
              | some ch =>
                  intro H
                  try dsimp only at H
                  by_cases he : entails cs ch = true
                  · rw [ite_eq_left he] at H
                    cases H
                    obtain ⟨HC1, Hpc⟩ := entails_sound segs A LIMIT SINV argH FS0 E cs ch R FULL model HC he
                    rw [← Hpc]
                    exact Hholes h ch hs E R FULL model HC1
                  · rw [ite_eq_right he] at H
                    cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hs : HS h = r0
              cases r0 with
              | none => intro H; cases H
              | some ch =>
                  intro H
                  try dsimp only at H
                  by_cases he : entails cs ch = true
                  · rw [ite_eq_left he] at H
                    cases H
                    obtain ⟨HC1, Hpc⟩ := entails_sound segs A LIMIT SINV argH FS0 E cs ch R FULL model HC he
                    rw [← Hpc]
                    exact Hholes h ch hs E R FULL model HC1
                  · rw [ite_eq_right he] at H
                    cases H
      | PExit =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_exit cs = r0
                cases r0 with
                | none => intro H; cases H
                | some code =>
                    intro H
                    try dsimp only at H
                    cases H
                    exact Hexit cs code E R FULL model HC hec hh
              · rw [ite_eq_right hec] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hec : is_ecall_at segs cs = true
              · rw [ite_eq_left hec] at H
                revert H
                generalize hh : node_exit cs = r0
                cases r0 with
                | none => intro H; cases H
                | some code =>
                    intro H
                    try dsimp only at H
                    cases H
                    exact Hexit cs code E R FULL model HC hec hh
              · rw [ite_eq_right hec] at H
                cases H
      | PSpin =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hs : node_spin segs cs = true
              · rw [ite_eq_left hs] at H
                cases H
                exact node_spin_sound segs A LIMIT SINV argH FS0 cs E R FULL model HC hs
              · rw [ite_eq_right hs] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hs : node_spin segs cs = true
              · rw [ite_eq_left hs] at H
                cases H
                exact node_spin_sound segs A LIMIT SINV argH FS0 cs E R FULL model HC hs
              · rw [ite_eq_right hs] at H
                cases H
      | PFog i sz k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fog cs i sz = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := fog_sound segs A LIMIT SINV argH FS0 E cs R FULL model i sz cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fog cs i sz = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := fog_sound segs A LIMIT SINV argH FS0 E cs R FULL model i sz cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PFogNew i sz k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fognew cs i sz = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := fognew_sound segs A LIMIT SINV argH FS0 E cs R FULL model i sz cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_fognew cs i sz = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := fognew_sound segs A LIMIT SINV argH FS0 E cs R FULL model i sz cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PGhost b n k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_ghost LIMIT cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := ghost_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_ghost LIMIT cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := ghost_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PUnvis b n k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_unvis A cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := unvis_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n cs' SHADOW_ok HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_unvis A cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := unvis_sound segs A LIMIT SINV argH FS0 E cs R FULL model b n cs' SHADOW_ok HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PHavocBrk lo hi k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocbrk nx0 cs lo hi = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocbrk_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model lo hi cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocbrk nx0 cs lo hi = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocbrk_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model lo hi cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
      | PIntro lo hi k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_intro nx0 cs lo hi = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := intro_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model lo hi cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_intro nx0 cs lo hi = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := intro_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model lo hi cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
      | PRename rnm k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_rename nx0 cs rnm = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  have Hgb : nx0 ≤ nx0 :=
                    LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES none D E (m_fs model) HL
                  obtain ⟨E', Hag, HC1, Hpc⟩ := rename_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                    FS0 nx0 E cs R FULL model rnm cs' Hgb HC hh
                  rw [← Hpc]
                  rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                    (env_agree_le nx0 nx0 E E' Hag Hgb) _ hsv]
                  exact IH bfuel none k cs' _ H E' R FULL model D HC1
                    (LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES none D E E' (m_fs model) HL Hag) HD
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_rename (lc_bnd c) cs rnm = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  have Hgb : nx0 ≤ (lc_bnd c) :=
                    LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL
                  obtain ⟨E', Hag, HC1, Hpc⟩ := rename_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                    FS0 (lc_bnd c) E cs R FULL model rnm cs' Hgb HC hh
                  rw [← Hpc]
                  rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                    (env_agree_le nx0 (lc_bnd c) E E' Hag Hgb) _ hsv]
                  exact IH bfuel (some c) k cs' _ H E' R FULL model D HC1
                    (LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E E' (m_fs model) HL Hag) HD
      | PCompact k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_compact nx0 cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  have Hgb : nx0 ≤ nx0 :=
                    LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES none D E (m_fs model) HL
                  obtain ⟨E', Hag, HC1, Hpc⟩ := compact_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                    FS0 nx0 E cs R FULL model cs' Hgb HC hh
                  rw [← Hpc]
                  rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                    (env_agree_le nx0 nx0 E E' Hag Hgb) _ hsv]
                  exact IH bfuel none k cs' _ H E' R FULL model D HC1
                    (LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES none D E E' (m_fs model) HL Hag) HD
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_compact (lc_bnd c) cs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  have Hgb : nx0 ≤ (lc_bnd c) :=
                    LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL
                  obtain ⟨E', Hag, HC1, Hpc⟩ := compact_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree
                    FS0 (lc_bnd c) E cs R FULL model cs' Hgb HC hh
                  rw [← Hpc]
                  rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                    (env_agree_le nx0 (lc_bnd c) E E' Hag Hgb) _ hsv]
                  exact IH bfuel (some c) k cs' _ H E' R FULL model D HC1
                    (LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E E' (m_fs model) HL Hag) HD
      | PVia j js lo karms k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hv : via_ok nx0 cs js lo = true
              · rw [ite_eq_left hv] at H
                revert H
                generalize hk : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f none js k = r0
                cases r0 with
                | CErr a b c => intro H; cases H
                | COk sk =>
                    intro H
                    try dsimp only at H
                    simp only [via_ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
                    obtain ⟨⟨⟨⟨-, hlen⟩, hn0⟩, hnl⟩, hlj⟩ := hv
                    refine IH bfuel (some (.JC j js sk (nxt cs) lo)) karms cs s H E R FULL model D HC ?_ HD
                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                    · exact hn0
                    · exact hnl
                    · exact hlen
                    · intro E' R' F' m' Hag HC' Hfs
                      rw [← Hfs]
                      refine IH bfuel none k js sk hk E' R' F' m' D HC' ?_ HD
                      rw [Hfs]
                      exact LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES none D E E' (m_fs model) HL
                        (env_agree_le nx0 (nxt cs) E E' Hag (by first | exact hn0 | exact of_decide_eq_true (by simpa only [lc_guard, lc_bnd] using Hg)))
              · rw [ite_eq_right hv] at H
                cases H
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              by_cases hv : via_ok nx0 cs js lo = true
              · rw [ite_eq_left hv] at H
                revert H
                generalize hk : AsanPlan.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel f (some c) js k = r0
                cases r0 with
                | CErr a b c => intro H; cases H
                | COk sk =>
                    intro H
                    try dsimp only at H
                    simp only [via_ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
                    obtain ⟨⟨⟨⟨-, hlen⟩, hn0⟩, hnl⟩, hlj⟩ := hv
                    refine IH bfuel (some (.JC j js sk (nxt cs) lo)) karms cs s H E R FULL model D HC ?_ HD
                    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
                    · exact hn0
                    · exact hnl
                    · exact hlen
                    · intro E' R' F' m' Hag HC' Hfs
                      rw [← Hfs]
                      refine IH bfuel (some c) k js sk hk E' R' F' m' D HC' ?_ HD
                      rw [Hfs]
                      exact LCOK_agree_gb segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E E' (m_fs model) HL
                        (env_agree_le (lc_bnd c) (nxt cs) E E' Hag (by first | exact hn0 | exact of_decide_eq_true (by simpa only [lc_guard, lc_bnd] using Hg)))
              · rw [ite_eq_right hv] at H
                cases H
      | PMerge j =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            · cases H
        | some c =>
            cases c with
            | LC u nx lo hi =>
                unfold AsanPlan.check_go at H
                dsimp only at H
                split at H
                · cases H
                · cases H
            | JC ja jsb skk bb loo =>
                unfold AsanPlan.check_go at H
                dsimp only at H
                split at H
                · cases H
                · by_cases ht : ((j == ja) && (pc cs == pc jsb) && shape_vars_lt nx0 skk
                      && entails_h A loo (nxt jsb) cs jsb) = true
                  · rw [ite_eq_left ht] at H
                    cases H
                    simp only [Bool.and_eq_true, beq_iff_eq] at ht
                    obtain ⟨⟨⟨-, hpc⟩, hsv'⟩, hent⟩ := ht
                    obtain ⟨⟨Hn0, Hbl, Hlen⟩, HJ⟩ := HL
                    obtain ⟨E', Hag, -, HC1, -⟩ := entails_h_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok
                      SINV SINV_agree argH argH_agree FS0 loo (nxt jsb) E cs jsb R FULL model HC hent
                      (by omega) Hlen
                    rw [sd_agree nx0 HOLES D E E' (m_fs model) HOLES_agree
                      (env_agree_le nx0 loo E E' Hag (by omega)) s hsv']
                    rw [hpc]
                    exact HJ E' R FULL model (env_agree_le bb loo E E' Hag Hbl) HC1 rfl
                  · rw [ite_eq_right ht] at H
                    cases H
      | PAbstractCell b n k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_abstractcell A cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := abstractcell_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok SINV argH FS0 E cs cs' R FULL model b n HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_abstractcell A cs b n = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := abstractcell_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok SINV argH FS0 E cs cs' R FULL model b n HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PHavocWords bs k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocwords nx0 cs bs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocwords_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model bs cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_havocwords nx0 cs bs = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨E', hag, HC1, Hpc⟩ := havocwords_sound segs A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E cs R FULL model bs cs' HC hh
                  rw [← Hpc]
                  exact CONT k cs' s H E' R FULL model hag HC1 rfl
      | PRespell r e k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_respell cs r e = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := respell_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model r e cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hh : node_respell cs r e = r0
              cases r0 with
              | none => intro H; cases H
              | some cs' =>
                  intro H
                  try dsimp only at H
                  obtain ⟨HC1, Hpc⟩ := respell_sound segs A LIMIT nx0 SINV argH FS0 E cs R FULL model r e cs' HC hh
                  rw [← Hpc]
                  exact SAME k cs' s H HC1
      | PDiamond joinpc rs k =>
        cases lc with
        | none =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hbp : branch_probe IT cs = r0
              cases r0 with
              | none => intro H; cases H
              | some e =>
                  intro H
                  try dsimp only at H
                  revert H
                  generalize hr : erange (kn cs) e = r1
                  cases r1 with
                  | none => intro H; cases H
                  | some pr =>
                      intro H
                      try dsimp only at H
                      obtain ⟨lo, hi⟩ := pr
                      by_cases hdec : (decide (hi < 1) || decide (0 < lo)) = true
                      · rw [ite_eq_left hdec] at H
                        revert H
                        generalize hrb : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A) cs = r2
                        cases r2 with
                        | none => intro H; cases H
                        | some cs1 =>
                            intro H
                            try dsimp only at H
                            by_cases hpc : (pc cs1 == joinpc) = true
                            · rw [ite_eq_left hpc] at H
                              exact run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok SEGS_wx
                                HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull nx0 bfuel
                                (joinpc :: STOPS A) cs cs1 E R FULL model _
                                (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES none D E (m_fs model) HL)
                                hrb HC (fun E' R' F' m' h1 h2 h3 h4 =>
                                  CONT k cs1 s H E' R' F' m' ⟨h1, h2⟩ h3 h4)
                            · rw [ite_eq_right hpc] at H
                              cases H
                      · rw [ite_eq_right hdec] at H
                        revert H
                        generalize hra : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A)
                          (set_kn cs (.KRange e lo 0 :: kn cs)) = r2
                        cases r2 with
                        | none => intro H; cases H
                        | some ca =>
                            intro H
                            try dsimp only at H
                            revert H
                            generalize hrb : run_block_gc segs IT nx0 KC bfuel (joinpc :: STOPS A)
                              (set_kn cs (.KRange e 1 hi :: kn cs)) = r3
                            cases r3 with
                            | none => intro H; cases H
                            | some cb =>
                                intro H
                                try dsimp only at H
                                revert H
                                generalize hj : node_diamond_join A nx0 (nxt cs) joinpc rs ca cb = r4
                                cases r4 with
                                | none => intro H; cases H
                                | some csj =>
                                    intro H
                                    try dsimp only at H
                                    obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e 0 lo hi
                                      E R FULL model HC hr
                                    obtain ⟨Ja, Jb⟩ := diamond_join_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok
                                      SINV SINV_agree argH argH_agree FS0 (nxt cs) joinpc rs ca cb csj hj
                                    by_cases hle : bv_unsigned (edenot E e) ≤ 0
                                    · rw [← pc_set_kn cs (.KRange e lo 0 :: kn cs)]
                                      refine run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok
                                        SEGS_wx HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull
                                        nx0 bfuel (joinpc :: STOPS A)
                                        (set_kn cs (.KRange e lo 0 :: kn cs)) ca E R FULL model
                                        (sd HOLES D E (m_fs model) s)
                                        (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES none D E (m_fs model) HL)
                                        hra (HCl hle) ?_
                                      intro E' R' F' m' h1 h2 h3 h4
                                      obtain ⟨E'', hag2, HC2, Hpc2⟩ := Ja E' R' F' m' h3
                                      rw [← Hpc2]
                                      exact CONT k csj s H E'' R' F' m'
                                        ⟨env_agree_trans nx0 E E' E'' h1 hag2.1, env_agree_trans (nxt cs) E E' E'' h2 hag2.2⟩ HC2 h4
                                    · rw [← pc_set_kn cs (.KRange e 1 hi :: kn cs)]
                                      refine run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok
                                        SEGS_wx HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull
                                        nx0 bfuel (joinpc :: STOPS A)
                                        (set_kn cs (.KRange e 1 hi :: kn cs)) cb E R FULL model
                                        (sd HOLES D E (m_fs model) s)
                                        (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES none D E (m_fs model) HL)
                                        hrb (HCr (by omega)) ?_
                                      intro E' R' F' m' h1 h2 h3 h4
                                      obtain ⟨E'', hag2, HC2, Hpc2⟩ := Jb E' R' F' m' h3
                                      rw [← Hpc2]
                                      exact CONT k csj s H E'' R' F' m'
                                        ⟨env_agree_trans nx0 E E' E'' h1 hag2.1, env_agree_trans (nxt cs) E E' E'' h2 hag2.2⟩ HC2 h4
        | some c =>
            unfold AsanPlan.check_go at H
            dsimp only at H
            split at H
            · cases H
            ·
              revert H
              generalize hbp : branch_probe IT cs = r0
              cases r0 with
              | none => intro H; cases H
              | some e =>
                  intro H
                  try dsimp only at H
                  revert H
                  generalize hr : erange (kn cs) e = r1
                  cases r1 with
                  | none => intro H; cases H
                  | some pr =>
                      intro H
                      try dsimp only at H
                      obtain ⟨lo, hi⟩ := pr
                      by_cases hdec : (decide (hi < 1) || decide (0 < lo)) = true
                      · rw [ite_eq_left hdec] at H
                        revert H
                        generalize hrb : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A) cs = r2
                        cases r2 with
                        | none => intro H; cases H
                        | some cs1 =>
                            intro H
                            try dsimp only at H
                            by_cases hpc : (pc cs1 == joinpc) = true
                            · rw [ite_eq_left hpc] at H
                              exact run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok SEGS_wx
                                HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull (lc_bnd c) bfuel
                                (joinpc :: STOPS A) cs cs1 E R FULL model _
                                (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL)
                                hrb HC (fun E' R' F' m' h1 h2 h3 h4 =>
                                  CONT k cs1 s H E' R' F' m' ⟨h1, h2⟩ h3 h4)
                            · rw [ite_eq_right hpc] at H
                              cases H
                      · rw [ite_eq_right hdec] at H
                        revert H
                        generalize hra : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A)
                          (set_kn cs (.KRange e lo 0 :: kn cs)) = r2
                        cases r2 with
                        | none => intro H; cases H
                        | some ca =>
                            intro H
                            try dsimp only at H
                            revert H
                            generalize hrb : run_block_gc segs IT (lc_bnd c) KC bfuel (joinpc :: STOPS A)
                              (set_kn cs (.KRange e 1 hi :: kn cs)) = r3
                            cases r3 with
                            | none => intro H; cases H
                            | some cb =>
                                intro H
                                try dsimp only at H
                                revert H
                                generalize hj : node_diamond_join A nx0 (nxt cs) joinpc rs ca cb = r4
                                cases r4 with
                                | none => intro H; cases H
                                | some csj =>
                                    intro H
                                    try dsimp only at H
                                    obtain ⟨HCl, HCr⟩ := split_sound segs A LIMIT SINV argH FS0 cs e 0 lo hi
                                      E R FULL model HC hr
                                    obtain ⟨Ja, Jb⟩ := diamond_join_sound segs A LIMIT nx0 SEGS_in_hull HULL_ok
                                      SINV SINV_agree argH argH_agree FS0 (nxt cs) joinpc rs ca cb csj hj
                                    by_cases hle : bv_unsigned (edenot E e) ≤ 0
                                    · rw [← pc_set_kn cs (.KRange e lo 0 :: kn cs)]
                                      refine run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok
                                        SEGS_wx HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull
                                        (lc_bnd c) bfuel (joinpc :: STOPS A)
                                        (set_kn cs (.KRange e lo 0 :: kn cs)) ca E R FULL model
                                        (sd HOLES D E (m_fs model) s)
                                        (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL)
                                        hra (HCl hle) ?_
                                      intro E' R' F' m' h1 h2 h3 h4
                                      obtain ⟨E'', hag2, HC2, Hpc2⟩ := Ja E' R' F' m' h3
                                      rw [← Hpc2]
                                      exact CONT k csj s H E'' R' F' m'
                                        ⟨env_agree_trans nx0 E E' E'' h1 hag2.1, env_agree_trans (nxt cs) E E' E'' h2 hag2.2⟩ HC2 h4
                                    · rw [← pc_set_kn cs (.KRange e 1 hi :: kn cs)]
                                      refine run_block_gc_sound segs IT A nx0 LIMIT SINV argH FS0 KC IT_ok
                                        SEGS_wx HULL_ok SINV_agree SINV_frame argH_agree argH_high SEGS_in_hull
                                        (lc_bnd c) bfuel (joinpc :: STOPS A)
                                        (set_kn cs (.KRange e 1 hi :: kn cs)) cb E R FULL model
                                        (sd HOLES D E (m_fs model) s)
                                        (LCOK_bnd segs A nx0 LIMIT SINV argH FS0 HOLES (some c) D E (m_fs model) HL)
                                        hrb (HCr (by omega)) ?_
                                      intro E' R' F' m' h1 h2 h3 h4
                                      obtain ⟨E'', hag2, HC2, Hpc2⟩ := Jb E' R' F' m' h3
                                      rw [← Hpc2]
                                      exact CONT k csj s H E'' R' F' m'
                                        ⟨env_agree_trans nx0 E E' E'' h1 hag2.1, env_agree_trans (nxt cs) E E' E'' h2 hag2.2⟩ HC2 h4

/-!
What follows is the measured recipe behind the block-run soundness proofs:
each entry cost a compilation round, in the order the file grew.  The two
theorems `run_block_sound` and
`run_block_gc_sound` (:2114), on top of `AxSymRun3.runTX_sound` /
`AxSymRun3.carry_after` (which rest on `AxSymExec3Sound.sym_execTX_ex` /
`AxSymExec3Sound.carry_sound`), plus the two boundary lemmas they need —
`lazy_cover_cs` (:372) and `cs_ok_frame` (:453).
**COMPLETE — HISTORICAL NOTE ONLY.**  Everything described below has LANDED:
`check_sound` itself is proved at line 12725 (all 44 plan-constructor arms), and
every node lemma listed in this narrative is in section 10.  The text is kept
because it records the dependency archaeology that made `check_sound` reachable
(`check` -> `check_go` so `check_succ` is `rfl`, then per-arm dispatch).  There
is **nothing deferred in this file**; read everything below as history.
--- (historical narrative follows) ---
ONE `[BLOCKED]` ENTRY *WAS* LEFT, and its blocker was NO LONGER a missing
*definition* — but it was NOT "just the case analysis" either.  Measured:
`check_sound`'s 45 arms call a set of node lemmas of which SIXTEEN HAVE NOW
`kn_contra_sound` (:1644), `loop_ok_facts` (:3077), `allow1_cost` (:3339),
`ghost_sound` (:3352), `respell_ok_sound` (:4024), `respell_sound` (:4047),
`havoc_sound` (:2424), `intro_sound` (:3649), `havocbrk_sound` (:3619),
`find_disj_sound` (:2230, a prerequisite of `casedisj_sound`), `casedisj_sound`
(:2270, the first of the `PCase2` family), `node_spin_sound` (:4065,
together with a adapted `self_jump_word`), `havocwords_sound` (:4003,
the `PHavocWords` arm, landed on top of `hw_apply_ok` / `hw_go_ok`), and of
the *second* layer
`shadow_of_val` (:2292), `regs_match_h_char` (:2913),
`regs_match_h_sound` (:2968) and `cs_ok_reenv` (:2980).  `shadow_of_val` came with one adapted
sibling, `shdisj_sound_of_apart` (:2316 minus its `ranges_apart_x` guard,
which this tree's `node_shdisj` never checks — see that entry).  Three
local helpers were added with them: `ediv8_add_gap` (integer division,
`allow1_cost`), `bv_eq_of_sub_mod` (`respell_ok_sound`), and the already
present `MInv_app_r` / `page_allowedb_app_l` pair (`ghost_sound`).
The node lemmas of this chain: NONE IS ABSENT ANY MORE.  `rename_sound`
(:3900) and `compact_sound` (:3916) LANDED in this pass, together with the
whole `cs_ok_rename` Section they need, so `check_sound` is the last entry of
the block.
`node_fresh_sound_pf` (:2138) LANDED two passes ago (section 10, together
with the helpers `fresh_entries_ok` and `node_fresh_step`).
`havocbig_sound` (:2504) LANDED in the latest pass (see the MEASURED note at
the end of this prose): with it every arm of `check_sound` that needs a
"re-value the knowledge" node lemma is covered, and the list above is what is
left of the node chain.
`abstractcell_sound` (:3926) LANDED in this pass too — its proof is 10 lines
on top of `kunk_covered_sound` + `cs_ok_set_kn` + `know_ok_cutout`, which is
exactly what the cover chain was for: `node_abstractcell` elaborates the
`let (bb, bo) := split_lit b` into the PROJECTIONS `(split_lit b).fst` /
`(split_lit b).snd` (do NOT `obtain ⟨bb,bo⟩ := split_lit b` — that only
introduces unrelated locals), so pass those to `know_ok_cutout`, whose Lean
argument order is `(b : expr) (n : expr) (o : Int)` — note the LAST two are
swapped relative to `kn_cutout`'s own `ub uk un`.
`entails_h_sound` (:3011) and `diamond_join_sound` (:3055) LANDED in this
pass — the latter is the second node lemma of the file after
`havocwords_sound` (:4003), and it completes the `PDiamond` arm of
`check_sound` (the `PVia` arms use `entails_h_sound` through the same
`node_diamond_join`-shaped join).  With the cover chain they rest on
(`cover1_sound` -> `cover_x_sound` -> `kunk_covered_sound` ->
`kn_incl_h_sound`, all landed with them) the only `[TODO]` entries left in
this corner are the four above —
`kn_bigsubst_sound` (:2477), `rdn_visible` (:919), `know_ok_unhide` (:943)
and `maps_match_remove` (:1184) have landed since, and `vis_add_sound`
(:1245) LANDED in the latest pass (see the on it in section 10:
it is now UNCONDITIONAL — the shadow's `flat_x` is the fourth of the nine
conjuncts of `vis_add_ref`'s guard, which this tree checks as `node_unvis_ref`
already did).
Those in turn need a second layer of which `shadow_of_val` (:2292),
`regs_match_h_char` (:2913), `regs_match_h_sound` (:2968),
`cs_ok_reenv` (:2980), `shdisj_sound` (:2316) and — as of this pass —
`kn_bigsubst_sound` (:2477) have LANDED (in section 10); the `[TODO]`
entries of this corner are GONE — the `cs_ok_rename` Section that
`rename_sound` (:3900) / `compact_sound` (:3916) need LANDED in this pass
(section 10) — and `vis_add_sound` (:1245) has LANDED
(section 10; UNCONDITIONAL since the guard gained the shadow's `flat_x`
conjunct, see its Note that
`abstractcell_sound` (:3926) has LANDED and no longer appears below, and for
it nothing was needed but the (now landed)
`cover1` / `cover_x` / `kunk_covered` chain
(`seg_rom_off_hull`, `flat_x_sound`, `henv_havoc`, `kzero_x_sound0`,
`split_lit_denot`, `u_of_split`, `disj_side_fact_sound`,
`casedisj_sound`, `self_jump_word` and `node_spin_sound` have LANDED in
section 10).  `self_jump_word` (:4060) needed RESTATING, because this tree's
`node_spin` tests `bv_unsigned w == SPIN_WORD` instead of calling
`is_self_jump`: this tree lemma takes those two facts as hypotheses
(`ms_svc_pending ms = none`, `fetch_word segs (ms_pc ms) = some (Z_to_bv 32
SPIN_WORD)`) and concludes `DivergeSim.is_self_jump segs ms = true` by
`unfold` + `rw` + `decide` (`is_self_jump` lives in `DivergeSim`, so it must
be namespace-qualified here).  `node_spin_sound` is then 15 lines:
`unfold node_spin`, `Bool.and_eq_true` twice, case the `fetch_word`,
`bv_unsigned w = SPIN_WORD → w = Z_to_bv 32 SPIN_WORD` by
`BitVec.eq_of_toNat_eq` + `decide`, and finish with
`srealizes.srz_spin _ (DivergeSim.is_self_jump_to_spin …) HC.co_halt` —
note `srz_spin`'s argument order is `(c) (hspin) (hh)`, and `mkst` makes
`ms_svc_pending = none` and `ms_pc = Z_to_bv 64 (pc cs)` both `rfl`.
So the truthful dependency order for what is left is: those node lemmas
first , then `check_sound`, whose own text is then the
mechanical 45-arm case analysis described below.  Everything `check_sound`
needs that is NOT in the list above has landed: `entails_h_sound` (:3011) /
`diamond_join_sound` (:3055) (the `PDiamond` and `PVia` join engine),
`kn_incl_h_sound` / `kunk_covered_sound` / `cover_x_sound` / `cover1_sound`
(the knowledge-entailment cover chain), `run_block_gc_sound`,
`LCOK_bnd` / `LCOK_agree` / `LCOK_agree_gb`, `check_vars`, `cont_agree`,
`split_sound`, `fact_sound`, `forget_sound`, `droprange_sound`,
`bump_sound`, `fog_sound` / `fognew_sound`, `entails_sound`,
`cs_ok_set_kn`, `cs_ok_inst`, `fresh_ok_parts`, `sd_agree` / `sd_has_nil` /
`sd_salt2`, the `t_eq_*` / `srz_conseq` trace-set algebra, and the Section
HYPOTHESES (`sys_stmt`, `mm2_stmt`, `mm3_stmt`, `brk2_stmt`, `x_stmt`,
`ext_stmt`, `ext2_stmt`, `emit_stmt`, `holes_stmt`, `join_stmt`,
`exit_stmt`, `fresh_stmt`), which `check_sound` takes as parameters.
It is worth stating plainly because it is
the opposite of what one would guess from the file's size: the per-node
obligations of part 7 (`sys_stmt`, `mm2_stmt`, `mm3_stmt`, `x_stmt`,
`ext_stmt`, `emit_stmt`, `holes_stmt`, ...) are Section HYPOTHESES here — the
"OBLIGATIONS (work packages)" block, discharged per node family in the
`AsanNodes*` files, not in this one — and part 7's "nodes proved here"
(`split_sound`, `estart_SA`, `xlo1_sound`, `deand_sound`, `fact_sound`,
`reg_sound`, `fresh_ok_parts`, `entails_sound`, ...) are boundary nodes that
never run the executor.  So no `[TODO]` entry below is missing a *definition*
or an * statement*: every one of them is missing a LEMMA it calls
(they are long `symexec`-tactic or case-analysis proofs).  The difference
matters for planning: a missing lemma is a scheduling constraint on the
entries that call it, not just an amount of work — see the `check_sound`
blocker list above.
Suggestions for the next pass, in dependency order: the part-7 node
soundness lemmas listed above (`kn_contra_sound`, `shdisj_sound`,
`casedisj_sound`, ...), cheapest first, then `check_sound` (:4135).  Note the
order is forced: `check_sound`'s arms call those lemmas, so it is the LAST
entry of that chain, not the next one.  The per-node obligations of part 7
(`sys_stmt`, `mm2_stmt`, ...) are NOT part of that chain — they are Section
hypotheses here, discharged per node family in the `AsanNodes*` files.
MEASURED while landing the `PCase2` / `PShDisj` prerequisites (each of these
was a real dead end first; they save the next pass the search):
  * `split_lit_denot` (:1033) needs NO case analysis: `to_saddr_denot E e 0`
    (already in `AxSymExec3Sound`) becomes the statement after
    `simp only [to_saddr, H, Int.add_zero]`, `adenot E (SA b k)` is defeq to
    the right-hand side, and `Z_to_bv_unsigned` finishes.  `u_of_split` is
    then `u_lit64a` + `Int.emod_eq_of_lt`, and `shadow_of_val` can use the
    same shortcut.
  * `flat_x_sound` (:1050) — listed above as "harder", actually 12 lines:
    `unfold flat_x at H; split at H`, then `base_range_sound` / `xlo_sound` /
    `xhi_sound`, then `dsimp only [estart] at *; omega`.
  * `disj_side_fact_sound` (:2244): normalise
    `bv_unsigned (edenot E (esub (eaddz cB oB) (eaddz cA oA)))` with
    `mkAlu_denot`, `u_sub64`, `u_add64`, `u_lit64`.  `u_lit64` produces
    `two64`, not `2 ^ 64`, so a `simp only [two64]` is needed before the
    `show`s; the two mod-eliminations are `emod_add_mod` (after
    `Int.add_comm`) plus `Int.emod_eq_of_lt`.
  * `node_casedisj`'s body starts with `have k := kn cs` (a zeta-let), which
    makes plain `unfold node_casedisj at H; split at H` FAIL with "Could not
    split an `if` or `match` expression".  `dsimp only at H` first
    substitutes the let, and the two `split at H`s then work
    (each `split` on the 4-way `match` needs its own `rename_i`).
  * `estart` and `elenZ` are DEFS: `omega` sees `elenZ E n` and
    `bv_unsigned (edenot E n)` as unrelated atoms.  Unfold them
    (`dsimp only [estart, elenZ] at *`) before every `omega`, and state
    helper `have`s in the unfolded form — a `by omega` that creates a NEW
    subgoal does not inherit a `dsimp … at ⊢` done on the outer goal.
  * for a list induction whose hypotheses mention the list (e.g.
    `Hlen : rs.length = ts.length`), `revert` + `induction` gives an
    induction hypothesis with a DIFFERENT number of binders than the goal
    (`intro` fails or the argument order shifts).  `induction rs
    generalizing ts i v` leaves the hypotheses in context — do not `intro`
    them again.
  * environment note: a scratch file under `/tmp` that `import`s this module
    sees the STALE `.olean` from the last `lake build`, so lemmas added to
    the source afterwards are "unknown identifier" there.  Iterate by
    editing this file and re-running `lake env lean` on it (~4 s).
  * `ends` matter: a `match ... with ... | _ => false` that is NOT
    parenthesised swallows a following `&&` into its last branch.  This is
    not cosmetic — it silently dropped `ranges_apart_x` from
    `AsanPlanCore.node_shdisj` (see the `shdisj_sound` entry).  When a node's
    guard has a `match` in the middle, `#print` the definition under
    `pp.all` before planning its soundness proof; `node_casedisj`'s
    `match flat_x ..., disj_side_fact ... with` is the shape that works
    (there the `match` IS the last conjunct).
  * `shadow_of_val` (:2292): `unfold shadow_of at Hs; split at Hs` gives the
    pair components as `sb' sk'` + an equation; do NOT `cases Hs` (it
    reverts the very variables you need) — `obtain` the three equations via
    `simpa only [Prod.mk.injEq] using Hs` and `subst` them, which LEAVES the
    `sb'`/`sk'` names in place (the goal keeps them, so write the rest of the
    proof in those names).  `mkSrl_denot` + `u_srl64` at `Z_to_bv 64 3`
    (`(bv_unsigned (Z_to_bv 64 3) % 64).toNat = 3` by `decide`, then
    `2 ^ 3 = 8` by `decide`) give the `/8` form; there is no `norm_num`.
  * a binder named `hi` SHADOWS the section parameter `hi : Nat` in these
    `is_havoc lo hi` lemmas: inside `fun i hi => ...` every later
    `is_havoc lo hi t` silently becomes `is_havoc lo hi✝ t`, and the error
    surfaces as "application type mismatch ... expected Nat" far away.
    Name the index bound `hilen`.
  * `cs_ok_reenv` (:2980) is `cs_ok_agree`'s proof with `set_regs cs sr'` in
    place of `cs`: every projection the record mentions is UNCHANGED by
    `set_regs` except the registers, so `hid_ext … rfl`,
    `allowA … (rfl : allowA A E' (set_regs cs sr') = allowA A E' cs)` and
    `rfl` for `co_log` do the whole bookkeeping.  Use a NAMED-field record
    literal with 11 `?_` (the 27-field positional `⟨…⟩` refused to
    elaborate: "don't know how to synthesize placeholder for argument
    co_sinv"); `cs_ok_frame` (:453) is the template.
  * `Int.mul_ediv_cancel_left` is `8 * q / 8 = q` with the FIRST explicit
    argument being `q` (the divisor is implicit): after `rw [hq]` with
    `hq : u = 8 * q` the goal is already in that shape, so no
    `Int.mul_comm` is needed.
`check_vars` (:3126) HAS LANDED (in section 10, on top of `check_all_ok` and
`check_zero_lc`): a plain induction on `fuel`, then one case analysis per plan
constructor, one per `lc` shape — 45 × 2 arms.  It needed the `AsanPlan.check`
refactor described next, which is now in `AsanPlan.lean`.
WHY THE REFACTOR WAS NECESSARY (measured, kept because `cont_agree` and
`check_sound` consume the same unfolding).  Before it, `AsanPlan.check` was
compiled with `Nat.brecOn`, not `Nat.rec`: its recursive call sat inside the
`let ck : Option loopctx -> acs -> plan -> cres := check segs ... f` of the
successor branch, so Lean's structural-recursion elaboration did not see it
and fell back to course-of-values recursion (`#print AsanPlan.check` showed
`Nat.brecOn ... (AsanPlan.check._f ...)`).  Consequences, all measured in
this tree at the time:
  * `check.eq_1` / `check.eq_2` were unusable: even `#check @check.eq_1`
    timed out (`deterministic timeout at whnf`, 200000 heartbeats), because
    `whnf` chases the `Nat.below` tower.  `rw [check.eq_2]`, `simp only
    [check]` and `unfold check` at a hypothesis were all unavailable.
  * Stating the whole 45-branch successor body once (one equation lemma, or
    one `change` of the full body) did not work either: the `rfl` / defeq
    check ran away (still unfinished after 10 minutes with the heartbeat
    limit disabled), because each `if` in the body elaborates its `Bool`
    `Decidable` instance differently from the one `check` was compiled with,
    so `isDefEq` tried to prove the instance terms equal.
  * What did work, per plan constructor, cheaply: `cases lc` first (`none` /
    `some c` — this also makes the leading `lc_bnd` guard reduce), then
    `cases p`, then one `change ((<the branch, copied verbatim from
    `AsanPlan.check`, with `ck` replaced by the recursive call at `nf`, `gcb`
    by `nx0` / `(lc_bnd c)` and `lc` by `none` / `(some c)>) : cres) = cres.COk s
    at h`.  The `(... : cres)` ascription is required, otherwise `.COk` /
    `.CErr` are ambiguous.  `split at h` then walks the branch; branches come
    out in source order (`some` before `none`, `true` before `false`), and a
    `| err => err` arm needs `rename_i err heq; rw [← heq] at h` before the
    induction hypothesis applies (that arm really can return `COk s`).
  * The clean fix, now IN `AsanPlan.lean`: give `AsanPlan.check` the
    recursive call as a parameter, exactly as `AxSymExec3.sym_execTX_go`
    does (a separate `check_go` taking `ck : Option loopctx -> acs -> plan ->
    cres`), so that one `rfl` equation `check ... (n+1) = check_go ... (check
    ... n)` unfolds it — that is `AsanPlan.check_succ`.  `check_vars` is then
    a plain induction, and `cont_agree` / `check_sound` follow.
MEASURED while proving `check_vars` (the 45-arm skeleton this block used to
describe as "compiling but stuck at 15 errors" is now a proof in section 10;
the eight causes behind those 15 errors are recorded here because
`cont_agree` and `check_sound` hit the same shapes).  The refactor gives a
usable unfolding, but only through `check_succ`, and several obvious tactics
that surround it time out or fail; the ones below were each timed out or
traced in this tree, so they save the next pass the search:
  * `rw [check_succ]` / `check_succ … ` used *in the goal* is instant and
    cheap; the same rewrite *at a hypothesis* (`rw [h] at H'`, `Eq.mp`-style
    transport included) times out at `whnf` (200k heartbeats) as soon as the
    plan argument is a concrete constructor.  Workaround that works: build
    `have hstep := AsanPlan.check_succ … f lc cs p` and
    `have H' := hstep.symm.trans H` **before** `cases p`, while `p` is still a
    variable (`Eq.trans` on two syntactically equal applications needs no
    `whnf`); `cases p` then specialises `H'` for free.
  * `simp only [AsanPlan.check_go] at H'` times out for the `PRun` / `PDiamond`
    arms (it normalises the whole 45-arm body, unfolding `run_block_gc`,
    `node_rename`, …).  `unfold AsanPlan.check_go at H'` followed by
    `dsimp only at H'` is the cheap replacement: it yields the body with the
    `let gcb`, the `lc_bnd` guard and the `match p` already reduced.  The
    `check_go.eq_*` equation lemmas are unusable — even `#check
    @AsanPlan.check_go.eq_1` times out.
  * the `lc_bnd` guard: `cases lc` first (both cases keep the same arm code),
    then `split at H'` kills the `.CErr 9` branch and leaves the body.  After
    that, `split at H'` on a *nested* `if` whose condition is a `Prop`-valued
    `bool = true` leaves a `Decidable.rec` in `H'`, which then blocks every
    later `cases`/`generalize`.  `by_cases hc : <cond>` + `rw [ite_eq_left hc]` /
    `rw [ite_eq_right hc] at H'` is clean, BUT the conditions must be spelled the way
    the elaborator built them: `(decide (lo ≤ mid) && decide (mid < hi)) = true`,
    `hi ≤ mid` (a bare `Prop`), `is_ecall_at segs cs = true`, …; the pretty
    printer's `lo ≤ mid ∧ mid < hi` is *not* the term.
  * `split at H'` on a `match f x with | some (a, b) => …` destructures the
    *components* too — `some (lo, hi)` with `hi : Int` becomes `Int.ofNat` /
    `Int.negSucc` goals with renamed pieces.  For every `Option` match use
    instead `revert H'` → `generalize hh : <the scrutinee> = r` → `cases r` →
    `intro H'` (+ `try dsimp only at H'` when the pattern was `some p` and
    `obtain ⟨…⟩ := p` was used).  Doing `cases` on the *goal* (after `revert`)
    is what makes the dependent elimination go through; `cases h : e` and
    `generalize … at H'` + `cases` both fail with “Dependent elimination
    failed” as soon as `e` occurs inside a `match` in a hypothesis.
  * `split at H'` on a `match ck … with | COk s => … | err => err`: `err` is a
    *variable* pattern, so the generated branch offers no equation; the useful
    equation (`ck … = .COk s`) does come out of `split`, but under an
    inaccessible name, so `rename_i s h` right after the split is required.
    For `| err => err` arms the split branch is unusable on its own (the
    scrutinee stays abstract) — the `revert`/`generalize`/`cases` recipe above
    is the one that works, because `cases` on `cres` gives the `CErr` arm a
    contradictory `H'` that `cases H'` closes.
  * `cases H'` is the contradiction closer: `simp at H'` reports “made no
    progress” on `.CErr … = .COk …` (simp has no discrimination lemma for
    `cres`).  For a *positive* shape, `cases H'` on `.COk X = .COk s`
    substitutes `s := X` in one step, which is what the `SCase` / `SEmitP` /
    `salt2` leaves want.
  * leaf shapes, once `H'` is `.COk <shape> = .COk s` and `s` is substituted:
    `simp only [shape_vars_lt]` then `rw [hv, IH … h1, IH … h2]` for `SCase`;
    `salt2_vars nx0 _ _ (IH …) (IH …)` for the `salt2` arms (the first three
    arguments are explicit, so the `nx0` cannot be left as `_`); for the
    `PMmapIn` / `PMmapInH` destroyed children `check_all_ok` supplies the
    third equation (`obtain ⟨⟨cs1, hin, hck⟩, -⟩ := check_all_ok A … h3`).
  * in this toolchain `expr_vars_lt` and friends are ambiguous between
    `AsanPlanCore.*` and `AxSymRun3.*` inside generated terms — qualify them.
WHAT THE LAST EIGHT FAILURES OF `check_vars` TURNED OUT TO BE (each measured;
they are the ones a reader re-deriving `cont_agree` will meet again):
  * `by_cases h : a == b = true` DOES NOT PARSE with this toolchain's parser:
    it stops at the `=`, and reports `unexpected token '='; expected command`
    on the *next* line, which misleads (it made eight of the fifteen errors
    look like proof failures).  Parenthesise: `by_cases h : (a == b) = true`.
  * `PDiamond`'s body is `match branch_probe IT cs with | some e => …` with
    `e : expr`: take it with `| some e =>`.  Destructuring a `some p` and then
    re-wrapping (`obtain ⟨e⟩ := p` gives an `Int` field, not the `expr`) makes
    the `erange (kn cs) e` `generalize` ill-typed.
  * `PCaseDisj` / `PCase2`: after the two `generalize`+`cases` of the children,
    `H'` can still carry the outer `match (cres.COk s1) with …`, and then
    `rw [ite_eq_left hc] at H'` finds nothing.  `dsimp only at H'` right after the
    last `intro H'` reduces it.
  * `PCase2` / `PCase2H`: the `if shape_eqb s1 s2` can come out of the
    dependent elimination already unfolded to
    `Decidable.rec … (instDecidableEqBool (shape_eqb s1 s2) true)`, which
    `cases H'` cannot discharge (“Dependent elimination failed”), and
    `revert H'` + `generalize hb : shape_eqb s1 s2 = t` + `cases t` does NOT
    reach the occurrence inside the `Decidable` instance argument.  What works:
    `dsimp only at H'`, then `by_cases hb : shape_eqb s1 s2 = true`; in the
    positive case `rw [hb] at H'` makes the instance closed (`instDecidableEqBool
    true true`), so `cases H'` whnf-reduces the whole `Decidable.rec` and
    leaves `s = s1`; in the negative case `have hbf : shape_eqb s1 s2 = false
    := by simpa using hb` and `rw [hbf] at H'` closes it.
  * `PVia`: `split at H'` on `match ck lc js k with | .COk sk => … | err =>
    err` leaves a second branch whose `H'` is a bare application (`COk s =
    check … cs kc`), on which `cases H'` fails.  Drop the `split`: after
    `revert H'` + `generalize h1 : check … = r` + `cases r`, the `COk` branch
    *is* the recursive call, so the induction hypothesis applies directly.
  * `PMerge`: `simp only [Bool.and_eq_true]` on a four-way `&&` gives a
    LEFT-nested conjunction, so the third conjunct is not `hg1.2.2.1`; use
    `have hsv := hg1; simp only [Bool.and_eq_true, and_assoc] at hsv;
    exact hsv.2.2.1`.
  * a `cases c with | LC … => intro H'` whose body starts on the SAME line as
    `=>` puts the rest of that arm at the wrong layout column: the following
    `try …` is then parsed as a new command.  Put `intro H'` on its own line.
  * `dsimp only` does NOT reduce `if !(…)`: `Bool.not` is not iota-reduced, so
    for `lc = none` the guard is still an `if` and the `split at H'` →
    `· cases H'` / `· <body>` frame is needed for BOTH `lc` cases; only the
    `gcb` occurrence differs (`nx0` versus `lc_bnd c`).
THE SHAPE OF THE `check_vars` PROOF ITSELF (a template for `cont_agree`):
`intro bfuel fuel; induction fuel`, base case from `check_zero_lc`, and at
`fuel + 1` build `have hstep := AsanPlan.check_succ … f lc cs p` and `have
H' := hstep.symm.trans H` BEFORE `cases p`; then `cases lc` and `cases p` and
one `unfold AsanPlan.check_go at H'` + `dsimp only at H'` + `split at H'` per
arm.  The ~35 leaf and single-recursion arms all end in
`first | exact IH _ _ _ _ H' | exact IH _ _ _ _ H'.symm`, which absorbs not
knowing the orientation of `H'` after the `dsimp`.
MEASURED while landing `kentry_eqb_h_sound` (:2713), the `PHavocWords` chain
`hw_apply_ok` (:3954) / `hw_go_ok` (:3991) / `havocwords_sound` (:4003) and
`rdn_bytes_some` (:2762) — each of these cost a compilation round:
  * `Bool`'s constructor order is `false`, `true`, so `cases h : e with` on a
    `Bool` and then a bullet list puts the `false` case FIRST (the opposite of
    what a `by_cases`-driven proof suggests).  Spell the two cases out as
    `cases h : e with | true => … | false => …`.
  * `upd` takes a **word**: `∀ e : word, kentry_ok segs (upd E x e) M X`.
  * `kentry`'s constructors are not in scope unqualified inside TERMS (only in
    `cases … with` patterns): write `kentry.KWord a w (.EVar x)`.
  * `List.not_mem_nil` is implicit-argument here (``List.not_mem_nil K hK``
    is a type error); close `K ∈ []` with `cases hK`.
  * `edenot E (.ELit o)` does NOT unify with `Z_to_bv 64 o` for `simpa`/
    `exact`: apply `u_lit64` after `show bv_unsigned (Z_to_bv 64 o) = o % 2^64`.
  * `alu64 .ADD` is NOT definitionally `+`: after `rw [mkAlu_denot]` the term
    is `alu64 AluOp.ADD`, on which `u_add64` does not fire; first
    `rw [SymExec.alu64_add_eq]` (`SymExec.` qualifies even though the file
    does not `open` it).
  * `saddr_eqb_h`'s second disjunct is about `eaddz x.a_base x.a_off`, and
    after `obtain ⟨b,o⟩ := a` the terms keep `(SA b o).a_base` projections
    that break the later `%`-rewrites: destructure the saddrs INSIDE the
    helper lemma (state it over `saddr`, `intro`, then `obtain`).
  * `omega` atomises `bv_unsigned x` and `↑(x.toNat)` as DIFFERENT atoms, so
    `u64_range x` cannot bound a `bv_unsigned`-form goal; go through Nat
    instead (`have := x.isLt; omega`, then `exact_mod_cast` to reach the Int
    form `u_add1` wants).  `BitVec.toNat_add_one` is not a global name here.
  * after `simp only [Bool.and_eq_true]`-less simplification a
    `… ∧ … = true` goal is still ONE equality and `⟨h1, h2⟩` reports the
    confusing "Constructor `Eq.refl` does not have explicit fields, but 2
    were provided" — add `Bool.and_eq_true` to the simp set first.
  * `Mr A argH E' (bump cs d) model FULL = Mr A argH E' cs model FULL` **is
    `rfl`** (`hid`/`vis`/`allowA` never read `s_next`), so `cs_ok` transports
    across `bump` with a named-field literal whose only changed field is
    `co_know` (`co_log := rfl`, because `mk_ss` clears the log).  For
    `cs_ok_set_kn` at a bumped state keep TWO hypotheses: `HKb` (the bumped
    state's own `co_know`, about the OLD `kn`) for the record, and `HK''`
    (about `hw_go …`) for `cs_ok_set_kn`; the valuation swap
    `Mr A argH E' … = Mr A argH E …` is exactly `hid_agree` + `argH_agree`.
  * `rdn_bytes_some` must quantify `bs` AFTER the `revert a` (state it as
    `∀ a w bs, rdn … = some bs → …`) or the induction hypothesis is stuck at
    the original `bs` and cannot be applied to the `some rest` of the tail.
  * `push_cast at hh` is the portable replacement for the missing
    `Nat.cast_zero` / `Nat.cast_add` names; `Int.add_right_comm` and
    `Int.add_assoc` do exist (left-assoc vs right-assoc matters).
MEASURED while landing the COVER CHAIN (`cover1_sound` :2779,
`cover_x_sound` :2822, `kunk_covered_sound` :2837, `kn_incl_h_sound` :2858,
`entails_h_sound` :3011, `diamond_join_sound` :3055) — every one of these
cost at least one compilation round:
  * `cover1` is compiled with `List.brecOn` (`#print cover1` shows
    `fun k b i => List.brecOn k (cover1._f b i)`), yet `simp only [cover1]
    at H` is FINE: the equation lemma unfolds one step and zeta-reduces the
    `let hit`, giving the decision tree INLINE (`match K with | KWord
    {a_base:=kb,a_off:=kk} w v => if … | KZero … (ELit l) => … | KFill … |
    KBlob … | KUnk … | x => none`).  So the old `check`-style problem does
    not recur here.
  * then `split at H` (the OUTER match, whose scrutinee is that tree) gives
    2 goals: inaccessibles `(Option Int) (Int) (hit = some e1)` with
    `H : some e1 = some e`, resp. `(Option Int) (hit = none)` with
    `H : cover1 rest b i = some e`.
  * then `split at heq` where `heq : (match K with …) = some e1` cases on K
    directly and resolves the inner `(ELit l)` sub-match itself.  SIX
    branches, in COMPILED order: KWord, KZero, KFill, KBlob, KUnk,
    catch-all.  Number of NEW inaccessible names to `rename_i` (the named
    `heq` is not renamed): KWord 5 (`Kx kb kk w v`), KZero 4 (`Kx kb kk l`),
    KFill 5, KBlob 5, KUnk 4, catch-all 6 (`Kx` + the five
    pattern-impossible hypotheses).  In each branch `HK` has been moved INTO
    the goal (it mentions K), so `intro HK` is required per branch; the
    catch-all's `heq : none = some e1` closes with `cases heq`, and the
    outer NONE branch needs `intro HK` too (its `split` also generalises HK).
  * `split at heq` on the residual `if` gives `isTrue: hg : (expr_eqb b kb
    && decide (0 ≤ l) && decide (l < two64) && decide (kk ≤ i) && decide (i <
    kk + l)) = true` plus `heq : some (kk+l) = some e1`, and `isFalse:
    ¬(that) = true` plus `heq : none = some e1`.  Bool `if`s elaborate as
    `ite (c = true)`, so this is the spelling to use if a `by_cases` route
    is preferred.
  * `subst h` with `h : b = kb` eliminates **kb**, not `b` (`subst` kills
    the RIGHT-hand variable).  When the goal must keep mentioning `kb`, use
    `rw [hbk] at ⊢` instead.
  * `exact HK _ (by simp)` for `kentry_ok segs E M ?K` does NOT work when
    ?K is still undetermined and the expected type is a conjunction:
    `kentry_ok` is a `match`, so it cannot reduce and the membership goal is
    left with an unsolved `?m`.  Spell the entry:
    `HK (kentry.KZero (SA kb kk) (.ELit l)) (by simp)`.
  * `u_small` has an IMPLICIT `{z : Int}`: write
    `u_small (z := …) ⟨h1, h2⟩`, otherwise `⟨h1, h2⟩` is checked at `Int`
    and fails with "the expected type `Int` has more than one constructor".
  * `rdn_bytes_some` wants `in_hull A (bv_unsigned (Z_to_bv 64 z)) = false`,
    not `in_hull A z = false`: build `hh' := by rw [hxs]; exact hh` from
    `hxs : bv_unsigned (Z_to_bv 64 z) = z`.
  * `zpow` is a DEF (`zpow a k = a ^ k.toNat`), so `omega` cannot bound it:
    pass `have h1 : zpow 2 40 < (2 : Int) ^ 64 := by decide` and let `omega`
    use that.  `KHI < 2^64` is also `by decide`.
  * `elenZ_lit E (A.img_hi - A.img_lo) …` needs `img_hi ≤ KHI < 2^64`, so
    `kunk_covered_sound` really does need `HULL_ok : hull_ok A` — but only
    for that one rewrite (the apartness itself comes from `off_image_x`).
    Materialise `HULL_ok.1` and `HULL_ok.2.2.2` as `have`s first: `omega`
    cannot see through the `hull_ok` def.
  * `omega` does NOT use projection applications such as `HC.co_totsz`; make
    them local (`have HCtotsz := HC.co_totsz`, `HCeager`, `HCabytes`) before
    any `omega` in a `cs_ok` record rebuild.  This was the only cause of the
    four `entails_h_sound` omega failures.
  * `holes_mono`'s first Int argument is the ORIGINAL (larger) bound:
    `holes_mono E cs.a_ylo T.a_ylo … Hylo`.
  * `entails_h_sound`'s `co_zero` field needs the `hid` swap through
    `hid_ext` (the goal is `hid … cs … = true`, the hypothesis
    `hid … Tc … = true`) and the `in_ghost` swap through
    `have hgE : in_ghost E Tc = in_ghost E cs := by unfold in_ghost; rw
    [Eghost]`; everything else in the record goes through `rfl` (`co_log`),
    `show`-rewrites (`co_totsz` / `co_eager` / `co_abytes`) or `holes_mono`,
    exactly as in `cs_ok_reenv` (:2980), which is the template.
  * `T = set_regs (set_regs T cs.a_ss.s_regs) T.a_ss.s_regs` needs the log
    and reservation facts: `obtain ⟨⟨p, sr, lg, k, nx, rv⟩, m,t,y,eg,v,g,ab,
    br,f,ti⟩ := T`, then `dsimp only at Hlog' Hresv' ⊢` (this iota-reduces the
    projections to `lg` / `rv` so `subst` can fire), then `subst Hlog';
    subst Hresv'; rfl`.  The companion `set_regs (set_regs T rs) ts =
    set_regs T ts` is `rfl`.
  * `pairs_vars_lt b (l1 ++ l2)`: unfold it in the HYPOTHESES too
    (`have h1 : pairs_vars_lt lo T.a_vis = true := Hvisv`, then
    `simp only [pairs_vars_lt, List.all_append] at h1 h2 ⊢`, then
    `rw [h1, h2]; rfl`); a folded `pairs_vars_lt` in a hypothesis will not
    `rw` against the unfolded goal.
  * `node_diamond_join`: `unfold node_diamond_join at H; dsimp only at H`
    zeta-expands the four `let`s (that is wanted — `v0` must be visible as
    `max nx (max (nxt ca) (nxt cb))` for `env_agree_le`), `split at H` gives
    the guard, `simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    at hg` peels 7 conjuncts as
    `⟨⟨⟨⟨⟨⟨hpa,hpb⟩,hvlt⟩,hlen⟩,hn0⟩,hea⟩,heb⟩`, and
    `simp only [Option.some.injEq] at H; subst H` eliminates `csj`.  The
    statement MUST be parenthesised
    `∃ E', (env_agree nx0 E E' ∧ env_agree nx E E') ∧ cs_ok … ∧ pc csj = …`
    (unparenthesised it parses right-nested and `⟨⟨hA,hB⟩, hC, hD⟩` then
    tries to use `hA` as the `∀ n` component of the unfolded `env_agree`).
  * both `entails_h_sound` calls in `diamond_join_sound` can leave ALL of
    `lo`, `hi` and the template as `_` — they are inferred from the guard's
    `entails_h` hypothesis — and `hlen` / `hn0` unify up to defeq
    (`T.a_ss.s_regs` is `sr_fresh …`; `v0` is `max nx (max …)`), so no
    `show` is needed for them.  `pc csj = pc ca` then follows from
    `entails_h_sound`'s own `pc T = pc cs` (no need for the guard's
    `pc ca == joinpc`).
  * a note on the arms whose template is NOT `KWord` and NOT a literal
    length: `kn_incl1_h`'s compiled tree puts `kflat_h` and
    `k.any (kentry_eqb_h …)` in ONE branch, so its `isFalse.isFalse.isTrue`
    arm carries `HK1 : (if false = true then true else …) = true` — clear it
    with `rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at HK1` before
    the `kimg_sub_covered` / `kunk_covered` split.
MEASURED while landing `kn_bigsubst_sound` (:2477) — the last missing link
under `havocbig_sound` (:2504):
  * `kn_bigsubst` / `kn_bigexprs` are non-structural in the list (they carry
    an `if bigb K v`, so the head is NOT kept when `bigb` fires), which makes
    the head case analysis unavoidable: `cases x` and then, for the nine
    shapes whose head is kept, the whole obligation is
    `know_ok segs E2 M (y :: (kn_bigsubst K r nx).1)` — factor it once as a
    local `TAIL : ∀ y r', know_ok … r' → kentry_ok … y → know_ok … (y :: r')`
    (`rw [List.mem_cons]` + `rcases`, then `Hx` / the IH) so each of the nine
    arms is 2 lines.
  * the `if (bigb K v) = true` in those definitions does NOT reduce under
    `simp only [name, h]`: add **`ite_true`** (`h : b = true`) resp.
    **`ite_false`** (after turning `¬(b = true)` into `b = false` by a
    `cases hh : bigb K v` two-liner, plus `Bool.false_eq_true`) to the simp
    set.  `ite_true`/`ite_false` are the right names here and they do exist.
  * the list identity `kn_bigexprs K (KWord a w v :: r) = v :: kn_bigexprs K r`
    (resp. `= kn_bigexprs K r` when `bigb` is false) must be produced
    EXPLICITLY (`have hge := by simp only [kn_bigexprs, hb, ite_true]`): the
    `if` blocks definitional reduction, so neither `getD (i+1)` nor the
    length/index of `Hvals` transports by defeq.  Rewrite `hge` into the
    hypothesis from `Hvals` (`rw [hge] at h`) and into the index bound
    (`by rw [hge]; exact hi`) — after that `simpa` handles
    `List.getD_cons_succ`.
  * `edenot E2 (.EVar nx)` is `E2.ev nx` by rfl, so do NOT `simpa` the two:
    state `show E2.ev nx = edenot E2 v` and apply the `nx + 0` form with
    `rwa [Nat.add_zero] at h1`.
  * a `have` in a `cases x with` arm that ALSO occurs in another theorem
    earlier in the file (here `kn_bigsubst_len` has the same `| KWord a w v =>
    by_cases hb : bigb K v = true` shape) makes a naive text edit with a
    line-range anchor hit the WRONG theorem — scope such edits by first
    `index`-ing the enclosing `theorem` name.
MEASURED while landing `havocbig_sound` (:2504) — the recipe below generalises
to every node whose body is a chain of `Option` matches (`node_rename`,
`node_compact`, `node_unvis` are all of that shape):
  * `unfold node_havocbig at H` + `dsimp only at H` gives the body with the
    two `let`s zeta-reduced, and the `let (k', c) := kn_bigsubst …` comes out
    as `(kn_bigsubst …).fst` / `.snd` (like `split_lit`; the printed
    `#print node_havocbig` shows the `match`, the elaborated H shows the
    projections — both are the same term).
  * `cases hh : node_havoc … = …` / `split at H` both FAIL here (“Dependent
    elimination failed”, resp. it destructures the `Prod` into `Nat` cases).
    What works, per node, is exactly the documented triple
    `revert H` → `generalize hh : <scrutinee> = r0` → `cases r0` → `intro H`,
    and it is needed TWICE (once for `node_havoc`, once for the `kn_bigsubst`
    pair; the second `generalize` can be written before the `cases` because
    its scrutinee no longer occurs in the *goal*).
  * after each `cases`, `dsimp only at H` is REQUIRED: `cases r0` with
    `r0 = some cs1` leaves `match some cs1 with | some cs1 => …` UNREDUCED in
    H (the goal gets iota-reduced, the hypothesis does not), and the later
    `rw [ite_eq_left hf] at H` then reports “Did not find an occurrence of the
    pattern”.
  * `obtain rfl : cs' = with_ss cs1 (…) := H.symm` right after
    `simp only [Option.some.injEq] at H` is what lets `pc`/`cs_ok` be closed
    afterwards: with `cs'` substituted, the last component is `exact Hpc1`
    (`pc (with_ss …) = pc cs1` is `rfl`, and `exact` closes it up to defeq)
    and the `cs_ok` component can be stated over `set_kn (bump cs1 c) k'`.
  * the *type* of `cs_ok` mentions `cs` only through the fields, so
    `cs_ok … cs1` and `cs_ok … (bump cs1 c)` are NOT defeq (`mk_ss` resets
    `s_log`): rebuild the bumped state with the structure-update literal
    `{ HC2 with co_log := rfl }` (one field, all 26 others are defeq checks).
  * `set_kn (bump cs1 c) k'` and `with_ss cs1 (mk_ss (pc cs1) cs1.a_ss.s_regs
    k' (nxt cs1 + c))` ARE defeq, but `rw` cannot see it: prove the equation
    (`:= rfl`) and `rw [← hset]` on the goal.  Writing it the other way round
    (`rw [hset]`) does not help — `rw` matches syntactically in both
    directions, only the stated orientation is present.
  * `fresh_ok_parts nx0 cs1 hf` is needed for BOTH `kn_vars_lt` (2nd
    component) and `nx0 ≤ nxt cs1` (7th): the first `env_agree` component is
    `env_agree nx0 E E1` trans `env_agree nx0 E1 E2`, and the latter comes
    from `env_agree_le` at `nx0 ≤ nxt cs1` — `nx0 ≤ nxt cs` is NOT enough
    (that was the one type mismatch of the first compile).
    `getD_map'` (already present) is what turns `vals.getD i` into
    `edenot E1 (getD i …)` — pass the default `x = .ELit 0` explicitly.
MEASURED while landing `rdn_visible` (:919) and `know_ok_unhide` (:943) —
the `mrestrict` / `mem_grows` / `rdn_ext` / `store_ok_mono` machinery:
  * this tree's `mrestrict H m a` is `if H a then none else m a`, and the
    condition is INTERNALLY `H a = true`, so `unfold mrestrict; rw [hHa]`
    leaves `if false = true then … else …` UNREDUCED (`rw` turns the
    condition into `false = true`, it does not evaluate it) — `omega`/`rfl`
    then both fail.  `simp [mrestrict, hHa]` is the spelling that works.
  * `omega` cannot evaluate `2 ^ 64`: it is an opaque atom, so a goal like
    `a.toNat + 1 < 2 ^ 64` is NOT provable from `a.toNat < 2 ^ 64` alone
    (“no usable constraints”).  `rdn_bytes_some` (:2762) gets away with it
    only because `x.isLt` supplies an upper bound for the SAME atom — copy
    that four-line block (`hx64`, `han : a.toNat < x.toNat` by
    `exact_mod_cast`, the Nat form by `omega`, then `exact_mod_cast` back to
    `Int`) verbatim rather than trying to shorten it.
  * `rdn_ext` is stated over `m1 m2` in the SAME orientation as the goal
    (`rdn segs m1 … = rdn segs m2 …`), so no `.symm`; and the two `?_`s must
    be `refine`'d (as an `exact … ?_ ?_` term they are unsynthesizable
    placeholders — nothing in the conclusion determines them).
  * `know_ok_unhide` is uniform once two locals are in place: `AG` (`H1 a =
    false → mrestrict H2 FULL a = mrestrict H1 FULL a`, from `Hsub` by
    `cases`/`simp`) and `H1false` (`mrestrict H1 FULL a ≠ none → H1 a =
    false`, by `cases H1 a`).  With them the four literal-length arms are
    three lines each: take `Hz i …`, then `rw [AG _ (H1false _ (by rw [hz];
    simp))]` and finish with `hz`; `KUnk` feeds `H1false` the `≠ none`
    directly.  `KWr` is the only arm that does not go through `AG`: it is
    `StoreOk.store_ok_mono` at `GR` (note the qualification — `AsanPlanSound`
    does not `open …Common.StoreOk`, and its `store_ok`/`wview` are NOT the
    `RiscvSemantics` ones of the same name).
  * `KImg` needs `0 ≤ i ∧ i < 2^64` for `u_small` — both follow from its own
    `kentry_ok` (`0 ≤ lo ≤ i`, `i < hi ≤ 2^64`), so `hull_ok` is not needed;
    after `u_small` the goal is a `Bool` conjunction, so
    `simp only [Bool.and_eq_true, decide_eq_true_eq]` then `omega` for each
    half (the `A.img_lo ≤ i` half needs `Ki1` AND `Hi1`, not `Ki1` alone).
MEASURED while landing `maps_match_remove` (:1184) — the `map_remove`/filter
half of the fog obligation:
  * **`!(b : Bool)` in a HYPOTHESIS TYPE elaborates as `Not` on the coerced
    `Prop`, i.e. `!decide (b = true)`, NOT as `Bool.not b`**: `have hall :
    ∀ x, x ∈ ms → !(amap_eqb x m) = true` came out as
    `(!decide (amap_eqb x m = true)) = true`, which then refused to be the
    `∀ x ∈ ms, f x = true` that `filter_all_true` wants ("application type
    mismatch … `!decide (…)` vs `!amap_eqb …`").  Rule: write
    `Bool.not (f x) = true` in hypothesis TYPES; `!(…)` is fine in term
    position with expected type `α → Bool` (where `List.filter`'s argument
    sits).  This is a silent shape change, so it is worth checking every
    `!` that ends up on the left of a `=` in a `have`'s type.  Same trap for
    `by rw [heq]; rfl` proving `¬(!(…) = true)`: use `by simp [heq]`.
  * `map_remove_head` / `map_remove_skip` live in `Common/RefNodes`, which is
    NOT in this file's import cone; the two restatements
    (`map_remove_head'`, `map_remove_skip'`) are 2 lines each and belong in
    this file.  State the skip form over a PAIR with the hypothesis
    `p.1 ≠ a` (`rw` then matches `iv` syntactically); the head form has to be
    applied through `show … from map_remove_head' _ _ _`, because
    `amap_den E m` is not syntactically a `(a, n)` tuple.
  * `subst hm0` on `hm0 : m0 = m` kills **m**, not `m0` (the same
    right-hand-side rule as everywhere else in this file) and the whole rest
    of the proof then loses `m`.  State it the other way round —
    `have hm0 : m = m0 := (amap_eqb_eq heq).symm` — so `m0` is the one that
    goes away.
  * `rw [maps_match]` does NOT fire on the GOAL until the head is a
    constructor: do it inside each `is_fog m0` branch (`cases hfog : is_fog
    m0` gives the equation AND the branch in one step), then
    `simp only [hfog, ite_true]` resp. `[hfog, Bool.false_eq_true, ite_false]`.
  * `map_remove_notin'` is an EQUATION (`map_remove l' a = l'`), so it must be
    `rw`'d into the goal and followed by `exact HM` — `refine … ?_` tries to
    use it as the conclusion and fails with a type mismatch on `maps_match`.
`unvis_sound` (:3447), the last big node lemma before
`check_sound` (see the MEASURED note at the end of this paragraph for what
the landing added to the scouting facts below).  Everything it calls was
already landed when it was scouted (`rdn_visible` / `know_ok_unhide`;
`shadow_of_val`,
`flat_x_sound`, `kzero_x_sound0`, `ealign_sound`, `xhi_sound`,
`split_lit_denot`, `vis_mono`, `hid_cons_sub`, `kentry_apart_keep`,
`kentry_apart_bp_eq`, `A_bytes_fm_split`, `A_bytes_fm_here`,
`A_bytes_allow1_nonneg`, `vis_here_eq` were already in).  The facts below were
CHECKED in this tree, so the next pass does not have to rediscover them:
  * the STATEMENT needs an extra hypothesis `(Hsh : shadow_ok A)`:
    `shadow_of_val` takes `(Hsh : shadow_ok A)` explicitly, exactly as
    `shdisj_sound` does — `check_sound` must therefore thread `SHADOW_ok`
    into its `PUnvis` arm.
  * H-decomposition: `rw [node_unvis_eq] at H` → `unfold node_unvis_ref at H`
    → `dsimp only at H` → `split at H`, i.e. verbatim the `shdisj_sound`
    (:2316) skeleton; `node_unvis` is the `…B` twin and `node_unvis_eq` is
    already proved, so the plain `xhi`/`shadow_of`/`flat_x`/`kzero_x` lemmas
    apply afterwards.  The `let (a, b) := …` patterns come out as the
    PROJECTIONS `(split_lit b).fst` / `.snd` and `(shadow_of A (kn cs) b
    n).fst` / `.2.fst` / `.2.snd` (see `abstractcell_sound`'s note and the
    `shadow_of_val` calls in `shdisj_sound`).
 Use the NAMED-field literal — `cs_ok_reenv`
    (:2980) is the template, and it is the reason the 27 positional `⟨…⟩`
    is not needed.
 `omega` cannot do this
    by itself (division is opaque to it).
bv_unsigned x) && (bv_unsigned x <? ub + un) then M' x
    else M x`, and its four facts (`Mmid_out`, `Mmid_none`, `HK1`, and the
    `kentry_apart_keep` at the second `kn_unfill`) are what `HK2` needs.
    `kn_unfill_keep` (LANDED, just above `maps_match_remove`) is exactly the
    engine of `HK1`/`HK2` — they are two calls to it, so that part of the
    proof no longer needs any list induction.
MEASURED while SCOUTING `unvis_sound` in a scratch harness (a `/tmp` file
that `import`s this module compiles in 0.7 s, so the whole node lemma can be
developed there and pasted in one piece — it was used again for
`vis_add_sound` (section 10) and is worth doing again for `check_sound`;
the olean is only stale w.r.t. edits made AFTER the last
`lake build`).  The skeleton below COMPILED up to the four remaining subgoals
at scouting time; THIS PASS THEN CLOSED THEM — the four are gone, so read the
bullets as the shape of the proof plus the traps, not as a to-do list:
  * `set` is NOT available in this tree — `set M : T := e with hM` reports
    **"unknown tactic"** (the file uses `let` + `have h : M = e := rfl`
    everywhere instead).  Use `let CS : acs := ACS … ` for the result state
    and prove `hcs' : cs' = CS` (so every helper lemma can be stated about
    the zeta-reducible `CS`); `rw [hcs']` on the goal must be done EXACTLY
    ONCE (a second one fails with "did not find an occurrence of `cs'`",
    which reads like a spelling problem but is not).
  * H's decomposition needs `dsimp only at H` after the `cases` of the two
    `xhi` results: `cases rb`/`cases rn` do NOT iota-reduce the
    `match some bh, some nh with …` that H carries, and without the `dsimp`
    the pair patterns are still `(bb, bk).fst` / `(sb, sk, sn).2.fst`, so the
    guard written in `by_cases hg : <guard> = true` does not match
    syntactically and `rw [ite_eq_left hg] at H` fails.  With the `dsimp` it fires.
  * the guard's exact shape (after `dsimp`) is
    `cs.a_vis.any (vis_here b n) && decide (3 ≤ ealign (kn cs) b) &&
     decide (3 ≤ ealign (kn cs) n) && flat_x (kn cs) bb bk n &&
     decide (bh + nh ≤ CEIL) && flat_x (kn cs) sb sk sn &&
     kzero_x (kn cs) (kn cs) sb sk sn`,
    and `simp only [Bool.and_eq_true, and_assoc, decide_eq_true_eq] at hc`
    peels it into the 7 facts, `decide`s already eliminated.
  * the 23-field `HC.co_*` record literal is CONFIRMED to compile: the only
    goals it leaves are `co_know`, `co_abytes`, `co_minv`, `co_zero` (plus
    `co_log := rfl` and `co_regs := HC.co_regs`), and `refine ⟨?_, rfl⟩`
    must come FIRST (the goal is the `∧`, so a bare record literal reports
    "`co_regs` is not a field of structure `And`").
  * numeric toolkit that works here: `Int.add_le_add`,
    `Int.ediv_le_self 8 (… : 0 ≤ a)`, `Int.ediv_nonneg`, `Int.add_nonneg`,
    `Int.emod_eq_of_lt`, `bv_unsigned_nonneg`, and `by decide` for the closed
    bounds (`2 ^ 47 ≤ CEIL`, `2 ^ 47 + 2 ^ 47 < 2 ^ 64`).  `le_trans` is
    `Int.le_trans` (the unqualified name is NOT in scope here).  For
    `HSS` (`estart (SA sb sk) = A.shadow_off + ub / 8`) pass `omega` an
    explicit `ub / 8 ≤ 2 ^ 47` (`Int.le_trans hdivb hub47`) — on its own it
    encodes the division as `8 * j ≤ i` and then cannot close the `0 ≤` half.
  * `HID_mono` needs `Bool.not_eq_true` to turn `!(vis …) = true` into
    `vis … = false`, and then `vis_mono A E CS cs model a ALLOW_sub` gives the
    contradiction; `ALLOW_sub` is the `List.any_eq_true` / `List.mem_filter`
    pair (`in_vis` and `in_sh` are the same argument).
MEASURED while LANDING `unvis_sound` from that skeleton — the four goals are
gone; the traps below are the ones that actually bit, in the order they bit:
  * `set` is really absent, but the replacement is not `let`: it is
    `generalize h : <term> = ub at *` (Lean core, works on hypotheses too).
    `ub` / `un` / `S` came out that way, and `Int.ediv_le_self 8 (… : 0 ≤ a)`
    then needs `0 ≤ ub` as an explicit hypothesis — `omega` will NOT derive it
    from `hub : bv_unsigned (edenot E b) = ub` (it cannot see that
    `bv_unsigned …` is a `Nat` cast), so state it: `by rw [← hub]; exact
    bv_unsigned_nonneg _`.  `uE E b` / `elenZ E n` are NOT the generalized
    atoms (`generalize` only rewrites the *unfolded* terms), so carry
    `have hubE : uE E b = ub := hub` and `have hlenZ : elenZ E n = un := hun`.
  * `generalize … at *` on `T` does NOT touch terms a lemma produces
    afterwards: `shadow_of_val`'s `bv_unsigned (edenot E n) / 8` /
    `kzero_x_sound0`'s `estart E (SA sb sk)` must be `rw`'d to `un / 8` /
    `S` in the lemma's own conclusion before use.
  * do NOT `rw [HB] at *` for the split-literal address: it rewrites `HB`
    itself into `ub = ub`, and the later `rw [HB]` then reports "did not find
    an occurrence of the pattern `ub`".  Keep `HB` intact; the only place
    that needs it is the `kn_unfill_keep` call (`rw [HB, hlenZ] at Hx`).
  * `shadow_of_val`'s parameter order is `(sb : expr) (sn : expr) (sk : Int)`
    while the pair is `(sb, sk, sn)`: pass `(shadow_of …).fst`, `… .2.snd`,
    `… .2.fst` (NOT `.2.fst` then `.2.snd`).
  * `unfold Mr mrestrict` leaves beta-redexes (`(fun a => hid …) x`), so
    `ite_eq_left` will not fire: use `simp only [Mr, mrestrict]` instead.  A
    `let`-bound `Mmid` is invisible to `rw` (no delta on the LHS it matches),
    so add `have Mmid_app : ∀ x, Mmid x = (if … then … else …) := fun x =>
    rfl` and `rw [Mmid_app x]` first; likewise repeating `Mmid`'s guard as the
    `ite_eq_left` pattern in a `show` is fragile — rewrite with `Mmid_app`.
  * `rw [HID_eq …]` inside `mrestrict`'s `if` fails with "motive is not type
    correct" (the `Decidable` instance depends on the scrutinee).  Proving
    `M_eq` / `M_none` pointwise with `by_cases hh : hid … = true` (and
    `rw [ite_eq_left hh]`, `rw [ite_eq_left (HID_mono x hh)]`) is the way through.
  * the `co_abytes` goal mentions the LITERAL state's `a_abytes`, which is the
    old one but not syntactically: `show A_bytes (allowA A E CS) ≤
    cs.a_abytes` before `omega` (same for `CS.a_vis` / `CS.a_ghost`, reached
    with `have hvis : CS.a_vis = … := rfl`).
  * `page_allowedb` monotonicity: `rw [HA', List.mem_append,
    List.mem_append]` must be applied to the *membership* goal, so
    `refine List.any_eq_true.mpr ⟨iv, ?_, hpg⟩` first (unfolding
    `page_allowedb` puts the membership inside `List.any`).
  * `Bool.not_eq_true'` (with the prime) is the one that rewrites
    `(!b) = true` to `(b = false)`; `Bool.not_eq_true` is the `¬(b = true)`
    form.  `Bool.or_eq_false_iff` splits the `||` in `in_allow`'s = false.
  * `AxSymExec3Sound.ofInt_toNat a` is `Z_to_bv 64 (bv_unsigned a) = a`
    (needed to feed `Hzero` the concrete `a`).
MEASURED while landing `node_fresh_sound_pf` (:2138) — the whole node is 240
lines in this tree, of which the arithmetic is the easy part; the ONE thing
that cost the pass is the `match` on `base`:
  * `node_fresh`'s `let b := match base with | some b => b | none => .ELit 0`
    is compiled to a SHARED AUXILIARY match function, not a `match` term:
    `#print node_fresh` shows the `match`, but `pp.all` on the hypothesis shows
    `AsanPlanCore.after_call.match_1 (fun _ => expr) base (fun b => b)
    (fun _ => .ELit 0)`.  Consequences, all measured: `rw` cannot rewrite it,
    `generalize h : (match base with …) = bb at Hn` SILENTLY does nothing (it
    produces `hb`, leaves `Hn` untouched), and `change` to a form using
    `Option.getD` fails ("not definitionally equal" — `change` matches at
    reducible transparency, so it will not unfold `getD`).  The same text
    written inside `∃ z, … = z` + `obtain` even elaborates to a DIFFERENT
    two-scrutinee match (`match base, Hn with | some b, Hn => b | …`), i.e.
    the visible shape of these terms is not a reliable guide.
  * What works, and is the recipe for any node with a `match` on a parameter:
    `cases base` first (it is a plain argument of `node_fresh`, so the
    elimination is fine), `dsimp only at Hn` (now the application is a redex
    and iota-reduces to `.ELit 0` / the `some` payload), then
    `generalize hb : (expr.ELit 0) = bb at Hn` resp. `generalize hb : b0 = bb
    at Hn`.  After that BOTH arms have the same context with an abstract `bb`.
  * The two arms cannot share a tactic block: `all_goals` is `try (t <;>
    all_goals t)`, so a goal-producing `t` (a `by_cases`, a `cases`) re-fires
    on its own subgoals and the bullets then address the wrong goals (measured:
    it leaves the outer goals untouched).  This tree therefore states the body
    once as `node_fresh_step`, over an ABSTRACT `b : expr` and with the whole
    `if … match … else none = some cs'` hypothesis written out in its
    statement: both arms are then a single `exact node_fresh_step … bb … Hn`
    (the hypothesis type there and the `match_1` form in `Hn` are `exact`-defeq
    — default transparency unfolds the auxiliary — even though `rw` cannot see
    it).
  * `split at Hn` on the `match xlo2 …, xhi2 … with` is NOT usable (two
    scrutinees; the fallback arm becomes `| x, x_1 => none`), and after the
    split the residue does not reduce under `dsimp`/`simp` ("made no
    progress"), so a hypothesis-level split is a dead end.  The recipe that
    works is the documented `revert Hn` → `generalize hh1 : xlo2 … = o1` →
    `generalize hh2 : xhi2 … = o2` → `cases o1` → `cases o2` → `intro Hn`:
    the `cases` must happen on the GOAL (after the `revert`), which is what
    makes the iota step fire; doing `intro Hn` before the `cases` puts the
    match back into a hypothesis, where it stays.
  * the three arithmetic facts `node_fresh` needs are
    `Int.ediv_lt_iff_lt_mul` (`(lo + c - 1) / c < q + 1 ↔ lo + c - 1 <
    (q + 1) * c`) and `Int.le_ediv_iff_mul_le` (`q ≤ hi / c ↔ q * c ≤ hi`),
    plus `Int.add_mul` to keep `omega` linear (`c * (q + 1)` is not related to
    `c * q` unless it is rewritten); `0 < c` and `c ≤ 2^40` are
    `two_pow_pos_int` / `int_pow_le_pow` (`pow_pos` / `pow_le_pow_right` are
    NOT in scope), and `0 ≤ q` is `Int.mul_neg_of_pos_of_neg` + `omega` (the
    `land_aligned_small` block), `q < 2^64` is
    `Int.mul_le_mul_of_nonneg_right` + `Int.one_mul` (`le_mul_of_one_le_left` is
    absent).
  * the extended valuation's `bv_unsigned` is `u_small` twice
    (`c = zpow 2 logc` and `q`) and `Int.emod_eq_of_lt` for `c * q < 2^64`;
    the `escale` denotation is `mkMd_denot` + `show mul_div MulOp.MUL
    (Z_to_bv 64 c) (Z_to_bv 64 q) = _` (`mul_div .MUL` reduces to `*` only
    after that `show`), and `ext1_at` is what turns `E'.ev (nxt cs)` into
    `Z_to_bv 64 q`.
SCOPE OF THE `Rename` / `RenameCS` SECTIONS, MEASURED: LANDED IN THIS PASS.
MEASURED for `rename_sound` (its own comment block has the details): the
`let ok (v) := match nt_get fw v with …` and the `match mk_fwd m, mk_bwd m`
of `node_rename`'s body are BOTH compiled into shared auxiliary match
functions, so `rw`/`generalize`/`cases` on the scrutinee do not reach the
hypothesis and `dsimp only at H` cannot reduce them while the scrutinee is a
variable.  The recipe: `unfold node_rename at H`, `by_cases` + `rw [ite_eq_left]`
for the outer `if`, then `revert H` -> `cases hfw : mk_fwd m` ->
`cases hbw : mk_bwd m` -> `intro H` -> `dsimp only at H`.  The `s_log`
conjunct of the inner guard is discharged by rewriting `HC.co_log` into `H`
first, so `match cs.a_ss.s_log` never has to be split at the hypothesis
level; and the `show … (rename_cs fw cs nx) …` step must keep the `nx` the
definition puts into `mk_ss` (`max gb (csmaxv (rename_cs fw cs 0))`).
`compact_sound` is then one line (`node_compact` calls `node_rename` at
`compact_map gb cs`).
WHAT HAPPENED TO THE LAST ENTRY.  `check_sound` was the last
one, and it LANDED — see `## 10+++.` in the file itself.  Its 
statement, kept here for the record since this block no longer lists it:
  Theorem check_sound : forall fuel bfuel lc p cs s,
    CHECK bfuel fuel lc cs p = COk s ->
    forall E R FULL model D, cs_ok E cs R FULL model -> LCOK lc D E (m_fs model) -> D [] ->
    srealizes SEGS (cfg R (pc cs) FULL model) (sd D E (m_fs model) s).
MEASURED while landing `check_sound` (each of these cost a compilation round;
they are the recipes the next node-family proof in this style will want):
  * the 44-arm structure.  The theorem is ONE proof: `intro bfuel fuel; revert
    bfuel; induction fuel` (`revert bfuel` is what makes the induction
    hypothesis come out as `∀ bfuel lc p cs s, …`, i.e. at the SAME executor
    fuel), the base case is `check_zero_lc` (`rfl` then `cases`), and the
    successor case builds `H : check_go … = COk s` from `check_succ` BEFORE
    `cases p` (as `check_vars` does), then `cases p` gives the 44 bullets.
  * do NOT `cases lc` once per arm and then `generalize` the recursive call:
    after `cases lc` the term is `check … f none cs' k` / `… (some c) …`, and
    every arm then needs its own copy of the same three-line block.  The
    shipped proof keeps `lc` abstract and splits the leading guard with a bare
    `split at H` (`· cases H` for the `CErr 9` branch), which substitutes `lc`
    for free and leaves SAME/CONT usable as they are.
  * the guard itself is recovered from the hypothesis, not assumed:
    `have Hg : lc_guard lc cs = true` by `cases lc` (then `rfl`), and in the
    `some c` case `unfold AsanPlan.check_go at Hne; dsimp only at Hne;
    split at Hne; · cases Hne; · simpa [lc_guard] using hgc`.  Do NOT try to
    rewrite the guard out of `H` with `ite_eq_right` and a lemma about the inline
    `match`: the `if`'s `Decidable` instance mentions the match, so the
    rewrite reports "did not find the occurrence of the pattern" on a goal
    that prints identically, and a `have` stating the match gets
    context-generalised (`match lc, HL, Hg, … with`) because hypotheses
    mention `lc`.
  * `gcd`/`generalize` per node shape: `revert H` → `generalize hh : <the
    node call> = r0` → `cases r0` → (`intro H`, `try dsimp only at H`,
    `obtain ⟨…⟩ := p` when the payload is a pair/triple) → for each child,
    `intro H; revert H; generalize h1 : <the child call> = r1; cases r1`.
    The `intro H; revert H` pair is NOT redundant: it forces the pair `match`
    that `obtain` left in the goal's domain to reduce, and without it the next
    `generalize`+`cases` fails with "Dependent elimination failed" on an
    equation that still contains the whole body.
  * `| err => err` arms: `cases r` on the `cres` scrutinee gives the `CErr a b
    c` branch whose hypothesis is `CErr a b c = COk s`, so `cases H` closes it;
    the `salt2`/`SAlt2` arms need NO trace-set algebra: `salt2 a b` is
    `SAlt2 a b` only when neither is `SNil`, so `sd_salt2` is needed for the
    `salt2` shapes (`PBrk2`, `PMmap`, `PMmapIn`, `PMmapInH`, `PMprotect`) but
    the `PExt2` arm is a plain `exact` (its body builds `SAlt2` directly).
  * `PCase2` / `PCaseDisj`: the two children must have EQUAL shapes, and the
    `shape_eqb s1 s2 = true` guard must be turned into `hse : s1 = s2`
    (`shape_eqb_eq s1 s2 hb`) and `rw [← hse]`'d into the second child's
    equation BEFORE `SAME` is applied — `cases H` substitutes only the first
    shape and drops `s1` from the context, so write the shape argument of
    `SAME` as `_`.
  * `PSplit` / `PCase2` use `bv_unsigned (edenot E e)` for the case split, not
    the hypothesis's `lo`/`hi`: `split_sound` gives the two `cs_ok`s and
    `dsimp only [sd]` + `by_cases hle : bv_unsigned (edenot E e) ≤ mid` +
    `rw [ite_eq_left hle]` turns the goal's `sd (SCase …)` into the child's.
  * `PNext` / `PMerge` are the only arms that must destructure `lc`: `cases lc`
    then `cases c` (`LC`/`JC`), and the wrong constructors are closed by
    `cases H` (their bodies are `.CErr 8`).  `PMerge` also needs
    `sd_agree` at `sk'` (whose `shape_vars_lt` comes from the guard) and one
    `rw [hpc]` for `pc cs = pc js'`.
  * `PRename` / `PCompact` recurse into the induction hypothesis instead of
    `CONT`: `rw [← Hpc]`, then `rw [sd_agree … s hsv]`, then
    `IH bfuel lc k cs' _ H E' R FULL model D HC1 (Hfs ▸ LCOK_agree_gb …) HD`.
    `LCOK_bnd` supplies `nx0 ≤ gcb` for `rename_sound` / `compact_sound`, and
    `sd_agree`'s shape argument must be `_` (see above).
  * `PVia` is proved by APPLYING the induction hypothesis at the join context
    `some (.JC j js sk (nxt cs) lo)` and proving the resulting `LCOK`: its
    three numeric components are `nx0 ≤ nxt cs`, `nxt cs ≤ lo` (both from the
    `via_ok` guard, after `simp only [via_ok, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]` peels it into four, LEFT-nested) and
    `js.a_ss.s_regs.length = 32`; the join frame's body is a second `IH` at
    the ORIGINAL `lc`, whose `LCOK` premise is
    `LCOK_agree_gb` at `env_agree_le gcb (nxt cs)` — for `lc = none` that
    bound is `nx0 ≤ nxt cs`, which also comes from `via_ok`, not from `Hg`.
  * `PLoop` is the one arm with a nested induction.  Its `Q` is the downward
    induction over the remaining iterations; the exit case converts
    `cs_ok E' (inst inv J (ELit j))` into `cs_ok E' (inst inv J N)` by the
    `cs_ok_inst` ROUND TRIP (`proj1` at `ELit j`, rewrite the denotation with
    `HNe`, `proj2` at `N`) — `HNe : edenot E' N = edenot E' (ELit j)` is
    `BitVec.eq_of_toNat_eq` on `u_small`; the step case builds the body state
    with `cs_ok_set_kn` from `know_ok` on `[KRange (EVar J) 0 (nhi-1), KRange
    (esub N (EVar J)) 1 nhi]`, whose two `kentry_ok`s are `u_sub64` +
    `Int.emod_eq_of_lt` (NOT `u_small`: `u_sub64` produces `… % 2^64`, and
    `omega` cannot look through `%`), and then hands `LCOK`'s inner obligation
    to `IHm` at `j+1` after the `cs_ok_inst` round trip at
    `eaddz (EVar J) 1` (its `lc_next` is exactly that expression).
  * `(.LC h nx lo hi)`'s `pc` is `lc_head = pc cs`, so `PBrz`-style arms reach
    the loop head with `rw [Hpc]`; `PDiamond`'s decided branch is literally the
    `PRun` arm (both `run_block_gc_sound` calls, with `{Gcb}` = `nx0` or
    `lc_bnd c`), and its undecided branch chains two `run_block_gc_sound`s
    whose continuation instantiates `diamond_join_sound` and re-transports the
    two `env_agree`s with `env_agree_trans`.
  * when the goal has to be re-stated over a `let`-bound child state, write
    the state out (`set_kn cs (.KRange e lo 0 :: kn cs)`) rather than naming
    the `let`: `unfold check_go`/`dsimp only` zeta-reduces it in the
    hypothesis, so the name is not in the goal, and `rw [← pc_set_kn …]`
    only rewrites the `pc`, not the state argument of `run_block_gc_sound`.
 Lean's `match`
swallows what follows it, so `&& ranges_apart_x …` slid into the
`| _ => false` branch: the node no longer TESTED the apartness it then
claimed, and its soundness statement was FALSE (take `b1 = b2 = ELit 0`,
`n1 = n2 = ELit 8`: both shadows are `shadow_off, +1`, so the appended
`KDisj` claims `estart + 1 <= estart`).
-/

