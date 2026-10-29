/-
  * AsanNodesMmLib — generic library for the soundness of the plan checker's memory-syscall
  * nodes on the spec.
  module-level imports `AX2`, `AX2S`, `AP`, `APS` (here: the `open`s below).

    Contents:
    - parts 1-9 (no Section): [RES_hull_def]; interval-list semantics
      ([APS.in_ivs] = [BackingAlgebra.covered]), [sum_sizes] = [live_bytes];
      [eager_used_sem], [mat_pages_le_A_bytes], [vm_backing_used_le];
      [page_in_ranges] across [maps_subtract]; pieces / survivors of
      [maps_subtract]; pointwise [zfill] / [unfill] / [mrestrict];
      [is_ecall_at_sound], [v_addi_pc], [page_up_eq]; valuation bookkeeping;
      reflexivity of the syntactic equalities; list lemmas for munmap.
    - part 10 (Sections over [segs] only): syscall nodes
      [srz_mmap_rw2] / [srz_mmap_none2] (hint-placed, flags core 34),
      [srz_mmap_fixed_rw_free2] / [srz_mmap_fixed_none_free2] (flags core 50,
      [region_free (reserved ++ maps)]), [srz_mprotect2]; the checker
      characterisations [mmap_rw_check] etc.; [srz_sys_lazy] (enter the ecall
      on ANY lazy ledger), [node_chk_ev_mat].
    - part 11 (Section [Nodes] = the parameter block of AsanNodesIface):
      helpers, Slice, knowledge across a slice, + [refuse_ok] /
      [refuse_cont] / [gap_ok_sound] (grant witness from [APC.gap_ok] via
      [AsanPlacement.free_gap_of_totals]).

  Translation notes (as in the sibling modules `AsanPlanSound`, `RefNodes`):
  - `Z` → `Int`; `fst`/`snd` → `.1`/`.2`; `List.Forall P l` → `∀ x ∈ l, P x`;
    `existsb`/`forallb` are `List.any`/`List.all`; `negb b` → `!b`;
    `Z.min`/`Z.max` → `min`/`max`; `Z.leb`/`Z.ltb` on `Int` are decided
    propositions; `Nat.eqb` → `==` (`BEq`).
  - `2 ^ k` on `Int` is `zpow 2 k` (`AsanPlanCore`).
  - a `match ... end` written directly under `!` / `&&` is parenthesized
    explicitly here (Lean's `match` swallows what follows it).
  - Word hygiene: this file contains no proof hole and no extra postulate.
 The thirteen
  that closed it are listed in the FINAL STRETCH paragraph below and again in
  the note at the end of the file; the `DEFERRED` block those two used to
  point at is gone.
 Their 62
  section-local declarations (31 + 31) are the private proof-engineering of
  the two big theorems of those sections, `slice_cs1_ok` (:2924) and
  `dest_cs1_ok` (the destroy resolution's `cs_ok`); of each 31, 15 are the
  section's `Let`s (`HC`, `Hm`, `lo`, `hi`, `SPo`, …), which appear here as
  leading explicit parameters of the `sl_*` / `d_*` helpers or as local
  `have`s, so 16 + 18 theorem/definition declarations remain:
  - §12 (`Section Slice`): `sl_bounds` (:2714), `sl_lohi`, `sl_in_maps`,
    `sl_wf'`, `sl_noacc_out` / `sl_noacc_in`, `sl_lazy_out` / `sl_lazy_in`,
    `sl_vis_out`, `sl_MR_out`, `sl_vis_in_E` / `sl_vis_in_G` / `sl_vis_in_F`,
    `sl_eager` (:2891), `page_base_aligned` (:2881) and `slice_cs1_ok`
    (:2924).
  - §13 (`Section Destroyed`): `d_bounds`, `d_lohi`, `d_in_maps`, `d_wf'`,
    `d_sub_out` / `d_sub_in`, `d_maps_out` / `d_maps_in`, `d_noacc_out` /
    `d_noacc_in`, `d_lazy_out`, `d_vis_out`, `d_vis_in`, `d_MR_out` /
    `d_MR_in`, `d_eager`, the definition `hole_prefix_ok` (:3413) and
    `dest_cs1_ok` (:3421).
  The only additional definition is the `slMaps` (the slice child's
  `a_maps` field — a `match` written directly in a theorem statement is
  generalized by Lean over every hypothesis whose type mentions the
  discriminant; see the note on the definition).
  All of parts 1-9 — the interval-list algebra,
  the backing meter, `maps_subtract` pieces/survivors, the page lemmas, the
  pointwise overlays, the AP-level facts, the valuation bookkeeping, the
  syntactic-reflexivity family and the munmap list lemmas; plus part 10 up to
  and including the four `*_check` checker equations and the two NULL-hint
  nodes and `mmap_fixed_gate_open` /
  `mmap_fixed_rw_free_check` / `mmap_fixed_none_free_check` (:885-:1054).
  PART 11 is IN PROGRESS: the pure interval algebra of
  its first stretch is landed here as §10c — `page_base_aligned'`,
  `iv_subtract_contained`, the `map_replace_entry` / `maps_subtract_map_replace`
  / `in_replace_entry` / `maps_subtract_in_pieces` family, `seps_app_intro` /
  `seps_iv_subtract` / `seps_maps_subtract`, `replace_entry_notin`,
  `maps_subtract_disjoint_id`, `maps_match_app_pcs`, `sum_sizes_maps_subtract_le`,
  `ledger_split_maps_subtract`, `maps_match_subtract` (the warp of a fog ledger
  across a destruction), and the two disjointness lemmas `seps_map_disjoint` /
  `maps_match_disjoint`, plus the page discipline of the pieces
  (`iv_subtract_left_ineq` / `iv_subtract_right_ineq` / `iv_subtract_bounds` /
  `maps_subtract_bounds`, with the `emod4096_*` / `ofInt_emod4096` helpers),
  and §11 the DEFINITIONS of the checker-side library: `kind_none` /
  `kind_lazy`, the `grant_post` / `grant_mem` pair, `null_cs1` / `fixed_cs1`,
  `slarm` with `sl_nn` / `sl_charge`, `slice_post` / `slice_mem` /
  `slice_hyps`, `dest_post` / `dest_mem` / `dest_hyps`, together with the
  small shared facts of  §2 (`CEIL_eq`, `KHI_eq`, `FLOOR_eq`,
  `Z_to_bv64_m1`, the `bv5_*` family, `some_inj`), the refused child's three
  equations (`refuse_eq` / `refuse_pc` / `refuse_nxt`), `gap_weight_eq`,
  `lazy_interior_fresh`, `null_kend_pure`, `kimg_in_hull_pure` and
  `covered_maps_subtract`, and the hole/token helpers `tok_of_hole`,
  `kimg_in_hull_cons2`, `in_allow_ext`, `maps_match_tok_prefix` and
  `maps_match_unhole`.
  PART 11, SECOND STRETCH (this session): the length argument
  `mmap_len_sound` (:1472); the GRANT block's `reserved_free_above` (:1548),
  `vis_add_inv` (:1558), `vis_grant_out` (:1605), `grant_wf` (:1626), the
  `maps_apart` definition (:1677) with `maps_apart_of_region_free` (:1682),
  `inside_maps_apart` (:1692), `safe_range_apart` (:1706),
  `grant_keep_apart` (:1720) and `kn_grant_filter_ok` (:1734); and (from the
  later blocks) `regs_ok_regupd_same` (:1756), `kdisj_new_pure` (:2105),
  `budget_slack` (:2185), `page_aligned_sound` (:2244), `split_flat_estart`
  (:2286), `same_val_sound` (:2440), `find_hole_sound` (:2451), `rekind_den`
  (:2657) and `in_rekind` (:2662).  Fifteen declarations in all.
  PART 11, FOURTH STRETCH (this session): the NULL-hint grant
  `mmap_null_cs1` (:1974), the first of the two `*_cs1` nodes, with its two
  `def`s `mmEnv` / `mmBase` (see the note on them below).  The
  proof is `grant_cs1_ok` plus the placement witness: the `null_kend` joint
  end fact (`null_kend_ok`), the `kdisj_new` disjointness facts
  (`maps_apart` read off `region_free` by `maps_apart_of_region_free`), and
  the `min Y (bv_unsigned a)` witness built by `null_hint_grant_step`.  Also
  `grant_vis_add` (:2116), the "declare the range visible" step: its two new
  `KWr` / `KZero` entries are knowledge by `kmem_ok` (the bytes are fresh and
  zero), and the old knowledge transfers from the less-visible to the
  more-visible state by `know_ok_unhide`, with
  `hid_cons_sub` for `Hsub` and `hid_hull` for the hull side.  Two measured
  details: `in_vis` needs `List.any_cons` (its `List.any` does NOT iota-reduce
  under `dsimp only` there), and the `if (<Bool>) then … else …` of
  `mrestrict` has a DEPENDENT `Decidable` instance, so `rw` on the condition
  fails with "motive is not type correct" — use `simp only [h, Bool.false_eq_true,
  ite_false]`.
  PART 11, FINAL STRETCH (this session): the last thirteen —
  `gap_ok_sound` (:2159, the gap-existence witness, from
  `AsanPlacement.free_gap_of_totals` plus `gap_weight_eq` / `RES_len` /
  `co_totsz`), `refuse_ok` (:2216) and `refuse_cont` (:2227, the refused
  child, rebuilt field-by-field because `AsanNodesLibE`'s `cs_ok_frame'` is
  out of reach here), `shadow_facts_new_ok` (:2322), `cs_ok_unhole` (:2463),
  `mmap_fixed_grant_cs1` (:2486) with its two read-backs
  `mmap_fixed_old_facts` (:2547) and `mmap_fixed_hole_facts` (:2573), the
  three `kn_rezero_*` knowledge lemmas (:3087, :3116, :3128 — one
  ten-constructor `kentry` case analysis, with `kn_unfill_clip_ok` as the
  shape template), and the Slice tail `vis_add_slice_ok` (:3150) and
  `slice_args` (:3198).  Thirteen declarations; this tree is complete.
  from `grant_cs1_ok` (:1798) — the four traps, all measured:
  - `cs1` must be introduced as a `let` and the goal `change`d to it, and
    the pieces `cs1.a_*` rewritten with `have Ha_x : cs1.a_x = … := rfl`
    before any `omega`: a projection of the `add_entry` literal does NOT
    reduce for `omega`/`simp`, it only reduces for `rfl`/`exact`, so the
    component equations are what make the arithmetic go through.
  - `if eager then … else …` on a `Bool` shows up as `if eager = true then
    … else …`, which `dsimp only` does NOT reduce ("made no progress" is an
    error here) and which `omega` then treats as an opaque atom.  Split with
    `cases eager` and discharge both layers explicitly (`rw [ite_eq_left (rfl :
    (true : Bool) = true)]`, `rw [ite_eq_right (by decide : ¬((false : Bool) =
    true))]`, and the same on the `(!eager)` inside `EG`).
  - a `->` hypothesis (`Hbudget : eager = true -> …`) is INVISIBLE to
    `omega`: extract it (`have hb := Hbudget rfl`) inside the branch.
  - `Int.lt_of_lt_of_le`'s implicit `c` is inferred from the SECOND
    argument, so a nested application gets the wrong `c`; split into two
    `have`s.  And `page_in_ranges_cons_out` (not a contradiction) is the
    right tool when the byte is ABOVE the region: `page_base x <= x`, so the
    left-of-the-region contradiction does not generalise upwards.
  from this stretch (measured, both cheap and decisive):
  - `null_kend_ok` / `escale_4096_denot` turn entirely on
    `simp only [two_pow_64, bv_unsigned] at *` applied to EVERY hypothesis
    (not just the goal) before `omega`, plus `Int.emod_eq_of_lt`;
    `Int.ediv_le_self` takes its divisor as the FIRST explicit argument
    (`Int.ediv_le_self 4096 h`), and the env accessor is the field `E.ev v`.
  - `overlap_sum_contained` must be proved by induction on the `seps`
    derivation (`induction Hs generalizing b s lo hi`), not on the list: the
    list induction leaves a `seps`/membership hypothesis that cannot be
    reverted.  After `induction Hs generalizing …` the hypothesis order is
    `b s lo hi`, then the reverted `Hin H1 H2 Hlh`, then the untouched `Hl`.
  - `AsanNodesLibE` is NOT imported here, so despite the `open` of its
    namespace its theorems (`cs_ok_refuse` …) are unreachable from this file.
  The rest of part 11 (the thirteen of the FINAL STRETCH above) is landed
  too, so nothing is deferred: see the note at the end of the file for the
  two measured traps that block closed (`Hknew` must be passed in tactic
  form, and `fixed_cs1`'s shadow list must be spelled with `kd`).
  for the next stretch (measured): `mmap_len_sound`,
  `null_kend_ok` and `escale_4096_denot` all turn on the same two traps —
  (a) `bv_unsigned a / 4096` needs `Int.ediv_le_self`'s IMPLICIT argument
  spelled `(a := …)` or `omega` sees `4096 / bv_unsigned a` instead, and
  (b) `bv_unsigned_range_u64` concludes `< two_pow_64` (an opaque `def` whose
  body is `2 ^ 64`), so every `omega` that mixes it with a `2 ^ 64` numeral
  must first `simp only [two_pow_64] at h` — including on the theorem's own
  hypotheses; `Int.emod_eq_of_lt` then closes the `%` introduced by
  `u_add64`/`u_mul64`.
  helpers added by this file (six more arrived with the
  `iv_subtract` page-discipline lemmas: `emod4096_sub` / `emod4096_add` /
  `ofInt_emod4096`, `min_sub_pos`, and the two "inequality half" lemmas
  `iv_subtract_left_ineq` / `iv_subtract_right_ineq`, split out because the
  `omega` calls that need `min`/`max` case splits must not share a context
  with the `mod 4096` hypotheses — `omega` unfolds `%` into divisions):
  `bv_ofInt_toNat` and
  `page_base_toNat` (the `ofInt` round trips the page arithmetic needs;
  `RefNodes.u64_roundtrip` is the other direction) and
  `page_in_iv_subtract_out` (the piece-level half of
  `page_in_ranges_subtract_out`, split out because the two directions have
  different case analyses).  Two aliases, `mkCfg` and `node_ok`,
  pin the `ShapeAlg` spelling of the two names `ShapeAlg` and `AsanAcct` both
  provide (the definitions are verbatim copies).
  1974), measured:
  - `obtain` DOES zeta-reduce the `let len := …` prefix of `mmap_len_sound`,
    so its nine facts come out in the explicit `page_round_up_Z (bv_unsigned
    (edenot E (reg cs 11)))` spelling — and that is the spelling `nZ`'s
    defining equation must use, or no `rw` matches it.
  - `omega` needs the page-round-up bounds in the goal's own spelling:
    `0 < nZ` is `0 < len ≤ nZ` by `page_round_up_Z_bounds`, not `omega`.
  - the placement-split `omega` must not see `min`/`%` at once: rewrite
    `Int.min_eq_left` / `Int.min_eq_right` into BOTH `hS2` and the goal and
    `clear` the `%` / `page_round_up_Z` hypotheses first.  Also
    `null_hint_grant_step`'s tuple is `K < a`, the floor-or-descent
    disjunction, `min ≤ Y`, `min % page_size = 0`, `min ≤ vm_mmap_base`,
    the split — convert with `simpa only [page_size, bv_unsigned]`.
  - `List.mem_append.mp HK` works where `rw [List.mem_append] at HK` cannot
    see through the `HAppend` instance on `null_kend … ++ kdisj_new …`.
  - `split at HK` on the `match m.am_base with | .ELit _ => [] | mb => …`
    inside `kdisj_new` gives exactly two goals and keeps `m.am_base` itself
    in the singleton, so no `cases` over the nine `expr` constructors (and
    no dependent-elimination trouble) is needed.
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.MmapSim
import LinuxSem.Common.RefNodes
import LinuxSem.Common.NoReserve
import LinuxSem.Common.AllocSim
import LinuxSem.Common.AsanCeil

namespace LinuxSem.Common.AsanNodesMmLib

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamExec
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AgentNodes
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.AxSymExec3B
open LinuxSem.Common.AxSymExec3Sound
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.BackingAlgebra
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.MmapSim
open LinuxSem.Common.AllocSim
open LinuxSem.Common.AsanCeil
open LinuxSem.Common.Nodes
open LinuxSem.Common.RefNodes
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork

/-- Alias: `ShapeAlg` and `AsanAcct` both spell the configuration
    constructor (they are verbatim copies); the file works in the `ShapeAlg`
    spelling, which is the one `TSet`/`config` come from. -/
abbrev mkCfg := ShapeAlg.mkCfg

/-- Alias, as `mkCfg`: the node interface. -/
abbrev node_ok := ShapeAlg.node_ok

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The entry FP state. -/
local instance asannodesmmlib_fx : PropExec.FPState := PropExec.fx0

/-! ## 1. The shared image hypothesis -/

/-- `RES_hull_def`: every reserved segment of the image lies inside the
    image hull. -/
def RES_hull_def (SEGS : List Segment) (A : atable) : Prop :=
  ∀ iv ∈ segments_reserved SEGS,
    A.img_lo ≤ bv_unsigned iv.1 ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ A.img_hi

/-! ## 2. Interval lists -/

/-- `in_ivs` is `covered`. -/
theorem in_ivs_covered (z : Int) (l : List (word × word)) :
    in_ivs z l = covered l z := by
  unfold in_ivs covered in_iv in_rng B S
  rfl

/-- `in_ivs` on a cons. -/
theorem in_ivs_cons (z : Int) (iv : word × word) (l : List (word × word)) :
    in_ivs z (iv :: l)
      = ((decide (bv_unsigned iv.1 ≤ z) && decide (z < bv_unsigned iv.1 + bv_unsigned iv.2))
          || in_ivs z l) := by
  unfold in_ivs
  rfl

/-- `in_ivs` on an append. -/
theorem in_ivs_app (z : Int) (l1 l2 : List (word × word)) :
    in_ivs z (l1 ++ l2) = (in_ivs z l1 || in_ivs z l2) := by
  unfold in_ivs
  exact List.any_append

/-- `in_ivs`, semantically. -/
theorem in_ivs_true' (z : Int) (l : List (word × word)) :
    in_ivs z l = true ↔
      ∃ iv, iv ∈ l ∧ bv_unsigned iv.1 ≤ z ∧ z < bv_unsigned iv.1 + bv_unsigned iv.2 :=
  AsanPlanSound.in_ivs_true z l

/-- `in_ivs`, semantically (negative form). -/
theorem in_ivs_false (z : Int) (l : List (word × word)) :
    in_ivs z l = false ↔
      ∀ iv, iv ∈ l → ¬ (bv_unsigned iv.1 ≤ z ∧ z < bv_unsigned iv.1 + bv_unsigned iv.2) := by
  constructor
  · intro H iv Hin Hz
    have T : in_ivs z l = true := (in_ivs_true' z l).mpr ⟨iv, Hin, Hz.1, Hz.2⟩
    rw [H] at T
    exact Bool.false_ne_true T
  · intro H
    cases E : in_ivs z l with
    | false => rfl
    | true =>
        obtain ⟨iv, Hin, H1, H2⟩ := (in_ivs_true' z l).mp E
        exact (H iv Hin ⟨H1, H2⟩).elim

/-- `sum_sizes` is `live_bytes`. -/
theorem sum_sizes_live (l : List (word × word)) : sum_sizes l = live_bytes l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, s⟩ := hd
      simp only [sum_sizes, live_bytes, ih]

/-- `sum_sizes` on an append. -/
theorem sum_sizes_app (l1 l2 : List (word × word)) :
    sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2 := by
  rw [sum_sizes_live, sum_sizes_live, sum_sizes_live]
  exact BackingAlgebra.live_bytes_app l1 l2

/-- `region_free`, read semantically (`RefNodes.region_free_In` /
    `region_free_intro` are the `Int` forms). -/
theorem region_free_sem (l : List (word × word)) (lo n : word) (z : Int)
    (Hrf : region_free l lo n = true) (Hn : 0 < bv_unsigned n)
    (Hz : bv_unsigned lo ≤ z ∧ z < bv_unsigned lo + bv_unsigned n) :
    in_ivs z l = false := by
  apply (in_ivs_false z l).mpr
  rintro ⟨b, s⟩ Hin ⟨h1, h2⟩
  dsimp only at h1 h2
  simp only [bv_unsigned] at *
  have Hov := RefNodes.region_free_In l lo n b s Hrf Hin
  omega

/-- `region_free` on an append. -/
theorem region_free_app (l1 l2 : List (word × word)) (lo n : word) :
    region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n) := by
  induction l1 with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, s⟩ := hd
      simp only [List.cons_append, region_free, ih, Bool.and_assoc]

/-- `map_contains`, semantically. -/
theorem map_contains_intro (l : List (word × word)) (lo n b s : word)
    (Hin : (b, s) ∈ l) (H1 : bv_unsigned b ≤ bv_unsigned lo)
    (H2 : bv_unsigned lo + bv_unsigned n ≤ bv_unsigned b + bv_unsigned s) :
    map_contains l lo n = true := by
  unfold map_contains
  rw [List.any_eq_true]
  refine ⟨(b, s), Hin, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨H1, H2⟩

/-- `map_has`, syntactically. -/
theorem map_has_intro (l : List (word × word)) (lo n : word) (Hin : (lo, n) ∈ l) :
    map_has l lo n = true := by
  unfold map_has
  rw [List.any_eq_true]
  refine ⟨(lo, n), Hin, ?_⟩
  simp

/-! ## 3. The backing meter -/

/-- `eager_used`, semantically. -/
theorem eager_used_sem (m : Model) (Hwf : model_ivs_wf m) :
    eager_used m
      = sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps := by
  have H := vm_backing_used_sem m Hwf
  rw [vm_backing_used_split] at H
  omega

/-- The materialized pages fit in the allowed set. -/
theorem mat_pages_le_A_bytes (A : List (Int × Int)) (m : Model) (HM : MInv A m)
    (Hwf : A_wf A) : ((m_vm_materialized m).length : Int) * page_size ≤ A_bytes A :=
  allowed_pages_bound A (m_vm_materialized m) Hwf HM.minv_nodup HM.minv_aligned
    HM.minv_allowed

/-- Backing use is eager use plus the allowed set. -/
theorem vm_backing_used_le (A : List (Int × Int)) (m : Model) (HM : MInv A m)
    (Hwf : A_wf A) : vm_backing_used m ≤ eager_used m + A_bytes A := by
  have H := mat_pages_le_A_bytes A m HM Hwf
  rw [vm_backing_used_split]
  omega

/-- Backing use is within the ledger limit. -/
theorem vm_backing_used_limit (A : List (Int × Int)) (m : Model) (HM : MInv A m)
    (Hwf : A_wf A) : vm_backing_used m ≤ (m_vmmaps m).vm_limit := by
  have H1 := vm_backing_used_le A m HM Hwf
  have H2 := HM.minv_budget
  omega

/-- Monotonicity of `sum_count` in the cut list. -/
theorem sum_count_negb_covered_mono (C C' l : List (word × word))
    (H : ∀ x, covered C x = true → covered C' x = true) :
    sum_count (fun x => !(covered C' x)) l ≤ sum_count (fun x => !(covered C x)) l := by
  apply sum_count_mono
  intro x Hx
  cases hc : covered C x with
  | false => rfl
  | true =>
      rw [H x hc] at Hx
      exact Bool.noConfusion Hx

/-! ## 4. `maps_subtract`: pieces, survivors, pages -/

/-- `ofInt` of a 64-bit value, read back. -/
theorem bv_ofInt_toNat (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  bv_unsigned_Z_to_bv_u64 z ⟨h0, h1⟩

/-- A piece of `iv_subtract` sits inside the original interval and outside
    the cut. -/
theorem iv_subtract_pieces (a sz : word) (lo hi : Int) (q : word × word)
    (Hwf : iv_wf (a, sz)) (Hin : q ∈ iv_subtract a sz lo hi) :
    bv_unsigned a ≤ bv_unsigned q.1 ∧
      bv_unsigned q.1 + bv_unsigned q.2 ≤ bv_unsigned a + bv_unsigned sz ∧
      (bv_unsigned q.1 + bv_unsigned q.2 ≤ lo ∨ hi ≤ bv_unsigned q.1) := by
  obtain ⟨qz, qs⟩ := q
  simp only [iv_wf, B, S, Prod.fst, Prod.snd] at Hwf ⊢
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  simp only [bv_unsigned] at *
  unfold iv_subtract at Hin
  dsimp only at Hin
  by_cases h1 : (a.toNat : Int) < lo
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · simp only [ite_eq_left h1, ite_eq_left h2, List.mem_append, List.mem_singleton,
        Prod.mk.injEq] at Hin
      rcases Hin with ⟨hqz1, hqs1⟩ | ⟨hqz2, hqs2⟩
      · rw [hqz1, hqs1]
        have hb : ((BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
            = min (sz.toNat : Int) (lo - (a.toNat : Int)) :=
          bv_ofInt_toNat _ (by omega) (by omega)
        rw [hb]
        omega
      · rw [hqz2, hqs2]
        have hb : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
            = max (a.toNat : Int) hi := bv_ofInt_toNat _ (by omega) (by omega)
        have hb2 : ((BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int)
              - max (a.toNat : Int) hi)).toNat : Int)
            = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi :=
          bv_ofInt_toNat _ (by omega) (by omega)
        rw [hb, hb2]
        omega
    · simp only [ite_eq_left h1, ite_eq_right h2, List.append_nil, List.mem_singleton,
        Prod.mk.injEq] at Hin
      obtain ⟨hqz, hqs⟩ := Hin
      rw [hqz, hqs]
      have hb : ((BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
          = min (sz.toNat : Int) (lo - (a.toNat : Int)) :=
        bv_ofInt_toNat _ (by omega) (by omega)
      rw [hb]
      omega
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · simp only [ite_eq_right h1, ite_eq_left h2, List.nil_append, List.mem_singleton,
        Prod.mk.injEq] at Hin
      obtain ⟨hqz, hqs⟩ := Hin
      rw [hqz, hqs]
      have hb : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
          = max (a.toNat : Int) hi := bv_ofInt_toNat _ (by omega) (by omega)
      have hb2 : ((BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int)
            - max (a.toNat : Int) hi)).toNat : Int)
          = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi :=
        bv_ofInt_toNat _ (by omega) (by omega)
      rw [hb, hb2]
      omega
    · simp only [ite_eq_right h1, ite_eq_right h2, List.nil_append, List.not_mem_nil] at Hin

/-- A piece of `maps_subtract` sits inside one entry of the ledger and outside
    the cut. -/
theorem maps_subtract_pieces (l : List (word × word)) (lo hi : Int) (q : word × word)
    (Hwf : ivs_wf l) (Hin : q ∈ maps_subtract l lo hi) :
    ∃ r, r ∈ l ∧ bv_unsigned r.1 ≤ bv_unsigned q.1 ∧
      bv_unsigned q.1 + bv_unsigned q.2 ≤ bv_unsigned r.1 + bv_unsigned r.2 ∧
      (bv_unsigned q.1 + bv_unsigned q.2 ≤ lo ∨ hi ≤ bv_unsigned q.1) := by
  induction l with
  | nil => simp [maps_subtract] at Hin
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      obtain ⟨Ha, Hl⟩ := ivs_wf_cons_inv _ _ Hwf
      simp only [maps_subtract] at Hin
      rw [List.mem_append] at Hin
      rcases Hin with Hin | Hin
      · exact ⟨(a, sz), by simp, iv_subtract_pieces a sz lo hi q Ha Hin⟩
      · obtain ⟨r, Hr, H1, H2, H3⟩ := ih Hl Hin
        exact ⟨r, List.mem_cons_of_mem _ Hr, H1, H2, H3⟩

/-- A nonempty interval disjoint from a nonempty cut survives verbatim. -/
theorem iv_subtract_disjoint (a sz : word) (lo hi : Int) (Hlh : lo < hi)
    (Hsz : 0 < bv_unsigned sz)
    (Hd : bv_unsigned a + bv_unsigned sz ≤ lo ∨ hi ≤ bv_unsigned a) :
    iv_subtract a sz lo hi = [(a, sz)] := by
  simp only [bv_unsigned] at *
  rcases Hd with h | h
  · exact RefNodes.iv_subtract_disjoint a sz lo hi Hsz (by omega) (Or.inr h)
  · exact RefNodes.iv_subtract_disjoint a sz lo hi Hsz (by omega) (Or.inl h)

/-- A nonempty interval disjoint from a nonempty cut survives `maps_subtract`. -/
theorem maps_subtract_keeps (l : List (word × word)) (b s : word) (lo hi : Int)
    (Hlh : lo < hi) (Hs : 0 < bv_unsigned s) (Hin : (b, s) ∈ l)
    (Hd : bv_unsigned b + bv_unsigned s ≤ lo ∨ hi ≤ bv_unsigned b) :
    (b, s) ∈ maps_subtract l lo hi := by
  induction l with
  | nil => simp at Hin
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [maps_subtract, List.mem_append]
      rcases List.mem_cons.mp Hin with h | h
      · injection h with h1 h2
        subst h1 h2
        left
        rw [iv_subtract_disjoint b s lo hi Hlh Hs Hd]
        simp
      · right
        exact ih h

/-- `page_in_ranges` on a cons. -/
theorem page_in_ranges_cons (p : word) (iv : word × word) (l : List (word × word)) :
    page_in_ranges p (iv :: l)
      = ((decide (bv_unsigned iv.1 ≤ bv_unsigned p)
            && decide (bv_unsigned p + page_size ≤ bv_unsigned iv.1 + bv_unsigned iv.2))
          || page_in_ranges p l) :=
  rfl

/-- `page_in_ranges` on an append. -/
theorem page_in_ranges_app (p : word) (l1 l2 : List (word × word)) :
    page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2) := by
  unfold page_in_ranges
  exact List.any_append

/-- `page_in_ranges`, semantically. -/
theorem page_in_ranges_true (p : word) (l : List (word × word)) :
    page_in_ranges p l = true ↔
      ∃ iv ∈ l, bv_unsigned iv.1 ≤ bv_unsigned p ∧
        bv_unsigned p + page_size ≤ bv_unsigned iv.1 + bv_unsigned iv.2 := by
  unfold page_in_ranges
  rw [List.any_eq_true]
  constructor
  · rintro ⟨iv, Hin, Hb⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hb
    exact ⟨iv, Hin, Hb.1, Hb.2⟩
  · rintro ⟨iv, Hin, H1, H2⟩
    exact ⟨iv, Hin, by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨H1, H2⟩⟩

/-- `page_in_ranges`, semantically (negative form). -/
theorem page_in_ranges_false (p : word) (l : List (word × word)) :
    page_in_ranges p l = false ↔
      ∀ iv ∈ l, ¬ (bv_unsigned iv.1 ≤ bv_unsigned p ∧
        bv_unsigned p + page_size ≤ bv_unsigned iv.1 + bv_unsigned iv.2) := by
  constructor
  · intro H iv Hin Hc
    have T : page_in_ranges p l = true := (page_in_ranges_true p l).mpr ⟨iv, Hin, Hc.1, Hc.2⟩
    rw [H] at T
    exact Bool.false_ne_true T
  · intro H
    cases E : page_in_ranges p l with
    | false => rfl
    | true =>
        obtain ⟨iv, Hin, H1, H2⟩ := (page_in_ranges_true p l).mp E
        exact (H iv Hin ⟨H1, H2⟩).elim

/-- A page inside a lazy range covers its bytes. -/
theorem page_in_ranges_covers (p : word) (l : List (word × word)) (z : Int)
    (Hp : page_in_ranges p l = true)
    (Hz : bv_unsigned p ≤ z ∧ z < bv_unsigned p + page_size) :
    in_ivs z l = true := by
  obtain ⟨iv, Hin, H1, H2⟩ := (page_in_ranges_true p l).mp Hp
  refine (in_ivs_true' z l).mpr ⟨iv, Hin, ?_, ?_⟩ <;> omega

/-- The page base of a word, in `Int`. -/
theorem page_base_toNat (x : word) :
    ((page_base x).toNat : Int) = (x.toNat : Int) / 4096 * 4096 := by
  have hx := bv_unsigned_range_u64 x
  have hge : 0 ≤ (x.toNat : Int) / 4096 * 4096 :=
    Int.mul_nonneg (Int.ediv_nonneg (by omega) (by decide)) (by decide)
  have hlt : (x.toNat : Int) / 4096 * 4096 < 2 ^ 64 := by
    have h := Int.ediv_mul_le (x.toNat : Int) (by decide : (4096 : Int) ≠ 0)
    omega
  unfold page_base page_base_of
  simp only [page_size]
  exact bv_ofInt_toNat _ hge hlt

/-- The page of a byte: inside an aligned range iff the byte is. -/
theorem page_base_facts (a : word) :
    bv_unsigned (page_base a) ≤ bv_unsigned a ∧
      bv_unsigned a < bv_unsigned (page_base a) + 4096 ∧
      bv_unsigned (page_base a) % 4096 = 0 :=
  AsanPlanSound.page_base_le a

/-- A byte inside an aligned range has its whole page inside. -/
theorem page_of_byte_in_aligned (x : word) (lo hi : Int)
    (Hlo : lo % 4096 = 0) (Hhi : hi % 4096 = 0)
    (Hx : lo ≤ bv_unsigned x ∧ bv_unsigned x < hi) :
    lo ≤ bv_unsigned (page_base x) ∧ bv_unsigned (page_base x) + 4096 ≤ hi := by
  have hq := page_base_toNat x
  have hxr := bv_unsigned_range_u64 x
  simp only [bv_unsigned] at Hx ⊢
  have hlod : (4096 : Int) ∣ lo := Int.dvd_of_emod_eq_zero Hlo
  have hhid : (4096 : Int) ∣ hi := Int.dvd_of_emod_eq_zero Hhi
  have hlo' : lo / 4096 * 4096 = lo := Int.ediv_mul_cancel hlod
  have hhi' : hi / 4096 * 4096 = hi := Int.ediv_mul_cancel hhid
  constructor
  · rw [hq, ← hlo']
    have h := Int.ediv_le_ediv (by decide : (0 : Int) < 4096) Hx.1
    omega
  · rw [hq, ← hhi']
    have h := Int.ediv_lt_ediv_of_lt Hx.2 hhid (by decide : (0 : Int) < 4096)
    have h2 : (x.toNat : Int) / 4096 + 1 ≤ hi / 4096 := by omega
    omega

/-- A byte outside an aligned range has its whole page outside. -/
theorem page_of_byte_out_aligned (x : word) (lo hi : Int)
    (Hlo : lo % 4096 = 0) (Hhi : hi % 4096 = 0)
    (Hx : bv_unsigned x < lo ∨ hi ≤ bv_unsigned x) :
    bv_unsigned (page_base x) + 4096 ≤ lo ∨ hi ≤ bv_unsigned (page_base x) := by
  have hq := page_base_toNat x
  have hxr := bv_unsigned_range_u64 x
  simp only [bv_unsigned] at Hx ⊢
  have hlod : (4096 : Int) ∣ lo := Int.dvd_of_emod_eq_zero Hlo
  have hhid : (4096 : Int) ∣ hi := Int.dvd_of_emod_eq_zero Hhi
  have hlo' : lo / 4096 * 4096 = lo := Int.ediv_mul_cancel hlod
  have hhi' : hi / 4096 * 4096 = hi := Int.ediv_mul_cancel hhid
  rw [hq]
  rcases Hx with h | h
  · left
    rw [← hlo']
    have hle : (x.toNat : Int) / 4096 + 1 ≤ lo / 4096 := by
      have h1 := Int.ediv_lt_ediv_of_lt h hlod (by decide : (0 : Int) < 4096)
      omega
    omega
  · right
    rw [← hhi']
    have hle : hi / 4096 ≤ (x.toNat : Int) / 4096 :=
      Int.ediv_le_ediv (by decide : (0 : Int) < 4096) h
    omega

/-- A page inside an aligned fresh range is lazy once the range is consed. -/
theorem page_in_ranges_cons_in (p a n : word) (l : List (word × word))
    (H1 : bv_unsigned a ≤ bv_unsigned p)
    (H2 : bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned n) :
    page_in_ranges p ((a, n) :: l) = true := by
  rw [page_in_ranges_cons, Bool.or_eq_true]
  left
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true H1, decide_eq_true H2⟩

/-- A page outside a range is unaffected by consing it. -/
theorem page_in_ranges_cons_out (p a n : word) (l : List (word × word))
    (H : bv_unsigned p + page_size ≤ bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned p)
    (Hn : 0 < bv_unsigned n) :
    page_in_ranges p ((a, n) :: l) = page_in_ranges p l := by
  rw [page_in_ranges_cons]
  have hfalse : (decide (bv_unsigned a ≤ bv_unsigned p)
      && decide (bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned n)) = false := by
    cases hx : (decide (bv_unsigned a ≤ bv_unsigned p)
        && decide (bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned n)) with
    | false => rfl
    | true =>
        rw [Bool.and_eq_true] at hx
        have h1 := of_decide_eq_true hx.1
        have h2 := of_decide_eq_true hx.2
        simp only [page_size] at h1 h2 H ⊢
        rcases H with h | h <;> omega
  rw [hfalse, Bool.false_or]

/-- A page wholly outside the cut meets `iv_subtract` exactly when it meets
    the interval (the piece-level half of `page_in_ranges_subtract_out`). -/
theorem page_in_iv_subtract_out (p a sz : word) (lo hi : Int)
    (Hwf : iv_wf (a, sz))
    (Hout : bv_unsigned p + page_size ≤ lo ∨ hi ≤ bv_unsigned p) :
    page_in_ranges p (iv_subtract a sz lo hi)
      = (decide (bv_unsigned a ≤ bv_unsigned p) &&
         decide (bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned sz)) := by
  have Hwf' := Hwf
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  have hp := bv_unsigned_range_u64 p
  simp only [iv_wf, B, S, bv_unsigned, page_size] at Hwf Hout
  cases hent : (decide (bv_unsigned a ≤ bv_unsigned p) &&
      decide (bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned sz)) with
  | false =>
      rw [page_in_ranges_false]
      intro q Hq ⟨hq1, hq2⟩
      obtain ⟨h11, h12, -⟩ := iv_subtract_pieces a sz lo hi q Hwf' Hq
      simp only [bv_unsigned, page_size, Prod.fst, Prod.snd] at h11 h12 hq1 hq2
      have hcont : (decide (bv_unsigned a ≤ bv_unsigned p) &&
          decide (bv_unsigned p + page_size ≤ bv_unsigned a + bv_unsigned sz)) = true := by
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · rw [decide_eq_true_iff]; simp only [bv_unsigned]; omega
        · rw [decide_eq_true_iff]; simp only [bv_unsigned, page_size]; omega
      rw [hent] at hcont
      exact Bool.false_ne_true hcont
  | true =>
      rw [Bool.and_eq_true] at hent
      have hp1 := of_decide_eq_true hent.1
      have hp2 := of_decide_eq_true hent.2
      simp only [bv_unsigned, page_size] at hp1 hp2
      by_cases h1 : (a.toNat : Int) < lo
      · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
        · unfold iv_subtract
          dsimp only
          rw [ite_eq_left h1, ite_eq_left h2]
          rcases Hout with ho | ho
          · refine (page_in_ranges_true p _).mpr
              ⟨(a, BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))),
                ?_, ?_, ?_⟩
            · simp only [List.mem_append, List.mem_singleton]; simp
            · simp only [bv_unsigned, page_size, Prod.fst, Prod.snd]; omega
            · simp only [bv_unsigned, Prod.fst, Prod.snd]
              rw [bv_ofInt_toNat _ (by omega) (by omega)]
              simp only [page_size]; omega
          · refine (page_in_ranges_true p _).mpr
              ⟨(BitVec.ofInt 64 (max (a.toNat : Int) hi),
                BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int)
                  - max (a.toNat : Int) hi)), ?_, ?_, ?_⟩
            · simp only [List.mem_append, List.mem_singleton]; simp
            · simp only [bv_unsigned, Prod.fst, Prod.snd]
              rw [bv_ofInt_toNat _ (by omega) (by omega)]
              omega
            · simp only [bv_unsigned, Prod.fst, Prod.snd]
              rw [bv_ofInt_toNat _ (by omega) (by omega),
                bv_ofInt_toNat _ (by omega) (by omega)]
              simp only [page_size]; omega
        · unfold iv_subtract
          dsimp only
          rw [ite_eq_left h1, ite_eq_right h2]
          have ho : (p.toNat : Int) + 4096 ≤ lo := by
            rcases Hout with ho | ho
            · exact ho
            · omega
          refine (page_in_ranges_true p _).mpr
            ⟨(a, BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))),
              ?_, ?_, ?_⟩
          · simp [List.append_nil, List.mem_singleton]
          · simp only [bv_unsigned, page_size, Prod.fst, Prod.snd]; omega
          · simp only [bv_unsigned, Prod.fst, Prod.snd]
            rw [bv_ofInt_toNat _ (by omega) (by omega)]
            simp only [page_size]; omega
      · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
        · unfold iv_subtract
          dsimp only
          rw [ite_eq_right h1, ite_eq_left h2]
          have ho : hi ≤ (p.toNat : Int) := by
            rcases Hout with ho | ho
            · omega
            · exact ho
          refine (page_in_ranges_true p _).mpr
            ⟨(BitVec.ofInt 64 (max (a.toNat : Int) hi),
              BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int)
                - max (a.toNat : Int) hi)), ?_, ?_, ?_⟩
          · simp [List.nil_append, List.mem_singleton]
          · simp only [bv_unsigned, Prod.fst, Prod.snd]
            rw [bv_ofInt_toNat _ (by omega) (by omega)]
            omega
          · simp only [bv_unsigned, Prod.fst, Prod.snd]
            rw [bv_ofInt_toNat _ (by omega) (by omega),
              bv_ofInt_toNat _ (by omega) (by omega)]
            simp only [page_size]; omega
        · -- the entry lies inside the cut and contains the page: impossible
          unfold iv_subtract
          dsimp only
          rw [ite_eq_right h1, ite_eq_right h2]
          exfalso
          simp only [page_size] at *
          rcases Hout with h | h <;> omega

/-- Pages wholly outside the cut are unaffected by `maps_subtract`. -/
theorem page_in_ranges_subtract_out (p : word) (l : List (word × word)) (lo hi : Int)
    (Hwf : ivs_wf l) (Hlh : lo ≤ hi)
    (Hout : bv_unsigned p + page_size ≤ lo ∨ hi ≤ bv_unsigned p) :
    page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      obtain ⟨Ha, Hl⟩ := ivs_wf_cons_inv _ _ Hwf
      simp only [maps_subtract, page_in_ranges_app, page_in_ranges_cons,
        ih Hl, page_in_iv_subtract_out p a sz lo hi Ha Hout]

/-- Pages inside the cut are no longer lazy (the page base is cut away). -/
theorem page_in_ranges_subtract_in (p : word) (l : List (word × word)) (lo hi : Int)
    (Hwf : ivs_wf l) (Hp : lo ≤ bv_unsigned p ∧ bv_unsigned p < hi) :
    page_in_ranges p (maps_subtract l lo hi) = false := by
  rw [page_in_ranges_false]
  intro q Hq ⟨h1, h2⟩
  obtain ⟨r, -, hr1, hr2, hr3⟩ := maps_subtract_pieces l lo hi q Hwf Hq
  simp only [bv_unsigned, page_size, Prod.fst, Prod.snd] at h1 h2 hr1 hr2 hr3 Hp ⊢
  rcases hr3 with h | h <;> omega

/-! ## 5. Memory overlays, pointwise -/

/-- `zfill` inside the range is zero. -/
theorem zfill_in (a n : word) (m : word → Option byte) (x : word)
    (Hx : bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + bv_unsigned n) :
    zfill a n m x = some (Z_to_bv 8 0) := by
  unfold zfill MmapSim.zmem
  simp only [bv_unsigned] at Hx
  rw [ite_eq_left (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega)]

/-- `unfill` inside the range is `none`. -/
theorem unfill_in (a n : word) (m : word → Option byte) (x : word)
    (Hx : bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + bv_unsigned n) :
    unfill a n m x = none := by
  unfold unfill
  simp only [bv_unsigned] at Hx
  rw [ite_eq_left (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega)]

/-- `mrestrict`, pointwise. -/
theorem mrestrict_at (H : word → Bool) (M : word → Option byte) (x : word) :
    mrestrict H M x = if H x then none else M x :=
  rfl

/-! ## 6. AP-level facts -/

/-- The pc after a 4-byte instruction. -/
theorem v_addi_pc (p : Int) (H0 : 0 ≤ p) (H4 : p + 4 < 2 ^ 64) :
    v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4) := by
  unfold v_addi
  rw [bv_ofInt_toNat p H0 (by omega)]

/-- `is_ecall_at`, unfolded. -/
theorem is_ecall_at_sound (SEGS : List Segment) (cs : acs)
    (H : is_ecall_at SEGS cs = true) :
    ∃ w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = some w ∧ is_ecall w = true ∧
      0 ≤ pc cs ∧ pc cs + 4 < 2 ^ 64 := by
  unfold is_ecall_at at H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨⟨HH1, HH2⟩, HH3⟩ := H
  cases hw : fetch_word SEGS (Z_to_bv 64 (pc cs)) with
  | none =>
      rw [hw] at HH3
      exact (Bool.false_ne_true HH3).elim
  | some w =>
      rw [hw] at HH3
      exact ⟨w, rfl, HH3, HH1, by simpa [two64] using HH2⟩

/-- `page_up` is the state's `page_round_up_Z`. -/
theorem page_up_eq (len : Int) : page_up len = page_round_up_Z len := by
  unfold page_up page_round_up_Z page_size
  rw [show len + 4096 - 1 = len + 4095 from by omega]

/-! ## 7. Valuation bookkeeping (argument-free copies of `AsanPlanSound` lemmas) -/

/-- Agreement is monotone in the bound. -/
theorem env_agree_le' (b b' : Nat) (E E' : env) (H : env_agree b' E E') (Hle : b ≤ b') :
    env_agree b E E' :=
  env_agree_le b b' E E' H Hle

/-- Agreement is reflexive. -/
theorem env_agree_refl' (b : Nat) (E : env) : env_agree b E E :=
  env_agree_refl b E

/-- Agreement is transitive. -/
theorem env_agree_trans' (b : Nat) (E1 E2 E3 : env) (H1 : env_agree b E1 E2)
    (H2 : env_agree b E2 E3) : env_agree b E1 E3 :=
  env_agree_trans b E1 E2 E3 H1 H2

/-- Extending at the bound agrees below it. -/
theorem ext1_agree'' (E : env) (v : Nat) (a : word) : env_agree v E (ext1 E v a) :=
  ext1_agree E v a

/-- `sr_vars_lt` gives the bound on each slot. -/
theorem nth_sr_vars_lt' (b : Nat) (sr : List expr) (r : Nat)
    (H : AsanPlanCore.sr_vars_lt b sr = true) (Hr : r < 32) :
    AsanPlanCore.expr_vars_lt b (sr.getD r (.ELit 0)) = true :=
  AsanPlanSound.nth_sr_vars_lt b sr r H Hr

/-- A literal's length. -/
theorem elenZ_lit'' (E : env) (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    elenZ E (.ELit z) = z :=
  elenZ_lit E z Hz

/-! ## 8. Reflexivity of the syntactic equalities -/

/-- `aluop_eqb` is reflexive. -/
theorem aluop_eqb_refl (o : AluOp) : aluop_eqb o o = true :=
  AsanPlanSound.aluop_eqb_refl' o

/-- `mulop_eqb` is reflexive. -/
theorem mulop_eqb_refl (o : MulOp) : mulop_eqb o o = true :=
  AsanPlanSound.mulop_eqb_refl' o

/-- `expr_eqb` is reflexive. -/
theorem expr_eqb_refl (e : expr) : expr_eqb e e = true :=
  AsanPlanSound.expr_eqb_refl' e

/-- `amap_eqb` is reflexive. -/
theorem amap_eqb_refl (m : amap) : amap_eqb m m = true :=
  AsanPlanSound.amap_eqb_refl' m

/-! ## 9. List lemmas for munmap (filters / permutations of the visible ranges) -/

/-- Filtering a pairwise-disjoint ledger keeps it so. -/
theorem seps_filter (f : word × word → Bool) (l : List (word × word)) (H : seps l) :
    seps (List.filter f l) := by
  induction H with
  | nil => exact seps.nil
  | @cons p l Hf Hl ih =>
      rw [List.filter_cons]
      by_cases hp : f p = true
      · rw [ite_eq_left hp]
        exact seps.cons p _ (fun q hq => Hf q (List.mem_filter.mp hq).1) ih
      · rw [ite_eq_right hp]
        exact ih

/-- Filtering cannot increase the total size. -/
theorem sum_sizes_filter_le (f : word × word → Bool) (l : List (word × word)) :
    sum_sizes (List.filter f l) ≤ sum_sizes l := by
  induction l with
  | nil => simp [sum_sizes]
  | cons hd tl ih =>
      obtain ⟨b, s⟩ := hd
      have hs := bv_unsigned_range_u64 s
      rw [List.filter_cons]
      by_cases hf : f (b, s) = true
      · rw [ite_eq_left hf]
        simp only [sum_sizes, bv_unsigned]
        omega
      · rw [ite_eq_right hf]
        simp only [sum_sizes, bv_unsigned]
        omega

/-- `A_bytes` is additive over concatenation. -/
theorem A_bytes_app' (l1 l2 : List (Int × Int)) : A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2 :=
  A_bytes_app l1 l2

/-- Splitting a list by a predicate and re-concatenating does not change
    `A_bytes` of a flat map. -/
theorem A_bytes_flat_map_split {T : Type} (f : T → List (Int × Int)) (g : T → Bool)
    (l r : List T) :
    A_bytes (List.flatMap f (List.filter g l ++ (List.filter (fun x => !(g x)) l ++ r)))
      = A_bytes (List.flatMap f (l ++ r)) := by
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, A_bytes_app', A_bytes_app',
    A_bytes_app']
  suffices h : A_bytes (List.flatMap f (List.filter g l))
      + A_bytes (List.flatMap f (List.filter (fun x => !(g x)) l))
      = A_bytes (List.flatMap f l) by omega
  induction l with
  | nil => simp [A_bytes]
  | cons x tl ih =>
      have hc : ∀ L : List T, A_bytes (List.flatMap f (x :: L))
          = A_bytes (f x) + A_bytes (List.flatMap f L) := by
        intro L
        rw [List.flatMap_cons, A_bytes_app']
      rw [List.filter_cons, List.filter_cons]
      by_cases hg : g x = true
      · rw [ite_eq_left hg, ite_eq_right (by simp [hg]), hc, hc]
        omega
      · rw [ite_eq_right hg, ite_eq_left (by simp [hg]), hc, hc]
        omega

/-- The same split, elementwise. -/
theorem in_flat_map_split {T U : Type} (f : T → List U) (g : T → Bool) (l r : List T)
    (y : U) :
    (y ∈ List.flatMap f (List.filter g l ++ (List.filter (fun x => !(g x)) l ++ r)))
      ↔ y ∈ List.flatMap f (l ++ r) := by
  rw [List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, ?_, hy⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mp hx).1)
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append.mpr (Or.inl (List.mem_filter.mp hx).1)
      · exact List.mem_append.mpr (Or.inr hx)
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, ?_, hy⟩
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_append]
      by_cases hg : g x = true
      · left
        exact List.mem_filter.mpr ⟨hx, hg⟩
      · right
        rw [List.mem_append]
        left
        exact List.mem_filter.mpr ⟨hx, by cases hgg : g x with
          | false => rfl
          | true => exact absurd hgg hg⟩
    · rw [List.mem_append]
      right
      rw [List.mem_append]
      right
      exact hx

/-- Counting over a filter costs at most counting over the whole list. -/
theorem sum_count_filter_le (P P' : Int → Bool) (f : word × word → Bool)
    (l : List (word × word))
    (H : ∀ q ∈ l, f q = true →
      ∀ x, B q ≤ x → x < B q + S q → P' x = P x) :
    sum_count P' (List.filter f l) ≤ sum_count P l := by
  induction l with
  | nil => simp [sum_count]
  | cons q tl ih =>
      have ih' : sum_count P' (List.filter f tl) ≤ sum_count P tl :=
        ih (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))
      rw [List.filter_cons]
      by_cases hf : f q = true
      · rw [ite_eq_left hf]
        have hq : iv_count P' q ≤ iv_count P q := by
          have heq : iv_count P' q = iv_count P q := by
            unfold iv_count
            exact zcount_ext P' P (B q) (S q).toNat
              (fun x h1 h2 => H q (by simp) hf x h1 (by
                have hS : (((S q).toNat : Nat) : Int) = S q :=
                  Int.toNat_of_nonneg (S_range q).1
                omega))
          omega
        simp only [sum_count]
        omega
      · rw [ite_eq_right hf]
        have hnn : 0 ≤ iv_count P q := zcount_nonneg P (B q) (S q).toNat
        simp only [sum_count]
        omega

/-- A filter that agrees pointwise after the map. -/
theorem filter_map_ext {T U : Type} (h : T → U) (f : U → Bool) (f' : T → Bool)
    (l : List T) (H : ∀ x ∈ l, f (h x) = f' x) :
    List.filter f (l.map h) = (List.filter f' l).map h := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
      have hx := H x (by simp)
      have htl : ∀ y ∈ tl, f (h y) = f' y := fun y hy => H y (by simp [hy])
      rw [List.map_cons, List.filter_cons, List.filter_cons, hx, ih htl]
      by_cases hf : f' x = true
      · rw [ite_eq_left hf, ite_eq_left hf, List.map_cons]
      · rw [ite_eq_right hf, ite_eq_right hf]

/-! ## 10. Spec syscall nodes for mmap (NULL hint / FIXED over a free range)
        and mprotect: two resolutions REFUSED (ENOMEM) | GRANTED,
        lazy-tolerant (no `m_vm_lazy = []` premise: these effects report no
        user-memory access), conclusions in `SpinAlg.srealizes`. -/

/-- `mmap_flags_core` of `MAP_PRIVATE|MAP_ANONYMOUS`. -/
theorem mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34 := by decide

/-- `mmap_flags_core` of `MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED`. -/
theorem mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50 := by decide

/-- `mmap_flags_core` at MAP_NORESERVE|MAP_PRIVATE|MAP_ANONYMOUS. -/
theorem mmap_flags_core_4022 : mmap_flags_core (Z_to_bv 64 16418) = 34 := by decide

/-- `mmap_flags_core` at MAP_NORESERVE|MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED. -/
theorem mmap_flags_core_4032 : mmap_flags_core (Z_to_bv 64 16434) = 50 := by decide

/-- `mmap_noreserve_b` of `MAP_PRIVATE|MAP_ANONYMOUS`. -/
theorem mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false := by decide

/-- `mmap_noreserve_b` of `MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED`. -/
theorem mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false := by decide

/-- `mmap_noreserve_b` at MAP_NORESERVE|MAP_PRIVATE|MAP_ANONYMOUS. -/
theorem mmap_noreserve_b_4022 : mmap_noreserve_b (Z_to_bv 64 16418) = true := by decide

/-- `mmap_noreserve_b` at MAP_NORESERVE|MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED. -/
theorem mmap_noreserve_b_4032 : mmap_noreserve_b (Z_to_bv 64 16434) = true := by decide

/-- A plain (non-NORESERVE) mapping leaves the model unchanged. -/
theorem with_mmap_backing_plain (flags a n : word) (m : Model)
    (H : mmap_noreserve_b flags = false) : with_mmap_backing flags a n m = m := by
  unfold with_mmap_backing
  rw [H]
  rfl

/-- A NORESERVE mapping records its range in the lazy ledger. -/
theorem with_mmap_backing_lazy (flags a n : word) (m : Model)
    (H : mmap_noreserve_b flags = true) : with_mmap_backing flags a n m = vm_add_lazy a n m := by
  unfold with_mmap_backing
  rw [H]
  rfl

/-- `with_mmap_backing` leaves `m_halted` alone. -/
theorem with_mmap_backing_halted (flags a n : word) (m : Model) :
    m_halted (with_mmap_backing flags a n m) = m_halted m := by
  unfold with_mmap_backing
  cases mmap_noreserve_b flags <;> rfl

/-- `with_mmap_backing` leaves `m_fs` alone. -/
theorem with_mmap_backing_fs (flags a n : word) (m : Model) :
    m_fs (with_mmap_backing flags a n m) = m_fs m := by
  unfold with_mmap_backing
  cases mmap_noreserve_b flags <;> rfl

/-- `with_mmap_backing` leaves `m_vmmaps` alone. -/
theorem with_mmap_backing_vmmaps (flags a n : word) (m : Model) :
    m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m := by
  unfold with_mmap_backing
  cases mmap_noreserve_b flags <;> rfl

/-- The shape gates for a symbolic `flags` (rw shape). -/
theorem mmap_gates_core34 (flags : word) (Hc : mmap_flags_core flags = 34) :
    mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true ∧
      mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false ∧
      mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true := by
  unfold mmap_modeled_b mmap_noaccess_b
  rw [Hc]
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The shape gates for a symbolic `flags` (MAP_FIXED shape). -/
theorem mmap_gates_core50 (flags prot : word) (Hc : mmap_flags_core flags = 50) :
    mmap_modeled_b prot flags (Z_to_bv 64 0) = false ∧
      mmap_noaccess_b prot flags (Z_to_bv 64 0) = false ∧
      mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true ∧
      mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false ∧
      mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true := by
  unfold mmap_modeled_b mmap_noaccess_b mmap_fixed_noaccess_b mmap_fixed_rw_b
  rw [Hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : ((50 : Int) == (LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_PRIVATE
        + LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_ANONYMOUS)) = false := by decide
    rw [h]; simp
  · have h : ((50 : Int) == (LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_PRIVATE
        + LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_ANONYMOUS)) = false := by decide
    rw [h]; simp
  · decide
  · decide
  · decide

/-- `region_free` over a nonempty range excludes containment in the same
    ledger. -/
theorem region_free_not_contains (l : List (word × word)) (lo n : word)
    (Hn : 0 < bv_unsigned n) (Hfree : region_free l lo n = true) :
    map_contains l lo n = false := by
  unfold map_contains
  cases hc : l.any (fun p => decide ((p.1.toNat : Int) ≤ (lo.toNat : Int)) &&
      decide ((lo.toNat : Int) + (n.toNat : Int) ≤ (p.1.toNat : Int) + (p.2.toNat : Int))) with
  | false => rfl
  | true =>
      rw [List.any_eq_true] at hc
      obtain ⟨⟨b, s⟩, Hin, Hb⟩ := hc
      rw [Bool.and_eq_true] at Hb
      simp only [Prod.fst, Prod.snd] at Hb
      have h1 := of_decide_eq_true Hb.1
      have h2 := of_decide_eq_true Hb.2
      have Hov := RefNodes.region_free_In l lo n b s Hfree Hin
      simp only [bv_unsigned] at Hn
      omega

/-- The only mmap errno is `ENOMEM`. -/
theorem mmap_errnos_ENOMEM (e : Int) (He : e ∈ mmap_errnos) : e = ENOMEM := by
  unfold mmap_errnos at He
  simpa using He

/-- The only mprotect errno is `ENOMEM`. -/
theorem mprotect_errnos_ENOMEM (e : Int) (He : e ∈ mprotect_errnos) : e = ENOMEM := by
  unfold mprotect_errnos at He
  simpa using He

/-- `-ENOMEM` as a word. -/
theorem errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12) := by
  decide

/-! ### 10a. The `ecall` entry step and the generic checker node -/

/-- The `ecall` instruction reports no memory access. -/
theorem stepacc_ecall_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport (epend regs pc mem rom (getr regs 17)) []) := by
  unfold step_accesses
  rw [show ms_pc (mkst regs pc mem rom) = pc from rfl]
  rw [HF]
  simp only [decode_exec_accesses, HE, ite_eq_left]
  rfl

/-- An access-free instruction is a silent deterministic node on ANY model. -/
theorem node_instr_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' [])) :
    node_ok segs (mkCfg ms model) Unit (fun _ => []) (fun _ => mkCfg ms' model) := by
  have Hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
    unfold mi_account_step
    rw [Hstep]
    dsimp only [mkAccessReport]
    rw [materialize_model_accesses_nil]
  constructor
  · intro _
    exact sstep.instr ms model ms' model Hh Hsvc Hacc
  · intro e st hss
    cases hss with
    | instr ms0 model0 ms1 model1 hh hsvc hstep =>
      rw [Hacc] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨(), rfl, rfl⟩
    | instr_fault ms0 model0 hh hsvc hstep =>
      rw [Hacc] at hstep; cases hstep
    | instr_unmodeled ms0 model0 hh hsvc hstep =>
      rw [Hacc] at hstep; cases hstep
    | syscall ms0 model0 x8 eff m' m'' evs hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc; cases hsvc
    | syscall_materialization_fault ms0 model0 x8 eff m' evs hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc; cases hsvc
    | exit ms0 model0 x8 eff m' evs code hh hsvc hspec hh' hk =>
      rw [Hsvc] at hsvc; cases hsvc
    | killed ms0 model0 x8 eff m' evs sig hh hsvc hspec hk =>
      rw [Hsvc] at hsvc; cases hsvc
    | syscall_unmodeled ms0 model0 x8 hh hsvc hspec =>
      rw [Hsvc] at hsvc; cases hsvc

/-- The `ecall` entry step, silently, for `srealizes`. -/
theorem srz_sys_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (HF : fetch_word segs pc = some w)
    (HE : is_ecall w = true)
    (Hc : srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  srz_silent1 segs _ _ T
    (node_instr_noacc segs (mkst regs pc mem rom) model
      (epend regs pc mem rom (getr regs 17)) Hh rfl
      (stepacc_ecall_epend segs regs pc mem rom w HF HE)) Hc

/-- Common register bookkeeping: `a1 = len` as an `Int`. -/
theorem epend_len (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (len : Int)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len ∧ len < 2 ^ 64) :
    bv_unsigned (ms_gpr (epend regs pc mem rom (getr regs 17)) 1) = len ∧
      ms_gpr (epend regs pc mem rom (getr regs 17)) 1 ≠ BitVec.ofInt 64 0 := by
  simp only [bv_unsigned]
  constructor
  · rw [ms_gpr_epend1, H11]; exact u64_lit len ⟨by omega, Hlen.2⟩
  · rw [ms_gpr_epend1, H11]
    intro hc
    have h := congrArg (fun (x : word) => (x.toNat : Int)) hc
    rw [u64_lit len ⟨by omega, Hlen.2⟩] at h
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0] at h
    omega

/-- An `I`-indexed node described through the checker whose every resolution
    materialises trivially (empty access list). -/
theorem node_chk_ev_mat (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (I : Type) (effs : I → SyscallEffect) (ms' : I → Model)
    (evs : I → List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : ∀ i, check_syscall (sys_input segs ms x8) (effs i) model = .CheckOk (ms' i) (evs i))
    (Hinv : ∀ eff m' ev, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
      ∃ i, eff = effs i ∧ m' = ms' i ∧ ev = evs i)
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh' : ∀ i, m_halted (ms' i) = none)
    (Hacc : ∀ i, syscall_effect_accesses (effs i) = []) :
    node_ok segs (mkCfg ms model) I evs
      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) := by
  constructor
  · intro i
    refine sstep.syscall ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc ?_ (Hh' i) ?_
    · exact (check_syscall_ok_iff _ _ _ _ _).mp (Hok i)
    · rw [Hacc i]; exact materialize_model_accesses_nil _
  · intro e st hss
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, h1 | h2 | h3⟩ | ⟨eff, hc, -, -⟩
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨m'', -, he, hmat, hst⟩ := h1
      rw [Hacc i, materialize_model_accesses_nil] at hmat
      obtain rfl : ms' i = m'' := by injection hmat
      exact ⟨i, he, hst⟩
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨-, -, hmat, -⟩ := h2
      rw [Hacc i, materialize_model_accesses_nil] at hmat
      exact absurd hmat (by simp)
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨code, hh2, -, -⟩ := h3
      rw [Hh' i] at hh2
      exact absurd hh2 (by simp)
    · exact absurd hc (Hnu eff)

/-- The checker equation for the rw mmap shape (`MAP_PRIVATE|MAP_ANONYMOUS`,
    `prot = PROT_READ|PROT_WRITE`, `off = 0`), symbolic in `flags`. -/
theorem mmap_rw_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (flags : word)
    (Hno : (x8.toNat : Int) = 222)
    (H1 : ms_gpr ms 1 ≠ BitVec.ofInt 64 0) (H2 : ms_gpr ms 2 = BitVec.ofInt 64 3)
    (H3 : ms_gpr ms 3 = flags) (Hcore : mmap_flags_core flags = 34)
    (H4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1)) (H5 : ms_gpr ms 5 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z ((ms_gpr ms 1).toNat : Int)) :
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
         | ⟨r, [], zs, [], [], []⟩ =>
             if errno_ret_in mmap_errnos r then
               (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
             else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                 && listNN_eqb zs [(r, BitVec.ofInt 64 nZ)]
               then .CheckOk (with_mmap_backing flags r (BitVec.ofInt 64 nZ)
                      (mmap_model r (BitVec.ofInt 64 nZ) model)) []
               else .CheckReject
         | _ => .CheckReject) := by
  subst HnZ
  obtain ⟨Gm, -, -⟩ := mmap_gates_core34 flags Hcore
  have hoff : mmap_off_aligned_b (BitVec.ofInt 64 0) = true := mmap_off_aligned_b_0
  have hanon : mmap_anon_b flags = true :=
    mmap_anon_b_of_core flags 34 Hcore (by decide)
  have hlen : w_is0 (ms_gpr ms 1) = false := by
    unfold w_is0
    exact bv_eqb_neq _ _ H1
  rw [RefNodes.mmap_check segs ms x8 model eff Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
  rw [H2, H3, H5, hoff, hanon, hlen, Gm]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws⟩
  · rcases zs with _ | ⟨z, zs⟩
    · rcases us with _ | ⟨u, us⟩
      · rcases cs with _ | ⟨c, cs⟩
        · rcases ci with _ | ⟨x, ci⟩
          · unfold grant_ok_na_pin mmap_model
            rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- The rw mmap node: REFUSED (`a0 := -ENOMEM`, nothing else) or GRANTED at
    any `grant_ok_na` address with the budget conjunct. -/
theorem srz_mmap_rw2 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (len : Int)
    (flags : word) (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hisp : init_sp_ok (m_vmmaps model))
    (H17 : getr regs 17 = BitVec.ofInt 64 222)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len ∧ len < 2 ^ 64)
    (H12 : getr regs 12 = BitVec.ofInt 64 3) (H13 : getr regs 13 = flags)
    (Hcore : mmap_flags_core flags = 34)
    (H14 : getr regs 14 = BitVec.ofInt 64 (-1)) (H15 : getr regs 15 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z len) (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (PLACEMENT : placement_policy)
    (Hex : ∃ a, grant_ok_na (getr regs 10) model a nZ = true ∧
      mmap_noreserve_backed_ok flags model nZ = true)
    (HA : srealizes segs
      (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA)
    (HB : ∀ a, grant_ok_na (getr regs 10) model a nZ = true →
      mmap_noreserve_backed_ok flags model nZ = true →
      srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom)
        (with_mmap_backing flags a n (mmap_model a n model))) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  obtain ⟨a0, Ha0, Hb0⟩ := Hex
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  have Hno : bv_unsigned (getr regs 17) = 222 := by
    rw [H17]; exact u64_lit 222 ⟨by omega, by omega⟩
  obtain ⟨Hl1, Hne1⟩ := epend_len regs pc mem rom len H11 Hlen
  have HnZ' : nZ = page_round_up_Z ((ms_gpr (epend regs pc mem rom (getr regs 17)) 1).toNat : Int) := by
    rw [HnZ, show ((ms_gpr (epend regs pc mem rom (getr regs 17)) 1).toNat : Int) = len from Hl1]
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
        = (match eff with
           | ⟨r, [], zs, [], [], []⟩ =>
               if errno_ret_in mmap_errnos r then
                 (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
               else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
                   && listNN_eqb zs [(r, n)]
                 then .CheckOk (with_mmap_backing flags r n (mmap_model r n model)) []
                 else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    have h := mmap_rw_check segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model eff flags
      Hno Hne1 (by rw [ms_gpr_epend2]; exact H12) (by rw [ms_gpr_epend3]; exact H13) Hcore
      (by rw [ms_gpr_epend4]; exact H14) (by rw [ms_gpr_epend5]; exact H15)
      nZ HnZ'
    rw [show BitVec.ofInt 64 nZ = n from Hn.symm] at h
    exact h
  have Hn0 : 0 ≤ nZ := by
    rw [HnZ]; exact LinuxSem.Checks.Sys.Mm.Mmap.page_round_up_Z_nonneg len (by omega)
  have HnZpos : 0 < nZ := by rw [HnZ]; exact page_round_up_Z_pos' len (by omega)
  have HnZal : nZ % page_size = 0 := by rw [HnZ]; exact page_round_up_Z_aligned' len
  refine srz_alt2 segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) Unit
    { a : word // grant_ok_na (getr regs 10) model a nZ = true }
    (fun i => mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17))
      (match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr a => ⟨a.1, [], [(a.1, n)], [], [], []⟩)))
      (match i with
       | .inl _ => model
       | .inr a => with_mmap_backing flags a.1 n (mmap_model a.1 n model)))
    KA KB () ⟨a0, Ha0⟩ ?_ ?_ ?_
  · refine node_chk_ev_mat segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17)
      (Unit ⊕ { a : word // grant_ok_na (getr regs 10) model a nZ = true })
      (fun i => match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr a => ⟨a.1, [], [(a.1, n)], [], [], []⟩)
      (fun i => match i with
       | .inl _ => model
       | .inr a => with_mmap_backing flags a.1 n (mmap_model a.1 n model))
      (fun _ => []) Hh rfl ?_ ?_ ?_ ?_ ?_
    · rintro (⟨⟩ | ⟨a, Ha⟩)
      · rw [Hchk]
        simp only [errno_ret_in_intro mmap_errnos ENOMEM ENOMEM_in_mmap_errnos, ite_eq_left]
      · rw [Hchk]
        dsimp only
        have hne : errno_ret_in mmap_errnos a = false := grant_na_not_errno _ model a nZ Hn0 Ha
        have hpin : grant_ok_na_pin model a nZ = true := grant_ok_na_pin_of_gate _ _ _ _ Hisp Ha
        have hl : listNN_eqb [(a, n)] [(a, n)] = true := (listNN_eqb_eq _ _).mpr rfl
        simp only [hne, hpin, Hb0, hl, Bool.and_true, Bool.false_eq_true, ite_false,
          reduceIte, ite_eq_left]
    · intro eff m' ev hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩
                · dsimp only at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  obtain ⟨e, He, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp h
                  rw [mmap_errnos_ENOMEM e He]
                  exact ⟨.inl (), rfl, rfl, rfl⟩
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (grant_ok_na_pin model r nZ
                    && mmap_noreserve_backed_ok flags model nZ
                    && listNN_eqb zs [(r, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  rw [Bool.and_eq_true, Bool.and_eq_true] at hconj
                  obtain ⟨⟨hpin, -⟩, hl⟩ := hconj
                  rw [(listNN_eqb_eq _ _).mp hl]
                  exact ⟨.inr ⟨r, grant_ok_na_of_pin PLACEMENT _ _ _ _ HnZpos HnZal hpin⟩,
                    rfl, rfl, rfl⟩
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · intro eff hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩
                · dsimp only at hc
                  simp at hc
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (grant_ok_na_pin model r nZ
                    && mmap_noreserve_backed_ok flags model nZ
                    && listNN_eqb zs [(r, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  simp at hc
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · rintro (⟨⟩ | ⟨a, Ha⟩)
      · exact Hh
      · rw [with_mmap_backing_halted, mmap_model_halted]; exact Hh
    · rintro (⟨⟩ | ⟨a, Ha⟩) <;> rfl
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
      ⟨errno_ret ENOMEM, [], [], [], [], []⟩)) model) KA
    rw [adv_ret_epend]
    exact HA
  · rintro ⟨a, Ha⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
      ⟨a, [], [(a, n)], [], [], []⟩)) (with_mmap_backing flags a n (mmap_model a n model))) KB
    rw [adv_zeros1_epend]
    exact HB a Ha Hb0
/-- The checker equation for the PROT_NONE mmap shape. -/
theorem mmap_none_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (flags : word)
    (Hno : (x8.toNat : Int) = 222)
    (H1 : ms_gpr ms 1 ≠ BitVec.ofInt 64 0) (H2 : ms_gpr ms 2 = BitVec.ofInt 64 0)
    (H3 : ms_gpr ms 3 = flags) (Hcore : mmap_flags_core flags = 34)
    (H4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1)) (H5 : ms_gpr ms 5 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z ((ms_gpr ms 1).toNat : Int)) :
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
         | ⟨r, [], [], us, [], []⟩ =>
             if errno_ret_in mmap_errnos r then
               (match us with | [] => .CheckOk model [] | _ => .CheckReject)
             else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, BitVec.ofInt 64 nZ)]
               then .CheckOk (with_mmap_backing flags r (BitVec.ofInt 64 nZ)
                      (noaccess_model r (BitVec.ofInt 64 nZ) model)) []
               else .CheckReject
         | _ => .CheckReject) := by
  subst HnZ
  obtain ⟨-, Gm, Gn⟩ := mmap_gates_core34 flags Hcore
  have hoff : mmap_off_aligned_b (BitVec.ofInt 64 0) = true := mmap_off_aligned_b_0
  have hanon : mmap_anon_b flags = true :=
    mmap_anon_b_of_core flags 34 Hcore (by decide)
  have hlen : w_is0 (ms_gpr ms 1) = false := by
    unfold w_is0
    exact bv_eqb_neq _ _ H1
  rw [RefNodes.mmap_check segs ms x8 model eff Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
  rw [H2, H3, H5, hoff, hanon, hlen, Gm, Gn]
  dsimp only
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws⟩
  · rcases zs with _ | ⟨z, zs⟩
    · rcases us with _ | ⟨u, us⟩
      · rcases cs with _ | ⟨c, cs⟩
        · rcases ci with _ | ⟨x, ci⟩
          · unfold grant_ok_na_pin noaccess_model
            rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- The PROT_NONE NULL-hint mmap node. -/
theorem srz_mmap_none2 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (len : Int)
    (flags : word) (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hisp : init_sp_ok (m_vmmaps model))
    (H17 : getr regs 17 = BitVec.ofInt 64 222)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len ∧ len < 2 ^ 64)
    (H12 : getr regs 12 = BitVec.ofInt 64 0) (H13 : getr regs 13 = flags)
    (Hcore : mmap_flags_core flags = 34)
    (H14 : getr regs 14 = BitVec.ofInt 64 (-1)) (H15 : getr regs 15 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z len) (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (PLACEMENT : placement_policy)
    (Hex : ∃ a, grant_ok_na (getr regs 10) model a nZ = true)
    (HA : srealizes segs
      (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA)
    (HB : ∀ a, grant_ok_na (getr regs 10) model a nZ = true →
      srealizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom)
        (with_mmap_backing flags a n (noaccess_model a n model))) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  obtain ⟨a0, Ha0⟩ := Hex
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  have Hno : bv_unsigned (getr regs 17) = 222 := by
    rw [H17]; exact u64_lit 222 ⟨by omega, by omega⟩
  obtain ⟨Hl1, Hne1⟩ := epend_len regs pc mem rom len H11 Hlen
  have HnZ' : nZ = page_round_up_Z ((ms_gpr (epend regs pc mem rom (getr regs 17)) 1).toNat : Int) := by
    rw [HnZ, show ((ms_gpr (epend regs pc mem rom (getr regs 17)) 1).toNat : Int) = len from Hl1]
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
        = (match eff with
           | ⟨r, [], [], us, [], []⟩ =>
               if errno_ret_in mmap_errnos r then
                 (match us with | [] => .CheckOk model [] | _ => .CheckReject)
               else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)]
                 then .CheckOk (with_mmap_backing flags r n (noaccess_model r n model)) []
                 else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    have h := mmap_none_check segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model eff flags
      Hno Hne1 (by rw [ms_gpr_epend2]; exact H12) (by rw [ms_gpr_epend3]; exact H13) Hcore
      (by rw [ms_gpr_epend4]; exact H14) (by rw [ms_gpr_epend5]; exact H15)
      nZ HnZ'
    rw [show BitVec.ofInt 64 nZ = n from Hn.symm] at h
    exact h
  have Hn0 : 0 ≤ nZ := by
    rw [HnZ]; exact LinuxSem.Checks.Sys.Mm.Mmap.page_round_up_Z_nonneg len (by omega)
  have HnZpos : 0 < nZ := by rw [HnZ]; exact page_round_up_Z_pos' len (by omega)
  have HnZal : nZ % page_size = 0 := by rw [HnZ]; exact page_round_up_Z_aligned' len
  refine srz_alt2 segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) Unit
    { a : word // grant_ok_na (getr regs 10) model a nZ = true }
    (fun i => mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17))
      (match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr a => ⟨a.1, [], [], [(a.1, n)], [], []⟩)))
      (match i with
       | .inl _ => model
       | .inr a => with_mmap_backing flags a.1 n (noaccess_model a.1 n model)))
    KA KB () ⟨a0, Ha0⟩ ?_ ?_ ?_
  · refine node_chk_ev_mat segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17)
      (Unit ⊕ { a : word // grant_ok_na (getr regs 10) model a nZ = true })
      (fun i => match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr a => ⟨a.1, [], [], [(a.1, n)], [], []⟩)
      (fun i => match i with
       | .inl _ => model
       | .inr a => with_mmap_backing flags a.1 n (noaccess_model a.1 n model))
      (fun _ => []) Hh rfl ?_ ?_ ?_ ?_ ?_
    · rintro (⟨⟩ | ⟨a, Ha⟩)
      · rw [Hchk]
        dsimp only
        simp only [errno_ret_in_intro mmap_errnos ENOMEM ENOMEM_in_mmap_errnos, ite_eq_left]
      · rw [Hchk]
        dsimp only
        have hne : errno_ret_in mmap_errnos a = false := grant_na_not_errno _ model a nZ Hn0 Ha
        have hpin : grant_ok_na_pin model a nZ = true := grant_ok_na_pin_of_gate _ _ _ _ Hisp Ha
        have hl : listNN_eqb [(a, n)] [(a, n)] = true := (listNN_eqb_eq _ _).mpr rfl
        simp only [hne, hpin, hl, Bool.and_true, Bool.false_eq_true, ite_false, ite_eq_left]
    · intro eff m' ev hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases zs with _ | ⟨z, zs⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases us with _ | ⟨u, us⟩
                · dsimp only at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  obtain ⟨e, He, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp h
                  rw [mmap_errnos_ENOMEM e He]
                  exact ⟨.inl (), rfl, rfl, rfl⟩
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (grant_ok_na_pin model r nZ
                    && listNN_eqb us [(r, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  rw [Bool.and_eq_true] at hconj
                  obtain ⟨hpin, hl⟩ := hconj
                  rw [(listNN_eqb_eq _ _).mp hl]
                  exact ⟨.inr ⟨r, grant_ok_na_of_pin PLACEMENT _ _ _ _ HnZpos HnZal hpin⟩,
                    rfl, rfl, rfl⟩
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · intro eff hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases zs with _ | ⟨z, zs⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases us with _ | ⟨u, us⟩ <;> (dsimp only at hc; simp at hc)
              · rw [ite_eq_right h] at hc
                by_cases hconj : (grant_ok_na_pin model r nZ
                    && listNN_eqb us [(r, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  simp at hc
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · rintro (⟨⟩ | ⟨a, Ha⟩)
      · exact Hh
      · rw [with_mmap_backing_halted, noaccess_model, with_vmmaps_halted]; exact Hh
    · rintro (⟨⟩ | ⟨a, Ha⟩) <;> rfl
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
      ⟨errno_ret ENOMEM, [], [], [], [], []⟩)) model) KA
    rw [adv_ret_epend]
    exact HA
  · rintro ⟨a, Ha⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
      ⟨a, [], [], [(a, n)], [], []⟩)) (with_mmap_backing flags a n (noaccess_model a n model))) KB
    rw [adv_unmaps1_epend]
    exact HB a Ha

/-- The MAP_FIXED argument gates, closed from the ceiling bound. -/
theorem mmap_fixed_gate_open (h : VmMaps) (addr len : word)
    (Hal : (addr.toNat : Int) % page_size = 0) (Hpos : 0 < (addr.toNat : Int))
    (Hlen : 0 < (len.toNat : Int))
    (Hce : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤ alloc_ceiling)
    (Hisp : init_sp_ok h) :
    ¬ (two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)) ∧
      ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤ alloc_top h) ∧
      (((addr.toNat : Int) % page_size) == 0) = true ∧
      (0 < (addr.toNat : Int)) ∧
      ((len.toNat : Int) < 2 ^ 64) ∧
      0 < page_round_up_Z (len.toNat : Int) ∧
      page_round_up_Z (len.toNat : Int) < 2 ^ 64 := by
  have ha := bv_unsigned_range_u64 addr
  have hl := bv_unsigned_range_u64 len
  obtain ⟨hb1, hb2⟩ := page_round_up_Z_bounds (len.toNat : Int) (by omega)
  have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
  refine ⟨by unfold two_pow_64; omega, alloc_top_ge_of_ceiling h _ Hisp Hce, ?_, Hpos,
    by omega, by omega, by omega⟩
  show ((addr.toNat : Int) % 4096 == 0) = true
  exact (beq_iff_eq).mpr Hal

/-- The checker equation for the MAP_FIXED rw shape over a free range. -/
theorem mmap_fixed_rw_free_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (flags addr len : word)
    (Hno : (x8.toNat : Int) = 222)
    (H0 : ms_gpr ms 0 = addr) (Hal : (addr.toNat : Int) % page_size = 0)
    (Hpos : 0 < (addr.toNat : Int))
    (H1 : ms_gpr ms 1 = len) (Hlen : 0 < (len.toNat : Int))
    (Hce : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 3) (H3 : ms_gpr ms 3 = flags)
    (Hcore : mmap_flags_core flags = 50)
    (H4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1)) (H5 : ms_gpr ms 5 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z (len.toNat : Int))
    (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) addr n
      = true) :
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
         | ⟨r, [], zs, [], [], []⟩ =>
             if errno_ret_in mmap_errnos r then
               (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
             else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                 && mmap_noreserve_backed_ok flags model nZ
               then .CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
               else .CheckReject
         | _ => .CheckReject) := by
  subst HnZ
  subst Hn
  obtain ⟨Gm, Gn, Gfn, -, Gfr⟩ := mmap_gates_core50 flags (BitVec.ofInt 64 3) Hcore
  have hanon : mmap_anon_b flags = true :=
    mmap_anon_b_of_core flags 50 Hcore (by decide)
  have hlen_ne : len ≠ BitVec.ofInt 64 0 := by
    intro h
    have h2 := congrArg (fun (x : word) => (x.toNat : Int)) h
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0] at h2
    omega
  have hlen0 : w_is0 len = false := by
    unfold w_is0
    exact bv_eqb_neq _ _ hlen_ne
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ :=
    mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp
  have hposn : 0 < ((BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))).toNat : Int) := by
    rw [bv_ofInt_toNat _ (by omega) (by omega)]
    exact g6
  have hparts := Hrf
  rw [RefNodes.region_free_app, Bool.and_eq_true] at hparts
  have hres : region_free (m_vmmaps model).vm_reserved addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true := hparts.1
  have hnc : map_contains (m_vmmaps model).vm_maps addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false :=
    region_free_not_contains _ _ _ hposn hparts.2
  rw [RefNodes.mmap_check segs ms x8 model eff Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
  simp only [H2, H3, H5, H0, H1, mmap_off_aligned_b_0, hanon, hlen0, Gm, Gn, Gfn, Gfr,
    g1, g2, g3, g4, hres, hnc, Hrf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ite_true, not_true_eq_false, not_false_eq_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws⟩
  · rcases zs with _ | ⟨z, zs⟩
    · rcases us with _ | ⟨u, us⟩
      · rcases cs with _ | ⟨c, cs⟩
        · rcases ci with _ | ⟨x, ci⟩
          · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- The checker equation for the MAP_FIXED PROT_NONE shape over a free
    range. -/
theorem mmap_fixed_none_free_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (flags addr len : word)
    (Hno : (x8.toNat : Int) = 222)
    (H0 : ms_gpr ms 0 = addr) (Hal : (addr.toNat : Int) % page_size = 0)
    (Hpos : 0 < (addr.toNat : Int))
    (H1 : ms_gpr ms 1 = len) (Hlen : 0 < (len.toNat : Int))
    (Hce : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 0) (H3 : ms_gpr ms 3 = flags)
    (Hcore : mmap_flags_core flags = 50)
    (H4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1)) (H5 : ms_gpr ms 5 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z (len.toNat : Int))
    (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) addr n
      = true) :
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
         | ⟨r, [], [], us, [], []⟩ =>
             if errno_ret_in mmap_errnos r then
               (match us with | [] => .CheckOk model [] | _ => .CheckReject)
             else if bv_eqb r addr && listNN_eqb us [(addr, n)]
               then .CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
               else .CheckReject
         | _ => .CheckReject) := by
  subst HnZ
  subst Hn
  obtain ⟨Gm, Gn, Gfn, -, -⟩ := mmap_gates_core50 flags (BitVec.ofInt 64 0) Hcore
  have hanon : mmap_anon_b flags = true :=
    mmap_anon_b_of_core flags 50 Hcore (by decide)
  have hlen_ne : len ≠ BitVec.ofInt 64 0 := by
    intro h
    have h2 := congrArg (fun (x : word) => (x.toNat : Int)) h
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0] at h2
    omega
  have hlen0 : w_is0 len = false := by
    unfold w_is0
    exact bv_eqb_neq _ _ hlen_ne
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ :=
    mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp
  have hposn : 0 < ((BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))).toNat : Int) := by
    rw [bv_ofInt_toNat _ (by omega) (by omega)]
    exact g6
  have hparts := Hrf
  rw [RefNodes.region_free_app, Bool.and_eq_true] at hparts
  have hres : region_free (m_vmmaps model).vm_reserved addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true := hparts.1
  have hnc : map_contains (m_vmmaps model).vm_maps addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false :=
    region_free_not_contains _ _ _ hposn hparts.2
  rw [RefNodes.mmap_check segs ms x8 model eff Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
  simp only [H2, H3, H5, H0, H1, mmap_off_aligned_b_0, hanon, hlen0, Gm, Gn, Gfn,
    g1, g2, g3, g4, hres, hnc, Hrf, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ite_true, not_true_eq_false, not_false_eq_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws⟩
  · rcases zs with _ | ⟨z, zs⟩
    · rcases us with _ | ⟨u, us⟩
      · rcases cs with _ | ⟨c, cs⟩
        · rcases ci with _ | ⟨x, ci⟩
          · rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- An aligned word is its own page base. -/
theorem page_base_aligned' (p : word) (Hp : bv_unsigned p % 4096 = 0) :
    page_base p = p := by
  unfold page_base page_base_of
  simp only [page_size]
  refine Z_to_bv_u_eq' p _ ?_
  simp only [bv_unsigned] at Hp
  rw [ediv_mul_4096, Hp]
  omega

/-- A cut contained in the interval leaves only the two outer pieces. -/
theorem iv_subtract_contained (a sz : word) (lo hi : Int)
    (H1 : bv_unsigned a ≤ lo) (H2 : hi ≤ bv_unsigned a + bv_unsigned sz)
    (H3 : lo ≤ hi) :
    iv_subtract a sz lo hi
      = (if bv_unsigned a < lo then [(a, Z_to_bv 64 (lo - bv_unsigned a))] else [])
        ++ (if hi < bv_unsigned a + bv_unsigned sz then
              [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))] else []) := by
  have hm : min (bv_unsigned sz) (lo - bv_unsigned a) = lo - bv_unsigned a := by
    rw [Int.min_def]; split <;> omega
  have hM : max (bv_unsigned a) hi = hi := by
    rw [Int.max_def]; split <;> omega
  unfold iv_subtract
  dsimp only
  rw [hm, hM]

/-- Replacing an entry, read through a denotation. -/
theorem map_replace_entry (f : amap → word × word) (l : List amap) (m : amap)
    (pcs : List amap) :
    (replace_entry l m pcs).map f
      = l.flatMap (fun m' => if amap_eqb m' m then pcs.map f else [f m']) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      unfold replace_entry at *
      simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil]
      by_cases hh : amap_eqb h m = true
      · simp only [hh, ite_true]
        rw [ih]
      · rw [ite_eq_right hh, ite_eq_right hh]
        simp only [List.map_cons, List.map_nil]
        rw [ih]

/-- Subtracting a range covered by one tracked entry matches replacing it by
    the syntactic pieces. -/
theorem maps_subtract_map_replace (f : amap → word × word) (l : List amap) (m : amap)
    (pcs : List amap) (lo hi : Int)
    (Hout : ∀ m', m' ∈ l → amap_eqb m' m = false →
      iv_subtract (f m').1 (f m').2 lo hi = [f m'])
    (Hin : ∀ m', m' ∈ l → amap_eqb m' m = true →
      iv_subtract (f m').1 (f m').2 lo hi = pcs.map f) :
    maps_subtract (l.map f) lo hi = (replace_entry l m pcs).map f := by
  rw [map_replace_entry]
  induction l with
  | nil => rfl
  | cons h t ih =>
      simp only [List.map_cons, maps_subtract, List.flatMap_cons]
      rw [ih (fun x hx => Hout x (List.mem_cons_of_mem _ hx))
            (fun x hx => Hin x (List.mem_cons_of_mem _ hx))]
      by_cases hh : amap_eqb h m = true
      · rw [ite_eq_left hh, Hin h (List.mem_cons_self ..) hh]
      · have hf : amap_eqb h m = false := by cases hab : amap_eqb h m <;> simp_all
        rw [ite_eq_right hh, Hout h (List.mem_cons_self ..) hf]

/-- What survives a `replace_entry` is an old entry (not the replaced one) or
    one of the pieces. -/
theorem in_replace_entry (l : List amap) (m : amap) (pcs : List amap) (m' : amap)
    (H : m' ∈ replace_entry l m pcs) :
    (m' ∈ l ∧ m' ≠ m) ∨ (m ∈ l ∧ m' ∈ pcs) := by
  unfold replace_entry at H
  rw [List.mem_flatMap] at H
  obtain ⟨m0, Hm0, Hin⟩ := H
  by_cases he : amap_eqb m0 m = true
  · have h0 : m0 = m := amap_eqb_eq he
    subst h0
    rw [ite_eq_left he] at Hin
    exact Or.inr ⟨Hm0, Hin⟩
  · rw [ite_eq_right he] at Hin
    rcases List.mem_singleton.mp Hin with rfl
    refine Or.inl ⟨Hm0, ?_⟩
    intro h
    subst h
    rw [amap_eqb_refl] at he
    exact he rfl

/-- A piece of one entry's subtraction is a piece of the ledger's. -/
theorem maps_subtract_in_pieces (l : List (word × word)) (b s : word) (lo hi : Int)
    (q : word × word) (Hin : (b, s) ∈ l) (Hq : q ∈ iv_subtract b s lo hi) :
    q ∈ maps_subtract l lo hi := by
  induction l with
  | nil => simp at Hin
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [maps_subtract, List.mem_append]
      rcases List.mem_cons.mp Hin with h | h
      · injection h with h1 h2
        subst h1 h2
        exact Or.inl Hq
      · exact Or.inr (ih h)

/-- `seps` of an append. -/
theorem seps_app_intro (l1 l2 : List (word × word)) (H1 : seps l1) (H2 : seps l2)
    (H12 : ∀ p ∈ l1, ∀ q ∈ l2, iv_disjoint p q) : seps (l1 ++ l2) := by
  induction H1 with
  | nil => simpa using H2
  | cons p l Hf Hl ih =>
      rw [List.cons_append]
      refine seps.cons p (l ++ l2) ?_
        (ih (fun a ha b hb => H12 a (List.mem_cons_of_mem _ ha) b hb))
      intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact Hf q h
      · exact H12 p (List.mem_cons_self ..) q h

/-- Every piece of `iv_subtract` is separated. -/
theorem seps_iv_subtract (a sz : word) (lo hi : Int) (Hwf : iv_wf (a, sz))
    (Hlh : lo ≤ hi) : seps (iv_subtract a sz lo hi) := by
  have hwf : (a.toNat : Int) + (sz.toNat : Int) ≤ 2 ^ 64 := by
    simpa only [iv_wf, B, S, Prod.fst, Prod.snd] using Hwf
  have ha := bv_unsigned_range_u64 a
  have hsz := bv_unsigned_range_u64 sz
  unfold iv_subtract
  dsimp only
  by_cases h1 : (a.toNat : Int) < lo
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · have hmin0 : 0 ≤ min (sz.toNat : Int) (lo - (a.toNat : Int)) :=
        Int.le_min.mpr ⟨hsz.1, by omega⟩
      have hmin1 : min (sz.toNat : Int) (lo - (a.toNat : Int)) < 2 ^ 64 :=
        Int.lt_of_le_of_lt (Int.min_le_left _ _) hsz.2
      have hmaxhi : max (a.toNat : Int) hi = hi := Int.max_eq_right (by omega)
      have hmax0 : 0 ≤ max (a.toNat : Int) hi :=
        Int.le_trans ha.1 (Int.le_max_left _ _)
      have hmax1 : max (a.toNat : Int) hi < 2 ^ 64 := by
        rw [hmaxhi]; exact Int.lt_of_lt_of_le h2 hwf
      have hrest0 : 0 ≤ (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by
        rw [hmaxhi]; omega
      have hrest1 : (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi < 2 ^ 64 := by
        rw [hmaxhi]; exact Int.lt_of_le_of_lt (by omega) hsz.2
      have hb1 : ((BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
          = min (sz.toNat : Int) (lo - (a.toNat : Int)) :=
        bv_ofInt_toNat _ hmin0 hmin1
      have hb2 : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
          = max (a.toNat : Int) hi := bv_ofInt_toNat _ hmax0 hmax1
      have hb3 : ((BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int)
            - max (a.toNat : Int) hi)).toNat : Int)
          = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi :=
        bv_ofInt_toNat _ hrest0 hrest1
      rw [ite_eq_left h1, ite_eq_left h2, List.singleton_append]
      refine seps.cons _ _ ?_ (seps.cons _ _ ?_ seps.nil)
      · intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        unfold iv_disjoint
        simp only [Prod.fst, Prod.snd, bv_unsigned]
        rw [hb1, hb2, hb3]
        left
        have := Int.min_le_right (sz.toNat : Int) (lo - (a.toNat : Int))
        omega
      · intro x hx
        exact (List.not_mem_nil hx).elim
    · rw [ite_eq_left h1, ite_eq_right h2, List.singleton_append]
      exact seps.cons _ _ (fun x hx => (List.not_mem_nil hx).elim) seps.nil
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_right h1, ite_eq_left h2, List.nil_append]
      exact seps.cons _ _ (fun x hx => (List.not_mem_nil hx).elim) seps.nil
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact seps.nil

/-- The pieces of a separated ledger are separated. -/
theorem seps_maps_subtract (l : List (word × word)) (lo hi : Int)
    (Hs : seps l) (Hwf : ivs_wf l) (Hlh : lo ≤ hi) : seps (maps_subtract l lo hi) := by
  induction l with
  | nil => exact seps.nil
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      obtain ⟨Ha, Hl⟩ := ivs_wf_cons_inv (a, sz) tl Hwf
      cases Hs with
      | cons p l' Hf Ht =>
          simp only [maps_subtract]
          refine seps_app_intro _ _ (seps_iv_subtract a sz lo hi Ha Hlh) (ih Ht Hl) ?_
          intro p1 hp q hq
          obtain ⟨P1, P2, P3⟩ := iv_subtract_pieces a sz lo hi p1 Ha hp
          obtain ⟨r, Hr, Q1, Q2, Q3⟩ := maps_subtract_pieces tl lo hi q Hl hq
          have D := Hf r Hr
          unfold iv_disjoint at D ⊢
          simp only [Prod.fst, Prod.snd] at D ⊢
          omega

/-- Replacing an entry that is absent changes nothing. -/
theorem replace_entry_notin (ms : List amap) (m : amap) (pcs : List amap)
    (H : m ∉ ms) : replace_entry ms m pcs = ms := by
  induction ms with
  | nil => rfl
  | cons h t ih =>
      unfold replace_entry at *
      simp only [List.flatMap_cons]
      have hh : amap_eqb h m = false := by
        cases hab : amap_eqb h m with
        | true => exact absurd (amap_eqb_eq hab) (fun he => H (he ▸ List.mem_cons_self ..))
        | false => rfl
      rw [ite_eq_right (by simp [hh]), ih (fun hin => H (List.mem_cons_of_mem _ hin))]
      simp

/-- Subtracting a range disjoint from every entry changes nothing. -/
theorem maps_subtract_disjoint_id (l : List (word × word)) (lo hi : Int)
    (Hlh : lo < hi)
    (H : ∀ iv ∈ l, 0 < bv_unsigned iv.2 ∧
      (bv_unsigned iv.1 + bv_unsigned iv.2 ≤ lo ∨ hi ≤ bv_unsigned iv.1)) :
    maps_subtract l lo hi = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      obtain ⟨P, D⟩ := H (a, sz) (List.mem_cons_self ..)
      simp only [maps_subtract]
      rw [iv_subtract_disjoint a sz lo hi Hlh P D, List.singleton_append,
        ih (fun iv hiv => H iv (List.mem_cons_of_mem _ hiv))]

/-- Pushing non-token pieces in front of a matched ledger. -/
theorem maps_match_app_pcs (E : env) (pcs : List amap) (ms : List amap)
    (l : List (word × word)) (Hpf : ∀ pc ∈ pcs, is_fog pc = false)
    (HM : maps_match E ms l) :
    maps_match E (pcs ++ ms) ((pcs.map (amap_den E)) ++ l) := by
  induction pcs with
  | nil => simpa using HM
  | cons pc pcs ih =>
      have hf : is_fog pc = false := Hpf pc (List.mem_cons_self ..)
      simp only [List.cons_append, List.map_cons, maps_match, hf, ite_false]
      exact ⟨_, rfl, ih (fun x hx => Hpf x (List.mem_cons_of_mem _ hx))⟩

/-- Distinct entries of a separated `map f` are disjoint. -/
theorem seps_map_disjoint (f : amap → word × word) (ms : List amap) (m m' : amap)
    (Hs : seps (ms.map f)) (Hm : m ∈ ms) (Hm' : m' ∈ ms) (Hne : m ≠ m') :
    iv_disjoint (f m) (f m') := by
  induction ms with
  | nil => simp at Hm
  | cons h t ih =>
      simp only [List.map_cons] at Hs
      cases Hs with
      | cons p l' Hhd Htl =>
          rcases List.mem_cons.mp Hm with hm | Hm
          · rw [hm] at Hne ⊢
            rcases List.mem_cons.mp Hm' with hm' | Hm'
            · rw [hm'] at Hne
              exact absurd rfl Hne
            · exact Hhd (f m') (List.mem_map_of_mem Hm')
          · rcases List.mem_cons.mp Hm' with hm' | Hm'
            · rw [hm'] at Hne ⊢
              have D := Hhd (f m) (List.mem_map_of_mem Hm)
              unfold iv_disjoint at D ⊢
              omega
            · exact ih Htl Hm Hm'

/-- Distinct tracked non-token entries of a matched separated ledger are
    disjoint. -/
theorem maps_match_disjoint (E : env) (ms : List amap) (l : List (word × word))
    (m m' : amap) (HM : maps_match E ms l) (Hs : seps l) (Hm : m ∈ ms) (Hm' : m' ∈ ms)
    (Hf : is_fog m = false) (Hf' : is_fog m' = false) (Hne : m ≠ m') :
    iv_disjoint (amap_den E m) (amap_den E m') := by
  induction ms generalizing l with
  | nil => simp at Hm
  | cons h t ih =>
      rw [maps_match] at HM
      by_cases hh : is_fog h = true
      · rw [ite_eq_left hh] at HM
        have hmt : m ∈ t := by
          rcases List.mem_cons.mp Hm with hm | h
          · rw [← hm] at hh
            rw [Hf] at hh
            exact absurd hh (by simp)
          · exact h
        have hmt' : m' ∈ t := by
          rcases List.mem_cons.mp Hm' with hm | h
          · rw [← hm] at hh
            rw [Hf'] at hh
            exact absurd hh (by simp)
          · exact h
        rcases HM with HM | ⟨iv, l', rfl, _, HM⟩
        · exact ih l HM Hs hmt hmt'
        · cases Hs with
          | cons p l0 Hfa Hl => exact ih l' HM Hl hmt hmt'
      · rw [ite_eq_right hh] at HM
        obtain ⟨l', rfl, HM⟩ := HM
        cases Hs with
        | cons p l0 Hfa Hl =>
            rcases List.mem_cons.mp Hm with hm | Hm
            · rw [hm] at Hne ⊢
              rcases List.mem_cons.mp Hm' with hm' | Hm'
              · rw [hm'] at Hne
                exact absurd rfl Hne
              · exact Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')
            · rcases List.mem_cons.mp Hm' with hm' | Hm'
              · rw [hm'] at Hne ⊢
                have D := Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)
                unfold iv_disjoint at D ⊢
                omega
              · exact ih l' HM Hl Hm Hm'

/-- A cut never increases the total tracked size. -/
theorem sum_sizes_maps_subtract_le (l : List (word × word)) (lo hi : Int)
    (Hwf : ivs_wf l) (Hlh : lo ≤ hi) : sum_sizes (maps_subtract l lo hi) ≤ sum_sizes l := by
  rw [sum_sizes_live, sum_sizes_live, live_bytes_sum_count, live_bytes_sum_count]
  rw [(maps_subtract_sem l lo hi Hwf Hlh).2.1 (fun _ => true)]
  exact sum_count_mono _ _ l (fun x _ => rfl)

/-- The high/low split survives a cut. -/
theorem ledger_split_maps_subtract (l : List (word × word)) (lo hi K Y : Int)
    (Hwf : ivs_wf l) (H : ledger_split l K Y) :
    ledger_split (maps_subtract l lo hi) K Y := by
  intro b s Hin
  obtain ⟨r, Hr, R1, R2, R3⟩ := maps_subtract_pieces l lo hi (b, s) Hwf Hin
  simp only [Prod.fst, Prod.snd, bv_unsigned] at R1 R2 ⊢
  rcases H r.1 r.2 Hr with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Subtracting a range contained in one tracked non-token entry matches
    replacing that entry by its syntactic pieces. -/
theorem maps_match_subtract (E : env) (ms : List amap) (l : List (word × word)) (m : amap)
    (pcs : List amap) (lo hi : Int)
    (HM : maps_match E ms l) (Hs : seps l) (Hpos : ∀ iv ∈ l, 0 < bv_unsigned iv.2)
    (Hm : m ∈ ms) (Hf : is_fog m = false) (Hlh : lo < hi)
    (Hc1 : bv_unsigned (edenot E m.am_base) ≤ lo)
    (Hc2 : hi ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))
    (Hpcs : pcs.map (amap_den E) = iv_subtract (edenot E m.am_base) (edenot E m.am_len) lo hi)
    (Hpf : ∀ pc ∈ pcs, is_fog pc = false) :
    maps_match E (replace_entry ms m pcs) (maps_subtract l lo hi) := by
  induction ms generalizing l with
  | nil => simp at Hm
  | cons h t ih =>
      rw [maps_match] at HM
      unfold replace_entry
      simp only [List.flatMap_cons]
      by_cases hfh : is_fog h = true
      · -- the head is a token: it stands for zero or one entry
        rw [ite_eq_left hfh] at HM
        have hHe : amap_eqb h m = false := by
          cases hb : amap_eqb h m with
          | false => rfl
          | true =>
              have hhm : h = m := amap_eqb_eq hb
              rw [hhm] at hfh
              rw [Hf] at hfh
              exact absurd hfh Bool.false_ne_true
        have hne : ¬ (amap_eqb h m = true) := by rw [hHe]; exact Bool.false_ne_true
        rw [ite_eq_right hne, List.singleton_append]
        unfold maps_match
        rw [ite_eq_left hfh]
        have hmt : m ∈ t := by
          rcases List.mem_cons.mp Hm with hm | h
          · rw [← hm] at hfh
            rw [Hf] at hfh
            exact absurd hfh (by simp)
          · exact h
        rcases HM with HM | ⟨iv, l', rfl, Hsz, HM⟩
        · exact Or.inl (ih l HM Hs Hpos hmt)
        · refine Or.inr ⟨iv, maps_subtract l' lo hi, ?_, Hsz, ?_⟩
          · cases Hs with
            | cons p l0 Hfa Hl =>
                have hpos : 0 < bv_unsigned iv.2 := Hpos iv (List.mem_cons_self ..)
                have D := Hfa (amap_den E m) (maps_match_In E t l' m HM hmt Hf)
                have hd : bv_unsigned iv.1 + bv_unsigned iv.2 ≤ lo ∨ hi ≤ bv_unsigned iv.1 := by
                  unfold iv_disjoint at D
                  simp only [Prod.fst, Prod.snd, amap_den] at D ⊢
                  omega
                simp only [maps_subtract, iv_subtract_disjoint iv.1 iv.2 lo hi Hlh hpos hd,
                  List.singleton_append]
          · cases Hs with
            | cons p l0 Hfa Hl =>
                exact ih l' HM Hl (fun iv hiv => Hpos iv (List.mem_cons_of_mem _ hiv)) hmt
      · -- the head is tracked: two cases on whether it is the replaced entry
        rw [ite_eq_right hfh] at HM
        obtain ⟨l', rfl, HM⟩ := HM
        cases Hs with
        | cons p l0 Hfa Hl =>
            by_cases hHe : amap_eqb h m = true
            · have hhm : h = m := amap_eqb_eq hHe
              rw [ite_eq_left hHe]
              rw [hhm] at Hpos Hfa ⊢
              have hnot : m ∉ t := by
                intro hmt
                have D := Hfa (amap_den E m) (maps_match_In E t l' m HM hmt Hf)
                have P : 0 < bv_unsigned (amap_den E m).2 := Hpos (amap_den E m) (by simp)
                unfold iv_disjoint at D
                simp only [Prod.fst, Prod.snd, amap_den] at D P
                omega
              have hrep : List.flatMap (fun m' => if amap_eqb m' m = true then pcs else [m']) t
                  = t := replace_entry_notin t m pcs hnot
              rw [hrep]
              have hdisj : ∀ iv ∈ l', 0 < bv_unsigned iv.2 ∧
                  (bv_unsigned iv.1 + bv_unsigned iv.2 ≤ lo ∨ hi ≤ bv_unsigned iv.1) := by
                intro iv hiv
                refine ⟨Hpos iv (List.mem_cons_of_mem _ hiv), ?_⟩
                have D := Hfa iv hiv
                unfold iv_disjoint at D
                simp only [Prod.fst, Prod.snd, amap_den] at D ⊢
                omega
              have hid : maps_subtract l' lo hi = l' := maps_subtract_disjoint_id l' lo hi Hlh hdisj
              have hsub : maps_subtract (amap_den E m :: l') lo hi
                  = pcs.map (amap_den E) ++ l' := by
                simp only [maps_subtract, amap_den, Prod.fst, Prod.snd, ← Hpcs, hid]
              rw [hsub]
              exact maps_match_app_pcs E pcs t l' Hpf HM
            · rw [ite_eq_right hHe, List.singleton_append]
              unfold maps_match
              rw [ite_eq_right hfh]
              have hmt : m ∈ t := by
                rcases List.mem_cons.mp Hm with hm | h
                · rw [hm] at hHe
                  exact absurd (amap_eqb_refl h) hHe
                · exact h
              have hpos : 0 < bv_unsigned (amap_den E h).2 :=
                Hpos (amap_den E h) (List.mem_cons_self ..)
              have D := Hfa (amap_den E m) (maps_match_In E t l' m HM hmt Hf)
              have hd : bv_unsigned (amap_den E h).1 + bv_unsigned (amap_den E h).2 ≤ lo ∨
                  hi ≤ bv_unsigned (amap_den E h).1 := by
                unfold iv_disjoint at D
                simp only [Prod.fst, Prod.snd, amap_den] at D ⊢
                omega
              refine ⟨maps_subtract l' lo hi, ?_, ?_⟩
              · show iv_subtract (amap_den E h).1 (amap_den E h).2 lo hi
                    ++ maps_subtract l' lo hi
                  = (amap_den E h) :: maps_subtract l' lo hi
                rw [iv_subtract_disjoint (amap_den E h).1 (amap_den E h).2 lo hi Hlh hpos hd,
                  List.singleton_append]
              · exact ih l' HM Hl (fun iv hiv => Hpos iv (List.mem_cons_of_mem _ hiv)) hmt

/-! ## 10d. The page discipline of the pieces -/

theorem emod4096_sub {x y : Int} (hx : x % 4096 = 0) (hy : y % 4096 = 0) :
    (x - y) % 4096 = 0 := by
  rw [Int.sub_emod, hx, hy, Int.sub_self, Int.zero_emod]

theorem emod4096_add {x y : Int} (hx : x % 4096 = 0) (hy : y % 4096 = 0) :
    (x + y) % 4096 = 0 := by
  rw [Int.add_emod, hx, hy, Int.add_zero, Int.zero_emod]

/-- `ofInt` of a page-aligned value is page aligned. -/
theorem ofInt_emod4096 (z : Int) (h0 : 0 ≤ z) (h64 : z < 2 ^ 64) (hm : z % 4096 = 0) :
    ((BitVec.ofInt 64 z).toNat : Int) % 4096 = 0 := by
  rw [bv_ofInt_toNat _ h0 h64]; exact hm

/-- `min` of a positive size and a positive slack. -/
theorem min_sub_pos {szZ loZ aZ : Int} (h1 : 0 < szZ) (h2 : aZ < loZ) :
    0 < min szZ (loZ - aZ) := by
  rw [Int.min_def]; split
  · exact h1
  · omega

/-- The left remnant is nonempty and inside `[ih, ce]`. -/
theorem iv_subtract_left_ineq (a sz : word) (lo : Int) (ih ce : Int)
    (Hsz : 0 < bv_unsigned sz) (Hih : ih ≤ bv_unsigned a)
    (Hce : bv_unsigned a + bv_unsigned sz ≤ ce)
    (Hminpos : 0 < min (bv_unsigned sz) (lo - bv_unsigned a)) :
    0 < bv_unsigned (BitVec.ofInt 64 (min (bv_unsigned sz) (lo - bv_unsigned a)))
      ∧ ih ≤ bv_unsigned a
      ∧ bv_unsigned a + bv_unsigned (BitVec.ofInt 64 (min (bv_unsigned sz) (lo - bv_unsigned a))) ≤ ce := by
  have hsz := bv_unsigned_range_u64 sz
  simp only [two_pow_64] at hsz
  have hmin0 : 0 ≤ min (bv_unsigned sz) (lo - bv_unsigned a) := Int.le_of_lt Hminpos
  have hmin64 : min (bv_unsigned sz) (lo - bv_unsigned a) < 2 ^ 64 :=
    Int.lt_of_le_of_lt (Int.min_le_left _ _) hsz.2
  have hb : ((BitVec.ofInt 64 (min (bv_unsigned sz) (lo - bv_unsigned a))).toNat : Int)
      = min (bv_unsigned sz) (lo - bv_unsigned a) := bv_ofInt_toNat _ hmin0 hmin64
  have hle : min (bv_unsigned sz) (lo - bv_unsigned a) ≤ bv_unsigned sz :=
    Int.min_le_left _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [bv_unsigned]; rw [hb]; exact Hminpos
  · exact Hih
  · simp only [bv_unsigned]; rw [hb]
    exact Int.le_trans (Int.add_le_add_left hle _) Hce

/-- The right remnant is nonempty and inside `[ih, ce]`. -/
theorem iv_subtract_right_ineq (a sz : word) (hi : Int) (ih ce : Int)
    (Hsz : 0 < bv_unsigned sz)
    (Hlt : hi < bv_unsigned a + bv_unsigned sz)
    (Hih : ih ≤ bv_unsigned a)
    (Hce : bv_unsigned a + bv_unsigned sz ≤ ce)
    (Hce64 : ce ≤ 2 ^ 64) :
    0 < bv_unsigned (BitVec.ofInt 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi))
      ∧ ih ≤ bv_unsigned (BitVec.ofInt 64 (max (bv_unsigned a) hi))
      ∧ bv_unsigned (BitVec.ofInt 64 (max (bv_unsigned a) hi))
        + bv_unsigned (BitVec.ofInt 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)) ≤ ce := by
  have ha := bv_unsigned_range_u64 a
  have hsz := bv_unsigned_range_u64 sz
  simp only [two_pow_64] at ha hsz Hce64
  have hmaxlt : max (bv_unsigned a) hi < bv_unsigned a + bv_unsigned sz :=
    Int.max_lt.mpr ⟨by omega, Hlt⟩
  have hmax64 : max (bv_unsigned a) hi < 2 ^ 64 :=
    Int.lt_of_lt_of_le hmaxlt (Int.le_trans Hce Hce64)
  have hmax0 : 0 ≤ max (bv_unsigned a) hi := Int.le_trans ha.1 (Int.le_max_left _ _)
  have hrestpos : 0 < bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi :=
    Int.sub_pos_of_lt hmaxlt
  have hrest0 : 0 ≤ bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi :=
    Int.le_of_lt hrestpos
  have hle : bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi ≤ bv_unsigned sz := by
    rw [Int.max_def]; split <;> omega
  have hrest64 : bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi < 2 ^ 64 :=
    Int.lt_of_le_of_lt hle hsz.2
  have hbb : ((BitVec.ofInt 64 (max (bv_unsigned a) hi)).toNat : Int)
      = max (bv_unsigned a) hi := bv_ofInt_toNat _ hmax0 hmax64
  have hbr : ((BitVec.ofInt 64 (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi)).toNat : Int)
      = bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi := bv_ofInt_toNat _ hrest0 hrest64
  refine ⟨?_, ?_, ?_⟩
  · simp only [bv_unsigned]; rw [hbr]; exact hrestpos
  · simp only [bv_unsigned]; rw [hbb]
    exact Int.le_trans Hih (Int.le_max_left _ _)
  · simp only [bv_unsigned]; rw [hbb, hbr, Int.add_comm, Int.sub_add_cancel]
    exact Hce

/-- The pieces of `iv_subtract` keep the page discipline of the ledger:
    nonempty, page-aligned, inside `[ih, ce]`. -/
theorem iv_subtract_bounds (a sz : word) (lo hi : Int) (q : word × word) (ih ce : Int)
    (Hlo : lo % 4096 = 0) (Hhi : hi % 4096 = 0) (Hsz : 0 < bv_unsigned sz)
    (Hal : bv_unsigned a % 4096 = 0) (Hszl : bv_unsigned sz % 4096 = 0)
    (Hih : ih ≤ bv_unsigned a) (Hce : bv_unsigned a + bv_unsigned sz ≤ ce)
    (Hce64 : ce ≤ 2 ^ 64)
    (Hq : q ∈ iv_subtract a sz lo hi) :
    0 < bv_unsigned q.2 ∧ bv_unsigned q.1 % 4096 = 0 ∧ bv_unsigned q.2 % 4096 = 0
      ∧ ih ≤ bv_unsigned q.1 ∧ bv_unsigned q.1 + bv_unsigned q.2 ≤ ce := by
  have hdvL : (4096 : Int) ∣ lo := Int.dvd_of_emod_eq_zero Hlo
  have hdvH : (4096 : Int) ∣ hi := Int.dvd_of_emod_eq_zero Hhi
  have hdvA : (4096 : Int) ∣ bv_unsigned a := Int.dvd_of_emod_eq_zero Hal
  have hdvSz : (4096 : Int) ∣ bv_unsigned sz := Int.dvd_of_emod_eq_zero Hszl
  unfold iv_subtract at Hq
  dsimp only at Hq
  by_cases h1 : bv_unsigned a < lo
  · by_cases h2 : hi < bv_unsigned a + bv_unsigned sz
    · rw [ite_eq_left h1, ite_eq_left h2] at Hq
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at Hq
      rcases Hq with hq | hq
      · rw [hq]
        obtain ⟨P1, P2, P3⟩ :=
          iv_subtract_left_ineq a sz lo ih ce Hsz Hih Hce (min_sub_pos Hsz h1)
        have hmm : min (bv_unsigned sz) (lo - bv_unsigned a) % 4096 = 0 := by
          refine Int.emod_eq_zero_of_dvd ?_
          rw [Int.min_def]; split
          · exact hdvSz
          · exact Int.dvd_sub hdvL hdvA
        have hminpos := min_sub_pos Hsz h1
        have hszr := bv_unsigned_range_u64 sz
        have hm := ofInt_emod4096 _ (Int.le_of_lt hminpos)
          (Int.lt_of_le_of_lt (Int.min_le_left _ _) hszr.2) hmm
        exact ⟨P1, Int.emod_eq_zero_of_dvd hdvA, hm, P2, P3⟩
      · rw [hq]
        obtain ⟨P1, P2, P3⟩ := iv_subtract_right_ineq a sz hi ih ce Hsz h2 Hih Hce Hce64
        have hmm1 : max (bv_unsigned a) hi % 4096 = 0 := by
          refine Int.emod_eq_zero_of_dvd ?_
          rw [Int.max_def]; split
          · exact hdvH
          · exact hdvA
        have hmm2 : (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi) % 4096 = 0 := by
          refine Int.emod_eq_zero_of_dvd ?_
          exact Int.dvd_sub (Int.dvd_add hdvA hdvSz) (Int.dvd_of_emod_eq_zero hmm1)
        have har := bv_unsigned_range_u64 a
        have hszr := bv_unsigned_range_u64 sz
        have hmlt : max (bv_unsigned a) hi < bv_unsigned a + bv_unsigned sz :=
          Int.max_lt.mpr ⟨by omega, h2⟩
        have hce64 : bv_unsigned a + bv_unsigned sz ≤ 2 ^ 64 := Int.le_trans Hce Hce64
        have hm1 : ((BitVec.ofInt 64 (max (bv_unsigned a) hi)).toNat : Int) % 4096 = 0 :=
          ofInt_emod4096 _ (Int.le_trans har.1 (Int.le_max_left _ _))
            (Int.lt_of_lt_of_le hmlt hce64) hmm1
        have hrestle : bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi
            ≤ bv_unsigned sz := by
          rw [Int.max_def]; split <;> omega
        have hm2 : ((BitVec.ofInt 64 (bv_unsigned a + bv_unsigned sz
              - max (bv_unsigned a) hi)).toNat : Int) % 4096 = 0 :=
          ofInt_emod4096 _ (Int.le_of_lt (Int.sub_pos_of_lt hmlt))
            (Int.lt_of_le_of_lt hrestle hszr.2) hmm2
        exact ⟨P1, hm1, hm2, P2, P3⟩
    · rw [ite_eq_left h1, ite_eq_right h2, List.append_nil] at Hq
      simp only [List.mem_singleton] at Hq
      rw [Hq]
      obtain ⟨P1, P2, P3⟩ := iv_subtract_left_ineq a sz lo ih ce Hsz Hih Hce (min_sub_pos Hsz h1)
      have hmm : min (bv_unsigned sz) (lo - bv_unsigned a) % 4096 = 0 := by
        refine Int.emod_eq_zero_of_dvd ?_
        rw [Int.min_def]; split
        · exact hdvSz
        · exact Int.dvd_sub hdvL hdvA
      have hminpos := min_sub_pos Hsz h1
      have hszr := bv_unsigned_range_u64 sz
      have hm := ofInt_emod4096 _ (Int.le_of_lt hminpos)
        (Int.lt_of_le_of_lt (Int.min_le_left _ _) hszr.2) hmm
      exact ⟨P1, Int.emod_eq_zero_of_dvd hdvA, hm, P2, P3⟩
  · by_cases h2 : hi < bv_unsigned a + bv_unsigned sz
    · rw [ite_eq_right h1, ite_eq_left h2, List.nil_append] at Hq
      simp only [List.mem_singleton] at Hq
      rw [Hq]
      obtain ⟨P1, P2, P3⟩ := iv_subtract_right_ineq a sz hi ih ce Hsz h2 Hih Hce Hce64
      have hmm1 : max (bv_unsigned a) hi % 4096 = 0 := by
        refine Int.emod_eq_zero_of_dvd ?_
        rw [Int.max_def]; split
        · exact hdvH
        · exact hdvA
      have hmm2 : (bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi) % 4096 = 0 := by
        refine Int.emod_eq_zero_of_dvd ?_
        exact Int.dvd_sub (Int.dvd_add hdvA hdvSz) (Int.dvd_of_emod_eq_zero hmm1)
      have har := bv_unsigned_range_u64 a
      have hszr := bv_unsigned_range_u64 sz
      have hmlt : max (bv_unsigned a) hi < bv_unsigned a + bv_unsigned sz :=
        Int.max_lt.mpr ⟨by omega, h2⟩
      have hce64 : bv_unsigned a + bv_unsigned sz ≤ 2 ^ 64 := Int.le_trans Hce Hce64
      have hm1 : ((BitVec.ofInt 64 (max (bv_unsigned a) hi)).toNat : Int) % 4096 = 0 :=
        ofInt_emod4096 _ (Int.le_trans har.1 (Int.le_max_left _ _))
          (Int.lt_of_lt_of_le hmlt hce64) hmm1
      have hrestle : bv_unsigned a + bv_unsigned sz - max (bv_unsigned a) hi ≤ bv_unsigned sz := by
        rw [Int.max_def]; split <;> omega
      have hm2 : ((BitVec.ofInt 64 (bv_unsigned a + bv_unsigned sz
            - max (bv_unsigned a) hi)).toNat : Int) % 4096 = 0 :=
        ofInt_emod4096 _ (Int.le_of_lt (Int.sub_pos_of_lt hmlt))
          (Int.lt_of_le_of_lt hrestle hszr.2) hmm2
      exact ⟨P1, hm1, hm2, P2, P3⟩
    · rw [ite_eq_right h1, ite_eq_right h2] at Hq
      simp at Hq

/-- Every piece of a page-aligned ledger stays in the page discipline. -/
theorem maps_subtract_bounds (l : List (word × word)) (lo hi ih ce : Int)
    (Hlo : lo % 4096 = 0) (Hhi : hi % 4096 = 0) (Hce64 : ce ≤ 2 ^ 64)
    (HB : ∀ iv ∈ l, 0 < bv_unsigned iv.2 ∧ bv_unsigned iv.1 % 4096 = 0
      ∧ bv_unsigned iv.2 % 4096 = 0 ∧ ih ≤ bv_unsigned iv.1
      ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ ce) :
    ∀ iv ∈ maps_subtract l lo hi, 0 < bv_unsigned iv.2 ∧ bv_unsigned iv.1 % 4096 = 0
      ∧ bv_unsigned iv.2 % 4096 = 0 ∧ ih ≤ bv_unsigned iv.1
      ∧ bv_unsigned iv.1 + bv_unsigned iv.2 ≤ ce := by
  induction l with
  | nil => intro iv hiv; simp [maps_subtract] at hiv
  | cons hd tl ih' =>
      obtain ⟨a, sz⟩ := hd
      obtain ⟨B1, B2, B3, B4, B5⟩ := HB (a, sz) (List.mem_cons_self ..)
      simp only [Prod.fst, Prod.snd] at B1 B2 B3 B4 B5
      intro iv hiv
      simp only [maps_subtract, List.mem_append] at hiv
      rcases hiv with hiv | hiv
      · exact iv_subtract_bounds a sz lo hi iv ih ce Hlo Hhi B1 B2 B3 B4 B5 Hce64 hiv
      · exact ih' (fun iv hiv => HB iv (List.mem_cons_of_mem _ hiv)) iv hiv

/-! ## 11. The checker-side library (`Section Nodes`)

   re-opens the standard parameter block of `AsanNodesIface` here
  (`SEGS A nx0 LIMIT SINV argH FS0` plus its hypotheses, and `PLACEMENT` in
  the mmap sections).  The definitions below need none of them. -/

/-- The kinds that leave the granted range PROT_NONE. -/
def kind_none (k : mkind) : Bool :=
  match k with
  | .KNONE | .KNONELAZY => true
  | _ => false

/-- The kinds that leave the granted range lazy. -/
def kind_lazy (k : mkind) : Bool :=
  match k with
  | .KRWLAZY | .KNONELAZY => true
  | _ => false

/-- Post-state of a grant: the new range is the newest `vm_maps` entry, the
    `vm_noaccess` / lazy ledgers grow exactly for the KINDS that say so, and
    every other component of the model is untouched. -/
structure grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop where
  gp_maps : (m_vmmaps model').vm_maps = (a, n) :: (m_vmmaps model).vm_maps
  gp_res : (m_vmmaps model').vm_reserved = (m_vmmaps model).vm_reserved
  gp_noacc : (m_vmmaps model').vm_noaccess
    = (if kind_none kd then [(a, n)] else []) ++ (m_vmmaps model).vm_noaccess
  gp_lazy : m_vm_lazy model' = (if kind_lazy kd then [(a, n)] else []) ++ m_vm_lazy model
  gp_mat : m_vm_materialized model' = m_vm_materialized model
  gp_limit : (m_vmmaps model').vm_limit = (m_vmmaps model).vm_limit
  gp_brk : (m_vmmaps model').vm_brk = (m_vmmaps model).vm_brk
  gp_sbrk : (m_vmmaps model').vm_start_brk = (m_vmmaps model).vm_start_brk
  gp_mbase : (m_vmmaps model').vm_mmap_base = (m_vmmaps model).vm_mmap_base
  gp_halted : m_halted model' = m_halted model
  gp_fds : m_fds model' = m_fds model
  gp_fs : m_fs model' = m_fs model
  gp_tid : m_tid model' = m_tid model
  gp_isp : (m_vmmaps model').vm_init_sp = (m_vmmaps model).vm_init_sp

/-- The memory side of a grant: outside the range nothing changes, inside it
    the range reads `none` (`kind_none`) or zero. -/
def grant_mem (kd : mkind) (a n : word) (FULL FULL' : word → Option byte) : Prop :=
  (∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x →
      FULL' x = FULL x)
  ∧ (∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + bv_unsigned n →
      FULL' x = if kind_none kd then none else some (Z_to_bv 8 0))

/-- The NULL-hint grant's successor state: a fresh variable places the range
    at `v * 4096`, the knowledge records the alignment range, the two joint
    end facts and the disjointness from the tracked ledger, and the visible
    application ranges keep their shadow facts. -/
def null_cs1 (A : atable) (cs : acs) (kd : mkind) (eager : Bool) (ne : expr)
    (nlo nhi : Int) : acs :=
  let v := nxt cs
  let base := escale 4096 (.EVar v)
  add_entry cs (sr_upd cs.a_ss.s_regs 10 base)
    ((.KRange (.EVar v) (KHI / 4096 + 1) ((CEIL - nlo) / 4096) ::
        null_kend base ne nlo ++ kdisj_new cs.a_maps base ne)
      ++ kn_grant_filter A (kn cs) cs.a_maps)
    (Nat.succ v) (amap.mk base ne kd) nhi eager (cs.a_ylo - 2 * nhi)

/-- The MAP_FIXED grant's successor state: the fixed address (register 10) is
    the base, and for a lazy rw kind the shadow facts of every visible
    application range are added on top of the grant filter. -/
def fixed_cs1 (A : atable) (cs : acs) (kd : mkind) (eager : Bool) (ne : expr)
    (nhi : Int) : acs :=
  let k := kn cs
  let m := amap.mk (reg cs 10) ne kd
  let ksh := if mkind_eqb kd .KRWLAZY then
      cs.a_vis.flatMap (fun p => shadow_facts A k [m] p.1 p.2)
    else []
  add_entry cs cs.a_ss.s_regs (ksh ++ kn_grant_filter A k (cs.a_maps)) (nxt cs) m nhi eager
    cs.a_ylo

/-- The four arms of the mprotect slice node: `SlE` / `SlF` / `SlG` / `SlM`
    (enter / fill / grant-empty / mixed). -/
inductive slarm : Type
  | SlE | SlF | SlG | SlM
  deriving DecidableEq, Repr

/-- Only `SlG` leaves the range NOT-VISIBLE (`noaccess`). -/
def sl_nn (s : slarm) : Bool :=
  match s with
  | .SlG => true
  | _ => false

/-- `SlE` / `SlM` charge the eager budget. -/
def sl_charge (s : slarm) : Bool :=
  match s with
  | .SlE | .SlM => true
  | _ => false

/-- The model side of a slice: `vm_maps` untouched, `vm_noaccess` grown for
    `SlG`, the lazy ledger extended / cut by arm and the materialized pages
    dropped by arm. -/
structure slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop where
  sp_maps : (m_vmmaps model').vm_maps = (m_vmmaps model).vm_maps
  sp_res : (m_vmmaps model').vm_reserved = (m_vmmaps model).vm_reserved
  sp_noacc : (m_vmmaps model').vm_noaccess
    = (if sl_nn s then [(addr, n)] else [])
      ++ maps_subtract ((m_vmmaps model).vm_noaccess) (bv_unsigned addr)
        (bv_unsigned addr + bv_unsigned n)
  sp_lazy : m_vm_lazy model' =
    match s with
    | .SlM => m_vm_lazy model
    | .SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr)
        (bv_unsigned addr + bv_unsigned n)
    | _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  sp_mat : m_vm_materialized model' =
    match s with
    | .SlM => m_vm_materialized model
    | _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
        (m_vm_materialized model)
  sp_limit : (m_vmmaps model').vm_limit = (m_vmmaps model).vm_limit
  sp_brk : (m_vmmaps model').vm_brk = (m_vmmaps model).vm_brk
  sp_sbrk : (m_vmmaps model').vm_start_brk = (m_vmmaps model).vm_start_brk
  sp_mbase : (m_vmmaps model').vm_mmap_base = (m_vmmaps model).vm_mmap_base
  sp_halted : m_halted model' = m_halted model
  sp_fds : m_fds model' = m_fds model
  sp_fs : m_fs model' = m_fs model
  sp_tid : m_tid model' = m_tid model
  sp_isp : (m_vmmaps model').vm_init_sp = (m_vmmaps model).vm_init_sp

/-- The memory side of a slice. -/
def slice_mem (s : slarm) (addr n : word) (FULL FULL' : word → Option byte) : Prop :=
  (∀ x : word, bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x →
      FULL' x = FULL x)
  ∧ (∀ x : word, bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + bv_unsigned n →
      FULL' x = if sl_nn s then none else some (Z_to_bv 8 0))

/-- The common situation of the four slice arms. -/
structure slice_hyps (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte) : Prop where
  sh_C : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model
  sh_m : m ∈ cs.a_maps
  sh_nf : is_fog m = false
  sh_Un : bv_unsigned n = nZ
  sh_pos : 0 < nZ
  sh_nal : nZ % 4096 = 0
  sh_al : bv_unsigned addr % 4096 = 0
  sh_in1 : bv_unsigned (edenot E m.am_base) ≤ bv_unsigned addr
  sh_in2 : bv_unsigned addr + nZ ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
  sh_post : slice_post s addr n model model'
  sh_mem : slice_mem s addr n FULL FULL'
  sh_F : s = .SlF → m.am_kind = .KRWLAZY
  sh_nF : s ≠ .SlF → m.am_kind ≠ .KRWLAZY

/-- The model side of a destruction. -/
structure dest_post (addr n : word) (model model' : Model) : Prop where
  dp_maps : (m_vmmaps model').vm_maps
    = maps_subtract ((m_vmmaps model).vm_maps) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  dp_res : (m_vmmaps model').vm_reserved = (m_vmmaps model).vm_reserved
  dp_noacc : (m_vmmaps model').vm_noaccess
    = maps_subtract ((m_vmmaps model).vm_noaccess) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  dp_lazy : m_vm_lazy model'
    = maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  dp_mat : m_vm_materialized model'
    = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
        (m_vm_materialized model)
  dp_limit : (m_vmmaps model').vm_limit = (m_vmmaps model).vm_limit
  dp_brk : (m_vmmaps model').vm_brk = (m_vmmaps model).vm_brk
  dp_sbrk : (m_vmmaps model').vm_start_brk = (m_vmmaps model).vm_start_brk
  dp_mbase : (m_vmmaps model').vm_mmap_base = (m_vmmaps model).vm_mmap_base
  dp_halted : m_halted model' = m_halted model
  dp_fds : m_fds model' = m_fds model
  dp_fs : m_fs model' = m_fs model
  dp_tid : m_tid model' = m_tid model
  dp_isp : (m_vmmaps model').vm_init_sp = (m_vmmaps model).vm_init_sp

/-- The memory side of a destruction: outside unchanged, inside `none`. -/
def dest_mem (addr n : word) (FULL FULL' : word → Option byte) : Prop :=
  (∀ x : word, bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x →
      FULL' x = FULL x)
  ∧ (∀ x : word, bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + bv_unsigned n →
      FULL' x = none)

/-- The common situation of the destroyed child. -/
structure dest_hyps (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte) : Prop where
  dh_C : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model
  dh_m : m ∈ cs.a_maps
  dh_nf : is_fog m = false
  dh_Un : bv_unsigned n = nZ
  dh_pos : 0 < nZ
  dh_nal : nZ % 4096 = 0
  dh_al : bv_unsigned addr % 4096 = 0
  dh_in1 : bv_unsigned (edenot E m.am_base) ≤ bv_unsigned addr
  dh_in2 : bv_unsigned addr + nZ ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
  dh_post : dest_post addr n model model'
  dh_mem : dest_mem addr n FULL FULL'

/-! ## 11b. Small shared facts -/

/-- The allocation ceiling is the address table's. -/
theorem CEIL_eq : alloc_ceiling = CEIL := rfl

/-- `kHighMemBeg` is the placement split's. -/
theorem KHI_eq : kHighMemBeg = KHI := rfl

/-- The floor is the placement policy's. -/
theorem FLOOR_eq : bottomup_floor = FLOOR := rfl

/-- `2^64 - 1` is `-1` as a word. -/
theorem Z_to_bv64_m1 (m1 : Int) (H : m1 = two64 - 1) :
    Z_to_bv 64 m1 = Z_to_bv 64 (-1) := by
  subst H
  unfold two64 Z_to_bv
  decide

theorem bv5_of_nat (n : Nat) (H : n < 32) : Z_to_bv 5 (n : Int) = Z_to_bv 5 (n : Int) := rfl
theorem bv5_10 : (10 : BitVec 5) = Z_to_bv 5 10 := by decide
theorem bv5_11 : (11 : BitVec 5) = Z_to_bv 5 11 := by decide
theorem bv5_12 : (12 : BitVec 5) = Z_to_bv 5 12 := by decide
theorem bv5_13 : (13 : BitVec 5) = Z_to_bv 5 13 := by decide
theorem bv5_14 : (14 : BitVec 5) = Z_to_bv 5 14 := by decide
theorem bv5_15 : (15 : BitVec 5) = Z_to_bv 5 15 := by decide
theorem bv5_17 : (17 : BitVec 5) = Z_to_bv 5 17 := by decide

theorem some_inj {T : Type} (a b : T) (H : some a = some b) : a = b := by
  injection H with h

/-- The refused child: exactly the state the checker's `refuse` builds. -/
theorem refuse_eq (cs : acs) :
    refuse cs = with_ss cs (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (.ELit ENOMEM_RET))
      (kn cs) (nxt cs)) := by
  unfold refuse
  rfl

theorem refuse_pc (cs : acs) : pc (refuse cs) = pc cs + 4 := by
  unfold refuse
  rfl

theorem refuse_nxt (cs : acs) : nxt (refuse cs) = nxt cs := by
  unfold refuse
  rfl

/-- The gap weight, in closed form. -/
theorem gap_weight_eq (nZ : Int) (l : List (word × word)) :
    gap_weight nZ l = sum_sizes l + (l.length : Int) * (nZ + 4095) := by
  induction l with
  | nil => simp [gap_weight, sum_sizes]
  | cons h t ih =>
      obtain ⟨b, sz⟩ := h
      simp only [gap_weight, sum_sizes, List.length_cons, bv_unsigned]
      rw [ih]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega

/-- An aligned range is its own lazy interior. -/
theorem lazy_interior_fresh (a n : word) (H1 : bv_unsigned a % 4096 = 0)
    (H2 : bv_unsigned n % 4096 = 0) (H3 : 0 < bv_unsigned n)
    (H4 : bv_unsigned a + bv_unsigned n ≤ 2 ^ 64) : lazy_interior a n = [(a, n)] :=
  lazy_interior_aligned a n H1 H2 H3 H4

/-- `null_kend` carries no image fact. -/
theorem null_kend_pure (base ne : expr) (nlo : Int) :
    ∀ K ∈ null_kend base ne nlo, (match K with | .KImg _ _ => False | _ => True) := by
  intro K hK
  unfold null_kend at hK
  cases ne with
  | ELit z => simp at hK
  | _ =>
      simp only [List.mem_singleton] at hK
      subst hK
      trivial

/-- `kimg_in_hull` holds when there is no image fact. -/
theorem kimg_in_hull_pure (A : atable) (k : List kentry)
    (H : ∀ K ∈ k, (match K with | .KImg _ _ => False | _ => True)) : kimg_in_hull A k := by
  intro K hK
  have h := H K hK
  cases K with
  | KImg lo hi => exact h.elim
  | _ => trivial

/-- What survives a cut covers exactly the uncut points. -/
theorem covered_maps_subtract (l : List (word × word)) (lo hi : Int)
    (Hwf : ivs_wf l) (Hlh : lo ≤ hi) (x : Int) :
    covered (maps_subtract l lo hi) x = (covered l x && !(in_rng lo hi x)) :=
  (maps_subtract_sem l lo hi Hwf Hlh).2.2 x

/-! ## 11c. Slice / destroyed helpers -/

/-- A hole token is a token. -/
theorem tok_of_hole (k : mkind) (H : mkind_eqb k .KHOLE = true) : is_tok_kind k = true := by
  cases k <;> simp_all [mkind_eqb, is_tok_kind]

/-- Two non-image facts in front of an image-free list. -/
theorem kimg_in_hull_cons2 (A : atable) (K1 K2 : kentry) (k : List kentry)
    (H1 : match K1 with | .KImg _ _ => False | _ => True)
    (H2 : match K2 with | .KImg _ _ => False | _ => True)
    (H : kimg_in_hull A k) : kimg_in_hull A (K1 :: K2 :: k) := by
  intro K hK
  rcases List.mem_cons.mp hK with h1 | hK
  · rw [h1]
    cases K1 with
    | KImg lo hi => exact H1.elim
    | _ => trivial
  · rcases List.mem_cons.mp hK with h2 | hK
    · rw [h2]
      cases K2 with
      | KImg lo hi => exact H2.elim
      | _ => trivial
    · exact H K hK

/-- The allowed set only depends on `a_vis`. -/
theorem in_allow_ext (A : atable) (E : env) (cs cs' : acs) (H : cs'.a_vis = cs.a_vis) :
    in_allow A E cs' = in_allow A E cs := by
  funext z
  unfold in_allow in_vis in_sh
  rw [H]

/-- Tokens in front of a matched ledger do not change what it matches. -/
theorem maps_match_tok_prefix (E : env) (hp ms : List amap) (l : List (word × word))
    (Hf : ∀ m0 ∈ hp, is_fog m0 = true) (HM : maps_match E ms l) :
    maps_match E (hp ++ ms) l := by
  induction hp with
  | nil => simpa using HM
  | cons h t ih =>
      have hh : is_fog h = true := Hf h (List.mem_cons_self ..)
      rw [List.cons_append, maps_match]
      rw [ite_eq_left hh]
      exact Or.inl (ih (fun x hx => Hf x (List.mem_cons_of_mem _ hx)))

/-- Punching a hole (turning it into a fog token) does not change what the
    ledger denotes. -/
theorem maps_match_unhole (E : env) (ms : List amap) (h : amap) (l : List (word × word)) :
    maps_match E ms l ↔ maps_match E (unhole ms h) l := by
  induction ms generalizing l with
  | nil => simp [unhole, maps_match]
  | cons m t ih =>
      by_cases hc : (is_hole m && amap_eqb m h) = true
      · -- the head is the hole: it becomes a KFOG token of the same extent
        have hhole : is_hole m = true := (Bool.and_eq_true ..).mp hc |>.1
        have hfog : is_fog m = true := by
          unfold is_hole at hhole
          exact tok_of_hole m.am_kind hhole
        have hfog' : is_fog (amap.mk m.am_base m.am_len .KFOG) = true := by
          simp [is_fog, is_tok_kind]
        have hun : unhole (m :: t) h
            = (amap.mk m.am_base m.am_len .KFOG) :: unhole t h := by
          unfold unhole
          simp only [List.map_cons]
          rw [ite_eq_left hc]
        rw [hun, maps_match, maps_match, ite_eq_left hfog, ite_eq_left hfog']
        constructor
        · rintro (H | ⟨iv, l', rfl, Hsz, HM⟩)
          · exact Or.inl ((ih l).mp H)
          · exact Or.inr ⟨iv, l', rfl, Hsz, (ih l').mp HM⟩
        · rintro (H | ⟨iv, l', rfl, Hsz, HM⟩)
          · exact Or.inl ((ih l).mpr H)
          · exact Or.inr ⟨iv, l', rfl, Hsz, (ih l').mpr HM⟩
      · have hun : unhole (m :: t) h = m :: unhole t h := by
          unfold unhole
          simp only [List.map_cons]
          rw [ite_eq_right hc]
        rw [hun]
        by_cases hfog : is_fog m = true
        · rw [maps_match, maps_match, ite_eq_left hfog, ite_eq_left hfog]
          constructor
          · rintro (H | ⟨iv, l', rfl, Hsz, HM⟩)
            · exact Or.inl ((ih l).mp H)
            · exact Or.inr ⟨iv, l', rfl, Hsz, (ih l').mp HM⟩
          · rintro (H | ⟨iv, l', rfl, Hsz, HM⟩)
            · exact Or.inl ((ih l).mpr H)
            · exact Or.inr ⟨iv, l', rfl, Hsz, (ih l').mpr HM⟩
        · rw [maps_match, maps_match, ite_eq_right hfog, ite_eq_right hfog]
          constructor
          · rintro ⟨l', rfl, HM⟩
            exact ⟨l', rfl, (ih l').mp HM⟩
          · rintro ⟨l', rfl, HM⟩
            exact ⟨l', rfl, (ih l').mpr HM⟩

/-- `mmap_len_sound`: the length argument.  Both arms of
    `mmap_len_ref` pin the register, the bounds and the page-rounded length
    expression; the knowledge-derived arm gets its `mod 4096 = 0` from
    `ealign_sound`'s divisibility. -/
theorem mmap_len_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (ne : expr) (nlo nhi : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HML : mmap_len cs = some (ne, nlo, nhi)) :
    let len := bv_unsigned (edenot E (reg cs 11))
    getr R (Z_to_bv 5 11) = Z_to_bv 64 len ∧ 0 < len ∧ len < 2 ^ 64 ∧
    edenot E ne = Z_to_bv 64 (page_round_up_Z len) ∧
    0 < nlo ∧ nlo ≤ page_round_up_Z len ∧ page_round_up_Z len ≤ nhi ∧
    page_round_up_Z len % 4096 = 0 ∧
    (∀ E', edenot E' (reg cs 11) = edenot E (reg cs 11) → edenot E' ne = edenot E ne) := by
  dsimp only
  have HK := HC.co_know
  have hidx : Z_to_bv 5 ((11 : Nat) : Int) = Z_to_bv 5 (11 : Int) := by decide
  have R11 : getr R (Z_to_bv 5 11) = edenot E (reg cs 11) :=
    reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 HC ⟨by omega, by omega⟩
  have Hu64 := u64_range (edenot E (reg cs 11))
  rw [mmap_len_eq] at HML
  cases h11 : reg_lit cs 11 with
  | some lz =>
      by_cases hpos : 0 < lz
      · simp only [mmap_len_ref, h11, ite_eq_left hpos] at HML
        simp only [Option.some.injEq, Prod.mk.injEq] at HML
        obtain ⟨hne, hnlo, hnhi⟩ := HML
        subst hne; subst hnlo; subst hnhi
        obtain ⟨R11', Hlz0, Hlz1⟩ :=
          reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 lz HC
            ⟨by omega, by omega⟩ h11
        rw [hidx] at R11'
        have Hlen : bv_unsigned (edenot E (reg cs 11)) = lz := by
          rw [← R11, R11']
          exact u64_lit lz ⟨Hlz0, Hlz1⟩
        have hb := (AllocSim.page_round_up_Z_bounds lz (by omega)).1
        rw [Hlen, edenot_lit, page_up_eq]
        refine ⟨?_, hpos, Hlz1, rfl, by omega, Int.le_refl _, Int.le_refl _,
          page_round_up_Z_aligned' lz, ?_⟩
        · exact R11'
        · intro E' _; rfl
      · simp only [mmap_len_ref, h11, ite_eq_right hpos] at HML
        simp at HML
  | none =>
      simp only [mmap_len_ref, h11] at HML
      split at HML
      · rename_i lo hi hxl hxh
        by_cases hc : (0 < lo && 12 ≤ ealign (kn cs) (reg cs 11) && hi ≤ zpow 2 46) = true
        · rw [ite_eq_left hc] at HML
          simp only [Option.some.injEq, Prod.mk.injEq] at HML
          obtain ⟨hne, hnlo, hnhi⟩ := HML
          subst hne; subst hnlo; subst hnhi
          have hcl : (0 < lo ∧ 12 ≤ ealign (kn cs) (reg cs 11)) ∧ hi ≤ zpow 2 46 := by
            have h := hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact h
          obtain ⟨⟨hlo, hal⟩, hhi⟩ := hcl
          have B1 := xlo_sound SEGS E (Mr A argH E cs model FULL) (kn cs) (reg cs 11) lo HK hxl
          have B2 := xhi_sound SEGS E (Mr A argH E cs model FULL) (kn cs) (reg cs 11) hi HK hxh
          obtain ⟨he0, he64⟩ :=
            (ealign_sound SEGS E (Mr A argH E cs model FULL) (kn cs) (reg cs 11) HK).1
          have hdvd :=
            (ealign_sound SEGS E (Mr A argH E cs model FULL) (kn cs) (reg cs 11) HK).2
          have h12n : (12 : Nat) ≤ (ealign (kn cs) (reg cs 11)).toNat :=
            (Int.le_toNat he0).mpr hal
          have h4096 : (4096 : Int) ∣ (2 : Int) ^ (ealign (kn cs) (reg cs 11)).toNat := by
            refine ⟨2 ^ ((ealign (kn cs) (reg cs 11)).toNat - 12), ?_⟩
            rw [show (2 : Int) ^ (ealign (kn cs) (reg cs 11)).toNat
                  = (2 : Int) ^ (12 : Nat) * 2 ^ ((ealign (kn cs) (reg cs 11)).toNat - 12) from by
                rw [← Int.pow_add, show 12 + ((ealign (kn cs) (reg cs 11)).toNat - 12)
                      = (ealign (kn cs) (reg cs 11)).toNat from by omega]]
            rfl
          have hlen4096 : (4096 : Int) ∣ bv_unsigned (edenot E (reg cs 11)) :=
            Int.dvd_trans h4096 hdvd
          have Hmod : bv_unsigned (edenot E (reg cs 11)) % 4096 = 0 :=
            Int.emod_eq_zero_of_dvd hlen4096
          have Hpr : page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))
              = bv_unsigned (edenot E (reg cs 11)) :=
            AllocSim.page_round_up_Z_aligned _ (by omega) Hmod
          rw [Hpr]
          refine ⟨?_, by omega, Hu64.2, ?_, by omega, by omega, by omega, Hmod, ?_⟩
          · rw [R11]; exact (AxSymExec3Sound.ofInt_toNat _).symm
          · exact (AxSymExec3Sound.ofInt_toNat _).symm
          · intro E' hE'; exact hE'
        · rw [ite_eq_right hc] at HML
          simp at HML
      · simp at HML

/-- `reserved_free_above`: the reserved intervals are apart
    from anything at or above the image hull. -/
theorem reserved_free_above (SEGS : List Segment) (A : atable) (model : Model)
    (lo n : word) (RES_hullH : RES_hull_def SEGS A)
    (Hres : (m_vmmaps model).vm_reserved = segments_reserved SEGS)
    (Hlo : A.img_hi ≤ bv_unsigned lo) :
    region_free ((m_vmmaps model).vm_reserved) lo n = true := by
  rw [Hres]
  refine RefNodes.region_free_intro _ lo n ?_
  intro b s Hin
  obtain ⟨H1, H2⟩ := RES_hullH (b, s) Hin
  dsimp only at H1 H2
  right
  simp only [bv_unsigned] at H1 H2 Hlo ⊢
  omega

/-- Inversion of `vis_add` as far as the other conjuncts need it. -/
theorem vis_add_inv (A : atable) (LIMIT : Int) (cs : acs) (b n : expr)
    (k : List kentry) (cs2 : acs) (Hv : vis_add A LIMIT cs b n k = some cs2) :
    ∃ nhi, xhi (kn cs) n = some nhi ∧
      cs2 = { a_ss := mk_ss (pc cs) cs.a_ss.s_regs
                (shadow_facts A (kn cs) cs.a_maps b n ++ k) (nxt cs),
              a_maps := cs.a_maps, a_totsz := cs.a_totsz, a_ylo := cs.a_ylo,
              a_eager := cs.a_eager, a_vis := (b, n) :: cs.a_vis, a_ghost := cs.a_ghost,
              a_abytes := cs.a_abytes + vis_cost nhi, a_brk := cs.a_brk, a_fd := cs.a_fd,
              a_tidset := cs.a_tidset } := by
  rw [vis_add_eq] at Hv
  unfold vis_add_ref at Hv
  simp only [] at Hv
  cases hx : xhi (kn cs) n with
  | none => rw [hx] at Hv; cases Hv
  | some nhi =>
    rw [hx] at Hv
    simp only [] at Hv
    split at Hv
    · simp only [Option.some.injEq] at Hv
      exact ⟨nhi, rfl, Hv.symm⟩
    · simp at Hv

/-- `page_aligned_sound`. -/
theorem page_aligned_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e : expr) (HK : know_ok SEGS E M k)
    (H : page_aligned k e = true) : bv_unsigned (edenot E e) % 4096 = 0 := by
  unfold page_aligned at H
  have GEN : 12 ≤ ealign k e → bv_unsigned (edenot E e) % 4096 = 0 := by
    intro Hle
    obtain ⟨-, Hdiv⟩ := ealign_sound SEGS E M k e HK
    have hdvd : zpow 2 12 ∣ bv_unsigned (edenot E e) :=
      Int.dvd_trans (pow2_divide_le 12 (ealign k e) ⟨by omega, Hle⟩) Hdiv
    have h4096 : (4096 : Int) = zpow 2 12 := by decide
    rw [h4096]
    exact Int.emod_eq_zero_of_dvd hdvd
  cases e with
  | ELit z =>
    have hz : z % 4096 = 0 := by
      have h' : (z % 4096 == 0) = true := H
      simpa using h'
    have hu : bv_unsigned (edenot E (.ELit z)) = z % two64 := u_lit64 z
    rw [hu]
    rw [show two64 = (2:Int)^64 from rfl]
    rw [Int.emod_emod_of_dvd z (by decide : (4096:Int) ∣ (2:Int)^64)]
    exact hz
  | EVar n => exact GEN (of_decide_eq_true H)
  | EAlu a b c => exact GEN (of_decide_eq_true H)
  | EAluw a b c => exact GEN (of_decide_eq_true H)
  | EMd a b c => exact GEN (of_decide_eq_true H)
  | EMdw a b c => exact GEN (of_decide_eq_true H)
  | EExt a b c d => exact GEN (of_decide_eq_true H)
  | EBlob a b c d => exact GEN (of_decide_eq_true H)

/-- Setting a register to the value it already holds. -/
theorem regs_ok_regupd_same (E : env) (sr : List expr) (R : BvMap word) (n : Nat)
    (v : word) (HR : regs_ok E sr R) (Hn : 0 < n ∧ n < 32)
    (Hv : getr R (Z_to_bv 5 (n : Int)) = v) :
    regs_ok E sr (regupd R (Z_to_bv 5 (n : Int)) v) := by
  intro r'
  by_cases h : r' = Z_to_bv 5 (n : Int)
  · rw [h]
    rw [getr_same R (Z_to_bv 5 (n : Int)) v (Z_to_bv_five_ne_zero n Hn.1 Hn.2), ← Hv]
    exact HR (Z_to_bv 5 (n : Int))
  · rw [getr_other R (Z_to_bv 5 (n : Int)) v r' h]
    exact HR r'

/-- `split_flat_estart`. -/
theorem split_flat_estart (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (e b : expr) (off : Int) (n : expr)
    (HK : know_ok SEGS E M k) (Hsp : split_lit e = (b, off))
    (Hfl : flat_x k b off n = true) :
    estart E (SA b off) = bv_unsigned (edenot E e) ∧
      estart E (SA b off) + bv_unsigned (edenot E n) ≤ 2 ^ 64 ∧
      0 < bv_unsigned (edenot E n) := by
  obtain ⟨F1, F2, F3⟩ := flat_x_sound SEGS E M k b off n HK Hfl
  have Up := u_of_split E e b off Hsp ⟨F1, by omega⟩
  exact ⟨Up.symm, F2, F3⟩

/-- Every tracked entry is apart from the fresh region. -/
def maps_apart (E : env) (ms : List amap) (lo n : Int) : Prop :=
  ∀ m, m ∈ ms → is_fog m = false →
    lo + n ≤ bv_unsigned (edenot E m.am_base) ∨
    bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ lo

/-- `maps_apart` from the region-freeness of the ledger. -/
theorem maps_apart_of_region_free (E : env) (ms : List amap) (model : Model) (a n : word)
    (Hmaps : maps_match E ms (m_vmmaps model).vm_maps)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) a n = true) :
    maps_apart E ms (bv_unsigned a) (bv_unsigned n) := by
  intro m Hin Hnf
  rw [region_free_app, Bool.and_eq_true] at Hrf
  exact RefNodes.region_free_In _ a n (edenot E m.am_base) (edenot E m.am_len) Hrf.2
    (maps_match_In E ms (m_vmmaps model).vm_maps m Hmaps Hin Hnf)

/-- `inside_maps` puts a range apart from the fresh region. -/
theorem inside_maps_apart (SEGS : List Segment) (A : atable) (E : env)
    (M : word → Option byte) (k : List kentry) (ms : List amap) (b : expr) (o : Int)
    (l : expr) (lo n : Int) (HK : know_ok SEGS E M k) (Hap : maps_apart E ms lo n)
    (H : inside_maps k ms b o l = true) :
    estart E (SA b o) + elenZ E l ≤ lo ∨ lo + n ≤ estart E (SA b o) := by
  induction ms with
  | nil => simp [inside_maps] at H
  | cons m ms ih =>
      simp only [inside_maps, Bool.or_eq_true, Bool.and_eq_true] at H
      rcases H with ⟨Hnf, H⟩ | H
      · have Hnf' : is_fog m = false := by simpa using Hnf
        obtain ⟨I1, I2⟩ :=
          xinside_sound SEGS E M k b o l m.am_base 0 m.am_len HK H
        simp only [estart, elenZ, SA] at I1 I2 ⊢
        rcases Hap m (by simp) Hnf' with h | h <;> omega
      · exact ih (fun m' hm' => Hap m' (by simp [hm'])) H

/-- `safe_range` puts a range apart from the fresh region. -/
theorem safe_range_apart (SEGS : List Segment) (A : atable) (E : env)
    (M : word → Option byte) (k : List kentry) (ms : List amap) (b : expr) (o : Int)
    (l : expr) (lo n : Int) (HK : know_ok SEGS E M k) (Hap : maps_apart E ms lo n)
    (Hlo : A.img_hi ≤ lo) (Hhi : lo + n ≤ CEIL)
    (H : safe_range A k ms b o l = true) :
    estart E (SA b o) + elenZ E l ≤ lo ∨ lo + n ≤ estart E (SA b o) := by
  unfold safe_range at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · revert H
    cases hx : xhi k l with
    | none =>
      intro H
      simp only [hx] at H
      simp at H
    | some lh =>
      cases hb : base_range k b with
      | none =>
        intro H
        simp only [hx, hb] at H
        simp at H
      | some p =>
        obtain ⟨blo, bhi⟩ := p
        intro H
        simp only [hx, hb] at H
        rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at H
        have L1 := xhi_sound SEGS E M k l lh HK hx
        obtain ⟨B1, B2⟩ := base_range_sound SEGS E M k b blo bhi HK hb
        rcases H with ⟨H1, H2⟩ | ⟨H1, H2⟩
        all_goals
          have h1 := of_decide_eq_true H1
          have h2 := of_decide_eq_true H2
          simp only [estart, elenZ, SA] at *
          omega
  · exact inside_maps_apart SEGS A E M k ms b o l lo n HK Hap H

/-- The kept knowledge's footprint is apart from the fresh region. -/
theorem grant_keep_apart (SEGS : List Segment) (A : atable) (E : env)
    (M : word → Option byte) (k : List kentry) (ms : List amap) (K : kentry)
    (lo n : Int) (HK : know_ok SEGS E M k) (Hap : maps_apart E ms lo n)
    (Hlo : A.img_hi ≤ lo) (Hhi : lo + n ≤ CEIL)
    (H : grant_keep_b A k ms K = true)
    (HnI : match K with | .KImg _ _ => False | _ => True) :
    kfoot_apart E K lo n := by
  cases K with
  | KWord a w v =>
      rw [grant_keep_b, Bool.and_eq_true] at H
      have hw : w ≤ 8 := of_decide_eq_true H.1
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off _ lo n HK Hap Hlo Hhi H.2
      rw [elenZ_lit'' E (w : Int) ⟨by omega, by omega⟩] at D
      show estart E a + (w : Int) ≤ lo ∨ lo + n ≤ estart E a
      exact D
  | KZero a l =>
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off l lo n HK Hap Hlo Hhi H
      show estart E a + elenZ E l ≤ lo ∨ lo + n ≤ estart E a
      exact D
  | KBlob a l c =>
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off l lo n HK Hap Hlo Hhi H
      show estart E a + elenZ E l ≤ lo ∨ lo + n ≤ estart E a
      exact D
  | KImg lo' hi' => simp at HnI
  | KAlign e m => trivial
  | KRange e rlo rhi => trivial
  | KDisj a1 n1 a2 n2 => trivial
  | KWr a l =>
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off l lo n HK Hap Hlo Hhi H
      show estart E a + elenZ E l ≤ lo ∨ lo + n ≤ estart E a
      exact D
  | KFill a l c =>
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off l lo n HK Hap Hlo Hhi H
      show estart E a + elenZ E l ≤ lo ∨ lo + n ≤ estart E a
      exact D
  | KUnk a l =>
      have D := safe_range_apart SEGS A E M k ms a.a_base a.a_off l lo n HK Hap Hlo Hhi H
      show estart E a + elenZ E l ≤ lo ∨ lo + n ≤ estart E a
      exact D

/-- A grant keeps the model's interval discipline. -/
theorem grant_wf (kd : mkind) (a n : word) (model model' : Model)
    (GPo : grant_post kd a n model model') (Hwf : model_ivs_wf model)
    (Hb : bv_unsigned a + bv_unsigned n ≤ 2 ^ 64) : model_ivs_wf model' := by
  obtain ⟨W1, W2, W3, Wsp⟩ := Hwf
  have Hiv : iv_wf (a, n) := Hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GPo.gp_maps]; exact ivs_wf_cons _ _ Hiv W1
  · rw [GPo.gp_noacc]
    cases hk : kind_none kd
    · simpa using W2
    · simpa using ivs_wf_cons (a, n) _ Hiv W2
  · rw [GPo.gp_lazy]
    cases hl : kind_lazy kd
    · simpa using W3
    · simpa using ivs_wf_cons (a, n) _ Hiv W3
  · unfold init_sp_ok at *
    rw [GPo.gp_isp]
    exact Wsp

/-- The kept knowledge holds on any memory that agrees outside the region. -/
theorem kn_grant_filter_ok (SEGS : List Segment) (A : atable) (E : env)
    (M M' : word → Option byte) (k : List kentry) (ms : List amap) (lo n : Int)
    (HK : know_ok SEGS E M k) (Hap : maps_apart E ms lo n) (Hlo : A.img_hi ≤ lo)
    (Hhi : lo + n ≤ CEIL)
    (Hout : ∀ x : word, bv_unsigned x < lo ∨ lo + n ≤ bv_unsigned x → M' x = M x) :
    know_ok SEGS E M' (kn_grant_filter A k ms) := by
  intro K Hin
  unfold kn_grant_filter at Hin
  have Hhull := kimg_clip_in_hull A (List.filter (grant_keep_b A k ms) k) K Hin
  have Hin' := kimg_clip_incl A (List.filter (grant_keep_b A k ms) k) K Hin
  rw [List.mem_filter] at Hin'
  have HKK : kentry_ok SEGS E M K := HK K Hin'.1
  refine kentry_keep_sem SEGS E M M' K lo n HKK ?_ Hout
  cases K with
  | KImg ilo ihi =>
      unfold kfoot_apart
      simp only [kfoot]
      simp only at Hhull
      omega
  | KWord a w v => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KZero a l => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KBlob a l c => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KAlign e m => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KRange e rlo rhi => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KDisj a1 n1 a2 n2 => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KWr a l => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KFill a l c => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial
  | KUnk a l => exact grant_keep_apart SEGS A E M k ms _ lo n HK Hap Hlo Hhi Hin'.2 trivial

/-- Two expressions of the same value. -/
theorem same_val_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (a b : expr) (HK : know_ok SEGS E M k)
    (H : same_val k a b = true) :
    bv_unsigned (edenot E a) = bv_unsigned (edenot E b) := by
  unfold same_val at H
  by_cases he : expr_eqb a b = true
  · rw [ite_eq_left he] at H
    rw [expr_eqb_eq a b he]
  · rw [ite_eq_right he] at H
    by_cases h1 : lin_ge0 k [(a, (0 : Int))] [(b, (0 : Int))] = true
    · rw [ite_eq_left h1] at H
      have X1 := lin_ge0_sound SEGS E M k [(a, (0 : Int))] [(b, (0 : Int))] HK h1
      have X2 := lin_ge0_sound SEGS E M k [(b, (0 : Int))] [(a, (0 : Int))] HK H
      simp only [xt_den] at X1 X2
      omega
    · rw [ite_eq_right h1] at H
      simp at H

/-- The hole token found denotes exactly `[a, a+ne)`. -/
theorem find_hole_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (ms : List amap) (a ne : expr) (h : amap)
    (HK : know_ok SEGS E M k) (H : find_hole k ms a ne = some h) :
    h ∈ ms ∧ is_hole h = true ∧
      bv_unsigned (edenot E h.am_base) = bv_unsigned (edenot E a) ∧
      bv_unsigned (edenot E h.am_len) = bv_unsigned (edenot E ne) := by
  unfold find_hole at H
  have Hin := List.mem_of_find?_eq_some H
  have Hc := List.find?_some H
  simp only [Bool.and_eq_true] at Hc
  obtain ⟨⟨Hh, H1⟩, H2⟩ := Hc
  exact ⟨Hin, Hh,
    (same_val_sound SEGS E M k a h.am_base HK H1).symm,
    (same_val_sound SEGS E M k ne h.am_len HK H2).symm⟩

/-- Re-kinding does not change the denotations (`rekind_den`, ). -/
theorem rekind_den (E : env) (ms : List amap) (m : amap) :
    List.map (amap_den E) (rekind ms m) = List.map (amap_den E) ms := by
  unfold rekind
  rw [List.map_map]
  apply List.map_congr_left
  intro m' _
  simp only [Function.comp]
  by_cases h : amap_eqb m' m = true
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]

/-- What re-kinding can produce (`in_rekind`, ). -/
theorem in_rekind (ms : List amap) (m m' : amap) (H : m' ∈ rekind ms m) :
    ∃ m0, m0 ∈ ms ∧
      ((m0 = m ∧ m' = AM m.am_base m.am_len .KRW) ∨ (m0 ≠ m ∧ m' = m0)) := by
  unfold rekind at H
  obtain ⟨m0, Hin, Hm0⟩ := List.mem_map.mp H
  refine ⟨m0, Hin, ?_⟩
  by_cases he : amap_eqb m0 m = true
  · left
    have h : m0 = m := amap_eqb_eq he
    rw [ite_eq_left he] at Hm0
    rw [h] at Hm0 ⊢
    exact ⟨rfl, Hm0.symm⟩
  · right
    rw [ite_eq_right he] at Hm0
    refine ⟨?_, Hm0.symm⟩
    intro h
    rw [h, amap_eqb_refl] at he
    exact absurd he (by simp)

/-- `kdisj_new` carries no image fact. -/
theorem kdisj_new_pure (ms : List amap) (nb ne : expr) :
    ∀ K ∈ kdisj_new ms nb ne, (match K with | .KImg _ _ => False | _ => True) := by
  intro K hK
  unfold kdisj_new at hK
  rw [List.mem_flatMap] at hK
  obtain ⟨m, _, hm⟩ := hK
  by_cases hf : is_fog m = true
  · rw [ite_eq_left hf] at hm
    simp at hm
  · rw [ite_eq_right hf] at hm
    cases hb : m.am_base with
    | ELit z =>
        rw [hb] at hm
        simp at hm
    | EVar n =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EAlu o x y =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EAluw o x y =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EMd o x y =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EMdw o x y =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EExt sx lo n x =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial
    | EBlob sx k i n =>
        rw [hb] at hm
        simp only [List.mem_singleton] at hm
        rw [hm]
        trivial

/-- The eager budget leaves the model's backing room. -/
theorem budget_slack (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (extra : Int) (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hb : budget_ok LIMIT cs extra = true) :
    vm_backing_used model + extra ≤ (m_vmmaps model).vm_limit := by
  unfold budget_ok at Hb
  have hb := of_decide_eq_true Hb
  have H1 := vm_backing_used_le (allowA A E cs) model HC.co_minv (A_wf_allowA A E cs)
  have H2 := HC.co_eager
  have H3 := HC.co_abytes
  have H4 := HC.co_limit
  omega

/-- Visibility outside the fresh region is unchanged. -/
theorem vis_grant_out (A : atable) (kd : mkind) (a n : word) (model model' : Model)
    (E : env) (cs cs1 : acs) (x : word)
    (GPo : grant_post kd a n model model') (Hvis : cs1.a_vis = cs.a_vis)
    (Hn : 0 < bv_unsigned n) (Hal : bv_unsigned a % 4096 = 0)
    (Hnl : bv_unsigned n % 4096 = 0)
    (Hx : bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x) :
    vis A E cs1 model' x = vis A E cs model x := by
  have T : (decide (bv_unsigned a ≤ bv_unsigned x)
      && decide (bv_unsigned x < bv_unsigned a + bv_unsigned n)) = false := by
    rcases Hx with h | h
    · rw [show decide (bv_unsigned a ≤ bv_unsigned x) = false from by
            simp only [decide_eq_false_iff_not]; omega]
      rfl
    · rw [show decide (bv_unsigned x < bv_unsigned a + bv_unsigned n) = false from by
            simp only [decide_eq_false_iff_not]; omega]
      simp
  have P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model)
      = page_in_ranges (page_base x) (m_vm_lazy model) := by
    refine page_in_ranges_cons_out (page_base x) a n _ ?_ Hn
    exact page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
      Hal (emod4096_add Hal Hnl) Hx
  have E0 : in_ivs (bv_unsigned x) ([] : List (word × word)) = false := rfl
  have HA : in_allow A E cs1 (bv_unsigned x) = in_allow A E cs (bv_unsigned x) := by
    simp only [in_allow, in_vis, in_sh, Hvis]
  cases hk : kind_none kd <;> cases hl : kind_lazy kd <;>
    simp only [vis, GPo.gp_maps, GPo.gp_noacc, GPo.gp_lazy, hk, hl, T, P, HA, E0,
      in_ivs_cons, in_ivs_app, List.singleton_append, List.nil_append,
      Bool.false_or, Bool.or_false, Bool.and_true, Bool.true_and, Bool.false_eq_true,
      Bool.not_false, Bool.not_true, ite_true, ite_false, ite_true, ite_false, decide_true]


/-- The rw MAP_FIXED node over a free range. -/
theorem srz_mmap_fixed_rw_free2 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (addr : word) (len : Int)
    (flags : word) (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 222)
    (H10 : getr regs 10 = addr) (Hal : bv_unsigned addr % page_size = 0)
    (Hpos : 0 < bv_unsigned addr)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hce : bv_unsigned addr + page_round_up_Z len ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (H12 : getr regs 12 = BitVec.ofInt 64 3) (H13 : getr regs 13 = flags)
    (Hcore : mmap_flags_core flags = 50)
    (H14 : getr regs 14 = BitVec.ofInt 64 (-1)) (H15 : getr regs 15 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z len) (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) addr n = true)
    (Hbk : mmap_noreserve_backed_ok flags model nZ = true)
    (HA : srealizes segs
      (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA)
    (HB : srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
        (with_mmap_backing flags addr n (mmap_model addr n model))) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  have Hno : bv_unsigned (getr regs 17) = 222 := by
    rw [H17]; exact u64_lit 222 ⟨by omega, by omega⟩
  have hlen64 : len < 2 ^ 64 := by
    have hb := (page_round_up_Z_bounds len (by omega)).1
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    omega
  have hlen_toNat : ((BitVec.ofInt 64 len).toNat : Int) = len :=
    u64_lit len ⟨by omega, hlen64⟩
  have HnZ' : nZ = page_round_up_Z ((BitVec.ofInt 64 len).toNat : Int) := by
    rw [HnZ, hlen_toNat]
  have Hn0 : 0 ≤ nZ := by
    rw [HnZ]
    exact LinuxSem.Checks.Sys.Mm.Mmap.page_round_up_Z_nonneg len (by omega)
  have HnZpos : 0 < nZ := by rw [HnZ]; exact page_round_up_Z_pos' len (by omega)
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
        = (match eff with
           | ⟨r, [], zs, [], [], []⟩ =>
               if errno_ret_in mmap_errnos r then
                 (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
               else if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                   && mmap_noreserve_backed_ok flags model nZ
                 then .CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
                 else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    exact mmap_fixed_rw_free_check segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
      eff flags addr (BitVec.ofInt 64 len) Hno
      (by rw [ms_gpr_epend0]; exact H10) (by simpa only [bv_unsigned] using Hal)
      (by simpa only [bv_unsigned] using Hpos)
      (by rw [ms_gpr_epend1]; exact H11)
      (by rw [hlen_toNat]; exact Hlen)
      (by rw [hlen_toNat]; simpa only [bv_unsigned] using Hce) Hisp
      (by rw [ms_gpr_epend2]; exact H12) (by rw [ms_gpr_epend3]; exact H13) Hcore
      (by rw [ms_gpr_epend4]; exact H14) (by rw [ms_gpr_epend5]; exact H15)
      nZ HnZ' n Hn Hrf
  have Hna : errno_ret_in mmap_errnos addr = false := by
    refine errno_ret_in_below _ _ (by decide) ?_
    have hz : 0 < page_round_up_Z len := by rw [← HnZ]; exact HnZpos
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    have hae : (addr.toNat : Int) + page_round_up_Z len ≤ 0x7fff7f800000 := by
      rw [← hcv]; exact Hce
    have h1 : (addr.toNat : Int) ≤ 0x7fff7f800000 := by omega
    unfold two_pow_64
    omega
  refine srz_alt2 segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) Unit Unit
    (fun i => mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17))
      (match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨addr, [], [(addr, n)], [], [], []⟩)))
      (match i with
       | .inl _ => model
       | .inr _ => with_mmap_backing flags addr n (mmap_model addr n model)))
    KA KB () () ?_ ?_ ?_
  · refine node_chk_ev_mat segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17)
      (Unit ⊕ Unit)
      (fun i => match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨addr, [], [(addr, n)], [], [], []⟩)
      (fun i => match i with
       | .inl _ => model
       | .inr _ => with_mmap_backing flags addr n (mmap_model addr n model))
      (fun _ => []) Hh rfl ?_ ?_ ?_ ?_ ?_
    · rintro (⟨⟩ | ⟨⟩)
      · rw [Hchk]
        simp only [errno_ret_in_intro mmap_errnos ENOMEM ENOMEM_in_mmap_errnos, ite_eq_left]
      · rw [Hchk]
        dsimp only
        rw [Hna, PropExec.bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl, Hbk]
        simp only [Bool.false_eq_true, Bool.true_and, reduceIte]
    · intro eff m' ev hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩
                · dsimp only at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  obtain ⟨e, He, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp h
                  rw [mmap_errnos_ENOMEM e He]
                  exact ⟨.inl (), rfl, rfl, rfl⟩
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags model nZ) = true
                · rw [ite_eq_left hconj] at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  rw [Bool.and_eq_true, Bool.and_eq_true] at hconj
                  obtain ⟨⟨hbv, hl⟩, -⟩ := hconj
                  rw [(bv_eqb_eq r addr).mp hbv, (listNN_eqb_eq zs [(addr, n)]).mp hl]
                  exact ⟨.inr (), rfl, rfl, rfl⟩
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · intro eff hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩ <;> (dsimp only at hc; simp at hc)
              · rw [ite_eq_right h] at hc
                by_cases hconj : (bv_eqb r addr && listNN_eqb zs [(addr, n)]
                    && mmap_noreserve_backed_ok flags model nZ) = true
                · rw [ite_eq_left hconj] at hc
                  simp at hc
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · rintro (⟨⟩ | ⟨⟩)
      · exact Hh
      · rw [with_mmap_backing_halted, mmap_model_halted]; exact Hh
    · rintro (⟨⟩ | ⟨⟩) <;> rfl
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨errno_ret ENOMEM, [], [], [], [], []⟩)) model) KA
    rw [adv_ret_epend]
    exact HA
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨addr, [], [(addr, n)], [], [], []⟩))
      (with_mmap_backing flags addr n (mmap_model addr n model))) KB
    rw [adv_zeros1_epend]
    exact HB


/-- The PROT_NONE MAP_FIXED node over a free range. -/
theorem srz_mmap_fixed_none_free2 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (addr : word) (len : Int)
    (flags : word) (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 222)
    (H10 : getr regs 10 = addr) (Hal : bv_unsigned addr % page_size = 0)
    (Hpos : 0 < bv_unsigned addr)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hce : bv_unsigned addr + page_round_up_Z len ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (H12 : getr regs 12 = BitVec.ofInt 64 0) (H13 : getr regs 13 = flags)
    (Hcore : mmap_flags_core flags = 50)
    (H14 : getr regs 14 = BitVec.ofInt 64 (-1)) (H15 : getr regs 15 = BitVec.ofInt 64 0)
    (nZ : Int) (HnZ : nZ = page_round_up_Z len) (n : word) (Hn : n = BitVec.ofInt 64 nZ)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) addr n = true)
    (HA : srealizes segs
      (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA)
    (HB : srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
        (with_mmap_backing flags addr n (noaccess_model addr n model))) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  have Hno : bv_unsigned (getr regs 17) = 222 := by
    rw [H17]; exact u64_lit 222 ⟨by omega, by omega⟩
  have hlen64 : len < 2 ^ 64 := by
    have hb := (page_round_up_Z_bounds len (by omega)).1
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    omega
  have hlen_toNat : ((BitVec.ofInt 64 len).toNat : Int) = len :=
    u64_lit len ⟨by omega, hlen64⟩
  have HnZ' : nZ = page_round_up_Z ((BitVec.ofInt 64 len).toNat : Int) := by
    rw [HnZ, hlen_toNat]
  have HnZpos : 0 < nZ := by rw [HnZ]; exact page_round_up_Z_pos' len (by omega)
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
        = (match eff with
           | ⟨r, [], [], us, [], []⟩ =>
               if errno_ret_in mmap_errnos r then
                 (match us with | [] => .CheckOk model [] | _ => .CheckReject)
               else if bv_eqb r addr && listNN_eqb us [(addr, n)]
                 then .CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
                 else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    exact mmap_fixed_none_free_check segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
      eff flags addr (BitVec.ofInt 64 len) Hno
      (by rw [ms_gpr_epend0]; exact H10) (by simpa only [bv_unsigned] using Hal)
      (by simpa only [bv_unsigned] using Hpos)
      (by rw [ms_gpr_epend1]; exact H11)
      (by rw [hlen_toNat]; exact Hlen)
      (by rw [hlen_toNat]; simpa only [bv_unsigned] using Hce) Hisp
      (by rw [ms_gpr_epend2]; exact H12) (by rw [ms_gpr_epend3]; exact H13) Hcore
      (by rw [ms_gpr_epend4]; exact H14) (by rw [ms_gpr_epend5]; exact H15)
      nZ HnZ' n Hn Hrf
  have Hna : errno_ret_in mmap_errnos addr = false := by
    refine errno_ret_in_below _ _ (by decide) ?_
    have hz : 0 < page_round_up_Z len := by rw [← HnZ]; exact HnZpos
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    have hae : (addr.toNat : Int) + page_round_up_Z len ≤ 0x7fff7f800000 := by
      rw [← hcv]; exact Hce
    have h1 : (addr.toNat : Int) ≤ 0x7fff7f800000 := by omega
    unfold two_pow_64
    omega
  refine srz_alt2 segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) Unit Unit
    (fun i => mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17))
      (match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨addr, [], [], [(addr, n)], [], []⟩)))
      (match i with
       | .inl _ => model
       | .inr _ => with_mmap_backing flags addr n (noaccess_model addr n model)))
    KA KB () () ?_ ?_ ?_
  · refine node_chk_ev_mat segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17)
      (Unit ⊕ Unit)
      (fun i => match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨addr, [], [], [(addr, n)], [], []⟩)
      (fun i => match i with
       | .inl _ => model
       | .inr _ => with_mmap_backing flags addr n (noaccess_model addr n model))
      (fun _ => []) Hh rfl ?_ ?_ ?_ ?_ ?_
    · rintro (⟨⟩ | ⟨⟩)
      · rw [Hchk]
        simp only [errno_ret_in_intro mmap_errnos ENOMEM ENOMEM_in_mmap_errnos, ite_eq_left]
      · rw [Hchk]
        dsimp only
        rw [Hna, PropExec.bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]
        simp only [Bool.false_eq_true, Bool.true_and, reduceIte]
    · intro eff m' ev hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases zs with _ | ⟨z, zs⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases us with _ | ⟨u, us⟩
                · dsimp only at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  obtain ⟨e, He, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp h
                  rw [mmap_errnos_ENOMEM e He]
                  exact ⟨.inl (), rfl, rfl, rfl⟩
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  rw [Bool.and_eq_true] at hconj
                  obtain ⟨hbv, hl⟩ := hconj
                  rw [(bv_eqb_eq r addr).mp hbv, (listNN_eqb_eq us [(addr, n)]).mp hl]
                  exact ⟨.inr (), rfl, rfl, rfl⟩
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · intro eff hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases zs with _ | ⟨z, zs⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases us with _ | ⟨u, us⟩ <;> (dsimp only at hc; simp at hc)
              · rw [ite_eq_right h] at hc
                by_cases hconj : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  simp at hc
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · rintro (⟨⟩ | ⟨⟩)
      · exact Hh
      · rw [with_mmap_backing_halted, noaccess_model, with_vmmaps_halted]; exact Hh
    · rintro (⟨⟩ | ⟨⟩) <;> rfl
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨errno_ret ENOMEM, [], [], [], [], []⟩)) model) KA
    rw [adv_ret_epend]
    exact HA
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨addr, [], [], [(addr, n)], [], []⟩))
      (with_mmap_backing flags addr n (noaccess_model addr n model))) KB
    rw [adv_unmaps1_epend]
    exact HB


/-- The `mprotect` rw-of-PROT_NONE node. -/
theorem srz_mprotect2 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (addr : word) (len : Int)
    (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 226)
    (H10 : getr regs 10 = addr) (Hal : bv_unsigned addr % page_size = 0)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hnw : bv_unsigned addr + page_round_up_Z len < two_pow_64)
    (H12 : getr regs 12 = BitVec.ofInt 64 3)
    (n : word) (Hn : n = BitVec.ofInt 64 (page_round_up_Z len))
    (Hna : map_contains (m_vmmaps model).vm_noaccess addr n = true)
    (Hma : map_contains (m_vmmaps model).vm_maps addr n = true)
    (Hbud : mprotect_budget_ok model addr n = true)
    (HA : srealizes segs
      (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) KA)
    (HB : srealizes segs (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 0)) (v_addi pc 4)
        (zfill addr n mem) rom) (mprotect_model addr n model)) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  have Hno : bv_unsigned (getr regs 17) = 226 := by
    rw [H17]; exact u64_lit 226 ⟨by omega, by omega⟩
  have Hna' : map_contains (m_vmmaps model).vm_noaccess addr
      (BitVec.ofInt 64 (page_round_up_Z len)) = true := by rw [← Hn]; exact Hna
  have Hma' : map_contains (m_vmmaps model).vm_maps addr
      (BitVec.ofInt 64 (page_round_up_Z len)) = true := by rw [← Hn]; exact Hma
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
        = (match eff with
           | ⟨r, [], zs, [], [], []⟩ =>
               if errno_ret_in mprotect_errnos r then
                 (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
               else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
                 then .CheckOk (mprotect_model addr n model) []
                 else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    have h := mprotect_check segs (epend regs pc mem rom (getr regs 17)) (getr regs 17) model
      eff addr len Hno
      (by rw [ms_gpr_epend0]; exact H10) (by simpa only [bv_unsigned] using Hal)
      (by rw [ms_gpr_epend1]; exact H11) Hlen
      (by simpa only [bv_unsigned] using Hnw)
      (by rw [ms_gpr_epend2]; exact H12) Hna' Hma'
    rw [show BitVec.ofInt 64 (page_round_up_Z len) = n from Hn.symm] at h
    exact h
  have Hna0 : errno_ret_in mprotect_errnos (BitVec.ofInt 64 0) = false := by
    refine errno_ret_in_below _ _ (by decide) ?_
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0]
    unfold two_pow_64
    omega
  refine srz_alt2 segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) Unit Unit
    (fun i => mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17))
      (match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨BitVec.ofInt 64 0, [], [(addr, n)], [], [], []⟩)))
      (match i with
       | .inl _ => model
       | .inr _ => mprotect_model addr n model))
    KA KB () () ?_ ?_ ?_
  · refine node_chk_ev_mat segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17)
      (Unit ⊕ Unit)
      (fun i => match i with
       | .inl _ => ⟨errno_ret ENOMEM, [], [], [], [], []⟩
       | .inr _ => ⟨BitVec.ofInt 64 0, [], [(addr, n)], [], [], []⟩)
      (fun i => match i with
       | .inl _ => model
       | .inr _ => mprotect_model addr n model)
      (fun _ => []) Hh rfl ?_ ?_ ?_ ?_ ?_
    · rintro (⟨⟩ | ⟨⟩)
      · rw [Hchk]
        simp only [errno_ret_in_intro mprotect_errnos ENOMEM ENOMEM_in_mprotect_errnos, ite_eq_left]
      · rw [Hchk]
        dsimp only
        rw [Hna0, Hbud, (listNN_eqb_eq _ _).mpr rfl]
        unfold w_is0
        rw [PropExec.bv_eqb_refl]
        simp only [Bool.false_eq_true, Bool.true_and, Bool.and_true, reduceIte]
    · intro eff m' ev hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mprotect_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩
                · dsimp only at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  obtain ⟨e, He, rfl⟩ := (errno_ret_in_true mprotect_errnos r).mp h
                  rw [mprotect_errnos_ENOMEM e He]
                  exact ⟨.inl (), rfl, rfl, rfl⟩
                · dsimp only at hc
                  simp at hc
              · rw [ite_eq_right h] at hc
                by_cases hconj : (mprotect_budget_ok model addr n && w_is0 r
                    && listNN_eqb zs [(addr, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hc
                  rw [Bool.and_eq_true, Bool.and_eq_true] at hconj
                  obtain ⟨⟨-, hr0⟩, hl⟩ := hconj
                  unfold w_is0 at hr0
                  rw [(bv_eqb_eq r (BitVec.ofInt 64 0)).mp hr0,
                    (listNN_eqb_eq zs [(addr, n)]).mp hl]
                  exact ⟨.inr (), rfl, rfl, rfl⟩
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · intro eff hc
      rw [Hchk] at hc
      obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
      rcases ws with _ | ⟨bw, ws⟩
      · rcases us with _ | ⟨u, us⟩
        · rcases cs with _ | ⟨c, cs⟩
          · rcases ci with _ | ⟨x, ci⟩
            · dsimp only at hc
              by_cases h : errno_ret_in mprotect_errnos r = true
              · rw [ite_eq_left h] at hc
                rcases zs with _ | ⟨z, zs⟩ <;> (dsimp only at hc; simp at hc)
              · rw [ite_eq_right h] at hc
                by_cases hconj : (mprotect_budget_ok model addr n && w_is0 r
                    && listNN_eqb zs [(addr, n)]) = true
                · rw [ite_eq_left hconj] at hc
                  simp at hc
                · rw [ite_eq_right hconj] at hc
                  simp at hc
            · exfalso; dsimp only at hc; simp at hc
          · exfalso; dsimp only at hc; simp at hc
        · exfalso; dsimp only at hc; simp at hc
      · exfalso; dsimp only at hc; simp at hc
    · rintro (⟨⟩ | ⟨⟩)
      · exact Hh
      · rw [mprotect_model, with_vmmaps_halted]; exact Hh
    · rintro (⟨⟩ | ⟨⟩) <;> rfl
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨errno_ret ENOMEM, [], [], [], [], []⟩)) model) KA
    rw [adv_ret_epend]
    exact HA
  · rintro ⟨⟩
    show srealizes segs (mkCfg (advance_past_svc (apply_effect
      (epend regs pc mem rom (getr regs 17)) ⟨BitVec.ofInt 64 0, [], [(addr, n)], [], [], []⟩))
      (mprotect_model addr n model)) KB
    rw [adv_zeros1_epend]
    exact HB


/-- The eager meter grows by at most the region, and only for a plain rw
    grant. -/
theorem grant_eager_le (kd : mkind) (a n : word) (model model' : Model)
    (GPo : grant_post kd a n model model') (Hwf : model_ivs_wf model)
    (Hb : bv_unsigned a + bv_unsigned n ≤ 2 ^ 64) :
    eager_used model'
      ≤ eager_used model
        + (if (kind_none kd || kind_lazy kd) then 0 else bv_unsigned n) := by
  have Hwf' := grant_wf kd a n model model' GPo Hwf Hb
  rw [eager_used_sem model' Hwf', eager_used_sem model Hwf, GPo.gp_maps]
  simp only [sum_count]
  have hna : ∀ x, covered ((m_vmmaps model).vm_noaccess) x = true →
      covered ((m_vmmaps model').vm_noaccess) x = true := by
    intro x hx
    rw [GPo.gp_noacc]
    by_cases hk : kind_none kd = true
    · rw [ite_eq_left hk]
      rw [covered_app, Bool.or_eq_true]
      exact Or.inr hx
    · rw [ite_eq_right hk]
      rw [covered_app, Bool.or_eq_true]
      exact Or.inr hx
  have hla : ∀ x, covered (m_vm_lazy model) x = true → covered (m_vm_lazy model') x = true := by
    intro x hx
    rw [GPo.gp_lazy]
    by_cases hl : kind_lazy kd = true
    · rw [ite_eq_left hl]
      rw [covered_app, Bool.or_eq_true]
      exact Or.inr hx
    · rw [ite_eq_right hl]
      rw [covered_app, Bool.or_eq_true]
      exact Or.inr hx
  have MONO : sum_count
      (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x))
      (m_vmmaps model).vm_maps
      ≤ sum_count (fun x => !(covered ((m_vmmaps model).vm_noaccess ++ m_vm_lazy model) x))
          (m_vmmaps model).vm_maps := by
    apply sum_count_negb_covered_mono
    intro x hx
    rw [covered_app] at hx
    rw [Bool.or_eq_true] at hx
    rw [covered_app, Bool.or_eq_true]
    rcases hx with hx | hx
    · exact Or.inl (hna x hx)
    · exact Or.inr (hla x hx)
  have HEAD : iv_count
      (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) (a, n)
      ≤ (if (kind_none kd || kind_lazy kd) then 0 else bv_unsigned n) := by
    have hSn : (((S (a, n)).toNat : Nat) : Int) = bv_unsigned n := rfl
    by_cases hk : (kind_none kd || kind_lazy kd) = true
    · rw [ite_eq_left hk]
      have hz : zcount
          (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x))
          (B (a, n)) (S (a, n)).toNat = 0 := by
        refine zcount_false _ _ _ ?_
        intro x h1 h2
        have h2' : x < B (a, n) + ((S (a, n)).toNat : Int) := h2
        have IN : in_iv (a, n) x = true := by
          show in_rng (B (a, n)) (B (a, n) + S (a, n)) x = true
          simp only [in_rng, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨h1, h2'⟩
        have hIN1 : covered ([(a, n)] ++ (m_vmmaps model).vm_noaccess) x = true := by
          rw [covered_app, Bool.or_eq_true]
          exact Or.inl (by simpa [covered] using IN)
        have hIN2 : covered ([(a, n)] ++ m_vm_lazy model) x = true := by
          rw [covered_app, Bool.or_eq_true]
          exact Or.inl (by simpa [covered] using IN)
        have hc : covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x = true := by
          rw [GPo.gp_noacc, GPo.gp_lazy, covered_app, Bool.or_eq_true]
          rw [Bool.or_eq_true] at hk
          rcases hk with h | h
          · left
            rw [ite_eq_left h]
            exact hIN1
          · right
            rw [ite_eq_left h]
            exact hIN2
        rw [hc]
        rfl
      unfold iv_count
      rw [hz]
      omega
    · rw [ite_eq_right hk]
      have h1 := zcount_le_len
        (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x))
        (B (a, n)) (S (a, n)).toNat
      unfold iv_count
      omega
  omega


/-- The joint end fact holds for the granted range. -/
theorem null_kend_ok (SEGS : List Segment) (E : env) (M : word → Option byte)
    (base ne : expr) (nlo : Int) (a n : word)
    (Hb : edenot E base = a) (Hn : edenot E ne = n)
    (Hlo : 4096 * (KHI / 4096 + 1) ≤ bv_unsigned a)
    (Hnlo : nlo ≤ bv_unsigned n) (HaC : bv_unsigned a + bv_unsigned n ≤ CEIL) :
    know_ok SEGS E M (null_kend base ne nlo) := by
  intro K HK
  unfold null_kend at HK
  split at HK
  · cases HK
  · rw [List.mem_singleton] at HK
    rw [HK]
    unfold kentry_ok
    have hab : bv_unsigned (edenot E (eadd base ne)) = bv_unsigned a + bv_unsigned n := by
      unfold eadd
      rw [mkAlu_denot, SymExec.alu64_add_eq]
      show bv_unsigned (edenot E base + edenot E ne) = bv_unsigned a + bv_unsigned n
      rw [Hb, Hn, u_add64]
      have ha := (bv_unsigned_range_u64 a).2
      have hn := (bv_unsigned_range_u64 n).2
      have hcv : CEIL = 0x7fff7f800000 := rfl
      simp only [two_pow_64, bv_unsigned] at *
      rw [Int.emod_eq_of_lt] <;> omega
    constructor
    · rw [hab]; omega
    · rw [hab]; exact HaC


/-- `4096 * (a / 4096)` reads back as `a` for an aligned `a`. -/
theorem escale_4096_denot (E : env) (v : Nat) (a : word)
    (Hv : E.ev v = Z_to_bv 64 (bv_unsigned a / 4096))
    (Hal : bv_unsigned a % 4096 = 0) :
    edenot E (escale 4096 (.EVar v)) = a := by
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat_inj.mp
  show bv_unsigned (edenot E (escale 4096 (.EVar v))) = bv_unsigned a
  unfold escale
  rw [mkMd_denot]
  have hmul : mul_div .MUL (edenot E (.ELit 4096)) (edenot E (.EVar v))
      = (Z_to_bv 64 4096) * (Z_to_bv 64 (bv_unsigned a / 4096)) := by
    show (edenot E (.ELit 4096)) * (edenot E (.EVar v)) = _
    rw [show edenot E (.EVar v) = Z_to_bv 64 (bv_unsigned a / 4096) from Hv]
    rfl
  rw [hmul, u_mul64]
  have hq0 : 0 ≤ bv_unsigned a / 4096 :=
    Int.ediv_nonneg (by simp only [bv_unsigned]; exact Int.natCast_nonneg _) (by decide)
  have hq1 : bv_unsigned a / 4096 < 2 ^ 64 := by
    have hle : bv_unsigned a / 4096 ≤ bv_unsigned a :=
      Int.ediv_le_self 4096 (by simp only [bv_unsigned]; exact Int.natCast_nonneg _)
    have ha := (bv_unsigned_range_u64 a).2
    simp only [two_pow_64, bv_unsigned] at *
    omega
  have h4096 : bv_unsigned (Z_to_bv 64 4096) = 4096 := u64_lit 4096 ⟨by decide, by decide⟩
  have hqbv : bv_unsigned (Z_to_bv 64 (bv_unsigned a / 4096)) = bv_unsigned a / 4096 :=
    u64_lit _ ⟨hq0, hq1⟩
  rw [h4096, hqbv]
  have hdvd : 4096 * (bv_unsigned a / 4096) = bv_unsigned a := by
    rw [Int.mul_comm]
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero Hal)
  rw [hdvd]
  have ha := (bv_unsigned_range_u64 a).2
  simp only [two_pow_64] at ha ⊢
  exact Int.emod_eq_of_lt (by omega) (by omega)


/-- Facts about the bytes of a fresh region, BEFORE the grant. -/
theorem grant_new_facts (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (a n : word) (nZ : Int)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) a n = true)
    (Un : bv_unsigned n = nZ) (HnZ : 0 < nZ)
    (Himg : A.img_hi ≤ bv_unsigned a) (HaC : bv_unsigned a + nZ ≤ CEIL) :
    ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ →
      in_ivs (bv_unsigned x) ((m_vmmaps model).vm_maps) = false
      ∧ in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false
      ∧ argH E x = false ∧ in_hull A (bv_unsigned x) = false
      ∧ (decide (CEIL ≤ bv_unsigned x)) = false
      ∧ vis A E cs model x = false := by
  intro x Hx
  obtain ⟨Hx1, Hx2⟩ := Hx
  rw [RefNodes.region_free_app, Bool.and_eq_true] at Hrf
  have Hnpos : 0 < bv_unsigned n := by rw [Un]; exact HnZ
  have M0 : in_ivs (bv_unsigned x) ((m_vmmaps model).vm_maps) = false :=
    region_free_sem _ a n (bv_unsigned x) Hrf.2 Hnpos ⟨Hx1, by rw [Un]; exact Hx2⟩
  have N0 : in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false := by
    cases h : in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess)
    · rfl
    · exfalso
      have h2 := HC.co_nasub (bv_unsigned x) h
      rw [h2] at M0
      exact Bool.noConfusion M0
  have Hh : in_hull A (bv_unsigned x) = false := by
    have hlt : ¬ (bv_unsigned x < A.img_hi) := by omega
    simp only [in_hull, hlt, decide_false, Bool.and_false]
  have Hc : (decide (CEIL ≤ bv_unsigned x)) = false := by
    rw [decide_eq_false_iff_not]
    omega
  have Ha : argH E x = false := by
    cases h : argH E x
    · rfl
    · exfalso
      have h2 := argH_high E x h
      omega
  refine ⟨M0, N0, Ha, Hh, Hc, ?_⟩
  have E0 : in_ivs (bv_unsigned x) ([] : List (word × word)) = false := rfl
  simp only [vis, Hh, Hc, M0, E0, Bool.false_or, Bool.or_false, Bool.and_false, Bool.false_and]


/-- The bytes of `[lo, hi)` inside a separated ledger: at most `hi - lo`. -/
theorem overlap_sum_contained (l : List (word × word)) (b s : word) (lo hi : Int)
    (Hs : seps l) (Hin : (b, s) ∈ l) (H1 : bv_unsigned b ≤ lo)
    (H2 : hi ≤ bv_unsigned b + bv_unsigned s) (Hlh : lo ≤ hi) :
    overlap_sum l lo hi ≤ hi - lo := by
  have HZ : ∀ (tl : List (word × word)) (b s : word) (lo hi : Int),
      (∀ x ∈ tl, iv_disjoint (b, s) x) → bv_unsigned b ≤ lo →
      hi ≤ bv_unsigned b + bv_unsigned s → overlap_sum tl lo hi = 0 := by
    intro tl
    induction tl with
    | nil => intro b s lo hi _ _ _; rfl
    | cons q ql ih =>
      intro b s lo hi Hf H1 H2
      rw [overlap_sum_cons]
      have hf' : ∀ x ∈ ql, iv_disjoint (b, s) x :=
        fun x hx => Hf x (List.mem_cons_of_mem _ hx)
      have hq : iv_disjoint (b, s) q := Hf q List.mem_cons_self
      rw [ih b s lo hi hf' H1 H2, iv_count_in_rng_disjoint q lo hi ?_]
      · omega
      · rcases hq with hq | hq
        · right; simp only [B, S, bv_unsigned] at *; omega
        · left; simp only [B, S, bv_unsigned] at *; omega
  induction Hs generalizing b s lo hi with
  | nil => cases Hin
  | cons p tl Hf Hl ih =>
    rw [overlap_sum_cons]
    rcases List.mem_cons.mp Hin with h | Hin
    · rw [← h] at Hf ⊢
      rw [HZ tl b s lo hi Hf H1 H2]
      have hle := iv_count_in_rng_le (b, s) lo hi Hlh
      omega
    · rw [iv_count_in_rng_disjoint p lo hi ?_]
      · have := ih b s lo hi Hin H1 H2 Hlh
        omega
      · rcases Hf (b, s) Hin with h | h
        · left; simp only [B, S, bv_unsigned] at *; omega
        · right; simp only [B, S, bv_unsigned] at *; omega


/-- `find_containing` returns a real, non-fog entry of the requested kinds
    that contains the range. -/
theorem find_containing_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (ms : List amap) (kinds : List mkind) (b : expr) (off : Int)
    (ne : expr) (m : amap)
    (HK : know_ok SEGS E M k)
    (Hf : find_containing k ms kinds b off ne = some m) :
    m ∈ ms ∧ (m.am_kind ∈ kinds ∧ is_fog m = false)
      ∧ bv_unsigned (edenot E (m.am_base)) ≤ estart E (SA b off)
      ∧ estart E (SA b off) + elenZ E ne ≤ bv_unsigned (edenot E (m.am_base))
          + bv_unsigned (edenot E (m.am_len)) := by
  have Hin := List.mem_of_find?_eq_some Hf
  have Hp := List.find?_some Hf
  unfold find_containing at Hp
  rw [Bool.and_eq_true, Bool.and_eq_true] at Hp
  obtain ⟨⟨hnf, hkd⟩, hins⟩ := Hp
  have hnf' : is_fog m = false := by
    cases h : is_fog m
    · rfl
    · rw [h] at hnf
      exact absurd hnf (by decide)
  rw [List.any_eq_true] at hkd
  obtain ⟨kd, hkdin, hkdeq⟩ := hkd
  obtain ⟨I1, I2⟩ := xinside_sound SEGS E M k b off ne m.am_base 0 m.am_len HK hins
  refine ⟨Hin, ⟨?_, hnf'⟩, ?_, ?_⟩
  · rw [mkind_eqb_eq hkdeq]; exact hkdin
  · simp only [estart] at I1 ⊢
    omega
  · simp only [estart, elenZ] at I2 ⊢
    omega


/-- Disjointness from every tracked entry, read back as `region_free`. -/
theorem region_free_of_apart (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (RES_hullH : RES_hull_def SEGS A)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b : expr) (off : Int) (ne : expr) (lo n : word)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hnf : no_fog (cs.a_maps) = true)
    (Hall : (cs.a_maps).all (fun m =>
      ranges_apart_x (kn cs) b off ne (m.am_base) 0 (m.am_len)) = true)
    (Hs : estart E (SA b off) = bv_unsigned lo) (Hn : elenZ E ne = bv_unsigned n)
    (Himg : A.img_hi ≤ bv_unsigned lo) :
    region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) lo n = true := by
  rw [RefNodes.region_free_app, Bool.and_eq_true]
  refine ⟨reserved_free_above SEGS A model lo n RES_hullH HC.co_res Himg, ?_⟩
  have hlen : (m_vmmaps model).vm_maps = (cs.a_maps).map (amap_den E) :=
    (maps_match_exact E (cs.a_maps) _ Hnf).mp HC.co_maps
  rw [hlen]
  refine RefNodes.region_free_intro _ lo n ?_
  intro bm sm Hin
  rw [List.mem_map] at Hin
  obtain ⟨m, hm, hden⟩ := Hin
  have hap := (List.all_eq_true.mp Hall) m hm
  have D := ranges_apart_x_sound SEGS E (Mr A argH E cs model FULL) (kn cs) b off ne
    m.am_base 0 m.am_len HC.co_know hap
  have hb : bm = edenot E m.am_base := (congrArg Prod.fst hden).symm
  have hs : sm = edenot E m.am_len := (congrArg Prod.snd hden).symm
  rw [hb, hs]
  simp only [estart, elenZ, bv_unsigned] at *
  omega


/-- The zero-fill facts of a fresh rw range. -/
theorem kmem_ok (SEGS : List Segment) (E : env) (M : word → Option byte) (b : expr)
    (ne : expr) (lo n : Int)
    (Hs : estart E (SA b 0) = lo) (Hn : elenZ E ne = n)
    (Hlo : 0 ≤ lo) (Hlo64 : lo < 2 ^ 64) (Hn0 : 0 ≤ n) (Hhi : lo + n ≤ 2 ^ 64)
    (BYTE : ∀ x : word, lo ≤ bv_unsigned x ∧ bv_unsigned x < lo + n →
      M x = some (Z_to_bv 8 0)) :
    know_ok SEGS E M [.KWr (SA b 0) ne, .KZero (SA b 0) ne] := by
  have Hfl : flat E (SA b 0) (elenZ E ne) := by
    unfold flat
    rw [Hs, Hn]
    exact ⟨Hlo, Hlo64, Hn0, Hhi⟩
  have h2 : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
  intro K HK
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at HK
  rcases HK with rfl | rfl
  · unfold kentry_ok
    refine ⟨Hfl, ?_⟩
    intro d m Hd Hdw
    cases m with
    | zero => rfl
    | succ m' =>
      rw [Hn] at Hdw
      have hu : ((BitVec.ofInt 64 (estart E (SA b 0) + d)).toNat : Int)
          = estart E (SA b 0) + d := by
        refine u64_lit (estart E (SA b 0) + d) ⟨?_, ?_⟩ <;> rw [Hs] <;> omega
      refine StoreOk.store_ok_of_all SEGS M (m' + 1)
        (BitVec.ofInt 64 (estart E (SA b 0) + d)) ?_ ?_
      · rw [hu, Hs]
        have h3 : lo + d + ↑(m' + 1) ≤ (2 : Int) ^ 64 := by omega
        calc lo + d + ↑(m' + 1) ≤ (2 : Int) ^ 64 := h3
          _ = ((2 ^ 64 : Nat) : Int) := h2.symm
      · intro x hx1 hx2
        rw [hu, Hs] at hx1 hx2
        have hb1 : lo ≤ (x.toNat : Int) := by omega
        have hb2 : (x.toNat : Int) < lo + n := by omega
        have hm : M x = some (Z_to_bv 8 0) := BYTE x ⟨hb1, hb2⟩
        unfold wview
        rw [hm]
        intro h
        cases h
  · unfold kentry_ok
    refine ⟨Hfl, ?_⟩
    intro i Hi Hi2
    have hu : ((BitVec.ofInt 64 (estart E (SA b 0) + i)).toNat : Int)
        = estart E (SA b 0) + i := by
      refine u64_lit (estart E (SA b 0) + i) ⟨?_, ?_⟩ <;> rw [Hs] <;> omega
    rw [Hn] at Hi2
    refine BYTE (BitVec.ofInt 64 (estart E (SA b 0) + i)) ⟨?_, ?_⟩
    · show lo ≤ ((BitVec.ofInt 64 (estart E (SA b 0) + i)).toNat : Int)
      rw [hu, Hs]; omega
    · show ((BitVec.ofInt 64 (estart E (SA b 0) + i)).toNat : Int) < lo + n
      rw [hu, Hs]; omega

/-- `cs_ok` survives a grant of the fresh region `[a, a+n)`: the state after
    `add_entry`, its knowledge and its restricted memory.

    The three conjuncts are exactly what the `*_cs1` nodes consume — the
    checker state; the fact that `MR` OUTSIDE the region is the old `MR`
    (which carries the kept knowledge, the old hole facts and `co_zero`
    across the grant); and the fact that `MR` with the NEW model is the old
    `MR` outright (`vis` reads the model only through the ledgers the grant
    extends strictly inside the region, and `a_vis`/`a_ghost` are untouched,
    so this half is definitional). -/
theorem grant_cs1_ok (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (kd : mkind) (a n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (sr' : List expr) (R' : BvMap word) (knew : List kentry) (be ne : expr)
    (nhi : Int) (eager : Bool) (ylo' : Int) (nx' : Nat)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Un : bv_unsigned n = nZ) (HnZpos : 0 < nZ) (HnZal : nZ % 4096 = 0)
    (Hal : bv_unsigned a % 4096 = 0) (Himg : A.img_hi ≤ bv_unsigned a)
    (HaC : bv_unsigned a + nZ ≤ CEIL)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) a n = true)
    (GPo : grant_post kd a n model model')
    (GM : grant_mem kd a n FULL FULL')
    (Hregs : regs_ok E sr' R') (Hbase : edenot E be = a) (HneE : edenot E ne = n)
    (Hknew : know_ok SEGS E (Mr A argH E cs model' FULL') knew)
    (Hkind : (kind_none kd || kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false) (Hnhi : nZ ≤ nhi)
    (Hbudget : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT)
    (Hsplit : ∀ Y, cs.a_ylo ≤ Y → Y % 4096 = 0 →
        Y ≤ bv_unsigned (m_vmmaps model).vm_mmap_base →
        ledger_split ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) kHighMemBeg Y →
        ∃ Y', ylo' ≤ Y' ∧ Y' % 4096 = 0 ∧
          Y' ≤ bv_unsigned (m_vmmaps model).vm_mmap_base ∧
          ledger_split ((m_vmmaps model).vm_reserved ++ (a, n) :: (m_vmmaps model).vm_maps)
            kHighMemBeg Y')
    (Hylo : ylo' ≤ cs.a_ylo)
    (Hholes : ∀ m, m ∈ cs.a_maps → is_hole m = true →
        bv_unsigned a + nZ ≤ AsanPlanSound.uE E m.am_base ∨
        AsanPlanSound.uE E m.am_base + AsanPlanSound.uE E m.am_len ≤ bv_unsigned a) :
    cs_ok SEGS A LIMIT SINV argH FS0 E
        (add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (cs.a_maps)) nx' (AM be ne kd) nhi
          eager ylo') R' FULL' model'
    ∧ (∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + nZ ≤ bv_unsigned x →
          Mr A argH E (add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (cs.a_maps)) nx'
              (AM be ne kd) nhi eager ylo') model' FULL' x
            = Mr A argH E cs model FULL x)
    ∧ Mr A argH E (add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) (cs.a_maps)) nx'
          (AM be ne kd) nhi eager ylo') model' FULL'
        = Mr A argH E cs model' FULL' := by
  let cs1 : acs := add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) cs.a_maps) nx'
    (AM be ne kd) nhi eager ylo'
  change cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R' FULL' model'
      ∧ (∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + nZ ≤ bv_unsigned x →
          Mr A argH E cs1 model' FULL' x = Mr A argH E cs model FULL x)
      ∧ Mr A argH E cs1 model' FULL' = Mr A argH E cs model' FULL'
  have Hcs1 : cs1 = add_entry cs sr' (knew ++ kn_grant_filter A (kn cs) cs.a_maps) nx'
      (AM be ne kd) nhi eager ylo' := rfl
  have Hkn : kn cs1 = knew ++ kn_grant_filter A (kn cs) cs.a_maps := rfl
  have Hmap : cs1.a_maps = (AM be ne kd) :: cs.a_maps := rfl
  have Hmr : Mr A argH E cs1 model' FULL' = Mr A argH E cs model' FULL' := rfl
  have Ha_totsz : cs1.a_totsz = cs.a_totsz + nhi := rfl
  have Ha_eager : cs1.a_eager = (if eager then cs.a_eager + nhi else cs.a_eager) := rfl
  have Ha_ylo : cs1.a_ylo = ylo' := rfl
  have Ha_abytes : cs1.a_abytes = cs.a_abytes := rfl
  have Ha_fd : cs1.a_fd = cs.a_fd := rfl
  have Ha_brk : cs1.a_brk = cs.a_brk := rfl
  have Ha_tid : cs1.a_tidset = cs.a_tidset := rfl
  have HCkeep : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model := HC
  obtain ⟨Xregs, Xlog, Xknow, Xhalt, Xfds, Xfs, Xtid, Xres, Xlimit, Xmaps, Xholes,
    Xseps, Xwf, Xbounds, Xlazyb, Xnasub, Xnone, Xkinds, Xtotsz, Xsplit, Xbrk, Xsbrk,
    Xeager, Xabytes, Xminv, Xzero, Xsinv⟩ := HC
  obtain ⟨N1, N2, N3, N4, N5⟩ := Xminv
  have Hrf2 : region_free (m_vmmaps model).vm_maps a n = true := by
    have h := Hrf
    rw [RefNodes.region_free_app, Bool.and_eq_true] at h
    exact h.2
  have Hapart : maps_apart E cs.a_maps (bv_unsigned a) nZ := by
    have h := maps_apart_of_region_free E cs.a_maps model a n Xmaps Hrf
    rwa [Un] at h
  have Hsum64 : bv_unsigned a + bv_unsigned n ≤ 2 ^ 64 := by
    rw [Un]
    have h2 : CEIL ≤ 2 ^ 64 := by decide
    omega
  have Hwf' : model_ivs_wf model' := grant_wf kd a n model model' GPo Xwf Hsum64
  have NEW := grant_new_facts SEGS A LIMIT SINV argH FS0 E cs R FULL model a n nZ
    argH_high HCkeep Hrf Un HnZpos Himg HaC
  have hkhole : is_hole (AM be ne kd) = false := by
    have h1 : mkind_eqb kd .KHOLE = false := by
      cases kd <;> simp only [is_tok_kind, mkind_eqb] at Hkfog ⊢
      exact Hkfog
    simpa only [is_hole] using h1
  have Hvis : ∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + nZ ≤ bv_unsigned x →
      vis A E cs1 model' x = vis A E cs model x := by
    intro x Hx
    have hx : bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ bv_unsigned x := by
      rcases Hx with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Un]; exact h)
    exact vis_grant_out A kd a n model model' E cs cs1 x GPo (by rfl)
      (by rw [Un]; exact HnZpos) Hal (by rw [Un]; exact HnZal) hx
  have HIDOUT : ∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + nZ ≤ bv_unsigned x →
      hid A argH E cs1 model' x = hid A argH E cs model x := by
    intro x Hx
    simp only [hid, Hvis x Hx]
  have MROUT : ∀ x : word, bv_unsigned x < bv_unsigned a ∨ bv_unsigned a + nZ ≤ bv_unsigned x →
      Mr A argH E cs1 model' FULL' x = Mr A argH E cs model FULL x := by
    intro x Hx
    have hgm : FULL' x = FULL x := GM.1 x (by
      rcases Hx with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Un]; exact h))
    simp only [Mr, mrestrict, HIDOUT x Hx, hgm]
  have HCSOK : cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R' FULL' model' := by
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
    · exact Hregs
    · rfl
    · intro K HK
      rw [Hkn, List.mem_append] at HK
      rcases HK with HK | HK
      · exact Hknew K HK
      · exact kn_grant_filter_ok SEGS A E (Mr A argH E cs model FULL)
          (Mr A argH E cs1 model' FULL') (kn cs) cs.a_maps (bv_unsigned a) nZ
          Xknow Hapart Himg HaC MROUT K HK
    · rw [GPo.gp_halted]; exact Xhalt
    · unfold fds_ok at *
      rw [GPo.gp_fds, GPo.gp_fs]; exact Xfds
    · rw [GPo.gp_fs]; exact Xfs
    · rw [GPo.gp_tid]; exact Xtid
    · rw [GPo.gp_res]; exact Xres
    · rw [GPo.gp_limit]; exact Xlimit
    · rw [GPo.gp_maps, ← Hbase, ← HneE]
      exact maps_match_cons E (cs.a_maps) ((m_vmmaps model).vm_maps) be ne kd Hkfog Xmaps
    · intro m Hm
      have Hm' : m = AM be ne kd ∨ m ∈ cs.a_maps :=
        List.mem_cons.mp (show m ∈ (AM be ne kd) :: cs.a_maps from Hm)
      rcases Hm' with rfl | Hm
      · intro Hh
        rw [hkhole] at Hh
        exact Bool.noConfusion Hh
      · rw [GPo.gp_res, GPo.gp_maps]
        intro Hk
        obtain ⟨F1, F2⟩ := Xholes m Hm Hk
        refine ⟨?_, ?_⟩
        · intro iv Hiv
          rw [List.mem_append] at Hiv
          rcases Hiv with Hiv | Hiv
          · exact F1 iv (List.mem_append.mpr (Or.inl Hiv))
          · rw [List.mem_cons] at Hiv
            rcases Hiv with rfl | Hiv
            · dsimp only
              rcases Hholes m Hm Hk with h | h
              · exact Or.inl (by rw [Un]; exact h)
              · exact Or.inr h
            · exact F1 iv (List.mem_append.mpr (Or.inr Hiv))
        · rcases F2 with h | h
          · exact Or.inl h
          · exact Or.inr (Int.le_trans Hylo h)
    · rw [GPo.gp_maps]
      refine seps.cons (a, n) _ ?_ Xseps
      intro iv Hiv
      obtain ⟨b, s⟩ := iv
      have hov := RefNodes.region_free_In ((m_vmmaps model).vm_maps) a n b s Hrf2 Hiv
      show bv_unsigned a + bv_unsigned n ≤ bv_unsigned b ∨
        bv_unsigned b + bv_unsigned s ≤ bv_unsigned a
      simp only [bv_unsigned] at hov ⊢
      exact hov
    · exact Hwf'
    · rw [GPo.gp_maps]
      intro iv Hiv
      rw [List.mem_cons] at Hiv
      rcases Hiv with rfl | Hiv
      · show 0 < bv_unsigned n ∧ bv_unsigned a % 4096 = 0 ∧ bv_unsigned n % 4096 = 0 ∧
          A.img_hi ≤ bv_unsigned a ∧ bv_unsigned a + bv_unsigned n ≤ CEIL
        exact ⟨by rw [Un]; exact HnZpos, Hal, by rw [Un]; exact HnZal, Himg,
          by rw [Un]; exact HaC⟩
      · exact Xbounds iv Hiv
    · intro iv Hiv
      rw [GPo.gp_lazy] at Hiv
      rw [List.mem_append] at Hiv
      rcases Hiv with h | h
      · by_cases hk : kind_lazy kd = true
        · rw [ite_eq_left hk, List.mem_cons] at h
          rcases h with rfl | h
          · show A.img_hi ≤ bv_unsigned a ∧ bv_unsigned a + bv_unsigned n ≤ CEIL
            exact ⟨Himg, by rw [Un]; exact HaC⟩
          · cases h
        · rw [ite_eq_right hk] at h
          cases h
      · exact Xlazyb iv h
    · intro z Hz
      rw [GPo.gp_maps, in_ivs_cons]
      rw [GPo.gp_noacc] at Hz
      by_cases hk : kind_none kd = true
      · rw [ite_eq_left hk, List.singleton_append, in_ivs_cons, Bool.or_eq_true] at Hz
        rcases Hz with hz | hz
        · rw [hz, Bool.true_or]
        · rw [Xnasub z hz, Bool.or_true]
      · rw [ite_eq_right hk, List.nil_append] at Hz
        rw [Xnasub z Hz, Bool.or_true]
    · intro m Hm
      have Hm' : m = AM be ne kd ∨ m ∈ cs.a_maps :=
        List.mem_cons.mp (show m ∈ (AM be ne kd) :: cs.a_maps from Hm)
      rcases Hm' with rfl | Hm
      · intro Hk
        have hk : kind_none kd = true := by
          have h' : kd = .KNONE ∨ kd = .KNONELAZY := Hk
          rcases h' with h | h <;> (rw [h] <;> rfl)
        rw [GPo.gp_noacc, ite_eq_left hk, List.singleton_append]
        have hden : amap_den E (AM be ne kd) = (a, n) := by
          simp only [amap_den, Hbase, HneE]
        rw [hden]
        exact List.mem_cons_self
      · intro Hk
        rw [GPo.gp_noacc]
        by_cases hk : kind_none kd = true
        · rw [ite_eq_left hk, List.singleton_append]
          exact List.mem_cons_of_mem _ (Xnone m Hm Hk)
        · rw [ite_eq_right hk, List.nil_append]
          exact Xnone m Hm Hk
    · intro m Hm
      have Hm' : m = AM be ne kd ∨ m ∈ cs.a_maps :=
        List.mem_cons.mp (show m ∈ (AM be ne kd) :: cs.a_maps from Hm)
      rcases Hm' with rfl | Hm
      · intro Hk x Hx
        have hkd : kd = .KRWLAZY := Hk
        have hkn : kind_none kd = false := by rw [hkd]; rfl
        have hkl : kind_lazy kd = true := by rw [hkd]; rfl
        have hx0 : bv_unsigned (edenot E be) ≤ bv_unsigned x ∧
            bv_unsigned x < bv_unsigned (edenot E be) + bv_unsigned (edenot E ne) := Hx
        have hx' : bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ := by
          rw [Hbase, HneE, Un] at hx0
          exact hx0
        have hn := NEW x hx'
        refine ⟨?_, ?_⟩
        · rw [GPo.gp_noacc, hkn, ite_eq_right (by decide), List.nil_append]
          exact hn.2.1
        · rw [GPo.gp_lazy, hkl, ite_eq_left rfl, List.singleton_append]
          have hp := page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal
            (emod4096_add Hal HnZal) hx'
          rw [← Un] at hp
          exact page_in_ranges_cons_in (page_base x) a n (m_vm_lazy model) hp.1 hp.2
      · intro Hk x Hx
        obtain ⟨K1, K2⟩ := Xkinds m Hm Hk x Hx
        have hfog : is_fog m = false := by rw [is_fog, Hk]; rfl
        have hD := Hapart m Hm hfog
        refine ⟨?_, ?_⟩
        · rw [GPo.gp_noacc]
          by_cases hk : kind_none kd = true
          · rw [ite_eq_left hk, List.singleton_append, in_ivs_cons, K1, Bool.or_false]
            dsimp only
            rcases hD with h | h
            · rw [show decide (bv_unsigned x < bv_unsigned a + bv_unsigned n) = false from by
                rw [decide_eq_false_iff_not]; omega]
              exact Bool.and_false _
            · rw [show decide (bv_unsigned a ≤ bv_unsigned x) = false from by
                rw [decide_eq_false_iff_not]; omega]
              exact Bool.false_and _
          · rw [ite_eq_right hk, List.nil_append]
            exact K1
        · rw [GPo.gp_lazy]
          by_cases hl : kind_lazy kd = true
          · rw [ite_eq_left hl, List.singleton_append, page_in_ranges_cons, K2, Bool.or_true]
          · rw [ite_eq_right hl, List.nil_append]
            exact K2
    · rw [GPo.gp_res, GPo.gp_maps, sum_sizes_app]
      rw [sum_sizes_app] at Xtotsz
      have hs : sum_sizes ((a, n) :: (m_vmmaps model).vm_maps)
          = bv_unsigned n + sum_sizes ((m_vmmaps model).vm_maps) := rfl
      rw [hs, Un, Ha_totsz]
      omega
    · rw [GPo.gp_res, GPo.gp_maps, GPo.gp_mbase]
      obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := Xsplit
      exact Hsplit Y HY1 HY2 HY3 HY4
    · rw [GPo.gp_brk]; exact Xbrk
    · rw [GPo.gp_brk, GPo.gp_sbrk]; exact Xsbrk
    · have EG := grant_eager_le kd a n model model' GPo Xwf Hsum64
      rw [Hkind] at EG
      rw [Ha_eager]
      cases eager with
      | false =>
          rw [ite_eq_left (by decide : ((!(false : Bool)) = true))] at EG
          rw [ite_eq_right (by decide : ¬((false : Bool) = true))]
          clear Hal HnZal
          omega
      | true =>
          rw [ite_eq_right (by decide : ¬((!(true : Bool)) = true))] at EG
          rw [Un] at EG
          rw [ite_eq_left (rfl : (true : Bool) = true)]
          clear Hal HnZal
          omega
    · exact Xabytes
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [GPo.gp_mat]; exact N1
      · intro p Hp
        rw [GPo.gp_mat] at Hp
        exact N2 p Hp
      · intro p Hp
        rw [GPo.gp_mat] at Hp
        exact N3 p Hp
      · intro p Hp
        rw [GPo.gp_mat] at Hp
        rw [GPo.gp_lazy]
        by_cases hl : kind_lazy kd = true
        · rw [ite_eq_left hl, List.singleton_append, page_in_ranges_cons, N4 p Hp, Bool.or_true]
        · rw [ite_eq_right hl, List.nil_append]
          exact N4 p Hp
      · have hAb : A_bytes (allowA A E cs1) = A_bytes (allowA A E cs) := rfl
        rw [hAb]
        have EG := grant_eager_le kd a n model model' GPo Xwf Hsum64
        rw [Hkind] at EG
        rw [GPo.gp_limit, Xlimit]
        cases eager with
        | false =>
            rw [ite_eq_left (by decide : ((!(false : Bool)) = true))] at EG
            clear Hal HnZal
            omega
        | true =>
            rw [ite_eq_right (by decide : ¬((!(true : Bool)) = true))] at EG
            rw [Un] at EG
            have hb : cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := Hbudget rfl
            clear Hal HnZal
            omega
    · intro x Hh Hm Hna Hlz Hgh
      by_cases hlt : bv_unsigned x < bv_unsigned a
      · rw [show FULL' x = FULL x from GM.1 x (Or.inl hlt)]
        have hha : hid A argH E cs model x = true := by
          rw [← HIDOUT x (Or.inl hlt)]; exact Hh
        refine Xzero x hha ?_ ?_ ?_ Hgh
        · rw [GPo.gp_maps, in_ivs_cons, Bool.or_eq_true] at Hm
          dsimp only at Hm
          rcases Hm with h | h
          · exfalso
            rw [Bool.and_eq_true] at h
            simp only [decide_eq_true_eq] at h
            omega
          · exact h
        · rw [GPo.gp_noacc] at Hna
          by_cases hk : kind_none kd = true
          · rw [ite_eq_left hk, List.singleton_append, in_ivs_cons, Bool.or_eq_false_iff] at Hna
            exact Hna.2
          · rw [ite_eq_right hk, List.nil_append] at Hna
            exact Hna
        · rw [GPo.gp_lazy] at Hlz
          by_cases hl : kind_lazy kd = true
          · rw [ite_eq_left hl, List.singleton_append, page_in_ranges_cons, Bool.or_eq_true] at Hlz
            rcases Hlz with h | h
            · exfalso
              rw [Bool.and_eq_true] at h
              simp only [decide_eq_true_eq] at h
              have hpb1 : bv_unsigned (page_base x) ≤ bv_unsigned x := (page_base_facts x).1
              clear Hal HnZal
              omega
            · exact h
          · rw [ite_eq_right hl, List.nil_append] at Hlz
            exact Hlz
      · have hge : bv_unsigned a ≤ bv_unsigned x := by omega
        by_cases hlt2 : bv_unsigned x < bv_unsigned a + nZ
        · have hx2 : bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + bv_unsigned n :=
            ⟨hge, by rw [Un]; exact hlt2⟩
          rw [show FULL' x = (if kind_none kd then none else some (Z_to_bv 8 0)) from
            GM.2 x hx2]
          by_cases hk : kind_none kd = true
          · rw [ite_eq_left hk]
            rw [GPo.gp_noacc, ite_eq_left hk, List.singleton_append, in_ivs_cons,
              Bool.or_eq_false_iff, Bool.and_eq_false_iff] at Hna
            dsimp only at Hna
            rcases Hna.1 with h | h
            · rw [decide_eq_false_iff_not] at h; omega
            · rw [decide_eq_false_iff_not] at h; omega
          · rw [ite_eq_right hk]
        · have hge2 : bv_unsigned a + nZ ≤ bv_unsigned x := by omega
          rw [show FULL' x = FULL x from GM.1 x (Or.inr (by rw [Un]; exact hge2))]
          have hha : hid A argH E cs model x = true := by
            rw [← HIDOUT x (Or.inr hge2)]; exact Hh
          refine Xzero x hha ?_ ?_ ?_ Hgh
          · rw [GPo.gp_maps, in_ivs_cons, Bool.or_eq_true] at Hm
            dsimp only at Hm
            rcases Hm with h | h
            · exfalso
              rw [Bool.and_eq_true] at h
              simp only [decide_eq_true_eq] at h
              have hpb1 : bv_unsigned (page_base x) ≤ bv_unsigned x := (page_base_facts x).1
              clear Hal HnZal
              omega
            · exact h
          · rw [GPo.gp_noacc] at Hna
            by_cases hk : kind_none kd = true
            · rw [ite_eq_left hk, List.singleton_append, in_ivs_cons, Bool.or_eq_false_iff] at Hna
              exact Hna.2
            · rw [ite_eq_right hk, List.nil_append] at Hna
              exact Hna
          · rw [GPo.gp_lazy] at Hlz
            by_cases hl : kind_lazy kd = true
            · rw [ite_eq_left hl, List.singleton_append] at Hlz
              have hout := page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal
                (emod4096_add Hal HnZal) (Or.inr hge2)
              rw [← Un] at hout
              rw [page_in_ranges_cons_out (page_base x) a n (m_vm_lazy model) hout
                (by rw [Un]; exact HnZpos)] at Hlz
              exact Hlz
            · rw [ite_eq_right hl, List.nil_append] at Hlz
              exact Hlz
    · refine SINV_frame E FULL FULL' ?_ Xsinv
      intro x Hx
      apply GM.1 x
      right
      have hc : bv_unsigned a + bv_unsigned n ≤ CEIL := by rw [Un]; exact HaC
      exact Int.le_trans hc (argH_high E x Hx)
  exact ⟨HCSOK, MROUT, Hmr⟩

/-- `fixed_args` read back: the split, the length triple, and the five facts
    the fixed-address node needs. -/
theorem fixed_args_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (top : Int) (b : expr) (off : Int) (ne : expr) (nlo nhi : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (H : fixed_args A cs top = some (b, off, ne, nlo, nhi)) :
    split_lit (reg cs 10) = (b, off) ∧ mmap_len cs = some (ne, nlo, nhi)
    ∧ bv_unsigned (edenot E (reg cs 10)) % 4096 = 0
    ∧ 0 < bv_unsigned (edenot E (reg cs 10))
    ∧ A.img_hi ≤ bv_unsigned (edenot E (reg cs 10))
    ∧ bv_unsigned (edenot E (reg cs 10)) + nhi ≤ top
    ∧ getr R (Z_to_bv 5 (10 : Int)) = edenot E (reg cs 10)
    ∧ flat_x (kn cs) b off ne = true := by
  have HK := HC.co_know
  unfold fixed_args at H
  dsimp only at H
  cases hsp : split_lit (reg cs 10) with
  | mk b0 off0 =>
    rw [hsp] at H
    dsimp only at H
    cases hml : mmap_len cs with
    | none => rw [hml] at H; exact absurd H (by simp)
    | some p =>
      obtain ⟨ne0, nlo0, nhi0⟩ := p
      rw [hml] at H
      cases hxl : xlo (kn cs) (reg cs 10) with
      | none => rw [hxl] at H; exact absurd H (by simp)
      | some alo =>
        rw [hxl] at H
        cases hxh : xhi (kn cs) (reg cs 10) with
        | none => rw [hxh] at H; exact absurd H (by simp)
        | some ahi =>
          rw [hxh] at H
          dsimp only at H
          split at H
          · rename_i hc
            have hc' := hc
            simp only [Bool.and_eq_true] at hc'
            obtain ⟨⟨⟨⟨hpa, hpos⟩, himg⟩, htop⟩, hflat⟩ := hc'
            rw [decide_eq_true_eq] at hpos himg htop
            simp only [Option.some.injEq, Prod.mk.injEq] at H
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := H
            have Hlo := xlo_sound SEGS E (Mr A argH E cs model FULL) (kn cs)
              (reg cs 10) alo HK hxl
            have Hhi := xhi_sound SEGS E (Mr A argH E cs model FULL) (kn cs)
              (reg cs 10) ahi HK hxh
            have Hal := page_aligned_sound SEGS E (Mr A argH E cs model FULL) (kn cs)
              (reg cs 10) HK hpa
            have HR := reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC
              ⟨by omega, by omega⟩
            exact ⟨rfl, rfl, Hal, by omega, by omega, by omega, HR, hflat⟩
          · exact absurd H (by simp)

/-- `kimg_clip` of `kn_unfill` survives a change confined to the range above
    the image hull. -/
theorem kn_unfill_clip_ok (SEGS : List Segment) (A : atable)
    (E : env) (M M' : word → Option byte) (k : List kentry) (b : expr) (off : Int)
    (ne : expr)
    (HK : know_ok SEGS E M k)
    (Hhull : A.img_hi ≤ estart E (SA b off))
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
        estart E (SA b off) + elenZ E ne ≤ bv_unsigned x → M' x = M x) :
    know_ok SEGS E M' (kimg_clip A (kn_unfill k b off ne)) := by
  intro K Hin
  have HKh := kimg_clip_in_hull A (kn_unfill k b off ne) K Hin
  have Hin' : K ∈ kn_unfill k b off ne := kimg_clip_incl A _ K Hin
  unfold kn_unfill at Hin'
  rw [List.mem_filter] at Hin'
  obtain ⟨Hin2, Hkeep⟩ := Hin'
  have HKK : kentry_ok SEGS E M K := HK K Hin2
  refine kentry_keep_sem SEGS E M M' K (estart E (SA b off)) (elenZ E ne) HKK ?_ Hout
  rw [Bool.or_eq_true] at Hkeep
  rcases Hkeep with Himg | Hap
  · cases K with
    | KImg lo hi =>
        unfold kfoot_apart kfoot
        simp only at HKh
        simp only [Prod.fst, Prod.snd]
        omega
    | KWord a w v => simp only [kimg_b] at Himg; cases Himg
    | KWr a l => simp only [kimg_b] at Himg; cases Himg
    | KZero a l => simp only [kimg_b] at Himg; cases Himg
    | KBlob a l c => simp only [kimg_b] at Himg; cases Himg
    | KAlign e m => simp only [kimg_b] at Himg; cases Himg
    | KRange e rlo rhi => simp only [kimg_b] at Himg; cases Himg
    | KDisj a1 n1 a2 n2 => simp only [kimg_b] at Himg; cases Himg
    | KFill a l c => simp only [kimg_b] at Himg; cases Himg
    | KUnk a l => simp only [kimg_b] at Himg; cases Himg
  · rw [kentry_apart_bp_eq] at Hap
    exact kentry_apart_b_sem SEGS E M k K b off ne HK Hap

/-- the valuation a NULL-hint grant continues in (
    `let E' := ext1 E v (Z_to_bv 64 (bv_unsigned a / 4096))`).  A `def`, not a
    `have`-bound local, so that it unfolds for `exact` / `simp`. -/
def mmEnv (E : env) (cs : acs) (a : word) : env :=
  ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))

/-- the fresh base `escale 4096 v` of a NULL-hint grant. -/
def mmBase (cs : acs) : expr := escale 4096 (.EVar (nxt cs))

/-- `mmap_null_cs1`: after a NULL-HINT grant the successor
    state is a checker state, and the fresh range is exactly what the checker
    then believes of it.  The heavy lifting is `grant_cs1_ok` — what this lemma
    contributes is the placement witness (the `null_kend` joint end fact and
    the `kdisj_new` disjointness facts are knowledge) plus the page arithmetic
    of the fresh base. -/
theorem mmap_null_cs1 (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (kd : mkind) (eager : Bool) (ne : expr) (nlo nhi : Int) (a : word) (nZ : Int)
    (model' : Model) (FULL' : word → Option byte)
    (HULL_ok : hull_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HML : mmap_len cs = some (ne, nlo, nhi))
    (Hfresh : fresh_ok nx0 cs = true)
    (Hnev : AsanPlanCore.expr_vars_lt (nxt cs) ne = true)
    (Hbudget : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT)
    (Hylo : KHI + 2 * nhi ≤ cs.a_ylo) (Hfloor : cs.a_ylo ≤ FLOOR)
    (Hkind : (kind_none kd || kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false) (Hnoh : no_holes cs.a_maps = true)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
    (GP : grant_ok_na (Z_to_bv 64 0) model a nZ = true)
    (GPo : grant_post kd a (Z_to_bv 64 nZ) model model')
    (GM : grant_mem kd a (Z_to_bv 64 nZ) FULL FULL') :
    cs_ok SEGS A LIMIT SINV argH FS0 (mmEnv E cs a) (null_cs1 A cs kd eager ne nlo nhi)
        (regupd R (Z_to_bv 5 (10 : Int)) a) FULL' model'
      ∧ edenot (mmEnv E cs a) (mmBase cs) = a
      ∧ edenot (mmEnv E cs a) ne = Z_to_bv 64 nZ
      ∧ bv_unsigned (Z_to_bv 64 nZ) = nZ
      ∧ env_agree nx0 E (mmEnv E cs a)
      ∧ (∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ →
          in_ivs (bv_unsigned x) ((m_vmmaps model').vm_maps) = true
          ∧ in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false
          ∧ argH (mmEnv E cs a) x = false
          ∧ in_hull A (bv_unsigned x) = false
          ∧ decide (CEIL ≤ bv_unsigned x) = false) := by
  -- ---- the length triple ----
  obtain ⟨R11, Hlen0, Hlen64, HneE, Hnlo0, HnZge, HnZhi, HnZal0, HneE'⟩ :=
    mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi HC HML
  have HnZal : nZ % 4096 = 0 := by rw [HnZ]; exact HnZal0
  have HnZhi' : nZ ≤ nhi := by rw [HnZ]; exact HnZhi
  have HnZge' : nlo ≤ nZ := by rw [HnZ]; exact HnZge
  have HnZpos : 0 < nZ := by
    have h1 : bv_unsigned (edenot E (reg cs 11)) ≤ nZ := by
      rw [HnZ]
      exact (page_round_up_Z_bounds _ (by omega)).1
    omega
  have Hnhipos : 0 < nhi := by omega
  -- ---- the grant gate ----
  have Hg := GP
  unfold grant_ok_na at Hg
  simp only [Bool.and_eq_true] at Hg
  obtain ⟨⟨⟨⟨Hal0, Hpos0⟩, Hceil0⟩, Hrf⟩, Hpl0⟩ := Hg
  rw [decide_eq_true_eq] at Hal0 Hpos0 Hceil0
  have Hal : bv_unsigned a % 4096 = 0 := by
    simpa only [bv_unsigned, page_size] using Hal0
  have Hceil : (a.toNat : Int) + nZ ≤ alloc_ceiling := Hceil0
  have HaC : bv_unsigned a + nZ ≤ CEIL := by
    have hc := CEIL_eq
    simp only [bv_unsigned]
    omega
  have Hpl : placement_ok_b (m_vmmaps model) (a.toNat : Int) nZ = true := by
    have hw0 : w_is0 (Z_to_bv 64 0) = true := by decide
    simpa only [hint_placement_ok_b, hw0, ite_true] using Hpl0
  have Un : bv_unsigned (Z_to_bv 64 nZ) = nZ := by
    refine u64_lit nZ ⟨by omega, ?_⟩
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    show nZ < two_pow_64
    unfold two_pow_64
    omega
  -- ---- move to the extended valuation ----
  have Hag : env_agree (nxt cs) E (mmEnv E cs a) := ext1_agree'' E (nxt cs) _
  obtain ⟨Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle⟩ := fresh_ok_parts nx0 cs Hfresh
  have HC' : cs_ok SEGS A LIMIT SINV argH FS0 (mmEnv E cs a) cs R FULL model :=
    cs_ok_agree SEGS A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E (mmEnv E cs a) cs
      R FULL model Hag Hfresh HC
  have Hag0 : env_agree nx0 E (mmEnv E cs a) := env_agree_le' nx0 (nxt cs) E _ Hag Fle
  have Hv : (mmEnv E cs a).ev (nxt cs) = Z_to_bv 64 (bv_unsigned a / 4096) :=
    ext1_at E (nxt cs) _
  have Hbase : edenot (mmEnv E cs a) (mmBase cs) = a :=
    escale_4096_denot (mmEnv E cs a) (nxt cs) a Hv Hal
  have HneE2 : edenot (mmEnv E cs a) ne = Z_to_bv 64 nZ := by
    have hv11 : AsanPlanCore.expr_vars_lt (nxt cs) (reg cs 11) = true :=
      nth_sr_vars_lt' (nxt cs) cs.a_ss.s_regs 11 Fsr (by omega)
    have hreg : edenot E (reg cs 11) = edenot (mmEnv E cs a) (reg cs 11) :=
      edenot_agree' (nxt cs) E (mmEnv E cs a) (reg cs 11) Hag hv11
    rw [HneE' (mmEnv E cs a) hreg.symm, HneE, ← HnZ]
  -- ---- placement ----
  obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := HC'.co_split
  have HKfl : kHighMemBeg < bottomup_floor := by
    obtain ⟨h1, h2⟩ := kHighMemBeg_below_mmap_base_min
    omega
  have HKa : kHighMemBeg < bv_unsigned a :=
    kHighMemBeg_le (m_vmmaps model) a nZ Y HnZpos
      (by simpa only [page_size] using HnZal)
      (by simpa only [bv_unsigned, page_size] using Hal)
      (by simpa only [page_size] using HY2)
      (by simpa only [bv_unsigned] using HY3)
      (by rw [KHI_eq]; omega) HY4 Hpl
  have Himg : A.img_hi ≤ bv_unsigned a := by
    have h1 : A.img_hi ≤ KHI := HULL_ok.2.2.2
    rw [← KHI_eq] at h1
    omega
  have Hapart : maps_apart (mmEnv E cs a) cs.a_maps (bv_unsigned a) nZ := by
    have h := maps_apart_of_region_free (mmEnv E cs a) cs.a_maps model a (Z_to_bv 64 nZ)
      HC'.co_maps Hrf
    rwa [Un] at h
  have NEW := grant_new_facts SEGS A LIMIT SINV argH FS0 (mmEnv E cs a) cs R FULL model a
    (Z_to_bv 64 nZ) nZ argH_high HC' Hrf Un HnZpos Himg HaC
  have Hnoholes : ∀ m, m ∈ cs.a_maps → is_hole m = true → False := by
    intro m Hm Hh
    have hall := Hnoh
    rw [no_holes, List.all_eq_true] at hall
    have h := hall m Hm
    rw [Hh] at h
    exact absurd h (by decide)
  -- ---- the new knowledge ----
  have HKmul : KHI = KHI / 4096 * 4096 := page_multiple_eq KHI (by decide)
  have HAmul : bv_unsigned a = bv_unsigned a / 4096 * 4096 := page_multiple_eq _ Hal
  have HKq : KHI / 4096 + 1 ≤ bv_unsigned a / 4096 := by
    have h1 : KHI / 4096 * 4096 < bv_unsigned a / 4096 * 4096 := by
      rw [← HKmul, ← HAmul]; exact HKa
    omega
  have Hmulu : 4096 * (KHI / 4096 + 1) ≤ bv_unsigned a := by omega
  have Hknew : know_ok SEGS (mmEnv E cs a) (Mr A argH (mmEnv E cs a) cs model' FULL')
      (.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)
        :: null_kend (mmBase cs) ne nlo ++ kdisj_new cs.a_maps (mmBase cs) ne) := by
    intro K HK
    rcases List.mem_cons.mp HK with rfl | HK
    · have hvb : bv_unsigned (edenot (mmEnv E cs a) (.EVar (nxt cs)))
          = bv_unsigned a / 4096 := by
        show bv_unsigned ((mmEnv E cs a).ev (nxt cs)) = bv_unsigned a / 4096
        rw [Hv]
        refine u64_lit _ ⟨?_, ?_⟩
        · exact Int.ediv_nonneg (by simp only [bv_unsigned]; exact Int.natCast_nonneg _) (by decide)
        · have hle : bv_unsigned a / 4096 ≤ bv_unsigned a :=
            Int.ediv_le_self 4096 (by simp only [bv_unsigned]; exact Int.natCast_nonneg _)
          have ha := (bv_unsigned_range_u64 a).2
          simp only [two_pow_64, bv_unsigned] at ha ⊢
          omega
      show (KHI / 4096 + 1) ≤ bv_unsigned (edenot (mmEnv E cs a) (.EVar (nxt cs))) ∧
        bv_unsigned (edenot (mmEnv E cs a) (.EVar (nxt cs))) ≤ (CEIL - nlo) / 4096
      rw [hvb]
      refine ⟨HKq, ?_⟩
      refine Int.ediv_le_ediv (a := bv_unsigned a) (b := CEIL - nlo) (c := 4096) (by decide) ?_
      omega
    · rcases List.mem_append.mp HK with HK | HK
      · exact null_kend_ok SEGS (mmEnv E cs a) (Mr A argH (mmEnv E cs a) cs model' FULL')
          (mmBase cs) ne nlo a (Z_to_bv 64 nZ) Hbase HneE2 Hmulu
          (by rw [Un]; exact HnZge') (by rw [Un]; exact HaC) K HK
      · unfold kdisj_new at HK
        rw [List.mem_flatMap] at HK
        obtain ⟨m, Hm, HK⟩ := HK
        cases hf : is_fog m with
        | true =>
          rw [hf] at HK
          simp only [ite_true] at HK
          cases HK
        | false =>
          rw [hf] at HK
          simp only [Bool.false_eq_true, ite_false] at HK
          split at HK
          · cases HK
          · rw [List.mem_singleton] at HK
            rw [HK]
            show estart (mmEnv E cs a) (SA m.am_base 0) + elenZ (mmEnv E cs a) m.am_len
                ≤ estart (mmEnv E cs a) (SA (mmBase cs) 0)
              ∨ estart (mmEnv E cs a) (SA (mmBase cs) 0) + elenZ (mmEnv E cs a) ne
                ≤ estart (mmEnv E cs a) (SA m.am_base 0)
            rcases Hapart m Hm hf with h | h
            · right
              simp only [estart, elenZ, SA]
              rw [Hbase, HneE2, Un]
              omega
            · left
              simp only [estart, elenZ, SA, Hbase]
              omega
  -- ---- the placement split ----
  have Hsplit : ∀ (Y0 : Int), cs.a_ylo ≤ Y0 → Y0 % 4096 = 0 →
      Y0 ≤ bv_unsigned (m_vmmaps model).vm_mmap_base →
      ledger_split ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) kHighMemBeg Y0 →
      ∃ Y', (cs.a_ylo - 2 * nhi) ≤ Y' ∧ Y' % 4096 = 0 ∧
        Y' ≤ bv_unsigned (m_vmmaps model).vm_mmap_base ∧
        ledger_split ((m_vmmaps model).vm_reserved ++
          (a, Z_to_bv 64 nZ) :: (m_vmmaps model).vm_maps) kHighMemBeg Y' := by
    intro Y0 HY01 HY02 HY03 HY04
    obtain ⟨S1, S2, S3, S4, S5, S6⟩ :=
      null_hint_grant_step (m_vmmaps model) a (Z_to_bv 64 nZ) nZ kHighMemBeg Y0
        HnZpos (by simpa only [page_size] using HnZal)
        (by simpa only [bv_unsigned, page_size] using Hal)
        (by simpa only [page_size] using HY02)
        (by simpa only [bv_unsigned] using HY03)
        (by decide) HKfl (by rw [KHI_eq]; omega) HY04 Hpl
    have hS2 := S2
    simp only [FLOOR_eq, page_size] at hS2
    have hY1 := HY01
    have hY2 := Hylo
    have hY3 := Hfloor
    have hY4 := HnZhi'
    have hY5 := Hnhipos
    clear HnZ HnZal HnZal0 HnZge HnZhi HnZhi' HnZge' HnZpos Hnhipos Hlen0 Hlen64 Hnlo0
      HAmul HKmul HKq Hmulu S1 S2 Hal Hal0 HneE HneE' R11
    refine ⟨min Y0 (bv_unsigned a), ?_,
      by simpa only [page_size, bv_unsigned] using S4,
      by simpa only [bv_unsigned] using S5, S6⟩
    rcases Int.le_total Y0 (bv_unsigned a) with hle | hge
    · rw [Int.min_eq_left hle] at hS2 ⊢
      rcases hS2 with h | h
      · omega
      · omega
    · rw [Int.min_eq_right hge] at hS2 ⊢
      rcases hS2 with h | h
      · omega
      · omega
  -- ---- the generic grant lemma ----
  obtain ⟨HC1, -, -⟩ :=
    grant_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame (mmEnv E cs a) cs R FULL
      model kd a (Z_to_bv 64 nZ) nZ model' FULL'
      (sr_upd cs.a_ss.s_regs 10 (mmBase cs)) (regupd R (Z_to_bv 5 (10 : Int)) a)
      (.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)
        :: null_kend (mmBase cs) ne nlo ++ kdisj_new cs.a_maps (mmBase cs) ne)
      (mmBase cs) ne nhi eager (cs.a_ylo - 2 * nhi) (Nat.succ (nxt cs))
      HC' Un HnZpos HnZal Hal Himg HaC Hrf GPo GM
      (regs_ok_set_n (mmEnv E cs a) cs.a_ss.s_regs R 10 (mmBase cs) a HC'.co_regs
        ⟨by omega, by omega⟩ Hbase)
      Hbase HneE2 Hknew Hkind Hkfog HnZhi' Hbudget Hsplit (by omega)
      (fun m Hm Hh => (Hnoholes m Hm Hh).elim)
  refine ⟨HC1, Hbase, HneE2, Un, Hag0, ?_⟩
  intro x Hx
  obtain ⟨N1, N2, N3, N4, N5, -⟩ := NEW x Hx
  refine ⟨?_, N2, ?_, N4, N5⟩
  · rw [GPo.gp_maps, in_ivs_cons, Bool.or_eq_true]
    left
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨Hx.1, by rw [Un]; exact Hx.2⟩
  · exact N3
/-- `grant_vis_add`: declaring the freshly granted range
    visible keeps the checker state.  The two new `KWr` / `KZero` entries are
    knowledge because the range is fresh (mapped, not PROT_NONE, outside the
    argument block: `NEW`) and zero-filled (`ZERO`), and the old knowledge
    survives because the new application range only UN-hides bytes
    (`know_ok_unhide`, with `hid_cons_sub` for the implication and `hid_hull`
    for the hull side). -/
theorem grant_vis_add (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (E : env) (cs1 cs2 : acs) (base ne : expr) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (a n : word) (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R FULL model)
    (Hva : vis_add A LIMIT cs1 base ne
      ([.KWr (SA base 0) ne, .KZero (SA base 0) ne] ++ kn cs1) = some cs2)
    (Hkh : kimg_in_hull A (kn cs1))
    (Hbase : edenot E base = a) (Hne : edenot E ne = n) (Un : bv_unsigned n = nZ)
    (HnZ : 0 ≤ nZ) (Hhi : bv_unsigned a + nZ ≤ 2 ^ 64)
    (NEW : ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ →
      in_ivs (bv_unsigned x) ((m_vmmaps model).vm_maps) = true
      ∧ in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false
      ∧ argH E x = false)
    (ZERO : ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ →
      FULL x = some (Z_to_bv 8 0)) :
    cs_ok SEGS A LIMIT SINV argH FS0 E cs2 R FULL model := by
  obtain ⟨nhi, Hnhi, Ecs2⟩ := vis_add_inv A LIMIT cs1 base ne _ cs2 Hva
  refine vis_add_sound SEGS A LIMIT SINV argH FS0 E cs1 base ne
    ([.KWr (SA base 0) ne, .KZero (SA base 0) ne] ++ kn cs1) cs2 R FULL model
    SHADOW_ok argH_high Hva HC ?_
  intro K HK
  rcases List.mem_append.mp HK with HK | HK
  · -- the fresh range: zero-filled and visible
    have Hs : estart E (SA base 0) = bv_unsigned a := by
      show bv_unsigned (edenot E base) + 0 = bv_unsigned a
      rw [Hbase]
      omega
    have Hn : elenZ E ne = nZ := by
      show bv_unsigned (edenot E ne) = nZ
      rw [Hne]; exact Un
    have Hlo0 : 0 ≤ bv_unsigned a := by
      have h := (bv_unsigned_range_u64 a).1
      simpa only [bv_unsigned] using h
    have Hlo64 : bv_unsigned a < 2 ^ 64 := by
      have h := (bv_unsigned_range_u64 a).2
      show bv_unsigned a < two_pow_64
      simp only [two_pow_64, bv_unsigned] at h ⊢
      omega
    refine kmem_ok SEGS E (Mr A argH E cs2 model FULL) base ne (bv_unsigned a) nZ
      Hs Hn Hlo0 Hlo64 HnZ Hhi ?_ K HK
    intro x Hx
    obtain ⟨N1, N2, N3⟩ := NEW x Hx
    have hv : in_vis E cs2 (bv_unsigned x) = true := by
      rw [Ecs2]
      simp only [in_vis, List.any_cons]
      rw [Bool.or_eq_true]
      left
      show (decide (AsanPlanSound.uE E base ≤ bv_unsigned x)
        && decide (bv_unsigned x < AsanPlanSound.uE E base + AsanPlanSound.uE E ne)) = true
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨by show bv_unsigned (edenot E base) ≤ bv_unsigned x; rw [Hbase]; exact Hx.1,
        by show bv_unsigned x < bv_unsigned (edenot E base) + bv_unsigned (edenot E ne)
           rw [Hbase, Hne, Un]; exact Hx.2⟩
    have Hal : in_allow A E cs2 (bv_unsigned x) = true := by
      simp only [in_allow, hv, Bool.true_or]
    have hvis : vis A E cs2 model x = true := by
      have h3 : (!(page_in_ranges (page_base x) (m_vm_lazy model))
          || in_allow A E cs2 (bv_unsigned x)) = true := by
        simp only [Hal, Bool.or_true]
      have hmid : (in_ivs (bv_unsigned x) ((m_vmmaps model).vm_maps)
          && !(in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess))
          && (!(page_in_ranges (page_base x) (m_vm_lazy model))
            || in_allow A E cs2 (bv_unsigned x))) = true := by
        simp only [N1, N2, h3, Bool.not_false, Bool.not_true, Bool.true_and,
          Bool.and_true]
      simp only [vis, hmid, Bool.or_true]
    have hhid : hid A argH E cs2 model x = false := by
      simp only [hid, N3, hvis, Bool.not_true, Bool.false_or, Bool.false_eq_true]
    unfold Mr mrestrict
    dsimp only
    simp only [hhid, Bool.false_eq_true, ite_false]
    exact ZERO x Hx
  · -- the old knowledge: fewer hidden bytes
    have Hoff : H_off_segments SEGS (hid A argH E cs1 model) :=
      H_off_segments_cs SEGS A argH E cs1 model HULL_ok SEGS_in_hull argH_high
    have Hsub : ∀ y : word, hid A argH E cs2 model y = true → hid A argH E cs1 model y = true := by
      intro y Hy
      rw [Ecs2] at Hy
      exact hid_cons_sub A argH E cs1 (base, ne) model y cs1.a_ss cs1.a_totsz cs1.a_ylo
        cs1.a_eager cs1.a_ghost cs1.a_abytes cs1.a_brk cs1.a_fd cs1.a_tidset Hy
    have Hhull : ∀ y : word, in_hull A (bv_unsigned y) = true →
        hid A argH E cs1 model y = false :=
      fun y hy => hid_hull A argH E cs1 model HULL_ok argH_high y hy
    exact know_ok_unhide SEGS A E (hid A argH E cs1 model) (hid A argH E cs2 model) FULL
      (kn cs1) Hoff Hkh Hsub Hhull HC.co_know K HK

/-- `fixed_pre`: the read-back of `fixed_args` at a `top` at or
    below the ceiling — the twelve facts the MAP_FIXED grant needs.  Pure
    re-assembly of `fixed_args_sound`, `mmap_len_sound` and
    `split_flat_estart`. -/
theorem fixed_pre (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (top : Int) (b : expr) (off : Int) (ne : expr) (nlo nhi : Int)
    (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model) (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HFA : fixed_args A cs top = some (b, off, ne, nlo, nhi)) (Htop : top ≤ CEIL)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) :
    edenot E ne = Z_to_bv 64 nZ
      ∧ bv_unsigned (Z_to_bv 64 nZ) = nZ
      ∧ estart E (SA b off) = bv_unsigned (edenot E (reg cs 10))
      ∧ bv_unsigned (edenot E (reg cs 10)) % 4096 = 0
      ∧ 0 < bv_unsigned (edenot E (reg cs 10))
      ∧ A.img_hi ≤ bv_unsigned (edenot E (reg cs 10))
      ∧ bv_unsigned (edenot E (reg cs 10)) + nZ ≤ top
      ∧ getr R (Z_to_bv 5 (10 : Int)) = edenot E (reg cs 10)
      ∧ nZ % 4096 = 0 ∧ 0 < nZ ∧ nZ ≤ nhi := by
  obtain ⟨Hsp, HML, Hal, Hpos, Himg, HtopA, R10, Hflat⟩ :=
    fixed_args_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model top b off ne nlo nhi
      HC HFA
  obtain ⟨R11, Hlen, Hlen64, Hne, Hnlo, HnZge, HnZhi, HnZal0, HneE'⟩ :=
    mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi HC HML
  have HnZal : nZ % 4096 = 0 := by rw [HnZ]; exact HnZal0
  have HnZhi' : nZ ≤ nhi := by rw [HnZ]; exact HnZhi
  have HnZpos : 0 < nZ := by
    have h1 : bv_unsigned (edenot E (reg cs 11)) ≤ nZ := by
      rw [HnZ]
      exact (page_round_up_Z_bounds _ (by omega)).1
    omega
  have Un : bv_unsigned (Z_to_bv 64 nZ) = nZ := by
    refine u64_lit nZ ⟨by omega, ?_⟩
    have h1 : bv_unsigned (edenot E (reg cs 10)) + nZ ≤ top := by omega
    have hcv : CEIL = 0x7fff7f800000 := rfl
    show nZ < two_pow_64
    unfold two_pow_64
    omega
  have Hest := split_flat_estart SEGS E (Mr A argH E cs model FULL) (kn cs) (reg cs 10) b off
    ne HC.co_know Hsp Hflat
  refine ⟨?_, Un, Hest.1, Hal, Hpos, Himg, by omega, R10, HnZal, HnZpos, HnZhi'⟩
  rw [Hne, ← HnZ]

/-- `cs_ok_unhole`: turning the consumed hole into a fog token
    of the same extent keeps the checker state — the ledger still denotes the
    model's, and the token's kind makes the hole/none/kind obligations vacuous. -/
theorem cs_ok_unhole (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (h : amap)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok SEGS A LIMIT SINV argH FS0 E (with_maps0 cs (unhole cs.a_maps h)) R FULL model := by
  have ELEM : ∀ m, m ∈ unhole cs.a_maps h → m ∈ cs.a_maps
      ∨ ∃ m0, m0 ∈ cs.a_maps ∧ m = AM m0.am_base m0.am_len .KFOG := by
    intro m Hm
    unfold unhole at Hm
    rw [List.mem_map] at Hm
    obtain ⟨m0, Hin, Hm0⟩ := Hm
    by_cases hc : (is_hole m0 && amap_eqb m0 h) = true
    · right
      exact ⟨m0, Hin, by rw [← Hm0]; simp only [hc, ite_true]⟩
    · left
      rw [← Hm0, ite_eq_right hc]
      exact Hin
  refine
  { co_regs := HC.co_regs
    co_log := HC.co_log
    co_know := HC.co_know
    co_halt := HC.co_halt
    co_fds := HC.co_fds
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
    co_brk := HC.co_brk
    co_sbrk := HC.co_sbrk
    co_eager := HC.co_eager
    co_abytes := HC.co_abytes
    co_minv := HC.co_minv
    co_zero := HC.co_zero
    co_sinv := HC.co_sinv }
  · exact (maps_match_unhole E cs.a_maps h (m_vmmaps model).vm_maps).mp HC.co_maps
  · intro m Hm Hh
    rcases ELEM m Hm with Hin | ⟨m0, -, rfl⟩
    · exact HC.co_holes m Hin Hh
    · simp only [is_hole, mkind_eqb] at Hh
      exact Bool.noConfusion Hh
  · intro m Hm Hk
    rcases ELEM m Hm with Hin | ⟨m0, -, rfl⟩
    · exact HC.co_none m Hin Hk
    · simp only at Hk
      rcases Hk with h | h <;> exact absurd h (by decide)
  · intro m Hm Hk
    rcases ELEM m Hm with Hin | ⟨m0, -, rfl⟩
    · exact HC.co_kinds m Hin Hk
    · cases Hk


/-- `shadow_facts_new_ok`: the shadow facts of a visible
    application range whose shadow lies inside the freshly granted rw-lazy
    entry are knowledge there — the entry is the shadow map, so its bytes are
    mapped, outside `vm_noaccess` and the argument block, and read zero. -/
theorem shadow_facts_new_ok (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (a n : word) (nZ : Int) (ne : expr) (model' : Model) (FULL' : word → Option byte)
    (SHADOW_ok : shadow_ok A)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Un : bv_unsigned n = nZ) (Hne : edenot E ne = n) (HaC : bv_unsigned a + nZ ≤ CEIL)
    (Hra : edenot E (reg cs 10) = a)
    (GPo : grant_post mkind.KRWLAZY a n model model')
    (GM : grant_mem mkind.KRWLAZY a n FULL FULL')
    (NEW : ∀ x : word, bv_unsigned a ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned a + nZ →
      in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false ∧ argH E x = false) :
    know_ok SEGS E (Mr A argH E cs model' FULL')
      (cs.a_vis.flatMap fun p =>
        shadow_facts A (kn cs) [AM (reg cs 10) ne mkind.KRWLAZY] p.1 p.2) := by
  intro K HK
  rw [List.mem_flatMap] at HK
  obtain ⟨p, Hp, HK⟩ := HK
  obtain ⟨sb0, sk0, hss⟩ :
      ∃ (sb0 : expr) (sk0 : Int),
        split_lit (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)) = (sb0, sk0) :=
    ⟨_, _, rfl⟩
  have hsh : shadow_of A (kn cs) p.1 p.2 = (sb0, sk0, mkSrl (kn cs) p.2 3) := by
    unfold shadow_of
    dsimp only
    rw [hss]
  cases hf : find_containing (kn cs) [AM (reg cs 10) ne mkind.KRWLAZY] [mkind.KRWLAZY]
      sb0 sk0 (mkSrl (kn cs) p.2 3) with
  | none =>
      have hz : shadow_facts A (kn cs) [AM (reg cs 10) ne mkind.KRWLAZY] p.1 p.2 = [] := by
        unfold shadow_facts
        dsimp only
        rw [hsh]
        dsimp only
        rw [hf]
      rw [hz] at HK
      exact absurd HK (by simp)
  | some m =>
      have hz : shadow_facts A (kn cs) [AM (reg cs 10) ne mkind.KRWLAZY] p.1 p.2
          = [.KWr (SA sb0 sk0) (mkSrl (kn cs) p.2 3),
             .KZero (SA sb0 sk0) (mkSrl (kn cs) p.2 3)] := by
        unfold shadow_facts
        dsimp only
        rw [hsh]
        dsimp only
        rw [hf]
      rw [hz] at HK
      -- the containing entry is the new one
      have Hm : m = AM (reg cs 10) ne mkind.KRWLAZY := by
        have h := List.mem_of_find?_eq_some hf
        simpa using h
      subst m
      have Hmb := List.find?_some hf
      unfold find_containing at Hmb
      rw [Bool.and_eq_true, Bool.and_eq_true] at Hmb
      obtain ⟨⟨-, -⟩, Hins⟩ := Hmb
      obtain ⟨I1, I2⟩ := xinside_sound SEGS E (Mr A argH E cs model FULL) (kn cs)
        sb0 sk0 (mkSrl (kn cs) p.2 3) (reg cs 10) 0 ne HC.co_know Hins
      -- the shadow interval's denotation
      have S3 : ∀ x : expr,
          bv_unsigned (edenot E (mkSrl (kn cs) x 3)) = bv_unsigned (edenot E x) / 8 := by
        intro x
        rw [mkSrl_denot SEGS E (Mr A argH E cs model FULL) (kn cs) x 3 (Z_to_bv 64 3)
          HC.co_know (by decide), u_srl64,
          show (bv_unsigned (Z_to_bv 64 3) % 64).toNat = 3 from by decide,
          show (2 : Int) ^ 3 = 8 from by decide]
      have Hlen : elenZ E (mkSrl (kn cs) p.2 3) = bv_unsigned (edenot E p.2) / 8 := S3 p.2
      simp only [estart, elenZ, SA, saddr.a_base, saddr.a_off, Int.add_zero] at I1 I2
      rw [Hra] at I1 I2
      rw [Hne, Un, S3 p.2] at I2
      have HSSr : estart E (SA sb0 sk0) = bv_unsigned (edenot E sb0) + sk0 := rfl
      rw [← HSSr] at I1 I2
      rw [← Hlen] at I2
      -- numeric setup
      have Ha0 : 0 ≤ bv_unsigned a := bv_unsigned_nonneg _
      have hub0 : 0 ≤ bv_unsigned (edenot E p.1) := bv_unsigned_nonneg _
      have hun0 : 0 ≤ bv_unsigned (edenot E p.2) := bv_unsigned_nonneg _
      have hbn64 : bv_unsigned (edenot E p.1) < 2 ^ 64 := by
        have h := (u64_range (edenot E p.1)).2
        simpa only [two_pow_64] using h
      have Hun64 : bv_unsigned (edenot E p.2) < 2 ^ 64 := by
        have h := (u64_range (edenot E p.2)).2
        simpa only [two_pow_64] using h
      have hun8 : 0 ≤ bv_unsigned (edenot E p.2) / 8 :=
        Int.ediv_nonneg hun0 (by decide)
      have hsh0 : 0 ≤ A.shadow_off := SHADOW_ok.1
      have hsh47 : A.shadow_off ≤ 2 ^ 47 := SHADOW_ok.2
      have hsh64 : A.shadow_off < 2 ^ 64 := by
        have h : (2 : Int) ^ 47 < 2 ^ 64 := by decide
        omega
      have Hlen0 : 0 ≤ elenZ E (mkSrl (kn cs) p.2 3) := by rw [Hlen]; exact hun8
      have Hest0 : 0 ≤ estart E (SA sb0 sk0) := by omega
      have Hceil64 : CEIL < 2 ^ 64 := by decide
      have Hest64 : estart E (SA sb0 sk0) < 2 ^ 64 := by omega
      -- the shadow base denotes `shadow_off + b / 8`
      have hu2 : bv_unsigned (edenot E (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)))
          = (bv_unsigned (edenot E p.1) / 8 + A.shadow_off) % 2 ^ 64 := by
        simp only [eadd]
        rw [mkAlu_denot]
        show bv_unsigned (edenot E (mkSrl (kn cs) p.1 3) + Z_to_bv 64 A.shadow_off) = _
        rw [u_add64, u_lit64a, S3 p.1, Int.emod_eq_of_lt hsh0 hsh64]
      have HSSmod : estart E (SA sb0 sk0)
          = (bv_unsigned (edenot E p.1) / 8 + A.shadow_off) % 2 ^ 64 := by
        rw [← u_of_split E (eadd (mkSrl (kn cs) p.1 3) (.ELit A.shadow_off)) sb0 sk0 hss
          ⟨Hest0, Hest64⟩, hu2]
      have HSS : estart E (SA sb0 sk0) = A.shadow_off + bv_unsigned (edenot E p.1) / 8 := by
        have h1 : 0 ≤ bv_unsigned (edenot E p.1) / 8 + A.shadow_off := by omega
        have h2 : bv_unsigned (edenot E p.1) / 8 + A.shadow_off < 2 ^ 64 := by
          have hle := Int.ediv_le_self 8 hub0
          omega
        rw [HSSmod, Int.emod_eq_of_lt h1 h2]
        omega
      -- the flatness of the shadow interval
      have Hfl : flat E (SA sb0 sk0) (elenZ E (mkSrl (kn cs) p.2 3)) := by
        unfold flat
        refine ⟨Hest0, Hest64, Hlen0, ?_⟩
        omega
      -- every byte of the shadow window reads zero
      have BYTE : ∀ y : word, estart E (SA sb0 sk0) ≤ bv_unsigned y →
          bv_unsigned y < estart E (SA sb0 sk0) + elenZ E (mkSrl (kn cs) p.2 3) →
          Mr A argH E cs model' FULL' y = some (Z_to_bv 8 0) := by
        intro y Hy1 Hy2
        have hya : bv_unsigned a ≤ bv_unsigned y ∧ bv_unsigned y < bv_unsigned a + nZ := by
          constructor <;> omega
        have hya' : bv_unsigned a ≤ bv_unsigned y ∧ bv_unsigned y < bv_unsigned a + bv_unsigned n := by
          rw [Un]; exact hya
        obtain ⟨N1, N2⟩ := NEW y hya
        -- the shadow byte is in the allowed set
        have hd : bv_unsigned (edenot E p.1) / 8 + bv_unsigned (edenot E p.2) / 8
            ≤ (bv_unsigned (edenot E p.1) + bv_unsigned (edenot E p.2)) / 8 := by
          have hle : 8 * (bv_unsigned (edenot E p.1) / 8 + bv_unsigned (edenot E p.2) / 8)
              ≤ bv_unsigned (edenot E p.1) + bv_unsigned (edenot E p.2) := by
            have e1 := Int.mul_ediv_add_emod (bv_unsigned (edenot E p.1)) 8
            have e2 := Int.mul_ediv_add_emod (bv_unsigned (edenot E p.2)) 8
            have r1 : 0 ≤ bv_unsigned (edenot E p.1) % 8 := Int.emod_nonneg _ (by decide)
            have r2 : 0 ≤ bv_unsigned (edenot E p.2) % 8 := Int.emod_nonneg _ (by decide)
            omega
          have h := Int.ediv_le_ediv (a := 8 * (bv_unsigned (edenot E p.1) / 8
            + bv_unsigned (edenot E p.2) / 8))
            (b := bv_unsigned (edenot E p.1) + bv_unsigned (edenot E p.2)) (c := 8)
            (by decide) hle
          rwa [Int.mul_ediv_cancel_left _ (by decide : (8 : Int) ≠ 0)] at h
        have Hsh2 : in_sh A E cs (bv_unsigned y) = true := by
          unfold in_sh
          rw [List.any_eq_true]
          refine ⟨p, Hp, ?_⟩
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          constructor
          · show A.shadow_off + AsanPlanSound.uE E p.1 / 8 ≤ bv_unsigned y
            rw [show AsanPlanSound.uE E p.1 = bv_unsigned (edenot E p.1) from rfl, ← HSS]
            exact Hy1
          · show bv_unsigned y
              < A.shadow_off + (AsanPlanSound.uE E p.1 + AsanPlanSound.uE E p.2) / 8
            rw [show AsanPlanSound.uE E p.1 = bv_unsigned (edenot E p.1) from rfl,
              show AsanPlanSound.uE E p.2 = bv_unsigned (edenot E p.2) from rfl]
            rw [Hlen] at Hy2
            omega
        have Hallow : in_allow A E cs (bv_unsigned y) = true := by
          unfold in_allow
          simp only [Hsh2, Bool.or_true]
        -- ... hence visible, and its bytes are mapped, not PROT_NONE
        have Hmap : in_ivs (bv_unsigned y) (m_vmmaps model').vm_maps = true := by
          rw [GPo.gp_maps, in_ivs_cons, Bool.or_eq_true]
          left
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          exact hya'
        have Hna : in_ivs (bv_unsigned y) (m_vmmaps model').vm_noaccess = false := by
          rw [GPo.gp_noacc]
          simpa only [kind_none, Bool.false_eq_true, ite_false, List.nil_append] using N1
        have Hvis : vis A E cs model' y = true := by
          show ((in_hull A (bv_unsigned y) || decide (CEIL ≤ bv_unsigned y)) ||
            (in_ivs (bv_unsigned y) (m_vmmaps model').vm_maps
              && !(in_ivs (bv_unsigned y) (m_vmmaps model').vm_noaccess)
              && (!(page_in_ranges (page_base y) (m_vm_lazy model'))
                  || in_allow A E cs (bv_unsigned y)))) = true
          simp only [Hmap, Hna, Hallow, Bool.not_false, Bool.not_true, Bool.and_true,
            Bool.true_and, Bool.or_true]
        have Hhid : hid A argH E cs model' y = false := by
          unfold hid
          rw [N2, Hvis]
          rfl
        have hfull : FULL' y = some (Z_to_bv 8 0) := by
          have h := GM.2 y hya'
          simpa only [kind_none, Bool.false_eq_true, ite_false] using h
        unfold Mr mrestrict
        simp only [Hhid, Bool.false_eq_true, ite_false]
        exact hfull
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at HK
      rcases HK with rfl | rfl
      · -- the writability facts
        unfold kentry_ok
        refine ⟨Hfl, ?_⟩
        intro d mm Hd Hdm
        cases mm with
        | zero => rfl
        | succ mm' =>
          have hu : ((BitVec.ofInt 64 (estart E (SA sb0 sk0) + d)).toNat : Int)
              = estart E (SA sb0 sk0) + d := by
            refine u64_lit _ ⟨by omega, by omega⟩
          refine StoreOk.store_ok_of_all SEGS (Mr A argH E cs model' FULL') (mm' + 1)
            (BitVec.ofInt 64 (estart E (SA sb0 sk0) + d)) ?_ ?_
          · rw [hu]
            have h2 : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
            have h3 : estart E (SA sb0 sk0) + d + ↑(mm' + 1) ≤ (2 : Int) ^ 64 := by
              have h4 : estart E (SA sb0 sk0) + bv_unsigned (edenot E p.2) / 8 ≤ 2 ^ 64 := by
                rw [← Hlen]; exact Hfl.2.2.2
              have h5 : d + ↑(mm' + 1) ≤ bv_unsigned (edenot E p.2) / 8 := by
                have h := Hdm
                rw [Hlen] at h
                exact h
              omega
            calc estart E (SA sb0 sk0) + d + ↑(mm' + 1) ≤ (2 : Int) ^ 64 := h3
              _ = ((2 ^ 64 : Nat) : Int) := h2.symm
          · intro x hx1 hx2
            rw [hu] at hx1 hx2
            have hb1 : estart E (SA sb0 sk0) ≤ (x.toNat : Int) := by omega
            have hb2 : (x.toNat : Int)
                < estart E (SA sb0 sk0) + elenZ E (mkSrl (kn cs) p.2 3) := by omega
            have hm : Mr A argH E cs model' FULL' x = some (Z_to_bv 8 0) := BYTE x hb1 hb2
            unfold wview
            rw [hm]
            intro h
            cases h
      · -- the zero facts
        unfold kentry_ok
        refine ⟨Hfl, ?_⟩
        intro i Hi Hi2
        have hu : ((BitVec.ofInt 64 (estart E (SA sb0 sk0) + i)).toNat : Int)
            = estart E (SA sb0 sk0) + i := by
          refine u64_lit _ ⟨by omega, by omega⟩
        refine BYTE (BitVec.ofInt 64 (estart E (SA sb0 sk0) + i)) ?_ ?_
        · show estart E (SA sb0 sk0)
              ≤ ((BitVec.ofInt 64 (estart E (SA sb0 sk0) + i)).toNat : Int)
          rw [hu]; omega
        · show ((BitVec.ofInt 64 (estart E (SA sb0 sk0) + i)).toNat : Int)
              < estart E (SA sb0 sk0) + elenZ E (mkSrl (kn cs) p.2 3)
          rw [hu]; omega

/-- `mmap_fixed_grant_cs1`: the granted child of a MAP_FIXED
    over a free range is a checker state, built from the ledger `ms0` (the
    tracked ledger itself, or it with the consumed hole turned into a fog
    token).  `fixed_pre` supplies the twelve facts about the arguments, and
    `grant_cs1_ok` does the work; what this lemma adds is the placement side
    (`Hside` chooses whether the split mark stays or drops to
    `min Y addr`) and, for the rw-lazy kind, the shadow facts of the visible
    application ranges (`shadow_facts_new_ok`). -/
theorem mmap_fixed_grant_cs1 (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (cs : acs) (ms0 : List amap) (kd : mkind) (eager : Bool) (top : Int) (b : expr)
    (off : Int) (ne : expr) (nlo nhi : Int) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (model' : Model) (FULL' : word → Option byte)
    (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HFA : fixed_args A cs top = some (b, off, ne, nlo, nhi)) (Htop : top ≤ CEIL)
    (HC0 : cs_ok SEGS A LIMIT SINV argH FS0 E (with_maps0 cs ms0) R FULL model)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
        (edenot E (reg cs 10)) (Z_to_bv 64 nZ) = true)
    (Hholes : ∀ m, m ∈ ms0 → is_hole m = true →
        bv_unsigned (edenot E (reg cs 10)) + nZ ≤ AsanPlanSound.uE E m.am_base ∨
        AsanPlanSound.uE E m.am_base + AsanPlanSound.uE E m.am_len
          ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hside : bv_unsigned (edenot E (reg cs 10)) + nZ ≤ KHI ∨
        cs.a_ylo ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hbudget : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT)
    (Hkind : (kind_none kd || kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false)
    (GPo : grant_post kd (edenot E (reg cs 10)) (Z_to_bv 64 nZ) model model')
    (GM : grant_mem kd (edenot E (reg cs 10)) (Z_to_bv 64 nZ) FULL FULL') :
    cs_ok SEGS A LIMIT SINV argH FS0 E (fixed_cs1 A (with_maps0 cs ms0) kd eager ne nhi)
        (regupd R (Z_to_bv 5 (10 : Int)) (edenot E (reg cs 10))) FULL' model'
      ∧ (∀ x : word, bv_unsigned (edenot E (reg cs 10)) ≤ bv_unsigned x ∧
            bv_unsigned x < bv_unsigned (edenot E (reg cs 10)) + nZ →
          in_ivs (bv_unsigned x) ((m_vmmaps model').vm_maps) = true
          ∧ in_ivs (bv_unsigned x) ((m_vmmaps model).vm_noaccess) = false
          ∧ argH E x = false) := by
  obtain ⟨Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZpos, HnZhi⟩ :=
    fixed_pre SEGS A LIMIT nx0 SINV argH FS0 cs top b off ne nlo nhi E R FULL model nZ
      HC HFA Htop HnZ
  have HaC : bv_unsigned (edenot E (reg cs 10)) + nZ ≤ CEIL := by omega
  have NEW := grant_new_facts SEGS A LIMIT SINV argH FS0 E cs R FULL model
    (edenot E (reg cs 10)) (Z_to_bv 64 nZ) nZ argH_high HC Hrf Un HnZpos Himg HaC
  -- the new knowledge: the shadow facts of a rw-lazy grant
  have Hknew : know_ok SEGS E (Mr A argH E (with_maps0 cs ms0) model' FULL')
      (if mkind_eqb kd mkind.KRWLAZY then
        cs.a_vis.flatMap fun p =>
          shadow_facts A (kn cs) [AM (reg cs 10) ne kd] p.1 p.2
       else []) := by
    by_cases hkd : mkind_eqb kd mkind.KRWLAZY = true
    · have hkd' : kd = mkind.KRWLAZY := mkind_eqb_eq hkd
      rw [ite_eq_left hkd]
      subst kd
      refine shadow_facts_new_ok SEGS A LIMIT nx0 SINV argH FS0 E (with_maps0 cs ms0)
        R FULL model (edenot E (reg cs 10)) (Z_to_bv 64 nZ) nZ ne model' FULL'
        SHADOW_ok HC0 Un Hne HaC rfl GPo GM ?_
      intro x Hx
      obtain ⟨N0, N1, N2, -, -, -⟩ := NEW x Hx
      exact ⟨N1, N2⟩
    · rw [ite_eq_right hkd]
      intro K HK
      cases HK
  -- the placement split
  have Hsplit : ∀ Y : Int, cs.a_ylo ≤ Y → Y % 4096 = 0 →
      Y ≤ bv_unsigned (m_vmmaps model).vm_mmap_base →
      ledger_split ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
        kHighMemBeg Y →
      ∃ Y', cs.a_ylo ≤ Y' ∧ Y' % 4096 = 0 ∧
        Y' ≤ bv_unsigned (m_vmmaps model).vm_mmap_base ∧
        ledger_split ((m_vmmaps model).vm_reserved ++
          (edenot E (reg cs 10), Z_to_bv 64 nZ) :: (m_vmmaps model).vm_maps)
          kHighMemBeg Y' := by
    intro Y HY1 HY2 HY3 HY4
    rcases Hside with Hlow | Hhigh
    · refine ⟨Y, HY1, HY2, HY3, ?_⟩
      obtain ⟨S1, S2⟩ := ledger_split_app_inv _ _ kHighMemBeg Y HY4
      refine ledger_split_app _ _ kHighMemBeg Y S1 ?_
      refine ledger_split_cons _ kHighMemBeg Y _ _ S2 ?_
      refine Or.inl ?_
      simp only [bv_unsigned] at Hlow Un ⊢
      rw [Un, KHI_eq]
      exact Hlow
    · refine ⟨min Y (bv_unsigned (edenot E (reg cs 10))),
        Int.le_min.mpr ⟨HY1, Hhigh⟩, ?_, ?_, ?_⟩
      · rcases Int.le_total Y (bv_unsigned (edenot E (reg cs 10))) with hle | hge
        · rw [Int.min_eq_left hle]; exact HY2
        · rw [Int.min_eq_right hge]; exact Hal
      · exact Int.le_trans (Int.min_le_left _ _) HY3
      · obtain ⟨S1, S2⟩ := ledger_split_app_inv _ _ kHighMemBeg Y HY4
        refine ledger_split_app _ _ kHighMemBeg _
          (ledger_split_mono _ _ Y _ S1 (Int.min_le_left _ _)) ?_
        refine ledger_split_cons _ kHighMemBeg _ _ _
          (ledger_split_mono _ _ Y _ S2 (Int.min_le_left _ _)) ?_
        exact Or.inr (Int.min_le_right _ _)
  obtain ⟨HC1, -, -⟩ :=
    grant_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame E (with_maps0 cs ms0) R FULL
      model kd (edenot E (reg cs 10)) (Z_to_bv 64 nZ) nZ model' FULL'
      (with_maps0 cs ms0).a_ss.s_regs
      (regupd R (Z_to_bv 5 (10 : Int)) (edenot E (reg cs 10)))
      (if mkind_eqb kd mkind.KRWLAZY then
        cs.a_vis.flatMap fun p =>
          shadow_facts A (kn cs) [AM (reg cs 10) ne kd] p.1 p.2
       else [])
      (reg cs 10) ne nhi eager cs.a_ylo (nxt cs)
      HC0 Un HnZpos HnZal Hal Himg HaC Hrf GPo GM
      (regs_ok_regupd_same E cs.a_ss.s_regs R 10 (edenot E (reg cs 10)) HC.co_regs
        ⟨by omega, by omega⟩ R10)
      rfl Hne (by intro K HK; exact Hknew K HK) Hkind Hkfog HnZhi Hbudget Hsplit (Int.le_refl _)
      (fun m hm hh => Hholes m hm hh)
  refine ⟨HC1, ?_⟩
  intro x Hx
  obtain ⟨N0, N1, N2, N3, N4, N5⟩ := NEW x Hx
  refine ⟨?_, N1, N2⟩
  rw [GPo.gp_maps, in_ivs_cons, Bool.or_eq_true]
  left
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨Hx.1, by rw [Un]; exact Hx.2⟩

/-- `mmap_fixed_old_facts`: the classic MAP_FIXED path — the
    tracked ledger itself, every entry apart, the target below `KHI`.  The
    ledger stays the checker's, the target range is free, no hole token can
    meet it (`no_fog`), and the placement split is the high one. -/
theorem mmap_fixed_old_facts (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (RES_hullH : RES_hull_def SEGS A)
    (cs : acs) (b : expr) (off : Int) (ne : expr) (nlo nhi : Int) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HFA : fixed_args A cs KHI = some (b, off, ne, nlo, nhi))
    (Hnf : no_fog cs.a_maps = true)
    (Hall : cs.a_maps.all (fun m =>
      ranges_apart_x (kn cs) b off ne m.am_base 0 m.am_len) = true)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) :
    cs_ok SEGS A LIMIT SINV argH FS0 E (with_maps0 cs cs.a_maps) R FULL model
      ∧ region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
          (edenot E (reg cs 10)) (Z_to_bv 64 nZ) = true
      ∧ (∀ m, m ∈ cs.a_maps → is_hole m = true →
          bv_unsigned (edenot E (reg cs 10)) + nZ ≤ AsanPlanSound.uE E m.am_base ∨
          AsanPlanSound.uE E m.am_base + AsanPlanSound.uE E m.am_len
            ≤ bv_unsigned (edenot E (reg cs 10)))
      ∧ (bv_unsigned (edenot E (reg cs 10)) + nZ ≤ KHI ∨
          cs.a_ylo ≤ bv_unsigned (edenot E (reg cs 10))) := by
  obtain ⟨Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZpos, HnZhi⟩ :=
    fixed_pre SEGS A LIMIT nx0 SINV argH FS0 cs KHI b off ne nlo nhi E R FULL model nZ
      HC HFA (by decide) HnZ
  refine ⟨HC, ?_, ?_, ?_⟩
  · refine region_free_of_apart SEGS A LIMIT SINV argH FS0 RES_hullH E cs R FULL model b off ne
      (edenot E (reg cs 10)) (Z_to_bv 64 nZ) HC Hnf Hall Hest ?_ Himg
    simp only [elenZ, Hne]
  · intro m Hm Hk
    exfalso
    have h1 : (!is_fog m) = true := List.all_eq_true.mp Hnf m Hm
    have h2 : is_fog m = false := by simpa using h1
    have h3 : is_fog m = true := by
      unfold is_hole at Hk
      exact tok_of_hole m.am_kind Hk
    rw [h3] at h2
    exact Bool.noConfusion h2
  · exact Or.inl HtopA

/-- `mmap_fixed_hole_facts`: the hole path — the target is
    exactly a hole token's range, so it is free by the hole facts, the other
    hole tokens are provably apart, and the split side is the hole's own. -/
theorem mmap_fixed_hole_facts (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (b : expr) (off : Int) (ne : expr) (nlo nhi : Int) (h : amap) (E : env)
    (R : BvMap word) (FULL : word → Option byte) (model : Model) (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HFA : fixed_args A cs CEIL = some (b, off, ne, nlo, nhi))
    (Hfh : find_hole (kn cs) cs.a_maps (reg cs 10) ne = some h)
    (Hap : (unhole cs.a_maps h).all (fun m =>
      !(is_hole m) || ranges_apart_x (kn cs) b off ne m.am_base 0 m.am_len) = true)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) :
    cs_ok SEGS A LIMIT SINV argH FS0 E (with_maps0 cs (unhole cs.a_maps h)) R FULL model
      ∧ region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
          (edenot E (reg cs 10)) (Z_to_bv 64 nZ) = true
      ∧ (∀ m, m ∈ unhole cs.a_maps h → is_hole m = true →
          bv_unsigned (edenot E (reg cs 10)) + nZ ≤ AsanPlanSound.uE E m.am_base ∨
          AsanPlanSound.uE E m.am_base + AsanPlanSound.uE E m.am_len
            ≤ bv_unsigned (edenot E (reg cs 10)))
      ∧ (bv_unsigned (edenot E (reg cs 10)) + nZ ≤ KHI ∨
          cs.a_ylo ≤ bv_unsigned (edenot E (reg cs 10))) := by
  obtain ⟨Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZpos, HnZhi⟩ :=
    fixed_pre SEGS A LIMIT nx0 SINV argH FS0 cs CEIL b off ne nlo nhi E R FULL model nZ
      HC HFA (by decide) HnZ
  obtain ⟨Hin, Hh, Hhb, Hhn⟩ :=
    find_hole_sound SEGS E (Mr A argH E cs model FULL) (kn cs) cs.a_maps (reg cs 10) ne h
      HC.co_know Hfh
  rw [Hne, Un] at Hhn
  obtain ⟨F1, F2⟩ := HC.co_holes h Hin Hh
  simp only [AsanPlanSound.uE] at F1 F2
  rw [Hhb, Hhn] at F1 F2
  refine ⟨?_, ?_, ?_, F2⟩
  · exact cs_ok_unhole SEGS A LIMIT SINV argH FS0 E cs R FULL model h HC
  · refine RefNodes.region_free_intro _ _ _ ?_
    intro b' s' Hin'
    have hUn : bv_unsigned (Z_to_bv 64 nZ) = nZ := Un
    simp only [bv_unsigned] at hUn ⊢
    rw [hUn]
    have hF := F1 (b', s') Hin'
    simp only [bv_unsigned] at hF
    rcases hF with hF | hF
    · exact Or.inr hF
    · exact Or.inl hF
  · intro m Hm Hk
    have h1 : ranges_apart_x (kn cs) b off ne m.am_base 0 m.am_len = true := by
      have h := List.all_eq_true.mp Hap m Hm
      rw [Hk] at h
      simpa using h
    have D := ranges_apart_x_sound SEGS E (Mr A argH E cs model FULL) (kn cs) b off ne
      m.am_base 0 m.am_len HC.co_know h1
    have hUn : bv_unsigned (Z_to_bv 64 nZ) = nZ := Un
    rw [Hest] at D
    simp only [estart, elenZ, SA, saddr.a_base, saddr.a_off, Int.add_zero] at D
    rw [Hne, hUn] at D
    simp only [AsanPlanSound.uE]
    exact D



/-- `kn_rezero_ok_gen`: after the slice was re-zeroed in
    place, every kept entry is knowledge for the new memory.  The ten-entry
    case analysis: the value-carrying entries (`KWord`/`KBlob`/`KFill`) are
    kept only when their footprint is apart from the slice (so they transfer
    by `kentry_keep_sem`); `KZero`/`KUnk` keep their facts under the
    definedness/zero transfer; `KWr` transfers writability through
    `store_ok_mono`; the image `KImg` is above the slice by `Hhull`; the
    rest carry no memory fact. -/
theorem kn_rezero_ok_gen (SEGS : List Segment) (A : atable)
    (E : env) (M M' : word → Option byte) (k : List kentry) (b : expr) (off : Int)
    (ne : expr)
    (HK : know_ok SEGS E M k)
    (Hhull : A.img_hi ≤ estart E (SA b off))
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
        estart E (SA b off) + elenZ E ne ≤ bv_unsigned x → M' x = M x)
    (Hin0 : ∀ x : word, estart E (SA b off) ≤ bv_unsigned x →
        bv_unsigned x < estart E (SA b off) + elenZ E ne → M x ≠ none →
        M' x = some (Z_to_bv 8 0)) :
    ∀ K, K ∈ kn_rezero k b off ne →
      (match K with | .KImg lo hi => A.img_lo ≤ lo ∧ hi ≤ A.img_hi | _ => True) →
      kentry_ok SEGS E M' K := by
  have DEF : StoreOk.mem_grows M M' := by
    intro x Hx
    by_cases h1 : bv_unsigned x < estart E (SA b off)
    · rw [Hout x (Or.inl h1)]; exact Hx
    · have h1' : estart E (SA b off) ≤ bv_unsigned x := by omega
      by_cases h2 : bv_unsigned x < estart E (SA b off) + elenZ E ne
      · rw [Hin0 x h1' h2 Hx]; simp
      · have h2' : estart E (SA b off) + elenZ E ne ≤ bv_unsigned x := by omega
        rw [Hout x (Or.inr h2')]; exact Hx
  have ZERO : ∀ x : word, M x = some (Z_to_bv 8 0) → M' x = some (Z_to_bv 8 0) := by
    intro x Hx
    by_cases h1 : bv_unsigned x < estart E (SA b off)
    · rw [Hout x (Or.inl h1)]; exact Hx
    · have h1' : estart E (SA b off) ≤ bv_unsigned x := by omega
      by_cases h2 : bv_unsigned x < estart E (SA b off) + elenZ E ne
      · exact Hin0 x h1' h2 (by rw [Hx]; simp)
      · have h2' : estart E (SA b off) + elenZ E ne ≤ bv_unsigned x := by omega
        rw [Hout x (Or.inr h2')]; exact Hx
  intro K Hin HKh
  unfold kn_rezero at Hin
  dsimp only at Hin
  rw [List.mem_filter] at Hin
  obtain ⟨Hin, Hkeep⟩ := Hin
  have HKK : kentry_ok SEGS E M K := HK K Hin
  cases K with
  | KWord a w v =>
      refine kentry_keep_sem SEGS E M M' _ _ _ HKK ?_ Hout
      exact kentry_apart_b_sem SEGS E M k _ b off ne HK
        (by simpa only [kentry_apart_bp_eq] using Hkeep)
  | KBlob a nn bk =>
      refine kentry_keep_sem SEGS E M M' _ _ _ HKK ?_ Hout
      exact kentry_apart_b_sem SEGS E M k _ b off ne HK
        (by simpa only [kentry_apart_bp_eq] using Hkeep)
  | KFill a nn fc =>
      refine kentry_keep_sem SEGS E M M' _ _ _ HKK ?_ Hout
      exact kentry_apart_b_sem SEGS E M k _ b off ne HK
        (by simpa only [kentry_apart_bp_eq] using Hkeep)
  | KImg lo hi =>
      have hKh := HKh
      simp only at hKh
      obtain ⟨h1, h2⟩ := hKh
      refine kentry_keep_sem SEGS E M M' _ _ _ HKK ?_ Hout
      simp only [kfoot_apart, kfoot]
      omega
  | KZero a nn =>
      obtain ⟨Hfl, Hz⟩ := HKK
      exact ⟨Hfl, fun i hi0 hil => ZERO _ (Hz i hi0 hil)⟩
  | KWr a nn =>
      obtain ⟨Hfl, Hs⟩ := HKK
      refine ⟨Hfl, ?_⟩
      intro d mm Hd Hdm
      exact StoreOk.store_ok_mono SEGS mm M M' (BitVec.ofInt 64 (estart E a + d))
        DEF (Hs d mm Hd Hdm)
  | KUnk a nn =>
      obtain ⟨Hfl, Hz⟩ := HKK
      exact ⟨Hfl, fun i hi0 hil => DEF _ (Hz i hi0 hil)⟩
  | KAlign e mm => exact HKK
  | KRange e lo hi => exact HKK
  | KDisj a1 n1 a2 n2 => exact HKK

/-- `kn_rezero_clip_ok`: the same, with the image facts
    clipped to the hull (what every hidden-set change keeps). -/
theorem kn_rezero_clip_ok (SEGS : List Segment) (A : atable)
    (E : env) (M M' : word → Option byte) (k : List kentry) (b : expr) (off : Int)
    (ne : expr)
    (HK : know_ok SEGS E M k)
    (Hhull : A.img_hi ≤ estart E (SA b off))
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
        estart E (SA b off) + elenZ E ne ≤ bv_unsigned x → M' x = M x)
    (Hin0 : ∀ x : word, estart E (SA b off) ≤ bv_unsigned x →
        bv_unsigned x < estart E (SA b off) + elenZ E ne → M x ≠ none →
        M' x = some (Z_to_bv 8 0)) :
    know_ok SEGS E M' (kimg_clip A (kn_rezero k b off ne)) := by
  intro K Hin
  exact kn_rezero_ok_gen SEGS A E M M' k b off ne HK Hhull Hout Hin0 K
    (kimg_clip_incl A _ K Hin) (kimg_clip_in_hull A _ K Hin)

/-- `kn_rezero_hull_ok`: the same when the whole knowledge
    already has its image facts in the hull. -/
theorem kn_rezero_hull_ok (SEGS : List Segment) (A : atable)
    (E : env) (M M' : word → Option byte) (k : List kentry) (b : expr) (off : Int)
    (ne : expr)
    (HK : know_ok SEGS E M k) (Hh : kimg_in_hull A k)
    (Hhull : A.img_hi ≤ estart E (SA b off))
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
        estart E (SA b off) + elenZ E ne ≤ bv_unsigned x → M' x = M x)
    (Hin0 : ∀ x : word, estart E (SA b off) ≤ bv_unsigned x →
        bv_unsigned x < estart E (SA b off) + elenZ E ne → M x ≠ none →
        M' x = some (Z_to_bv 8 0)) :
    know_ok SEGS E M' (kn_rezero k b off ne) := by
  intro K Hin
  have Hin' : K ∈ k := by
    unfold kn_rezero at Hin
    exact (List.mem_filter.mp Hin).1
  exact kn_rezero_ok_gen SEGS A E M M' k b off ne HK Hhull Hout Hin0 K Hin (Hh K Hin')



/-- `vis_add_slice_ok`: declaring the re-zeroed slice visible
    keeps the checker state.  The two new `KWr` / `KZero` entries are
    knowledge (the slice is mapped, outside `vm_noaccess` and the argument
    block, and reads zero — `NEW`), and the old knowledge survives through
    `know_ok_unhide` because the new application range only UN-hides bytes. -/
theorem vis_add_slice_ok (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (E : env) (cs1 cs2 : acs) (ea : expr) (b : expr) (off : Int) (ne : expr)
    (R : BvMap word) (FULL' : word → Option byte) (model' : Model) (lo nZ : Int)
    (HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R FULL' model')
    (Hva : vis_add A LIMIT cs1 ea ne
      (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1) = some cs2)
    (Hkh : kimg_in_hull A (kn cs1))
    (Hea : AsanPlanSound.uE E ea = lo) (Hest : estart E (SA b off) = lo)
    (Hne : elenZ E ne = nZ) (Hlo : 0 ≤ lo) (HnZpos : 0 < nZ) (Hhi : lo + nZ ≤ CEIL)
    (NEW : ∀ x : word, lo ≤ bv_unsigned x ∧ bv_unsigned x < lo + nZ →
      in_ivs (bv_unsigned x) ((m_vmmaps model').vm_maps) = true
      ∧ in_ivs (bv_unsigned x) ((m_vmmaps model').vm_noaccess) = false
      ∧ argH E x = false ∧ FULL' x = some (Z_to_bv 8 0)) :
    cs_ok SEGS A LIMIT SINV argH FS0 E cs2 R FULL' model' := by
  obtain ⟨nhi, Hnhi, Ecs2⟩ :=
    vis_add_inv A LIMIT cs1 ea ne (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1)
      cs2 Hva
  refine vis_add_sound SEGS A LIMIT SINV argH FS0 E cs1 ea ne
    (.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1) cs2 R FULL' model'
    SHADOW_ok argH_high Hva HC1 ?_
  have HCEIL64 : CEIL < 2 ^ 64 := by decide
  have HnZpos' : 0 < nZ := HnZpos
  -- every byte of the slice reads zero in the restricted new memory
  have BYTE : ∀ x : word, lo ≤ bv_unsigned x ∧ bv_unsigned x < lo + nZ →
      Mr A argH E cs2 model' FULL' x = some (Z_to_bv 8 0) := by
    intro x Hx
    obtain ⟨N1, N2, N3, N4⟩ := NEW x Hx
    have hv : in_vis E cs2 (bv_unsigned x) = true := by
      unfold in_vis
      rw [Ecs2, List.any_cons, Bool.or_eq_true]
      left
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      refine ⟨?_, ?_⟩
      · show AsanPlanSound.uE E ea ≤ bv_unsigned x
        rw [Hea]; exact Hx.1
      · show bv_unsigned x < AsanPlanSound.uE E ea + AsanPlanSound.uE E ne
        rw [Hea]
        have hne : AsanPlanSound.uE E ne = nZ := Hne
        rw [hne]; exact Hx.2
    have Hal : in_allow A E cs2 (bv_unsigned x) = true := by
      simp only [in_allow, hv, Bool.true_or]
    have hvis : vis A E cs2 model' x = true := by
      have h3 : (!(page_in_ranges (page_base x) (m_vm_lazy model'))
          || in_allow A E cs2 (bv_unsigned x)) = true := by
        simp only [Hal, Bool.or_true]
      have hmid : (in_ivs (bv_unsigned x) ((m_vmmaps model').vm_maps)
          && !(in_ivs (bv_unsigned x) ((m_vmmaps model').vm_noaccess))
          && (!(page_in_ranges (page_base x) (m_vm_lazy model'))
            || in_allow A E cs2 (bv_unsigned x))) = true := by
        simp only [N1, N2, h3, Bool.not_false, Bool.not_true, Bool.true_and,
          Bool.and_true]
      simp only [vis, hmid, Bool.or_true]
    have hhid : hid A argH E cs2 model' x = false := by
      simp only [hid, N3, hvis, Bool.not_true, Bool.false_or, Bool.false_eq_true]
    unfold Mr mrestrict
    dsimp only
    simp only [hhid, Bool.false_eq_true, ite_false]
    exact N4
  intro K HK
  rcases List.mem_cons.mp HK with rfl | HK
  · -- the writability fact
    have Hfl : flat E (SA b off) (elenZ E ne) := by
      unfold flat
      rw [Hest, Hne]
      exact ⟨Hlo, by omega, by omega, by omega⟩
    unfold kentry_ok
    refine ⟨Hfl, ?_⟩
    intro d mm Hd Hdm
    cases mm with
    | zero => rfl
    | succ mm' =>
      rw [Hne] at Hdm
      have hu : ((BitVec.ofInt 64 (estart E (SA b off) + d)).toNat : Int)
          = estart E (SA b off) + d := by
        refine u64_lit _ ⟨by omega, by omega⟩
      refine StoreOk.store_ok_of_all SEGS (Mr A argH E cs2 model' FULL') (mm' + 1)
        (BitVec.ofInt 64 (estart E (SA b off) + d)) ?_ ?_
      · rw [hu, Hest]
        have h2 : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
        have h3 : lo + d + ↑(mm' + 1) ≤ (2 : Int) ^ 64 := by omega
        calc lo + d + ↑(mm' + 1) ≤ (2 : Int) ^ 64 := h3
          _ = ((2 ^ 64 : Nat) : Int) := h2.symm
      · intro x hx1 hx2
        rw [hu, Hest] at hx1 hx2
        have hb1 : lo ≤ (x.toNat : Int) := by omega
        have hb2 : (x.toNat : Int) < lo + nZ := by omega
        have hm := BYTE x ⟨hb1, hb2⟩
        unfold wview
        rw [hm]
        intro h
        cases h
  · rcases List.mem_cons.mp HK with rfl | HK
    · -- the zero fact
      have Hfl : flat E (SA b off) (elenZ E ne) := by
        unfold flat
        rw [Hest, Hne]
        exact ⟨Hlo, by omega, by omega, by omega⟩
      unfold kentry_ok
      refine ⟨Hfl, ?_⟩
      intro i Hi Hi2
      rw [Hne] at Hi2
      have hu : ((BitVec.ofInt 64 (estart E (SA b off) + i)).toNat : Int)
          = estart E (SA b off) + i := by
        refine u64_lit _ ⟨by omega, by omega⟩
      have hb1 : lo ≤ ((BitVec.ofInt 64 (estart E (SA b off) + i)).toNat : Int) := by
        rw [hu, Hest]; omega
      have hb2 : ((BitVec.ofInt 64 (estart E (SA b off) + i)).toNat : Int)
          < lo + nZ := by
        rw [hu, Hest]; omega
      exact BYTE _ ⟨hb1, hb2⟩
    · -- the old knowledge: fewer hidden bytes
      have Hoff : H_off_segments SEGS (hid A argH E cs1 model') :=
        H_off_segments_cs SEGS A argH E cs1 model' HULL_ok SEGS_in_hull argH_high
      have Hsub : ∀ y : word, hid A argH E cs2 model' y = true →
          hid A argH E cs1 model' y = true := by
        intro y Hy
        rw [Ecs2] at Hy
        exact hid_cons_sub A argH E cs1 (ea, ne) model' y cs1.a_ss cs1.a_totsz cs1.a_ylo
          cs1.a_eager cs1.a_ghost cs1.a_abytes cs1.a_brk cs1.a_fd cs1.a_tidset Hy
      have Hhull : ∀ y : word, in_hull A (bv_unsigned y) = true →
          hid A argH E cs1 model' y = false :=
        fun y hy => hid_hull A argH E cs1 model' HULL_ok argH_high y hy
      exact know_ok_unhide SEGS A E (hid A argH E cs1 model') (hid A argH E cs2 model') FULL'
        (kn cs1) Hoff Hkh Hsub Hhull HC1.co_know K HK

/-- `slice_args`: the arguments, the containing entry and the
    slice — the twenty facts the four slice nodes read off `fixed_args`,
    `mmap_len` and `find_containing`.  `nZ` is a parameter with its defining
    equation. -/
theorem slice_args (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (RES_hullH : RES_hull_def SEGS A)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (b : expr) (off : Int) (ne : expr) (nlo nhi : Int) (kinds : List mkind) (m : amap)
    (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (HFA : fixed_args A cs CEIL = some (b, off, ne, nlo, nhi))
    (Hf : find_containing (kn cs) cs.a_maps kinds b off ne = some m)
    (HnZ : nZ = page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) :
    m ∈ cs.a_maps ∧ (m.am_kind ∈ kinds ∧ is_fog m = false)
      ∧ getr R (Z_to_bv 5 (10 : Int)) = edenot E (reg cs 10)
      ∧ getr R (Z_to_bv 5 (11 : Int)) = Z_to_bv 64 (bv_unsigned (edenot E (reg cs 11)))
      ∧ 0 < bv_unsigned (edenot E (reg cs 11))
      ∧ bv_unsigned (edenot E (reg cs 11)) < 2 ^ 64
      ∧ edenot E ne = Z_to_bv 64 nZ ∧ bv_unsigned (Z_to_bv 64 nZ) = nZ
      ∧ 0 < nZ ∧ nZ ≤ nhi ∧ nZ % 4096 = 0
      ∧ bv_unsigned (edenot E (reg cs 10)) % 4096 = 0
      ∧ 0 < bv_unsigned (edenot E (reg cs 10))
      ∧ A.img_hi ≤ bv_unsigned (edenot E (reg cs 10))
      ∧ estart E (SA b off) = bv_unsigned (edenot E (reg cs 10))
      ∧ bv_unsigned (edenot E m.am_base) ≤ bv_unsigned (edenot E (reg cs 10))
      ∧ bv_unsigned (edenot E (reg cs 10)) + nZ
          ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
      ∧ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ CEIL
      ∧ map_contains ((m_vmmaps model).vm_maps) (edenot E (reg cs 10))
          (Z_to_bv 64 nZ) = true
      ∧ region_free ((m_vmmaps model).vm_reserved) (edenot E (reg cs 10))
          (Z_to_bv 64 nZ) = true
      ∧ overlap_sum ((m_vmmaps model).vm_maps) (bv_unsigned (edenot E (reg cs 10)))
          (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 nZ)) ≤ nZ := by
  have HK := HC.co_know
  obtain ⟨Hsp, HML, Hal, Hpos, Himg, Htop, R10, Hflat⟩ :=
    fixed_args_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model CEIL b off ne nlo nhi
      HC HFA
  obtain ⟨R11, Hlenpos, Hlen64, Hne, Hnlopos, Hnlo, HnZhi0, HnZal0, HneE'⟩ :=
    mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi HC HML
  have HnZal : nZ % 4096 = 0 := by rw [HnZ]; exact HnZal0
  have HnZhi : nZ ≤ nhi := by rw [HnZ]; exact HnZhi0
  have HnZpos : 0 < nZ := by
    have h1 : bv_unsigned (edenot E (reg cs 11)) ≤ nZ := by
      rw [HnZ]
      exact (page_round_up_Z_bounds _ (by omega)).1
    omega
  have Hne' : edenot E ne = Z_to_bv 64 nZ := by rw [Hne, HnZ]
  have Un : bv_unsigned (Z_to_bv 64 nZ) = nZ := by
    refine u64_lit nZ ⟨by omega, ?_⟩
    have hcv : CEIL = 0x7fff7f800000 := rfl
    show nZ < two_pow_64
    unfold two_pow_64
    omega
  obtain ⟨Hm, ⟨Hkind, Hnf⟩, I1, I2⟩ :=
    find_containing_sound SEGS E (Mr A argH E cs model FULL) (kn cs) cs.a_maps kinds b off ne m
      HK Hf
  have HIN : amap_den E m ∈ (m_vmmaps model).vm_maps :=
    maps_match_In E cs.a_maps _ m HC.co_maps Hm Hnf
  obtain ⟨B1, B2, B3, B4, B5⟩ := HC.co_bounds (amap_den E m) HIN
  dsimp only [amap_den, Prod.fst, Prod.snd] at B1 B2 B3 B4 B5
  have Hbase0 : 0 ≤ bv_unsigned (edenot E m.am_base) := bv_unsigned_nonneg _
  have HCEIL64 : CEIL < 2 ^ 64 := by decide
  simp only [elenZ] at I2
  rw [Hne', Un] at I2
  -- the two interval facts, in the goal's own spelling
  have I1' : bv_unsigned (edenot E m.am_base) ≤ estart E (SA b off) := I1
  have I2' : estart E (SA b off) + nZ
      ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := I2
  have Hest : bv_unsigned (edenot E (reg cs 10)) = estart E (SA b off) := by
    refine u_of_split E (reg cs 10) b off Hsp ⟨?_, ?_⟩
    · omega
    · omega
  have Hmc : map_contains ((m_vmmaps model).vm_maps) (edenot E (reg cs 10))
      (Z_to_bv 64 nZ) = true := by
    refine map_contains_intro _ _ _ (edenot E m.am_base) (edenot E m.am_len) HIN ?_ ?_
    · rw [Hest]; exact I1'
    · rw [Hest, Un]; exact I2'
  refine ⟨Hm, ⟨Hkind, Hnf⟩, R10, R11, Hlenpos, Hlen64, Hne', Un, HnZpos, HnZhi, HnZal,
    Hal, Hpos, Himg, Hest.symm, ?_, ?_, B5, Hmc, ?_, ?_⟩
  · rw [Hest]; exact I1'
  · rw [Hest]; exact I2'
  · refine reserved_free_above SEGS A model (edenot E (reg cs 10)) (Z_to_bv 64 nZ)
      RES_hullH HC.co_res ?_
    exact Himg
  · have h := overlap_sum_contained ((m_vmmaps model).vm_maps) (edenot E m.am_base)
      (edenot E m.am_len) (bv_unsigned (edenot E (reg cs 10)))
      (bv_unsigned (edenot E (reg cs 10)) + nZ) HC.co_seps HIN ?_ ?_ ?_
    · rw [Un]
      have hsub : bv_unsigned (edenot E (reg cs 10)) + nZ
          - bv_unsigned (edenot E (reg cs 10)) = nZ := by omega
      rw [hsub] at h
      exact h
    · rw [Hest]; exact I1'
    · rw [Hest]; exact I2'
    · omega



/-- `gap_ok_sound`: the GRANT child of a NULL-hint request is
    inhabited — `gap_ok`'s slack bound is exactly the band
    `AsanPlacement.free_gap_of_totals` needs, since the model's ledger is no
    longer than `n_res A + |a_maps cs|` and its total size is at most
    `a_totsz cs`. -/
theorem gap_ok_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (RES_lenH : res_len_ok SEGS A)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (nhi nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hg : gap_ok A cs nhi = true) (HnZ : 0 ≤ nZ ∧ nZ ≤ nhi) :
    ∃ a : word, grant_ok_na (Z_to_bv 64 0) model a nZ = true := by
  obtain ⟨HnZ0, HnZle⟩ := HnZ
  have Hg' : FLOOR + nhi + cs.a_totsz
      + ((A.n_res + cs.a_maps.length : Nat) : Int) * (nhi + 4095) ≤ CEIL := by
    have h := Hg
    unfold gap_ok at h
    dsimp only at h
    simpa only [decide_eq_true_eq] using h
  -- the model's ledger is no longer than the tracked one
  have Llen : ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps).length
      ≤ A.n_res + cs.a_maps.length := by
    rw [List.length_append]
    have hres : (m_vmmaps model).vm_reserved.length = A.n_res := by
      rw [HC.co_res]
      exact RES_lenH
    have hmaps : (m_vmmaps model).vm_maps.length ≤ cs.a_maps.length :=
      maps_match_length E cs.a_maps _ HC.co_maps
    omega
  -- its total size is at most the accumulated one
  have GW : gw_sizes ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
      ≤ cs.a_totsz := by
    have G1 := gap_weight_sizes nZ
      ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
    rw [gap_weight_eq nZ] at G1
    have T := HC.co_totsz
    omega
  -- the band of `free_gap_of_totals`
  have hband : bottomup_floor + nZ + cs.a_totsz
      + (((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps).length : Int)
        * (nZ + 4095) ≤ alloc_ceiling := by
    have hF : bottomup_floor = FLOOR := FLOOR_eq
    have hC : alloc_ceiling = CEIL := CEIL_eq
    have hlen : (((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps).length : Int)
        ≤ ((A.n_res + cs.a_maps.length : Nat) : Int) := Int.ofNat_le.mpr Llen
    have hlen0 : (0 : Int)
        ≤ (((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps).length : Int) :=
      Int.natCast_nonneg _
    have hcnt0 : (0 : Int) ≤ ((A.n_res + cs.a_maps.length : Nat) : Int) :=
      Int.natCast_nonneg _
    have hmul1 : (((m_vmmaps model).vm_reserved
          ++ (m_vmmaps model).vm_maps).length : Int) * (nZ + 4095)
        ≤ ((A.n_res + cs.a_maps.length : Nat) : Int) * (nZ + 4095) :=
      Int.mul_le_mul_of_nonneg_right hlen (by omega)
    have hmul2 : ((A.n_res + cs.a_maps.length : Nat) : Int) * (nZ + 4095)
        ≤ ((A.n_res + cs.a_maps.length : Nat) : Int) * (nhi + 4095) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hcnt0
    omega
  obtain ⟨g, Hal, Hfl, Hc, Hfree, Hpl⟩ :=
    free_gap_of_totals (m_vmmaps model) nZ cs.a_totsz HnZ0 GW hband
  have Hfloor0 : (0 : Int) < bottomup_floor := by
    have h : bottomup_floor = 0x2aaaaaaab000 := bottomup_floor_val
    rw [h]
    decide
  have Hg0 : 0 < g := Int.lt_of_lt_of_le Hfloor0 Hfl
  have Hg64 : g < 2 ^ 64 := by
    have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
    have h2 : (0x7fff7f800000 : Int) < 2 ^ 64 := by decide
    omega
  refine ⟨Z_to_bv 64 g, ?_⟩
  have hu : ((Z_to_bv 64 g).toNat : Int) = g := u64_lit g ⟨by omega, Hg64⟩
  have Hfree' : region_free ((m_vmmaps model).vm_reserved
      ++ (m_vmmaps model).vm_maps) (Z_to_bv 64 g) (BitVec.ofInt 64 nZ) = true := Hfree
  have Hpl' : hint_placement_ok_b (Z_to_bv 64 0) (m_vmmaps model) g nZ = true := Hpl
  unfold grant_ok_na
  rw [hu]
  have h1 : decide (g % page_size = 0) = true := by
    rw [decide_eq_true_eq]; exact Hal
  have h2 : decide (0 < g) = true := by
    rw [decide_eq_true_eq]; exact Hg0
  have h3 : decide (g + nZ ≤ alloc_ceiling) = true := by
    rw [decide_eq_true_eq]; exact Hc
  rw [h1, h2, h3, Hfree', Hpl']
  rfl

/-- `refuse_ok`: the REFUSED child (`a0 := -ENOMEM`, `pc+4`,
    model unchanged) is a checker state — only the register file changed, so
    only `co_regs` is rebuilt. -/
theorem refuse_ok (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok SEGS A LIMIT SINV argH FS0 E (refuse cs)
      (regupd R (Z_to_bv 5 (10 : Int)) (errno_ret ENOMEM)) FULL model := by
  have Hv : edenot E (.ELit ENOMEM_RET) = errno_ret ENOMEM := by
    show Z_to_bv 64 ENOMEM_RET = errno_ret ENOMEM
    rw [errno_ret_ENOMEM]
    rfl
  refine
  { co_regs := ?_
    co_log := ?_
    co_know := HC.co_know
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
    co_abytes := HC.co_abytes
    co_minv := HC.co_minv
    co_zero := HC.co_zero
    co_sinv := HC.co_sinv }
  · exact regs_ok_set_n E cs.a_ss.s_regs R 10 (.ELit ENOMEM_RET) (errno_ret ENOMEM)
      HC.co_regs ⟨by omega, by omega⟩ Hv
  · rfl

/-- `refuse_cont`: the refused continuation of a two-child
    statement, at the original valuation.  `HKA` supplies the continuation of
    the refused child; `v_addi_pc` turns its `pc + 4` back into the `v_addi`
    the machine state is built at. -/
theorem refuse_cont (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (cs : acs) (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (TA : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hp0 : 0 ≤ pc cs) (Hp4 : pc cs + 4 < 2 ^ 64)
    (HKA : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA) :
    srealizes SEGS (mkCfg (mkst (regupd R (Z_to_bv 5 (10 : Int)) (errno_ret ENOMEM))
      (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA := by
  have h1 := HKA E (regupd R (Z_to_bv 5 (10 : Int)) (errno_ret ENOMEM)) FULL model
    ⟨env_agree_refl' nx0 E, env_agree_refl' (nxt cs) E⟩
    (refuse_ok SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model HC) rfl
  unfold cfg_of at h1
  rw [refuse_pc] at h1
  rw [← v_addi_pc (pc cs) Hp0 Hp4] at h1
  exact h1


/-! ## 12. `Section Slice` -/

theorem sl_bounds (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL') :
    0 < bv_unsigned (edenot E m.am_len) ∧ bv_unsigned (edenot E m.am_base) % 4096 = 0 ∧
      bv_unsigned (edenot E m.am_len) % 4096 = 0 ∧
      A.img_hi ≤ bv_unsigned (edenot E m.am_base) ∧
      bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ CEIL := by
  obtain ⟨B1, B2, B3, B4, B5⟩ := SH.sh_C.co_bounds (amap_den E m)
    (maps_match_In E cs.a_maps _ m SH.sh_C.co_maps SH.sh_m SH.sh_nf)
  dsimp only [amap_den, Prod.fst, Prod.snd] at B1 B2 B3 B4 B5
  exact ⟨B1, B2, B3, B4, B5⟩

theorem sl_lohi (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL') :
    A.img_hi ≤ bv_unsigned addr ∧
      bv_unsigned addr + nZ ≤ CEIL ∧
      bv_unsigned addr < bv_unsigned addr + nZ ∧
      bv_unsigned addr + nZ ≤ 2 ^ 64 ∧
      bv_unsigned addr % 4096 = 0 ∧
      (bv_unsigned addr + nZ) % 4096 = 0 := by
  obtain ⟨B1, B2, B3, B4, B5⟩ :=
    sl_bounds SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  have hin1 := SH.sh_in1
  have hin2 := SH.sh_in2
  have hpos := SH.sh_pos
  have hC : CEIL < 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_, ?_, SH.sh_al, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · rw [Int.add_emod, SH.sh_al, SH.sh_nal]
    decide

theorem sl_in_maps (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (m_vmmaps model).vm_maps = true := by
  have hin1 := SH.sh_in1
  have hin2 := SH.sh_in2
  refine in_ivs_maps_match E cs.a_maps _ m (bv_unsigned x) SH.sh_C.co_maps SH.sh_m SH.sh_nf ?_
  constructor <;> omega

theorem sl_wf' (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL') :
    model_ivs_wf model' := by
  obtain ⟨W1, W2, W3, Wsp⟩ := SH.sh_C.co_wf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    sl_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  have hiv : iv_wf (addr, n) := by
    have h4 : bv_unsigned addr + bv_unsigned n ≤ 2 ^ 64 := by rw [SH.sh_Un]; exact L4
    simpa only [iv_wf, B, S, Prod.fst, Prod.snd, bv_unsigned] using h4
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by
    rw [SH.sh_Un]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [SH.sh_post.sp_maps]
    exact W1
  · rw [SH.sh_post.sp_noacc]
    cases h : sl_nn s
    · simp only [h, Bool.false_eq_true, ite_false, List.nil_append]
      exact maps_subtract_wf _ _ _ W2 hlf
    · simp only [h, ite_true, List.cons_append, List.nil_append]
      exact ivs_wf_app _ _ (ivs_wf_cons _ _ hiv ivs_wf_nil) (maps_subtract_wf _ _ _ W2 hlf)
  · rw [SH.sh_post.sp_lazy]
    cases s
    · exact maps_subtract_wf _ _ _ W3 hlf
    · exact ivs_wf_cons _ _ hiv (maps_subtract_wf _ _ _ W3 hlf)
    · exact maps_subtract_wf _ _ _ W3 hlf
    · exact W3
  · unfold init_sp_ok at *
    rw [SH.sh_post.sp_isp]
    exact Wsp

theorem sl_noacc_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_noaccess
      = in_ivs (bv_unsigned x) (m_vmmaps model).vm_noaccess := by
  obtain ⟨W1, W2, W3, _⟩ := SH.sh_C.co_wf
  have hpos := SH.sh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
  have hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x := by
    rcases Hx with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [SH.sh_Un]; exact h)
  have hrng : in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (bv_unsigned x) = false := by
    unfold in_rng
    rcases hx with h | h
    · rw [decide_eq_false (by omega : ¬ (bv_unsigned addr ≤ bv_unsigned x)), Bool.false_and]
    · rw [decide_eq_false (by omega : ¬ (bv_unsigned x < bv_unsigned addr + bv_unsigned n)),
        Bool.and_false]
  have hcov : covered [(addr, n)] (bv_unsigned x) = false := by
    simpa only [covered, List.any_cons, List.any_nil, Bool.or_false, in_iv, B, S, Prod.fst,
      Prod.snd, bv_unsigned] using hrng
  rw [SH.sh_post.sp_noacc, in_ivs_app]
  simp only [in_ivs_covered]
  rw [covered_maps_subtract ((m_vmmaps model).vm_noaccess) (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) W2 hlf (bv_unsigned x), hrng]
  simp only [Bool.not_false, Bool.and_true]
  cases h : sl_nn s
  · simp only [h, Bool.false_eq_true, ite_false, List.nil_append, covered, List.any_nil,
      Bool.false_or]
  · simp only [h, ite_true, List.cons_append, List.nil_append, hcov, Bool.false_or]

theorem sl_noacc_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_noaccess = sl_nn s := by
  obtain ⟨W1, W2, W3, _⟩ := SH.sh_C.co_wf
  have hpos := SH.sh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
  have hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + bv_unsigned n :=
    ⟨Hx.1, by rw [SH.sh_Un]; exact Hx.2⟩
  have hrng : in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (bv_unsigned x) = true := by
    simp only [in_rng, decide_eq_true_eq, Bool.and_eq_true]
    exact hx
  have hcov : covered [(addr, n)] (bv_unsigned x) = true := by
    simpa only [covered, List.any_cons, List.any_nil, Bool.or_false, in_iv, B, S, Prod.fst,
      Prod.snd, bv_unsigned] using hrng
  rw [SH.sh_post.sp_noacc, in_ivs_app]
  simp only [in_ivs_covered]
  rw [covered_maps_subtract ((m_vmmaps model).vm_noaccess) (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) W2 hlf (bv_unsigned x), hrng]
  simp only [Bool.not_true, Bool.and_false, Bool.or_false]
  cases h : sl_nn s
  · simp only [h, Bool.false_eq_true, ite_false, List.nil_append, covered, List.any_nil]
  · simp only [h, ite_true, List.cons_append, List.nil_append, hcov]

theorem sl_lazy_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    page_in_ranges (page_base x) (m_vm_lazy model')
      = page_in_ranges (page_base x) (m_vm_lazy model) := by
  obtain ⟨W1, W2, W3, _⟩ := SH.sh_C.co_wf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    sl_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  have hpos := SH.sh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
  have hp : bv_unsigned (page_base x) + page_size ≤ bv_unsigned addr ∨
      bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (page_base x) := by
    have h := page_of_byte_out_aligned x (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 Hx
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [SH.sh_Un]; exact h)
  rw [SH.sh_post.sp_lazy]
  cases s
  · exact page_in_ranges_subtract_out _ _ _ _ W3 hlf hp
  · rw [page_in_ranges_cons_out _ _ _ _ hp (by rw [SH.sh_Un]; omega)]
    exact page_in_ranges_subtract_out _ _ _ _ W3 hlf hp
  · exact page_in_ranges_subtract_out _ _ _ _ W3 hlf hp
  · rfl

theorem sl_lazy_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    page_in_ranges (page_base x) (m_vm_lazy model')
      = (match s with
          | .SlM => page_in_ranges (page_base x) (m_vm_lazy model)
          | .SlF => true
          | _ => false) := by
  obtain ⟨W1, W2, W3, _⟩ := SH.sh_C.co_wf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    sl_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  obtain ⟨P1, P2⟩ :=
    page_of_byte_in_aligned x (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 Hx
  have hp2 : bv_unsigned (page_base x) < bv_unsigned addr + bv_unsigned n := by
    rw [SH.sh_Un]; omega
  have h2 : bv_unsigned (page_base x) + page_size ≤ bv_unsigned addr + bv_unsigned n := by
    show bv_unsigned (page_base x) + 4096 ≤ bv_unsigned addr + bv_unsigned n
    rw [SH.sh_Un]
    exact P2
  rw [SH.sh_post.sp_lazy]
  cases s
  · exact page_in_ranges_subtract_in _ _ _ _ W3 ⟨P1, hp2⟩
  · exact page_in_ranges_cons_in _ _ _ _ P1 h2
  · exact page_in_ranges_subtract_in _ _ _ _ W3 ⟨P1, hp2⟩
  · rfl

theorem sl_vis_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (cs1 : acs) (x : word) (Hv : cs1.a_vis = cs.a_vis)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    vis A E cs1 model' x = vis A E cs model x := by
  have h1 := sl_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH x Hx
  have h2 := sl_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH x Hx
  have h3 := in_allow_ext A E cs cs1 Hv
  simp only [vis, SH.sh_post.sp_maps, h1, h2, h3]

theorem sl_MR_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (cs1 : acs) (x : word) (Hv : cs1.a_vis = cs.a_vis)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    Mr A argH E cs1 model' FULL' x = Mr A argH E cs model FULL x := by
  have h1 := sl_vis_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH cs1 x Hv Hx
  have hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x := by
    rcases Hx with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [SH.sh_Un]; exact h)
  have h2 : FULL' x = FULL x := SH.sh_mem.1 x hx
  /- The two guards differ only by `h1`, which is applied to the BOOL in
     its own step: `simp` rewriting it inside the `ite` leaves that
     `ite`'s `Decidable` instance at the old spelling and the goal stops
     type-checking.  Each `ite` then gets its own guard fact, and each is
     peeled with `ite_eq_left`/`ite_eq_right` rather than `rw [ite_eq_left]`,
     which does not find the occurrence in this goal. -/
  have hg : (argH E x || !vis A E cs1 model' x) = (argH E x || !vis A E cs model x) := by
    rw [h1]
  simp only [Mr, mrestrict, hid]
  by_cases hc : (argH E x || !vis A E cs1 model' x) = true
  · have hc' : (argH E x || !vis A E cs model x) = true := by
      rw [← hg]; exact hc
    refine (ite_eq_left hc).trans ?_
    exact (ite_eq_left hc').symm
  · have hc' : ¬ ((argH E x || !vis A E cs model x) = true) := by
      rw [← hg]; exact hc
    refine (ite_eq_right hc).trans ?_
    exact h2.trans (ite_eq_right hc').symm

theorem sl_vis_in_E (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (Hs : s = .SlE) (cs1 : acs) (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    vis A E cs1 model' x = true := by
  cases s
  case SlE =>
    have h1 := sl_in_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlE m addr n nZ
      model' FULL' SH x Hx
    have h2 := sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlE m addr n nZ
      model' FULL' SH x Hx
    have h3 := sl_lazy_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlE m addr n nZ
      model' FULL' SH x Hx
    simp only [vis, SH.sh_post.sp_maps, h1, h2, h3, sl_nn, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.true_or, Bool.false_and, Bool.and_true, Bool.or_true, Bool.or_false]
  case SlF => exact absurd Hs (by decide)
  case SlG => exact absurd Hs (by decide)
  case SlM => exact absurd Hs (by decide)

theorem sl_vis_in_G (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (Hs : s = .SlG) (cs1 : acs) (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ)
    (Ha : argH E x = false) :
    vis A E cs1 model' x = false := by
  cases s
  case SlG =>
    obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
      sl_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlG m addr n nZ model'
        FULL' SH
    have hh : in_hull A (bv_unsigned x) = false := by
      simp only [in_hull]
      rw [decide_eq_false (by omega : ¬ (bv_unsigned x < A.img_hi)), Bool.and_false]
    have hc : decide (CEIL ≤ bv_unsigned x) = false :=
      decide_eq_false (by omega : ¬ (CEIL ≤ bv_unsigned x))
    have h1 := sl_in_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlG m addr n nZ
      model' FULL' SH x Hx
    have h2 := sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlG m addr n nZ
      model' FULL' SH x Hx
    simp only [vis, SH.sh_post.sp_maps, h1, h2, hh, hc, sl_nn, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.true_or, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_true,
      Bool.or_false, Bool.or_self]
  case SlE => exact absurd Hs (by decide)
  case SlF => exact absurd Hs (by decide)
  case SlM => exact absurd Hs (by decide)

theorem sl_vis_in_F (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (Hs : s = .SlF) (cs1 : acs) (x : word) (Hv : cs1.a_vis = cs.a_vis)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    vis A E cs1 model' x = vis A E cs model x := by
  cases s
  case SlF =>
    have hin1 := SH.sh_in1
    have hin2 : bv_unsigned addr + bv_unsigned n
        ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
      rw [SH.sh_Un]; exact SH.sh_in2
    have hx2 : bv_unsigned x < bv_unsigned addr + bv_unsigned n := by
      rw [SH.sh_Un]; exact Hx.2
    obtain ⟨K1, K2⟩ := SH.sh_C.co_kinds m SH.sh_m (SH.sh_F Hs) x ⟨by omega, by omega⟩
    have h1 := sl_in_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlF m addr n nZ
      model' FULL' SH x Hx
    have h2 := sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlF m addr n nZ
      model' FULL' SH x Hx
    have h3 := sl_lazy_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlF m addr n nZ
      model' FULL' SH x Hx
    have h4 := in_allow_ext A E cs cs1 Hv
    simp only [vis, SH.sh_post.sp_maps, h1, h2, h3, h4, K1, K2, sl_nn, Bool.not_false,
      Bool.not_true, Bool.true_and, Bool.true_or, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.or_true, Bool.or_false, Bool.or_self]
  case SlE => exact absurd Hs (by decide)
  case SlG => exact absurd Hs (by decide)
  case SlM => exact absurd Hs (by decide)

theorem page_base_aligned (p : word) (Hp : bv_unsigned p % 4096 = 0) : page_base p = p :=
  page_base_aligned' p Hp

theorem sl_eager (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL') :
    eager_used model' ≤ eager_used model + (if sl_charge s then nZ else 0) := by
  obtain ⟨W1, W2, W3, _⟩ := SH.sh_C.co_wf
  have hwf' := sl_wf' SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH
  have hpos := SH.sh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
  rw [eager_used_sem model' hwf', eager_used_sem model SH.sh_C.co_wf, SH.sh_post.sp_maps]
  let na := (m_vmmaps model).vm_noaccess
  let lz := m_vm_lazy model
  let maps := (m_vmmaps model).vm_maps
  change sum_count (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) maps
    ≤ sum_count (fun x => !(covered (na ++ lz) x)) maps + (if sl_charge s then nZ else 0)
  have CHall : sum_count (fun x =>
      in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x && sl_charge s) maps
      ≤ (if sl_charge s then nZ else 0) := by
    have SEPS := SH.sh_C.co_seps
    have HIN := maps_match_In E cs.a_maps _ m SH.sh_C.co_maps SH.sh_m SH.sh_nf
    have hin2 : bv_unsigned addr + bv_unsigned n
        ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
      rw [SH.sh_Un]; exact SH.sh_in2
    cases hch : sl_charge s
    · simp only [Bool.false_eq_true, ite_false]
      have hzero : sum_count (fun x =>
          in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x && false) maps = 0 := by
        rw [sum_count_ext _ (fun _ => false) _ (fun x => Bool.and_false _)]
        induction maps with
        | nil => simp [sum_count]
        | cons q t ih => simp [sum_count, iv_count, zcount_const_false, ih]
      rw [hzero]
      omega
    · simp only [ite_true, Bool.and_true]
      have OV := overlap_sum_contained maps (edenot E m.am_base) (edenot E m.am_len)
        (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) SEPS HIN SH.sh_in1 hin2 hlf
      have h2 : bv_unsigned addr + bv_unsigned n - bv_unsigned addr = nZ := by
        rw [SH.sh_Un]; omega
      rw [h2] at OV
      simpa only [overlap_sum] using OV
  cases s
  case SlE =>
    have hna' : (m_vmmaps model').vm_noaccess
        = maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_noacc
      simpa only [sl_nn, Bool.false_eq_true, ite_false, List.nil_append] using h
    have hlz' : m_vm_lazy model'
        = maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_lazy
      simpa only using h
    have MONO : sum_count (fun x =>
        !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) maps
        ≤ sum_count (fun x => !(covered (na ++ lz) x)
            || in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) maps := by
      apply sum_count_mono
      intro x hx
      rw [hna', hlz', covered_app] at hx
      rw [covered_maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
          W2 hlf x,
        covered_maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
          W3 hlf x] at hx
      rw [covered_app]
      rw [not_or_or_both (covered na x) (covered lz x)
        (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x)]
      exact hx
    have OR := sum_count_or_le (fun x => !(covered (na ++ lz) x))
      (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) maps
    have CH : sum_count (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) maps
        ≤ nZ := by
      have h := CHall
      simpa only [sl_charge, Bool.and_true, Bool.false_eq_true, ite_true] using h
    simp only [sl_charge, Bool.false_eq_true, ite_true]
    omega
  case SlF =>
    have hna' : (m_vmmaps model').vm_noaccess
        = maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_noacc
      simpa only [sl_nn, Bool.false_eq_true, ite_false, List.nil_append] using h
    have hlz' : m_vm_lazy model'
        = (addr, n) :: maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_lazy
      simpa only using h
    have hcons : ∀ x : Int, covered ((addr, n) :: maps_subtract lz (bv_unsigned addr)
        (bv_unsigned addr + bv_unsigned n)) x
        = (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x
          || (covered lz x && !(in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x))) := by
      intro x
      rw [show covered ((addr, n) :: maps_subtract lz (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) x
          = (in_iv (addr, n) x || covered (maps_subtract lz (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n)) x) from rfl]
      rw [show in_iv (addr, n) x
          = in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x from by
        simp only [in_iv, B, S, Prod.fst, Prod.snd, bv_unsigned]]
      rw [covered_maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W3 hlf x]
    have MONO : sum_count (fun x =>
        !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) maps
        ≤ sum_count (fun x => !(covered (na ++ lz) x)) maps := by
      apply sum_count_mono
      intro x hx
      rw [hna', hlz', covered_app] at hx
      rw [covered_maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
          W2 hlf x, hcons x] at hx
      rw [covered_app]
      exact (by
        decide : ∀ p q r : Bool, (!((p && !r) || (r || (q && !r)))) = true →
          Bool.not (p || q) = true) (covered na x) (covered lz x)
        (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) hx
    simp only [sl_charge, Bool.false_eq_true, ite_false, Int.add_zero]
    omega
  case SlG =>
    have hna' : (m_vmmaps model').vm_noaccess
        = ([(addr, n)] : List (word × word))
          ++ maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_noacc
      simpa only [sl_nn, ite_true] using h
    have hlz' : m_vm_lazy model'
        = maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_lazy
      simpa only using h
    have hcov1 : ∀ x : Int, covered [(addr, n)] x
        = in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x := by
      intro x
      simp only [covered, List.any_cons, List.any_nil, Bool.or_false, in_iv, B, S, Prod.fst,
        Prod.snd, bv_unsigned]
    have MONO : sum_count (fun x =>
        !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) maps
        ≤ sum_count (fun x => !(covered (na ++ lz) x)) maps := by
      apply sum_count_mono
      intro x hx
      rw [hna', hlz', covered_app, covered_app] at hx
      rw [hcov1 x,
        covered_maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W2 hlf x,
        covered_maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
          W3 hlf x] at hx
      rw [covered_app]
      exact (by
        decide : ∀ p q r : Bool, (!((r || (p && !r)) || (q && !r))) = true →
          Bool.not (p || q) = true) (covered na x) (covered lz x)
        (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) hx
    simp only [sl_charge, Bool.false_eq_true, ite_false, Int.add_zero]
    omega
  case SlM =>
    have hna' : (m_vmmaps model').vm_noaccess
        = maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      have h := SH.sh_post.sp_noacc
      simpa only [sl_nn, Bool.false_eq_true, ite_false, List.nil_append] using h
    have hlz' : m_vm_lazy model' = lz := by
      have h := SH.sh_post.sp_lazy
      simpa only using h
    have MONO : sum_count (fun x =>
        !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x)) maps
        ≤ sum_count (fun x => !(covered (na ++ lz) x)
            || in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) maps := by
      apply sum_count_mono
      intro x hx
      rw [hna', hlz', covered_app] at hx
      rw [covered_maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
        W2 hlf x] at hx
      rw [covered_app]
      exact not_or_or_left (covered na x) (covered lz x)
        (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) hx
    have OR := sum_count_or_le (fun x => !(covered (na ++ lz) x))
      (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) maps
    have CH : sum_count (in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) maps
        ≤ nZ := by
      have h := CHall
      simpa only [sl_charge, Bool.and_true, Bool.false_eq_true, ite_true] using h
    simp only [sl_charge, Bool.false_eq_true, ite_true]
    omega


/-- the slice child's ledger (`Section Slice`'s successor state, the
    `a_maps` field). -/
def slMaps (cs : acs) (s : slarm) (m : amap) : List amap :=
  match s with
  | .SlF => cs.a_maps
  | _ => rekind cs.a_maps m

theorem slice_cs1_ok (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (s : slarm) (m : amap) (addr n : word) (nZ : Int) (model' : Model)
    (FULL' : word → Option byte)
    (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL')
    (sr' : List expr) (R' : BvMap word) (k' : List kentry) (p : Int) (nx : Nat) (nhi : Int)
    (Hregs : regs_ok E sr' R')
    (Hknow : know_ok SEGS E (Mr A argH E cs model' FULL') k')
    (Hnhi : nZ ≤ nhi)
    (Hbudget : sl_charge s = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT) :
    cs_ok SEGS A LIMIT SINV argH FS0 E
      (ACS (mk_ss p sr' k' nx) (slMaps cs s m)
        cs.a_totsz cs.a_ylo
        (if sl_charge s then cs.a_eager + nhi else cs.a_eager)
        cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset) R' FULL' model' := by
  obtain ⟨Xregs, Xlog, Xknow, Xhalt, Xfds, Xfs, Xtid, Xres, Xlimit, Xmaps, Xholes,
    Xseps, Xwf, Xbounds, Xlazyb, Xnasub, Xnone, Xkinds, Xtotsz, Xsplit, Xbrk, Xsbrk,
    Xeager, Xabytes, Xminv, Xzero, Xsinv⟩ := SH.sh_C
  obtain ⟨N1, N2, N3, N4, N5⟩ := Xminv
  obtain ⟨W1, W2, W3, _⟩ := Xwf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    sl_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  obtain ⟨B1, B2, B3, B4, B5⟩ :=
    sl_bounds SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model' FULL' SH
  have hwf' := sl_wf' SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH
  have EG := sl_eager SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
    FULL' SH
  have hpos := SH.sh_pos
  have hUn := SH.sh_Un
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
  have hin1 := SH.sh_in1
  have hin2 : bv_unsigned addr + bv_unsigned n
      ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
    rw [SH.sh_Un]; exact SH.sh_in2
  have SEPS := Xseps
  have DISJ : ∀ m', m' ∈ cs.a_maps → is_fog m' = false → m ≠ m' →
      iv_disjoint (amap_den E m) (amap_den E m') := by
    intro m' hm' hnf' hne
    exact maps_match_disjoint E cs.a_maps _ m m' Xmaps SEPS SH.sh_m hm' SH.sh_nf hnf' hne
  have DISJ' : ∀ m', m' ∈ cs.a_maps → is_fog m' = false → m ≠ m' →
      bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len) ≤ bv_unsigned addr ∨
      bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (edenot E m'.am_base) := by
    intro m' hm' hnf' hne
    have hd := DISJ m' hm' hnf' hne
    unfold iv_disjoint at hd
    dsimp only [amap_den, Prod.fst, Prod.snd] at hd
    rcases hd with hd | hd
    · exact Or.inr (Int.le_trans hin2 hd)
    · exact Or.inl (Int.le_trans hd hin1)
  have KNF : ∀ m', m'.am_kind = .KNONE ∨ m'.am_kind = .KNONELAZY ∨ m'.am_kind = .KRWLAZY →
      is_fog m' = false := by
    intro m' hk
    rcases hk with hk | hk | hk <;> rw [is_fog, hk] <;> rfl
  have NONE : ∀ m', m' ∈ cs.a_maps → m ≠ m' →
      (m'.am_kind = .KNONE ∨ m'.am_kind = .KNONELAZY) →
      amap_den E m' ∈ (m_vmmaps model').vm_noaccess := by
    intro m' hm' hne hk
    rw [SH.sh_post.sp_noacc, List.mem_append]
    right
    have hnf' : is_fog m' = false := by
      rcases hk with hk | hk
      · exact KNF m' (Or.inl hk)
      · exact KNF m' (Or.inr (Or.inl hk))
    have hX := Xnone m' hm' hk
    obtain ⟨Bm1, _⟩ := Xbounds (amap_den E m') (maps_match_In E cs.a_maps _ m' Xmaps hm' hnf')
    dsimp only [amap_den, Prod.fst, Prod.snd] at Bm1
    have hd : bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len)
        ≤ bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (edenot E m'.am_base) :=
      DISJ' m' hm' hnf' hne
    have hlt : bv_unsigned addr < bv_unsigned addr + bv_unsigned n := by rw [SH.sh_Un]; omega
    exact maps_subtract_keeps _ _ _ _ _ hlt Bm1 (by simpa only [amap_den] using hX) hd
  have KINDS : ∀ m', m' ∈ cs.a_maps → m'.am_kind = .KRWLAZY →
      ∀ x : word, bv_unsigned (edenot E m'.am_base) ≤ bv_unsigned x ∧
        bv_unsigned x < bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len) →
        in_ivs (bv_unsigned x) (m_vmmaps model').vm_noaccess = false ∧
        page_in_ranges (page_base x) (m_vm_lazy model') = true := by
    intro m' hm' hk x hx
    obtain ⟨K1, K2⟩ := Xkinds m' hm' hk x hx
    by_cases h1 : bv_unsigned x < bv_unsigned addr
    · rw [sl_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
          FULL' SH x (Or.inl h1),
        sl_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
          FULL' SH x (Or.inl h1)]
      exact ⟨K1, K2⟩
    · by_cases h2 : bv_unsigned x < bv_unsigned addr + nZ
      · have hge : bv_unsigned addr ≤ bv_unsigned x := by omega
        have hmm : m = m' := by
          by_cases he : amap_eqb m m' = true
          · exact amap_eqb_eq he
          · exfalso
            have hne : m ≠ m' := by
              intro h
              rw [h, amap_eqb_refl] at he
              exact absurd he (by simp)
            have hnf' : is_fog m' = false := by rw [is_fog, hk]; rfl
            have hd := DISJ' m' hm' hnf' hne
            omega
        have hk' : m.am_kind = .KRWLAZY := by rw [hmm]; exact hk
        have hx2 : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ :=
          ⟨hge, h2⟩
        cases s
        · exact absurd hk' (SH.sh_nF (by decide))
        · rw [sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlF m addr n nZ
              model' FULL' SH x hx2,
            sl_lazy_in SEGS A LIMIT SINV argH FS0 E cs R FULL model slarm.SlF m addr n nZ
              model' FULL' SH x hx2]
          exact ⟨rfl, rfl⟩
        · exact absurd hk' (SH.sh_nF (by decide))
        · exact absurd hk' (SH.sh_nF (by decide))
      · have hge2 : bv_unsigned addr + nZ ≤ bv_unsigned x := by omega
        rw [sl_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
            FULL' SH x (Or.inr hge2),
          sl_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
            FULL' SH x (Or.inr hge2)]
        exact ⟨K1, K2⟩
  have RK : maps_match E (rekind cs.a_maps m) (m_vmmaps model).vm_maps := by
    unfold rekind
    refine maps_match_rekind E cs.a_maps _ _ ?_ Xmaps
    intro m0
    by_cases he : amap_eqb m0 m = true
    · have h0 : m0 = m := amap_eqb_eq he
      rw [ite_eq_left he]
      refine ⟨rfl, rfl, ?_⟩
      show is_fog (AM m0.am_base m0.am_len .KRW) = is_fog m0
      rw [h0]
      rw [is_fog, SH.sh_nf]
      rfl
    · rw [ite_eq_right he]
      exact ⟨rfl, rfl, rfl⟩
  have SUB : ∀ q ∈ maps_subtract (m_vm_lazy model) (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n),
      A.img_hi ≤ bv_unsigned q.1 ∧ bv_unsigned q.1 + bv_unsigned q.2 ≤ CEIL := by
    intro q hq
    obtain ⟨r, hr, R1, R2, _⟩ := maps_subtract_pieces (m_vm_lazy model) (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) q W3 hq
    obtain ⟨Y1, Y2⟩ := Xlazyb r hr
    exact ⟨Int.le_trans Y1 R1, Int.le_trans R2 Y2⟩
  let cs1 : acs := ACS (mk_ss p sr' k' nx) (slMaps cs s m)
    cs.a_totsz cs.a_ylo (if sl_charge s then cs.a_eager + nhi else cs.a_eager)
    cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
  change cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R' FULL' model'
  have Hmaps : cs1.a_maps = slMaps cs s m := rfl
  have Heager : cs1.a_eager
      = (if sl_charge s then cs.a_eager + nhi else cs.a_eager) := rfl
  have Htotsz : cs1.a_totsz = cs.a_totsz := rfl
  have Hab : cs1.a_abytes = cs.a_abytes := rfl
  have Hvis : cs1.a_vis = cs.a_vis := rfl
  have Hkn : kn cs1 = k' := rfl
  have Hmr : Mr A argH E cs1 model' FULL' = Mr A argH E cs model' FULL' := rfl
  have hAb : allowA A E cs1 = allowA A E cs := rfl
  have HIDOUT : ∀ x : word,
      bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x →
      hid A argH E cs1 model' x = hid A argH E cs model x := by
    intro x hx
    have hv := sl_vis_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
      FULL' SH cs1 x Hvis hx
    simp only [hid, hv]
  have mat_out : ∀ q, q ∈ List.filter (page_outside_range (bv_unsigned addr)
        (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) →
      bv_unsigned q < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned q := by
    intro q hq
    have h := (List.mem_filter.mp hq).2
    simp only [page_outside_range, Bool.not_eq_true', Bool.and_eq_false_iff] at h
    rcases h with h | h
    · left
      rw [decide_eq_false_iff_not] at h
      simp only [bv_unsigned] at h ⊢
      omega
    · right
      rw [decide_eq_false_iff_not] at h
      simp only [bv_unsigned] at h ⊢
      omega
  have pageBase_out : s ≠ .SlM → ∀ q, q ∈ m_vm_materialized model' →
      bv_unsigned (page_base q) + page_size ≤ bv_unsigned addr ∨
      bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (page_base q) := by
    intro hs q hq
    cases s
    case SlE =>
      rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
          SH.sh_post.sp_mat] at hq
      have h := page_of_byte_out_aligned q (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 (by
        rcases mat_out q hq with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← SH.sh_Un]; exact h))
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [SH.sh_Un]; exact h)
    case SlF =>
      rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
          SH.sh_post.sp_mat] at hq
      have h := page_of_byte_out_aligned q (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 (by
        rcases mat_out q hq with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← SH.sh_Un]; exact h))
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [SH.sh_Un]; exact h)
    case SlG =>
      rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
          SH.sh_post.sp_mat] at hq
      have h := page_of_byte_out_aligned q (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 (by
        rcases mat_out q hq with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← SH.sh_Un]; exact h))
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [SH.sh_Un]; exact h)
    case SlM => exact absurd rfl hs
  refine
  { co_regs := Hregs
    co_log := rfl
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
    co_wf := hwf'
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
  · rw [Hmr, Hkn]
    exact Hknow
  · rw [SH.sh_post.sp_halted]
    exact Xhalt
  · unfold fds_ok at *
    rw [SH.sh_post.sp_fds, SH.sh_post.sp_fs]
    exact Xfds
  · rw [SH.sh_post.sp_fs]
    exact Xfs
  · rw [SH.sh_post.sp_tid]
    exact Xtid
  · rw [SH.sh_post.sp_res]
    exact Xres
  · rw [SH.sh_post.sp_limit]
    exact Xlimit
  · rw [SH.sh_post.sp_maps]
    cases s
    · exact RK
    · exact Xmaps
    · exact RK
    · exact RK
  · intro m0 hm0
    cases s
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0]
        intro hh
        have hf : is_hole (AM m.am_base m.am_len .KRW) = false := by
          show mkind_eqb mkind.KRW mkind.KHOLE = false
          rfl
        rw [hf] at hh
        exact Bool.noConfusion hh
      · rw [hm0, SH.sh_post.sp_res, SH.sh_post.sp_maps]
        exact Xholes m1 hm1
    · rw [SH.sh_post.sp_res, SH.sh_post.sp_maps]
      exact Xholes m0 hm0
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0]
        intro hh
        have hf : is_hole (AM m.am_base m.am_len .KRW) = false := by
          show mkind_eqb mkind.KRW mkind.KHOLE = false
          rfl
        rw [hf] at hh
        exact Bool.noConfusion hh
      · rw [hm0, SH.sh_post.sp_res, SH.sh_post.sp_maps]
        exact Xholes m1 hm1
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0]
        intro hh
        have hf : is_hole (AM m.am_base m.am_len .KRW) = false := by
          show mkind_eqb mkind.KRW mkind.KHOLE = false
          rfl
        rw [hf] at hh
        exact Bool.noConfusion hh
      · rw [hm0, SH.sh_post.sp_res, SH.sh_post.sp_maps]
        exact Xholes m1 hm1
  · rw [SH.sh_post.sp_maps]
    exact Xseps
  · rw [SH.sh_post.sp_maps]
    exact Xbounds
  · rw [SH.sh_post.sp_lazy]
    cases s
    · exact SUB
    · intro iv hiv
      rw [List.mem_cons] at hiv
      rcases hiv with rfl | hiv
      · exact ⟨L1, by rw [SH.sh_Un]; exact L2⟩
      · exact SUB iv hiv
    · exact SUB
    · exact Xlazyb
  · intro z hz
    rw [SH.sh_post.sp_maps]
    have key : ∀ l : List (word × word), ivs_wf l → in_ivs z
        (maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) = true →
        in_ivs z l = true := by
      intro l hlw hl
      rw [in_ivs_covered] at hl ⊢
      rw [covered_maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
        hlw hlf z] at hl
      rw [Bool.and_eq_true] at hl
      exact hl.1
    rw [SH.sh_post.sp_noacc, in_ivs_app] at hz
    rw [Bool.or_eq_true] at hz
    rcases hz with hz | hz
    · cases h : sl_nn s
      · rw [h] at hz
        simp only [Bool.false_eq_true, ite_false] at hz
        rw [show in_ivs z ([] : List (word × word)) = false from rfl] at hz
        exact Bool.noConfusion hz
      · rw [h] at hz
        simp only [ite_true] at hz
        rw [in_ivs_cons] at hz
        rw [Bool.or_eq_true] at hz
        rcases hz with hz | hz
        · rw [Bool.and_eq_true] at hz
          have h1 : bv_unsigned addr ≤ z := by
            simpa only [decide_eq_true_eq] using hz.1
          have h2 : z < bv_unsigned addr + bv_unsigned n := by
            simpa only [decide_eq_true_eq] using hz.2
          exact in_ivs_maps_match E cs.a_maps _ m z Xmaps SH.sh_m SH.sh_nf
            ⟨by omega, by omega⟩
        · rw [show in_ivs z ([] : List (word × word)) = false from rfl] at hz
          exact Bool.noConfusion hz
    · exact Xnasub z (key _ W2 hz)
  · intro m0 hm0 hk
    cases s
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        rcases hk with hk | hk
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONE); decide)
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONELAZY); decide)
      · rw [hm0] at hk ⊢
        exact NONE m1 hm1 (fun h => hne h.symm) hk
    · refine NONE m0 hm0 ?_ hk
      intro h
      rw [← h, SH.sh_F rfl] at hk
      rcases hk with hk | hk
      · exact absurd hk (by show ¬ (mkind.KRWLAZY = mkind.KNONE); decide)
      · exact absurd hk (by show ¬ (mkind.KRWLAZY = mkind.KNONELAZY); decide)
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        rcases hk with hk | hk
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONE); decide)
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONELAZY); decide)
      · rw [hm0] at hk ⊢
        exact NONE m1 hm1 (fun h => hne h.symm) hk
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        rcases hk with hk | hk
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONE); decide)
        · exact absurd hk (by show ¬ (mkind.KRW = mkind.KNONELAZY); decide)
      · rw [hm0] at hk ⊢
        exact NONE m1 hm1 (fun h => hne h.symm) hk
  · intro m0 hm0 hk x hx
    cases s
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        exact absurd hk (by show ¬ (mkind.KRW = mkind.KRWLAZY); decide)
      · rw [hm0] at hk hx
        exact KINDS m1 hm1 hk x hx
    · exact KINDS m0 hm0 hk x hx
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        exact absurd hk (by show ¬ (mkind.KRW = mkind.KRWLAZY); decide)
      · rw [hm0] at hk hx
        exact KINDS m1 hm1 hk x hx
    · obtain ⟨m1, hm1, hcase⟩ := in_rekind cs.a_maps m m0 hm0
      rcases hcase with ⟨hm1m, hm0⟩ | ⟨hne, hm0⟩
      · rw [hm0] at hk
        exact absurd hk (by show ¬ (mkind.KRW = mkind.KRWLAZY); decide)
      · rw [hm0] at hk hx
        exact KINDS m1 hm1 hk x hx
  · rw [Htotsz, SH.sh_post.sp_res, SH.sh_post.sp_maps]
    exact Xtotsz
  · obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := Xsplit
    exact ⟨Y, HY1, HY2, by rw [SH.sh_post.sp_mbase]; exact HY3,
      by rw [SH.sh_post.sp_res, SH.sh_post.sp_maps]; exact HY4⟩
  · rw [SH.sh_post.sp_brk]
    exact Xbrk
  · rw [SH.sh_post.sp_brk, SH.sh_post.sp_sbrk]
    exact Xsbrk
  · rw [Heager]
    cases hc : sl_charge s
    · rw [hc] at EG
      rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at EG
      rw [ite_eq_right (by decide : ¬((false : Bool) = true))]
      simp only [Int.add_zero] at EG
      omega
    · rw [hc] at EG
      rw [ite_eq_left (rfl : (true : Bool) = true)] at EG
      rw [ite_eq_left (rfl : (true : Bool) = true)]
      have hb := Hbudget hc
      omega
  · rw [Hab]
    exact Xabytes
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases s
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat]
        exact List.Sublist.nodup List.filter_sublist N1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat]
        exact List.Sublist.nodup List.filter_sublist N1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat]
        exact List.Sublist.nodup List.filter_sublist N1
      · rw [show m_vm_materialized model' = m_vm_materialized model from SH.sh_post.sp_mat]
        exact N1
    · intro q hq
      cases s
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N2 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N2 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N2 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = m_vm_materialized model from SH.sh_post.sp_mat] at hq
        exact N2 q hq
    · intro q hq
      rw [hAb]
      cases s
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N3 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N3 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
            (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from SH.sh_post.sp_mat] at hq
        exact N3 q (List.mem_filter.mp hq).1
      · rw [show m_vm_materialized model' = m_vm_materialized model from SH.sh_post.sp_mat] at hq
        exact N3 q hq
    · intro q hq
      cases s
      case SlE =>
        have hpb := pageBase_out (by decide) q hq
        rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
            SH.sh_post.sp_mat] at hq
        have hq0 : q ∈ m_vm_materialized model := (List.mem_filter.mp hq).1
        rw [page_base_aligned q (N2 q hq0)] at hpb
        rw [show m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n) from SH.sh_post.sp_lazy]
        rw [page_in_ranges_subtract_out _ _ _ _ W3 hlf hpb]
        exact N4 q hq0
      case SlF =>
        have hpb := pageBase_out (by decide) q hq
        rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
            SH.sh_post.sp_mat] at hq
        have hq0 : q ∈ m_vm_materialized model := (List.mem_filter.mp hq).1
        rw [page_base_aligned q (N2 q hq0)] at hpb
        rw [show m_vm_lazy model' = (addr, n) :: maps_subtract (m_vm_lazy model)
              (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) from SH.sh_post.sp_lazy]
        rw [page_in_ranges_cons_out q addr n _ hpb (by rw [SH.sh_Un]; omega)]
        rw [page_in_ranges_subtract_out _ _ _ _ W3 hlf hpb]
        exact N4 q hq0
      case SlG =>
        have hpb := pageBase_out (by decide) q hq
        rw [show m_vm_materialized model' = List.filter (page_outside_range (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model) from
            SH.sh_post.sp_mat] at hq
        have hq0 : q ∈ m_vm_materialized model := (List.mem_filter.mp hq).1
        rw [page_base_aligned q (N2 q hq0)] at hpb
        rw [show m_vm_lazy model' = maps_subtract (m_vm_lazy model) (bv_unsigned addr)
              (bv_unsigned addr + bv_unsigned n) from SH.sh_post.sp_lazy]
        rw [page_in_ranges_subtract_out _ _ _ _ W3 hlf hpb]
        exact N4 q hq0
      case SlM =>
        rw [show m_vm_materialized model' = m_vm_materialized model from SH.sh_post.sp_mat] at hq
        rw [show m_vm_lazy model' = m_vm_lazy model from SH.sh_post.sp_lazy]
        exact N4 q hq
    · rw [hAb]
      rw [Xlimit] at N5
      rw [SH.sh_post.sp_limit, Xlimit]
      cases hc : sl_charge s
      · rw [hc] at EG
        rw [ite_eq_right (by decide : ¬((false : Bool) = true))] at EG
        simp only [Int.add_zero] at EG
        omega
      · rw [hc] at EG
        rw [ite_eq_left (rfl : (true : Bool) = true)] at EG
        have hb := Hbudget hc
        omega
  · intro x Hh Hmx Hna Hlz Hgh
    by_cases h1 : bv_unsigned x < bv_unsigned addr
    · rw [show FULL' x = FULL x from SH.sh_mem.1 x (Or.inl h1)]
      have hha : hid A argH E cs model x = true := by
        rw [← HIDOUT x (Or.inl h1)]; exact Hh
      exact Xzero x hha (by rw [SH.sh_post.sp_maps] at Hmx; exact Hmx)
        (by rw [sl_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ
              model' FULL' SH x (Or.inl h1)] at Hna; exact Hna)
        (by rw [sl_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ
              model' FULL' SH x (Or.inl h1)] at Hlz; exact Hlz) Hgh
    · by_cases h2 : bv_unsigned x < bv_unsigned addr + nZ
      · have hx2 : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ :=
          ⟨by omega, h2⟩
        have hx2' : bv_unsigned addr ≤ bv_unsigned x ∧
            bv_unsigned x < bv_unsigned addr + bv_unsigned n :=
          ⟨hx2.1, by rw [SH.sh_Un]; exact hx2.2⟩
        rw [show FULL' x = (if sl_nn s then none else some (Z_to_bv 8 0)) from
          SH.sh_mem.2 x hx2']
        rw [sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ model'
          FULL' SH x hx2] at Hna
        cases h : sl_nn s
        · rw [h] at Hna
          rfl
        · rw [h] at Hna
          exact absurd Hna (by simp)
      · have hge2 : bv_unsigned addr + nZ ≤ bv_unsigned x := by omega
        rw [show FULL' x = FULL x from SH.sh_mem.1 x (Or.inr (by
          rw [SH.sh_Un]; exact hge2))]
        have hha : hid A argH E cs model x = true := by
          rw [← HIDOUT x (Or.inr hge2)]; exact Hh
        exact Xzero x hha (by rw [SH.sh_post.sp_maps] at Hmx; exact Hmx)
          (by rw [sl_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ
                model' FULL' SH x (Or.inr hge2)] at Hna; exact Hna)
          (by rw [sl_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model s m addr n nZ
                model' FULL' SH x (Or.inr hge2)] at Hlz; exact Hlz) Hgh
  · refine SINV_frame E FULL FULL' ?_ Xsinv
    intro x Hx
    exact SH.sh_mem.1 x (Or.inr (by
      have hc : bv_unsigned addr + bv_unsigned n ≤ CEIL := by rw [SH.sh_Un]; exact L2
      exact Int.le_trans hc (argH_high E x Hx)))

/-! ## 13. `Section Destroyed` -/

theorem d_bounds (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL') :
    0 < bv_unsigned (edenot E m.am_len) ∧ bv_unsigned (edenot E m.am_base) % 4096 = 0 ∧
      bv_unsigned (edenot E m.am_len) % 4096 = 0 ∧
      A.img_hi ≤ bv_unsigned (edenot E m.am_base) ∧
      bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ CEIL := by
  obtain ⟨B1, B2, B3, B4, B5⟩ := DH.dh_C.co_bounds (amap_den E m)
    (maps_match_In E cs.a_maps _ m DH.dh_C.co_maps DH.dh_m DH.dh_nf)
  dsimp only [amap_den, Prod.fst, Prod.snd] at B1 B2 B3 B4 B5
  exact ⟨B1, B2, B3, B4, B5⟩

theorem d_lohi (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL') :
    A.img_hi ≤ bv_unsigned addr ∧
      bv_unsigned addr + nZ ≤ CEIL ∧
      bv_unsigned addr < bv_unsigned addr + nZ ∧
      bv_unsigned addr + nZ ≤ 2 ^ 64 ∧
      bv_unsigned addr % 4096 = 0 ∧
      (bv_unsigned addr + nZ) % 4096 = 0 := by
  obtain ⟨B1, B2, B3, B4, B5⟩ :=
    d_bounds SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have hin1 := DH.dh_in1
  have hin2 := DH.dh_in2
  have hpos := DH.dh_pos
  have hC : CEIL < 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_, ?_, DH.dh_al, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · rw [Int.add_emod, DH.dh_al, DH.dh_nal]
    decide

theorem d_in_maps (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (m_vmmaps model).vm_maps = true := by
  have hin1 := DH.dh_in1
  have hin2 := DH.dh_in2
  refine in_ivs_maps_match E cs.a_maps _ m (bv_unsigned x) DH.dh_C.co_maps DH.dh_m DH.dh_nf ?_
  constructor <;> omega

theorem d_wf' (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL') :
    model_ivs_wf model' := by
  obtain ⟨W1, W2, W3, Wsp⟩ := DH.dh_C.co_wf
  have hpos := DH.dh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [DH.dh_post.dp_maps]
    exact maps_subtract_wf _ _ _ W1 hlf
  · rw [DH.dh_post.dp_noacc]
    exact maps_subtract_wf _ _ _ W2 hlf
  · rw [DH.dh_post.dp_lazy]
    exact maps_subtract_wf _ _ _ W3 hlf
  · unfold init_sp_ok at *
    rw [DH.dh_post.dp_isp]
    exact Wsp

theorem d_sub_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (l : List (word × word)) (x : word) (W : ivs_wf l)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    in_ivs (bv_unsigned x) (maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      = in_ivs (bv_unsigned x) l := by
  have hpos := DH.dh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  have hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x := by
    rcases Hx with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [DH.dh_Un]; exact h)
  have hrng : in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (bv_unsigned x) = false := by
    unfold in_rng
    rcases hx with h | h
    · rw [decide_eq_false (by omega : ¬ (bv_unsigned addr ≤ bv_unsigned x)), Bool.false_and]
    · rw [decide_eq_false (by omega : ¬ (bv_unsigned x < bv_unsigned addr + bv_unsigned n)),
        Bool.and_false]
  rw [in_ivs_covered, in_ivs_covered,
    covered_maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W hlf
      (bv_unsigned x), hrng]
  exact Bool.and_true _

theorem d_sub_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (l : List (word × word)) (x : word) (W : ivs_wf l)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
      = false := by
  have hpos := DH.dh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  have hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + bv_unsigned n :=
    ⟨Hx.1, by rw [DH.dh_Un]; exact Hx.2⟩
  have hrng : in_rng (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (bv_unsigned x) = true := by
    simp only [in_rng, decide_eq_true_eq, Bool.and_eq_true]
    exact hx
  rw [in_ivs_covered,
    covered_maps_subtract l (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W hlf
      (bv_unsigned x), hrng]
  exact Bool.and_false _

theorem d_maps_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_maps
      = in_ivs (bv_unsigned x) (m_vmmaps model).vm_maps := by
  rw [DH.dh_post.dp_maps]
  exact d_sub_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
    _ x DH.dh_C.co_wf.1 Hx

theorem d_maps_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_maps = false := by
  rw [DH.dh_post.dp_maps]
  exact d_sub_in SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
    _ x DH.dh_C.co_wf.1 Hx

theorem d_noacc_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_noaccess
      = in_ivs (bv_unsigned x) (m_vmmaps model).vm_noaccess := by
  rw [DH.dh_post.dp_noacc]
  exact d_sub_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
    _ x DH.dh_C.co_wf.2.1 Hx

theorem d_noacc_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    in_ivs (bv_unsigned x) (m_vmmaps model').vm_noaccess = false := by
  rw [DH.dh_post.dp_noacc]
  exact d_sub_in SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
    _ x DH.dh_C.co_wf.2.1 Hx

theorem d_lazy_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (x : word)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    page_in_ranges (page_base x) (m_vm_lazy model')
      = page_in_ranges (page_base x) (m_vm_lazy model) := by
  obtain ⟨_, _, W3, _⟩ := DH.dh_C.co_wf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    d_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have hpos := DH.dh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  have hp : bv_unsigned (page_base x) + page_size ≤ bv_unsigned addr ∨
      bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (page_base x) := by
    have h := page_of_byte_out_aligned x (bv_unsigned addr) (bv_unsigned addr + nZ) L5 L6 Hx
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [DH.dh_Un]; exact h)
  rw [DH.dh_post.dp_lazy]
  exact page_in_ranges_subtract_out _ _ _ _ W3 hlf hp

theorem d_vis_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (cs1 : acs) (x : word) (Hv : cs1.a_vis = cs.a_vis)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    vis A E cs1 model' x = vis A E cs model x := by
  have h1 := d_maps_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH x Hx
  have h2 := d_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH x Hx
  have h3 := d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH x Hx
  have h4 := in_allow_ext A E cs cs1 Hv
  simp only [vis, h1, h2, h3, h4]

theorem d_vis_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (cs1 : acs) (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    vis A E cs1 model' x = false := by
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    d_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have hh : in_hull A (bv_unsigned x) = false := by
    simp only [in_hull]
    rw [decide_eq_false (by omega : ¬ (bv_unsigned x < A.img_hi)), Bool.and_false]
  have hc : decide (CEIL ≤ bv_unsigned x) = false :=
    decide_eq_false (by omega : ¬ (CEIL ≤ bv_unsigned x))
  have h1 := d_maps_in SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH x Hx
  simp only [vis, h1, hh, hc, Bool.false_and, Bool.and_false, Bool.or_false]

theorem d_MR_out (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (cs1 : acs) (x : word) (Hv : cs1.a_vis = cs.a_vis)
    (Hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x) :
    Mr A argH E cs1 model' FULL' x = Mr A argH E cs model FULL x := by
  have h1 := d_vis_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH cs1 x Hv Hx
  have hx : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned x := by
    rcases Hx with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [DH.dh_Un]; exact h)
  have h2 : FULL' x = FULL x := DH.dh_mem.1 x hx
  /- The two guards differ only by `h1`, which is applied to the BOOL in
     its own step: `simp` rewriting it inside the `ite` leaves that
     `ite`'s `Decidable` instance at the old spelling and the goal stops
     type-checking.  Each `ite` then gets its own guard fact, and each is
     peeled with `ite_eq_left`/`ite_eq_right` rather than `rw [ite_eq_left]`,
     which does not find the occurrence in this goal. -/
  have hg : (argH E x || !vis A E cs1 model' x) = (argH E x || !vis A E cs model x) := by
    rw [h1]
  simp only [Mr, mrestrict, hid]
  by_cases hc : (argH E x || !vis A E cs1 model' x) = true
  · have hc' : (argH E x || !vis A E cs model x) = true := by
      rw [← hg]; exact hc
    refine (ite_eq_left hc).trans ?_
    exact (ite_eq_left hc').symm
  · have hc' : ¬ ((argH E x || !vis A E cs model x) = true) := by
      rw [← hg]; exact hc
    refine (ite_eq_right hc).trans ?_
    exact h2.trans (ite_eq_right hc').symm

theorem d_MR_in (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (cs1 : acs) (x : word)
    (Hx : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ) :
    Mr A argH E cs1 model' FULL' x = none := by
  have h1 := d_vis_in SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH cs1 x Hx
  simp only [Mr, mrestrict, hid, h1, Bool.not_false, Bool.or_true]
  rfl

theorem d_eager (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL') :
    eager_used model' ≤ eager_used model := by
  obtain ⟨W1, W2, W3, _⟩ := DH.dh_C.co_wf
  have hwf' := d_wf' SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
    FULL' DH
  have hpos := DH.dh_pos
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  rw [eager_used_sem model' hwf', eager_used_sem model DH.dh_C.co_wf, DH.dh_post.dp_maps]
  let na := (m_vmmaps model).vm_noaccess
  let lz := m_vm_lazy model
  let maps := (m_vmmaps model).vm_maps
  change sum_count (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x))
      (maps_subtract maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    ≤ sum_count (fun x => !(covered (na ++ lz) x)) maps
  have hna : (m_vmmaps model').vm_noaccess
      = maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) :=
    DH.dh_post.dp_noacc
  have hlz : m_vm_lazy model'
      = maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) :=
    DH.dh_post.dp_lazy
  have hsum := (maps_subtract_sem maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    W1 hlf).2.1 (fun x => !(covered ((m_vmmaps model').vm_noaccess ++ m_vm_lazy model') x))
  rw [hsum]
  apply sum_count_mono
  intro x hx
  rw [Bool.and_eq_true] at hx
  obtain ⟨hx, hr⟩ := hx
  rw [Bool.not_eq_true'] at hx hr
  rw [hna, hlz, covered_app] at hx
  rw [covered_maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W2 hlf x,
    covered_maps_subtract lz (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) W3 hlf x]
    at hx
  rw [hr] at hx
  simp only [Bool.not_false, Bool.and_true] at hx
  rw [covered_app, hx]
  rfl

/-- The optional hole token `hp` = `[]` or `[AM ha hn KHOLE]` denoting exactly
    the destroyed range. -/
def hole_prefix_ok (E : env) (addr : word) (nZ : Int) (hp : List amap) : Prop :=
  hp = [] ∨ ∃ ha hn, hp = [AM ha hn .KHOLE] ∧ bv_unsigned (edenot E ha) = bv_unsigned addr ∧
    bv_unsigned (edenot E hn) = nZ

theorem dest_cs1_ok (SEGS : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (RES_hullH : RES_hull_def SEGS A)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (m : amap) (addr n : word) (nZ : Int) (model' : Model) (FULL' : word → Option byte)
    (DH : dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL')
    (sr' : List expr) (R' : BvMap word) (k' : List kentry) (p : Int) (nx : Nat)
    (pcs hp : List amap)
    (Hregs : regs_ok E sr' R')
    (Hknow : know_ok SEGS E (Mr A argH E cs model' FULL') k')
    (Hpcs : List.map (amap_den E) pcs
      = iv_subtract (edenot E m.am_base) (edenot E m.am_len)
          (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (Hkinds : ∀ pc ∈ pcs, pc.am_kind = m.am_kind)
    (Hhp : hole_prefix_ok E addr nZ hp) :
    cs_ok SEGS A LIMIT SINV argH FS0 E
      (ACS (mk_ss p sr' k' nx) (hp ++ replace_entry cs.a_maps m pcs)
        cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
      R' FULL' model' := by
  obtain ⟨Xregs, Xlog, Xknow, Xhalt, Xfds, Xfs, Xtid, Xres, Xlimit, Xmaps, Xholes,
    Xseps, Xwf, Xbounds, Xlazyb, Xnasub, Xnone, Xkinds, Xtotsz, Xsplit, Xbrk, Xsbrk,
    Xeager, Xabytes, Xminv, Xzero, Xsinv⟩ := DH.dh_C
  obtain ⟨N1, N2, N3, N4, N5⟩ := Xminv
  obtain ⟨W1, W2, W3, _⟩ := Xwf
  obtain ⟨L1, L2, L3, L4, L5, L6⟩ :=
    d_lohi SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  obtain ⟨B1, B2, B3, B4, B5⟩ :=
    d_bounds SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have hwf' := d_wf' SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have EG := d_eager SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model' FULL' DH
  have hpos := DH.dh_pos
  have hUn := DH.dh_Un
  have hlf : bv_unsigned addr ≤ bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  have hlt : bv_unsigned addr < bv_unsigned addr + bv_unsigned n := by rw [DH.dh_Un]; omega
  have hin1 := DH.dh_in1
  have hin2 : bv_unsigned addr + bv_unsigned n
      ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) := by
    rw [DH.dh_Un]; exact DH.dh_in2
  have SEPS := Xseps
  have DISJ : ∀ m', m' ∈ cs.a_maps → is_fog m' = false → m ≠ m' →
      iv_disjoint (amap_den E m) (amap_den E m') := by
    intro m' hm' hnf' hne
    exact maps_match_disjoint E cs.a_maps _ m m' Xmaps SEPS DH.dh_m hm' DH.dh_nf hnf' hne
  have DISJ' : ∀ m', m' ∈ cs.a_maps → is_fog m' = false → m ≠ m' →
      bv_unsigned (edenot E m'.am_base) + bv_unsigned (edenot E m'.am_len) ≤ bv_unsigned addr ∨
      bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (edenot E m'.am_base) := by
    intro m' hm' hnf' hne
    have hd := DISJ m' hm' hnf' hne
    unfold iv_disjoint at hd
    dsimp only [amap_den, Prod.fst, Prod.snd] at hd
    rcases hd with hd | hd
    · exact Or.inr (Int.le_trans hin2 hd)
    · exact Or.inl (Int.le_trans hd hin1)
  have KNF : ∀ m', m'.am_kind = .KNONE ∨ m'.am_kind = .KNONELAZY ∨ m'.am_kind = .KRWLAZY →
      is_fog m' = false := by
    intro m' hk
    rcases hk with hk | hk | hk <;> rw [is_fog, hk] <;> rfl
  have BND : ∀ m' ∈ cs.a_maps, is_fog m' = false →
      0 < bv_unsigned (edenot E m'.am_len) := by
    intro m' hm' hnf'
    obtain ⟨Bm1, _⟩ := Xbounds (amap_den E m') (maps_match_In E cs.a_maps _ m' Xmaps hm' hnf')
    dsimp only [amap_den, Prod.fst, Prod.snd] at Bm1
    exact Bm1
  have BNDl : ∀ iv ∈ (m_vmmaps model).vm_maps, 0 < bv_unsigned iv.2 := by
    intro iv hiv
    exact (Xbounds iv hiv).1
  have HPnone : ∀ m0 ∈ hp, (m0.am_kind = .KNONE ∨ m0.am_kind = .KNONELAZY) → False := by
    intro m0 hm0 hk
    rcases Hhp with rfl | ⟨ha, hn, rfl, _, _⟩
    · simp at hm0
    · rw [List.mem_singleton] at hm0
      rw [hm0] at hk
      rcases hk with hk | hk
      · exact absurd hk (by show ¬ (mkind.KHOLE = mkind.KNONE); decide)
      · exact absurd hk (by show ¬ (mkind.KHOLE = mkind.KNONELAZY); decide)
  have HPlazy : ∀ m0 ∈ hp, m0.am_kind = .KRWLAZY → False := by
    intro m0 hm0 hk
    rcases Hhp with rfl | ⟨ha, hn, rfl, _, _⟩
    · simp at hm0
    · rw [List.mem_singleton] at hm0
      rw [hm0] at hk
      exact absurd hk (by show ¬ (mkind.KHOLE = mkind.KRWLAZY); decide)
  have HPfog : ∀ m0 ∈ hp, is_fog m0 = true := by
    intro m0 hm0
    rcases Hhp with rfl | ⟨ha, hn, rfl, _, _⟩
    · simp at hm0
    · rw [List.mem_singleton] at hm0
      rw [hm0]
      show is_tok_kind mkind.KHOLE = true
      rfl
  have PCS : ∀ pc ∈ pcs,
      bv_unsigned (edenot E m.am_base) ≤ bv_unsigned (edenot E pc.am_base) ∧
      bv_unsigned (edenot E pc.am_base) + bv_unsigned (edenot E pc.am_len)
        ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ∧
      (bv_unsigned (edenot E pc.am_base) + bv_unsigned (edenot E pc.am_len) ≤ bv_unsigned addr ∨
       bv_unsigned addr + bv_unsigned n ≤ bv_unsigned (edenot E pc.am_base)) ∧
      amap_den E pc ∈ iv_subtract (edenot E m.am_base) (edenot E m.am_len)
        (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
    intro pc hpc
    have hin : amap_den E pc ∈ iv_subtract (edenot E m.am_base) (edenot E m.am_len)
        (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) := by
      rw [← Hpcs]
      exact List.mem_map.mpr ⟨pc, hpc, rfl⟩
    have hwfm : iv_wf (edenot E m.am_base, edenot E m.am_len) := by
      have h5 : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ 2 ^ 64 := by
        have hC : CEIL < 2 ^ 64 := by decide
        omega
      simpa only [iv_wf, B, S, Prod.fst, Prod.snd, bv_unsigned] using h5
    obtain ⟨P1, P2, P3⟩ :=
      iv_subtract_pieces (edenot E m.am_base) (edenot E m.am_len)
        (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (amap_den E pc) hwfm hin
    dsimp only [amap_den, Prod.fst, Prod.snd] at P1 P2 P3
    exact ⟨P1, P2, P3, hin⟩
  have MATout : ∀ q ∈ List.filter (page_outside_range (bv_unsigned addr)
        (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model),
      bv_unsigned q < bv_unsigned addr ∨ bv_unsigned addr + bv_unsigned n ≤ bv_unsigned q := by
    intro q hq
    have h := (List.mem_filter.mp hq).2
    simp only [page_outside_range, Bool.not_eq_true', Bool.and_eq_false_iff] at h
    rcases h with h | h
    · left
      rw [decide_eq_false_iff_not] at h
      simp only [bv_unsigned] at h ⊢
      omega
    · right
      rw [decide_eq_false_iff_not] at h
      simp only [bv_unsigned] at h ⊢
      omega
  have SUBL : ∀ iv ∈ ((m_vmmaps model).vm_reserved ++
        maps_subtract (m_vmmaps model).vm_maps (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)),
      ∃ r, r ∈ ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) ∧
        bv_unsigned r.1 ≤ bv_unsigned iv.1 ∧
        bv_unsigned iv.1 + bv_unsigned iv.2 ≤ bv_unsigned r.1 + bv_unsigned r.2 ∧
        (r ∈ (m_vmmaps model).vm_reserved ∨
          (bv_unsigned iv.1 + bv_unsigned iv.2 ≤ bv_unsigned addr ∨
           bv_unsigned addr + bv_unsigned n ≤ bv_unsigned iv.1)) := by
    intro iv hiv
    rw [List.mem_append] at hiv
    rcases hiv with hiv | hiv
    · exact ⟨iv, List.mem_append.mpr (Or.inl hiv), Int.le_refl _,
        Int.le_refl _, Or.inl hiv⟩
    · obtain ⟨r, hr, R1, R2, R3⟩ := maps_subtract_pieces (m_vmmaps model).vm_maps
        (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) iv W1 hiv
      exact ⟨r, List.mem_append.mpr (Or.inr hr), R1, R2, Or.inr R3⟩
  let cs1 : acs := ACS (mk_ss p sr' k' nx) (hp ++ replace_entry cs.a_maps m pcs)
    cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset
  change cs_ok SEGS A LIMIT SINV argH FS0 E cs1 R' FULL' model'
  have Hkn : kn cs1 = k' := rfl
  have Hmr : Mr A argH E cs1 model' FULL' = Mr A argH E cs model' FULL' := rfl
  have Hab : cs1.a_abytes = cs.a_abytes := rfl
  have HIDOUT : ∀ x : word,
      bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x →
      hid A argH E cs1 model' x = hid A argH E cs model x := by
    intro x hx
    have hv := d_vis_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
      FULL' DH cs1 x (by rfl) hx
    simp only [hid, hv]
  refine
  { co_regs := Hregs
    co_log := rfl
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
    co_wf := hwf'
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
    co_abytes := Hab ▸ Xabytes
    co_minv := ?_
    co_zero := ?_
    co_sinv := ?_ }
  · rw [Hmr, Hkn]
    exact Hknow
  · rw [DH.dh_post.dp_halted]
    exact Xhalt
  · unfold fds_ok at *
    rw [DH.dh_post.dp_fds, DH.dh_post.dp_fs]
    exact Xfds
  · rw [DH.dh_post.dp_fs]
    exact Xfs
  · rw [DH.dh_post.dp_tid]
    exact Xtid
  · rw [DH.dh_post.dp_res]
    exact Xres
  · rw [DH.dh_post.dp_limit]
    exact Xlimit
  · rw [DH.dh_post.dp_maps]
    refine maps_match_tok_prefix E hp (replace_entry cs.a_maps m pcs) _ HPfog ?_
    exact maps_match_subtract E cs.a_maps _ m pcs (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) Xmaps Xseps BNDl DH.dh_m DH.dh_nf hlt
      DH.dh_in1 hin2 Hpcs
      (fun pc hpc => by
        show is_tok_kind pc.am_kind = false
        rw [Hkinds pc hpc]
        exact DH.dh_nf)
  · intro m0 hm0
    rw [DH.dh_post.dp_res, DH.dh_post.dp_maps]
    rw [List.mem_append] at hm0
    rcases hm0 with hm0 | hm0
    · rcases Hhp with rfl | ⟨ha, hn, rfl, Hha, Hhn⟩
      · simp at hm0
      · rw [List.mem_singleton] at hm0
        rw [hm0]
        intro _
        have hbase : AsanPlanSound.uE E (AM ha hn .KHOLE).am_base = bv_unsigned addr := Hha
        have hlen : AsanPlanSound.uE E (AM ha hn .KHOLE).am_len = bv_unsigned n :=
          Hhn.trans DH.dh_Un.symm
        rw [hbase, hlen]
        constructor
        · intro iv hiv
          obtain ⟨r, hr, R1, R2, R3⟩ := SUBL iv hiv
          rcases R3 with hres | hout
          · rw [Xres] at hres
            obtain ⟨Z1, Z2⟩ := RES_hullH r hres
            exact Or.inl (Int.le_trans R2 (Int.le_trans Z2 L1))
          · rcases hout with hout | hout
            · exact Or.inl hout
            · exact Or.inr hout
        · obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := Xsplit
          have hm : amap_den E m ∈ ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps) :=
            List.mem_append.mpr (Or.inr (maps_match_In E cs.a_maps _ m Xmaps DH.dh_m DH.dh_nf))
          have h4 := HY4 (edenot E m.am_base) (edenot E m.am_len) hm
          rcases h4 with h4 | h4
          · exact Or.inl (by rw [← KHI_eq]; exact Int.le_trans hin2 h4)
          · exact Or.inr (Int.le_trans HY1 (Int.le_trans h4 hin1))
    · obtain ⟨Hin, Hne⟩ | ⟨_, Hpc⟩ := in_replace_entry cs.a_maps m pcs m0 hm0
      · intro hk
        obtain ⟨F1, F2⟩ := Xholes m0 Hin hk
        refine ⟨?_, ?_⟩
        · intro iv hiv
          obtain ⟨r, hr, R1, R2, _⟩ := SUBL iv hiv
          rcases F1 r hr with h | h
          · left
            exact Int.le_trans R2 h
          · right
            exact Int.le_trans h R1
        · exact F2
      · intro hk
        exfalso
        have hk' : m0.am_kind = m.am_kind := Hkinds m0 Hpc
        have hh : mkind_eqb m0.am_kind .KHOLE = true := hk
        rw [hk'] at hh
        have hfog : is_tok_kind m.am_kind = true := tok_of_hole _ hh
        have hnf := DH.dh_nf
        rw [is_fog, hfog] at hnf
        exact Bool.noConfusion hnf
  · rw [DH.dh_post.dp_maps]
    exact seps_maps_subtract _ _ _ Xseps W1 hlf
  · rw [DH.dh_post.dp_maps]
    exact maps_subtract_bounds (m_vmmaps model).vm_maps (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) A.img_hi CEIL DH.dh_al (by rw [DH.dh_Un]; exact L6)
      (by have hC : CEIL < 2 ^ 64 := (by decide); omega) Xbounds
  · rw [DH.dh_post.dp_lazy]
    intro q hq
    obtain ⟨r, hr, R1, R2, _⟩ := maps_subtract_pieces (m_vm_lazy model) (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) q W3 hq
    obtain ⟨Y1, Y2⟩ := Xlazyb r hr
    exact ⟨Int.le_trans Y1 R1, Int.le_trans R2 Y2⟩
  · intro z hz
    rw [DH.dh_post.dp_maps]
    rw [DH.dh_post.dp_noacc] at hz
    rw [in_ivs_covered] at hz ⊢
    rw [covered_maps_subtract (m_vmmaps model).vm_noaccess _ _ W2 hlf z] at hz
    rw [covered_maps_subtract (m_vmmaps model).vm_maps _ _ W1 hlf z]
    rw [Bool.and_eq_true] at hz
    rw [← in_ivs_covered] at hz ⊢
    rw [Xnasub z hz.1, hz.2]
    rfl
  · intro m0 hm0 hk
    rw [DH.dh_post.dp_noacc]
    rw [List.mem_append] at hm0
    rcases hm0 with hm0 | hm0
    · exact absurd hk (HPnone m0 hm0)
    · obtain ⟨Hin, Hne⟩ | ⟨_, Hpc⟩ := in_replace_entry cs.a_maps m pcs m0 hm0
      · have hnf' : is_fog m0 = false := by
          rcases hk with hk | hk
          · exact KNF m0 (Or.inl hk)
          · exact KNF m0 (Or.inr (Or.inl hk))
        have hX := Xnone m0 Hin hk
        obtain ⟨Bm1, _⟩ := Xbounds (amap_den E m0) (maps_match_In E cs.a_maps _ m0 Xmaps Hin hnf')
        dsimp only [amap_den, Prod.fst, Prod.snd] at Bm1
        have hd := DISJ' m0 Hin hnf' (fun h => Hne h.symm)
        exact maps_subtract_keeps _ _ _ _ _ hlt Bm1 (by simpa only [amap_den] using hX) hd
      · have hk' : m0.am_kind = m.am_kind := Hkinds m0 Hpc
        have hX := Xnone m DH.dh_m (by rw [← hk']; exact hk)
        obtain ⟨_, _, _, P4⟩ := PCS m0 Hpc
        exact maps_subtract_in_pieces (m_vmmaps model).vm_noaccess (edenot E m.am_base)
          (edenot E m.am_len) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
          (amap_den E m0) (by simpa only [amap_den] using hX) P4
  · intro m0 hm0 hk x hx
    rw [List.mem_append] at hm0
    rcases hm0 with hm0 | hm0
    · exact absurd hk (HPlazy m0 hm0)
    · obtain ⟨Hin, Hne⟩ | ⟨_, Hpc⟩ := in_replace_entry cs.a_maps m pcs m0 hm0
      · obtain ⟨K1, K2⟩ := Xkinds m0 Hin hk x hx
        have hnf' : is_fog m0 = false := KNF m0 (Or.inr (Or.inr hk))
        have hd := DISJ' m0 Hin hnf' (fun h => Hne h.symm)
        have hxout : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x := by
          rcases hd with hd | hd
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        rw [d_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
            FULL' DH x hxout,
          d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
            FULL' DH x hxout]
        exact ⟨K1, K2⟩
      · have hk' : m0.am_kind = m.am_kind := Hkinds m0 Hpc
        obtain ⟨P1, P2, P3, _⟩ := PCS m0 Hpc
        obtain ⟨K1, K2⟩ := Xkinds m DH.dh_m (by rw [← hk']; exact hk) x (by omega)
        have hxout : bv_unsigned x < bv_unsigned addr ∨ bv_unsigned addr + nZ ≤ bv_unsigned x := by
          rcases P3 with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        rw [d_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
            FULL' DH x hxout,
          d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
            FULL' DH x hxout]
        exact ⟨K1, K2⟩
  · rw [DH.dh_post.dp_res, DH.dh_post.dp_maps, sum_sizes_app]
    rw [sum_sizes_app] at Xtotsz
    have hle := sum_sizes_maps_subtract_le (m_vmmaps model).vm_maps (bv_unsigned addr)
      (bv_unsigned addr + bv_unsigned n) W1 hlf
    exact Int.le_trans (Int.add_le_add_left hle _) Xtotsz
  · obtain ⟨Y, HY1, HY2, HY3, HY4⟩ := Xsplit
    refine ⟨Y, HY1, HY2, ?_, ?_⟩
    · rw [DH.dh_post.dp_mbase]; exact HY3
    · rw [DH.dh_post.dp_res, DH.dh_post.dp_maps]
      obtain ⟨S1, S2⟩ := ledger_split_app_inv _ _ _ _ HY4
      exact ledger_split_app _ _ _ _ S1 (ledger_split_maps_subtract _ _ _ _ _ W1 S2)
  · rw [DH.dh_post.dp_brk]
    exact Xbrk
  · rw [DH.dh_post.dp_brk, DH.dh_post.dp_sbrk]
    exact Xsbrk
  · exact Int.le_trans EG Xeager
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [DH.dh_post.dp_mat]
      exact List.Sublist.nodup List.filter_sublist N1
    · intro q hq
      rw [DH.dh_post.dp_mat] at hq
      exact N2 q (List.mem_filter.mp hq).1
    · intro q hq
      rw [DH.dh_post.dp_mat] at hq
      exact N3 q (List.mem_filter.mp hq).1
    · intro q hq
      rw [DH.dh_post.dp_mat] at hq
      have hq0 : q ∈ m_vm_materialized model := (List.mem_filter.mp hq).1
      have hout := MATout q hq
      rw [← page_base_aligned' q (N2 q hq0)]
      rw [d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
        FULL' DH q (by
          rcases hout with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [← DH.dh_Un]; exact h))]
      rw [page_base_aligned' q (N2 q hq0)]
      exact N4 q hq0
    · have hAb' : allowA A E cs1 = allowA A E cs := rfl
      rw [hAb']
      rw [Xlimit] at N5
      rw [DH.dh_post.dp_limit, Xlimit]
      omega
  · intro x Hh Hmx Hna Hlz Hgh
    by_cases h1 : bv_unsigned x < bv_unsigned addr
    · rw [show FULL' x = FULL x from DH.dh_mem.1 x (Or.inl h1)]
      have hha : hid A argH E cs model x = true := by
        rw [← HIDOUT x (Or.inl h1)]; exact Hh
      exact Xzero x hha
        (by rw [d_maps_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
              model' FULL' DH x (Or.inl h1)] at Hmx
            exact Hmx)
        (by rw [d_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
              model' FULL' DH x (Or.inl h1)] at Hna; exact Hna)
        (by rw [d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
              model' FULL' DH x (Or.inl h1)] at Hlz; exact Hlz) Hgh
    · by_cases h2 : bv_unsigned x < bv_unsigned addr + nZ
      · have hx2 : bv_unsigned addr ≤ bv_unsigned x ∧ bv_unsigned x < bv_unsigned addr + nZ :=
          ⟨by omega, h2⟩
        have hx2' : bv_unsigned addr ≤ bv_unsigned x ∧
            bv_unsigned x < bv_unsigned addr + bv_unsigned n :=
          ⟨hx2.1, by rw [DH.dh_Un]; exact hx2.2⟩
        rw [show FULL' x = none from DH.dh_mem.2 x hx2']
        rw [d_maps_in SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ model'
          FULL' DH x hx2] at Hmx
        exact absurd Hmx (by simp)
      · have hge2 : bv_unsigned addr + nZ ≤ bv_unsigned x := by omega
        rw [show FULL' x = FULL x from DH.dh_mem.1 x (Or.inr (by
          rw [DH.dh_Un]; exact hge2))]
        have hha : hid A argH E cs model x = true := by
          rw [← HIDOUT x (Or.inr hge2)]; exact Hh
        exact Xzero x hha
          (by rw [d_maps_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
                model' FULL' DH x (Or.inr hge2)] at Hmx
              exact Hmx)
          (by rw [d_noacc_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
                model' FULL' DH x (Or.inr hge2)] at Hna; exact Hna)
          (by rw [d_lazy_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m addr n nZ
                model' FULL' DH x (Or.inr hge2)] at Hlz; exact Hlz) Hgh
  · refine SINV_frame E FULL FULL' ?_ Xsinv
    intro x Hx
    exact DH.dh_mem.1 x (Or.inr (by
      have hc : bv_unsigned addr + bv_unsigned n ≤ CEIL := by rw [DH.dh_Un]; exact L2
      exact Int.le_trans hc (argH_high E x Hx)))

/-!  The thirteen that the `DEFERRED` block used
  to record are the ones added by the final stretch: `gap_ok_sound`
  (:2159), `refuse_ok` (:2216), `refuse_cont` (:2227), `shadow_facts_new_ok`
  (:2322), `cs_ok_unhole` (:2463), `mmap_fixed_grant_cs1` (:2486),
  `mmap_fixed_old_facts` (:2547), `mmap_fixed_hole_facts` (:2573), the three
  `kn_rezero_*` knowledge lemmas (:3087, :3116, :3128), `vis_add_slice_ok`
  (:3150) and `slice_args` (:3198).
  Their section context is the standard parameter block of `AsanNodesIface` —
  `SEGS`, `A`, `nx0`, `LIMIT`, `SINV`, `argH`, `FS0` plus `SEGS_in_hull`,
  `RES_len`, `RES_hull`, `HULL_ok`, `SHADOW_ok`, `argH_high`, `argH_agree`,
  `SINV_frame`, `SINV_agree` — and, as everywhere else in this file, each of
  those hypotheses appears as a leading EXPLICIT argument of the declarations
  that actually use it (`gap_ok_sound` takes `RES_len`, `slice_args` takes
  `RES_hull`, `mmap_fixed_grant_cs1` / `vis_add_slice_ok` take `SHADOW_ok`,
  `argH_high` and the `SINV` frame, `mmap_fixed_old_facts` takes `RES_hull`,
  and the `kn_rezero_*` family takes nothing beyond its own hypotheses).
  NOTHING IS ABSENT.  Their `Let`-bound section variables are leading explicit
  parameters (or local `have`s) here; the one definition is
  `slMaps`, documented where it is introduced.
  - **A hypothesis whose type is a `know_ok` application can cost minutes of
    `whnf`.**  Passing the local `Hknew : know_ok … (if … then flatMap … else
    [])` *as an argument* to `grant_cs1_ok` (whose own `knew` is
    syntactically the same term) sends `isDefEq` into a `know_ok` /`ite` /
    `flatMap` comparison that did not finish in ten minutes.  What works is to
    pass the *tactic* form, which drives unification goal-first:
    `(by intro K HK; exact Hknew K HK)`.  The whole file then checks in ~6 s.
  - **`knew` must be spelled with `kd`, not `KRWLAZY`.**  `fixed_cs1`'s
    shadow list is `[AM (reg cs 10) ne kd]`; `shadow_facts_new_ok`'s
    statement hardcodes `KRWLAZY` (it is only ever used in that branch).  With
    the `if`'s condition stuck on the variable `kd`, the two are NOT defeq, so
    the final `exact` fails; state `knew` with `kd` and `subst kd` inside the
    `KRWLAZY` branch before calling `shadow_facts_new_ok`.
  - `gap_ok_sound` needs the product monotonicity
    `len * (nZ + 4095) ≤ cnt * (nhi + 4095)` by hand
    (`Int.mul_le_mul_of_nonneg_right` / `_left`): `omega` is linear and
    treats each product as an atom, so it cannot derive it.
  - `rw` cannot match `BitVec.ofInt 64 g` against `Z_to_bv 64 g` (different
    spellings of the same word), so `gap_ok_sound` states its `region_free` /
    `hint_placement_ok_b` facts in the goal's own spelling before rewriting.
  - the refused child changes ONLY the register file, so `refuse_ok` is a
    plain 27-field rebuild of `cs_ok` whose `co_regs` is
    `regs_ok_set_n … (.ELit ENOMEM_RET) (errno_ret ENOMEM)` with
    `edenot E (.ELit ENOMEM_RET) = errno_ret ENOMEM` from
    `errno_ret_ENOMEM` (`ENOMEM_RET = two64 - 12` is definitional).   - `refuse_cont` is then just `HKA` at the refused child, `unfold cfg_of`,
    `rw [refuse_pc]`, and `rw [← v_addi_pc (pc cs) Hp0 Hp4]` to turn the
    `pc + 4` back into the `v_addi` the machine state is built at.
  - **A `match` written in a theorem statement is generalised over the
    hypotheses.**  `slice_cs1_ok`'s successor state has
    `a_maps := match s with | .SlF => cs.a_maps | _ => rekind cs.a_maps m`, and
    a `match` on the section variable `s` is elaborated as
    `match s, SH, Hbudget with …` (every hypothesis whose type mentions `s`
    becomes an extra discriminant).  That form is not defeq to the plain
    `match`, so `change … cs1 …` and any `have h : … = match s with …` fail.
    The fix is the `def slMaps cs s m`, exactly as `mmEnv` /
    `mmBase` are devices of this kind.
  - **`cases s` early, `subst s` never.**  With `slice_hyps … s … / dest_hyps …
    s …` in context, `cases s` is fine (Lean reverts and reinstates the
    hypothesis), and the arm-specific facts must be *computed after* the
    split.  `subst s` (or `rw [Hs] at *`) instead rewrites inside the
    hypothesis and produces `match s, SH with …` terms that no longer reduce;
    `rw [SH.sh_Un] at h` then fails with "motive is not type correct" when `h`
    is a projection whose type is a dependent match (`sp_lazy`, `sp_mat`).
    Writing the arm's value as an explicit `have h : … = <concrete> from
    SH.sh_post.sp_lazy` works only *after* the split, where iota discharges it.
  - **`cases h : sl_charge s` substitutes in the goal but NOT in other
    hypotheses** (`sl_eager`'s `EG`, `co_eager`): follow it with
    `rw [h] at EG`.  And `if (false = true) then … else …` is not reduced by
    `simp only [Bool.false_eq_true, ite_false]` here; use
    `rw [ite_eq_right (by decide : ¬((false : Bool) = true))]` (and `ite_eq_left rfl`).
  - `rw [a, b, c] at h` requires **every** lemma in the list to match `h`, and
    `rw [in_ivs_covered]` rewrites only the first `in_ivs` occurrence
.
  - `Bool.or_eq_true` / `Bool.and_eq_true` are Prop *equalities*
    (`(a || b) = true) = (a = true ∨ b = true)`), so `rw` them into the
    hypothesis, not `.mp`.  `Bool.not_eq_true` is the `¬`-version; the `!`
    version is `Bool.not_eq_true'` (and `Bool.not_eq_false'`).
  - `List.mem_of_mem_filter` and `List.Nodup.filter` do not exist:
    `(List.mem_filter.mp h).1` and `List.Sublist.nodup List.filter_sublist h`.
  - In `co_minv` the goal's page is the ledger entry `q` itself
    (`MInv.minv_lazy : page_in_ranges p …`), not `page_base q`; the
    `page_base_aligned'` rewrites go *into* `d_lazy_out`'s hypothesis, and the
    `page_outside_range` membership is `!(lo ≤ q && q < hi)` — one `Bool` case
    split, no modular arithmetic.
  - `omega` does not unfold the local definition `cs1`: state the successor
    field equations (`rfl` `have`s) or finish with `Int.le_trans` instead of
    `omega` (`co_totsz`, `co_eager`).
-/
