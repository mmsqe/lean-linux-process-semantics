/-
  * Common.AxSymExec3B — the BLOCK-CONTEXT machinery for the AX2 executor.
  module `AX2B`.  Companion of `AxSymExec3` (read that file's header
  first: it records this tree's deviations — the 64-bit-window
  `zland`/`zlor`/`zlxor`, the `Nat`-keyed ptree, the irreducible
  `erange_fuel`, the structural-core splits and the extended driver
  names).
 Within one executor block
  (and within one plan-node call) the knowledge's FACT list is fixed, yet
  the reference functions re-derive everything from it on every call:
  `facts_of` re-filters, `sum_facts kn kn` re-digests all composite
  `KRange` facts inside every `lin_test_rel`, `find_range` scans the whole
  list for every atom of every `erange` query (with unary `nat` variable
  indices an `expr_eqb` miss between two variables costs `min(i,j)`
  steps).  `bctx` carries the list together with its digests, computed
  ONCE; the `..B` functions below are the reference functions with the
  context threaded through, each provably equal to its reference
  (`.._eqf` lemmas: `fooB (mkbc fk) = foo fk`), so results — and hence
  all certificates and soundness theorems — are unchanged.
  - `B2`  expression simplifiers (`mkSrlB` .. `amo_newvalB`) with `.._eqf`.
  - `B3`  `sym_readB` / `sym_stepB` / `know_lookupB` with `.._eqf`.
  - `B4`  the `kix` page index and `know_lookupABI` / `sym_stepBI`.
  - `B5`  the drivers `sym_execTXB` / `sym_execTXBI`.
  - `B6`  the prune layer (`prune_zfB` .. `prunepcB`).
  - `B7`  the vertical carry (`carryK` and its grouping machinery `gst`).
  - DONE  `B1`   the range index (`rindex`,
          `find_rangeI`, `find_rangeI_eq`), the block context (`bctx`,
          `mkbc0`, `mkbc`), the whole interval/alignment domain
          (`erange_fB` .. `sum_factsB`) and the facts layer
          (`lin_test_relB` .. `ranges_apart_pB`) with every `.._eqf0` /
          `.._eqf` lemma of that stretch.
  - DONE  `B2` (first half)  `coeffs_divkB`,
          `lin_lowbits_knB`, `lin_nowrap_lB`, `mkSrlB`, `lowbitsB`,
          `lsplit_divB`, `and_high_splitB`, `and_low_splitB`,
          `narrow_maskB`, `mkAnd0B`, `mkAndB`, `mkAndKB`, `or_disjointB`,
          `mkOrB` and their `.._eqf` lemmas.
  - DONE  `B2` (second half)  `conc_tryB`,
          `concretizeB`, `foldKB`, `lin_branchB`, `decide_branchB`,
          `mkSltB`, `mkAluK0B`, `mkAluKB`, `mkMdKB`, `zband32B`,
          `mkAluwK0B`, `mkAluwKB`, `extK0B`, `extKB`, `flat_scB`,
          `wr_coveredB`, `storeok_scB`, `conc_exprB`, `enum_branchB`,
          `to_saddrKB`, `amo_alignedbB`, `amo_newvalB`, with every `.._eqf`
          lemma (`conc_tryB_eqf` .. `amo_newvalB_eqf`).
  - DONE  `B3`  `log_lookupB`, `know_lookupA0B`,
          `know_lookupAB`, `sym_readB`, `sym_stepB`, `know_lookupB`, with
          `log_lookupB_eqf`, `know_lookupA0B_eqf`, `know_lookupAB_eqf`,
          `sym_readB_eqf`, `know_lookupB_eqf`, `sym_stepB_eq`.
  - DONE  `B4`  every definition and every proof.
          `gran` .. `sym_stepBI` as before, plus the whole equality chain:
          `gran_div` (definitional in this module — see the deviations),
          `gran_mono`, `gran_between`, `kx_aluop_eqb_refl` /
          `kx_mulop_eqb_refl` / `kx_expr_eqb_refl`, `rel_lit_same` /
          `rel_lit_other`, `is_lit0_eqb` / `expr_eqb_lit0_l` / `_r` /
          `is_lit0_true`, `know_lookupA0B_skip0` / `_skipf` / `_filter0` /
          `_filterf`, `filter_tagged_gt`, `kx_merge_nil_l` / `_nil_r` /
          `_cons_l` / `_cons_r` / `kx_merge_filters`, `kx_cand0_split` /
          `narrow_not_wide` / `kx_gkey_inj` / `kx_bucket_leaf` /
          `_add_same` / `_add_other` / `kx_add_bucket_step`,
          `kx_build_spec`, `kx_select_eq`, `know_lookupA0I_eq`,
          `know_lookupABI_eq`, `sym_readBI_eqf`, `sym_stepBI_eq`.
  - DONE  `B5`  every definition and every proof
          (`zf_coversB` .. `sym_stepXBI`, `sym_execTXB(_go)`,
          `sym_execTXBI(_go)`): `zf_coversB_eqf`, `kentry_overlayB_eqf`,
          `kentry_readableB_eqf`, `kn_readableB_eqf`, `kn_overlayB_eqf`,
          `x_dischargeableB_eq`, `x_filterB_eq`, `sym_stepXB_eq`, the
          `s_know` invariance (`sym_step_know`, `cap_rd_know`,
          `sym_stepX_know`, `sym_execTX_go_know`, `sym_execTX_know`) and the
          driver equalities `sym_execTXB_go_eq`, `sym_execTXB_eq`,
          `sym_stepXBI_eq`, `sym_execTXBI_go_eq`, `sym_execTXBI_eq`.
  - DONE  `B6`  the whole prune layer (`kcutB`,
          `kzero_cutB`, `kfill_cutB`, `kunk_cutB`, `prune_zfB`, `prune1pB`,
          `ranges_apart_pcB`, `prune1pcB`, `prunepcB`) with all nine
          `.._eqf` lemmas (`kcutB_eqf` .. `prunepcB_eqf`).
  - DONE  `B7` .  The HORIZONTAL carry (`carryB`,
          `carryB_eq`) with the whole fact-invariance chain it needs
          (`filter_nil_app`, `filter_if_single`,
          `filter_if_nofacts`, `kcut_nofacts`, `ktrim_nofacts`,
          `kword_cut_nofacts`, `prune_zf_nofacts`, `prune1p_facts`,
          `prune1pc_facts`, `prunepc_facts`, `carry_facts`), AND the whole
          VERTICAL carry: `g1`/`prune1p_nil`/`prunep_nil`, the `pk_res`/
          `pk_list`/`prune1pcK` fast path with `prune1pcK_eq`, the
          `AxSymExec3Sound` copies the vertical carry needs
          (`ranges_apart_pc_base_range`, `p_prune1pc_eq`, `p_br_cache_ok`,
          `p_br_lookup_ok`, `p_prunepc_eq`), the base interning (`bkey`,
          `binfo`/`BI`, `ntab`, `nt_empty`, `alookupE`, `nt_bucket`,
          `nt_add`, `intern`, `NTI`, with `nt_bucket_empty`, `NTI_empty`,
          `alookupE_Some`/`_None`, `nt_add_bucket`/`_next`/`_info`,
          `intern_ok`, `nt_same_eq`), the `stx` chains (`mk_stxs`, `obrB`,
          `g1cB`, `chain_slow`, `chainK`, `chainK2`, `entriesV`,
          `stores_part`, `carryV`, `carryK0`), the reference vertical form
          (`FM`, `chainRo`, `kw`, `SPRo`, `strip`, `SX_OK`,
          `flat_map_app'`, `FM_app`, `chainRo_snoc`/`_app`, `SPRo_snoc`,
          `carry_vertical`), and its equalities (`g1cB_eq`,
          `chain_slow_eq`, `chainK_eq`, `chainK2_eq`, `flat_map_flat_map`,
          `chain_slow_flat_map`, `flat_map_singleton_id`, `FM_nil`,
          `SX_OK_mono`, `mk_stxs_ok`, `Forall_SX_sp`/`_same`,
          `entriesV_eq`, `stores_part_eq`) down to the concluding
          `carryK0_eq`: `carryK0 (mkbc (facts_of kn)) log kn hints =
          carry log kn hints`.
  - DONE  `B7` (second half)  the whole GROUPED
          vertical carry.  The trie map (`pt_map`, `pt_get_map`), the entry
          descriptor (`kdescr`), the pass-1 info/state (`einfo`/`EI`,
          `gval`, `gtab`, `gst`/`GST`, `gst_empty`, `gkey`, `ggroup`,
          `bnd_add`, `scan_entries`), the group membership test and the
          per-group filtered store list (`sx_m1`, `verdict`, `mk_fl`,
          `gfl`, `mk_gl`, `obr_eqb`, `inb`), the grouped chains (`chainKF`,
          `entriesG`, `carryG`) and the entry point `carryK`, with every
          lemma of the block (`zlit64_idem`, `kdescr_kbase`/
          `_None_kbase`, `prune1pcK_keep_based`/`_keep_img`, `EINF`,
          `EINF_mono`, `scan_entries_ok`, `chainKF_eq`, `verdict_inb_num`,
          `entriesG_eq`, `carryG_eq`) down to `carryK_eq`:
          `carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints` —
          the grouped counterpart of `carryK0_eq`.
 None is absent.  The three whose presence this file used to
  merely CLAIM, in prose, while they were not declared — `gran_div`,
  `sym_execTXB_go_eq`, `sym_execTXB_eq` — are now declared: `gran_div` by
  `rfl` (Section B4), the two driver equalities by induction on `fuel`
  (Section B5).  Re-run the diff before trusting this paragraph.
 `NTI`/`SX_OK` and every
    "for all members" side condition are stated as `∀ x ∈ l, P x`
    (this core has no `List.Forall`).
 NO proof inspects that encoding:
    `inb` re-checks membership, so any grouping is sound, and the group
    lemmas only use `gkey`'s value through `pt_get`/`pt_set`.
  - four local helper lemmas stand in for `cbn`-plus-`lia` steps of the
    grouped block: `kdescr_len_ELit` (a `kdescr` byte length is literal
    only for a literal length expression), `ranges_apart_pcB_lit_true` /
    `ranges_apart_pB_lit_true` (the numeric apartness test fires, the
    `prune1pcK_keep_*` core) and `append_cancel_right_iff` (right
    cancellation for `List.append`, which this core has only as an
    implication).
  on the proof idiom for the `.._eqf` lemmas.  In Lean the same shape works as
  `funext ...; simp only [fooB, foo, <earlier .._eqf lemmas>, ...]`
  followed by `try (with_unfolding_all exact rfl)`.
  THE CLOSER THAT MATTERS: a RECURSIVE definition's compiled matcher is
  `[implicit_reducible]`, so plain `rfl` canNOT see through
  `fooB.match_1` vs `foo.match_1` (they are the same function but distinct
  constants).  `with_unfolding_all exact rfl` (transparency `.all`) closes
  every such residual goal — it made the whole of `B2`/`B3`/`B6`'s
  `.._eqf` set go through.  Use it as the last resort in every `.._eqf`
  proof (it is fast: the whole file typechecks in ~10 s).  Only where two
  DIFFERENT functions must be shown pointwise equal (e.g. `List.filter`
  with different lambdas) does it need help from the `.._eqf` lemmas
  inside the lambda first.
  Where the older idiom still applies: the equation compiler gives `fooB` its own
  `match_N` auxiliary constants, so the residual goal after the rewrites is
  equal only up to conversion, which `exact rfl` discharges.  Where a
  definition's fall-through arm is a `_` pattern the unconditional
  `fooB.eq_def` equation is used once (inside `rw`, never in a simp set, to
  avoid unfolding the recursion).
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AxSymExec3

namespace LinuxSem.Common.AxSymExec3B

open LinuxSem.Riscv hiding zlog2
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec hiding zland zlor zlxor
open LinuxSem.Common.AxSymExec3

local instance axsymexec3b_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! ## B1: block context, range index, facts layer -/

/-! ### Syntactic equalities decided by the boolean tests

    (copies of `AxSymExec3Sound`'s lemmas, needed here for the index lemma) -/

theorem p_aluop_eqb_eq {a b : AluOp} (h : aluop_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp [aluop_eqb] at h ⊢

theorem p_mulop_eqb_eq {a b : MulOp} (h : mulop_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp [mulop_eqb] at h ⊢

theorem p_expr_eqb_eq (x : expr) : ∀ y, expr_eqb x y = true → x = y := by
  induction x with
  | ELit a =>
      intro y h
      cases y <;> simp [expr_eqb] at h
      exact congrArg expr.ELit h
  | EVar a =>
      intro y h
      cases y <;> simp [expr_eqb] at h
      exact congrArg expr.EVar h
  | EAlu o a b iha ihb =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨ho, ha⟩, hb⟩ := h
      show expr.EAlu o a b = expr.EAlu _ _ _
      rw [p_aluop_eqb_eq ho, iha _ ha, ihb _ hb]
  | EAluw o a b iha ihb =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨ho, ha⟩, hb⟩ := h
      show expr.EAluw o a b = expr.EAluw _ _ _
      rw [p_aluop_eqb_eq ho, iha _ ha, ihb _ hb]
  | EMd o a b iha ihb =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨ho, ha⟩, hb⟩ := h
      show expr.EMd o a b = expr.EMd _ _ _
      rw [p_mulop_eqb_eq ho, iha _ ha, ihb _ hb]
  | EMdw o a b iha ihb =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨ho, ha⟩, hb⟩ := h
      show expr.EMdw o a b = expr.EMdw _ _ _
      rw [p_mulop_eqb_eq ho, iha _ ha, ihb _ hb]
  | EExt s l n a ih =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hs, hl⟩, hn⟩, ha⟩ := h
      show expr.EExt s l n a = expr.EExt _ _ _ _
      rw [hs, hl, hn, ih _ ha]
  | EBlob s k i n =>
      intro y h
      cases y <;> simp [expr_eqb, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hs, hk⟩, hi⟩, hn⟩ := h
      show expr.EBlob s k i n = expr.EBlob _ _ _ _
      rw [hs, hk, hi, hn]

/-! ### Range index

    The `KRange` facts bucketed (original order kept) by the shape of the
    literal-stripped subject: subject `EVar n` (possibly plus a literal) ->
    bucket `n` of a `Nat`-indexed table (lookup = `getD`, no conversion of
    the unary index); any other subject -> one common list.  A fact can
    answer `find_range _ e` only if its stripped subject equals `e`'s
    (exact or shifted match), hence only from `e`'s bucket. -/

/-- The first ambient variable of an expression, if it mentions one. -/
def first_var : expr → Option Nat
  | .ELit _ => none
  | .EVar n => some n
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b =>
      match first_var a with
      | some n => some n
      | none => first_var b
  | .EExt _ _ _ a => first_var a
  | .EBlob _ _ _ _ => none

/-- The bucket key of `e`: the first variable of its literal-stripped form. -/
def vkey_of (e : expr) : Option Nat := first_var (lit_strip e).1

/-- Insert `x` into bucket `n` (extending the table as needed). -/
def lset {A : Type} : List (List A) → Nat → A → List (List A)
  | [], 0, x => [[x]]
  | b :: rest, 0, x => (x :: b) :: rest
  | [], m + 1, x => [] :: lset [] m x
  | b :: rest, m + 1, x => b :: lset rest m x

/-- `n`-th bucket (`[]` when out of range). -/
def lget {A : Type} (l : List (List A)) (n : Nat) : List A := l.getD n []

/-- Lookup after insert: the inserted element heads its own bucket. -/
theorem lget_lset {A : Type} (n : Nat) :
    ∀ (l : List (List A)) (x : A) (m : Nat),
      lget (lset l n x) m = if m == n then x :: lget l m else lget l m := by
  induction n with
  | zero =>
      intro l x m
      cases l with
      | nil => cases m <;> simp [lset, lget]
      | cons b rest => cases m <;> simp [lset, lget]
  | succ n ih =>
      intro l x m
      cases l with
      | nil =>
          cases m with
          | zero => simp [lset, lget]
          | succ m => simpa [lset, lget] using ih [] x m
      | cons b rest =>
          cases m with
          | zero => simp [lset, lget]
          | succ m => simpa [lset, lget] using ih rest x m

/-- The range index: per-variable buckets of `KRange` facts, plus the
    bucket of facts whose subject has no variable. -/
structure rindex where
  /-- bucket `n`: facts whose stripped subject starts with `EVar n` -/
  ri_vars : List (List kentry)
  /-- facts about subjects with no variable at all -/
  ri_other : List kentry
  deriving DecidableEq, Repr

/-- `RI` — the record constructor. -/
abbrev RI (v : List (List kentry)) (o : List kentry) : rindex := ⟨v, o⟩

/-- The bucket a query with key `k` may be answered from. -/
def ri_bucket (ri : rindex) (k : Option Nat) : List kentry :=
  match k with
  | some n => lget ri.ri_vars n
  | none => ri.ri_other

/-- Build the index from an already filtered knowledge list. -/
def mk_ri : List kentry → rindex
  | [] => RI [] []
  | K :: rest =>
      let t := mk_ri rest
      match K with
      | .KRange e' _ _ =>
          match vkey_of e' with
          | some n => RI (lset t.ri_vars n K) t.ri_other
          | none => RI t.ri_vars (K :: t.ri_other)
      | _ => t

/-- The indexed `find_range`: scan only the query's own bucket. -/
def find_rangeI (ri : rindex) (e : expr) : Option (Int × Int) :=
  find_range (ri_bucket ri (vkey_of e)) e

/-- Equality of bucket keys. -/
def okey_eqb (a b : Option Nat) : Bool :=
  match a, b with
  | some x, some y => x == y
  | none, none => true
  | _, _ => false

/-- `okey_eqb` decides key equality. -/
theorem okey_eqb_spec (a b : Option Nat) : okey_eqb a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [okey_eqb]

/-- One step of `mk_ri`, seen from a query: the new fact heads its own
    bucket and nothing else moves. -/
theorem ri_bucket_cons (t : rindex) (K : kentry) (e' : expr) (lo hi : Int)
    (k : Option Nat) (hK : K = .KRange e' lo hi) :
    ri_bucket (match vkey_of e' with
               | some n => RI (lset t.ri_vars n K) t.ri_other
               | none => RI t.ri_vars (K :: t.ri_other)) k
      = if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k := by
  subst hK
  cases h : vkey_of e' with
  | none => cases k <;> simp [ri_bucket, okey_eqb, lget, h]
  | some n => cases k <;> simp [ri_bucket, okey_eqb, lget_lset, h]

/-- A `KRange` fact on another bucket's subject cannot answer `e`: both the
    exact match and the shifted match miss. -/
theorem find_range_cons_miss (e' : expr) (lo hi : Int) (rest : List kentry) (e : expr)
    (h1 : expr_eqb e e' = false) (h2 : expr_eqb (lit_strip e).1 (lit_strip e').1 = false) :
    find_range (.KRange e' lo hi :: rest) e = find_range rest e := by
  simp only [find_range]
  rw [ite_eq_right (by rw [h1]; simp)]
  cases e <;> simp only [lit_strip] at h2 ⊢ <;> simp [h2]

/-- The index answers exactly what the linear scan answers. -/
theorem find_rangeI_eq (fk : List kentry) (e : expr) :
    find_rangeI (mk_ri fk) e = find_range fk e := by
  induction fk generalizing e with
  | nil =>
      simp only [mk_ri, find_rangeI, ri_bucket, find_range]
      cases h : vkey_of e <;> simp [lget, h, find_range]
  | cons K rest ih =>
      simp only [find_rangeI] at ih ⊢
      cases K with
      | KRange e' lo hi =>
          simp only [mk_ri, find_rangeI, find_range]
          rw [ri_bucket_cons (mk_ri rest) (.KRange e' lo hi) e' lo hi (vkey_of e) rfl]
          by_cases hk : vkey_of e = vkey_of e'
          · rw [ite_eq_left ((okey_eqb_spec _ _).2 hk)]
            simp only [find_range, ih]
          · rw [ite_eq_right (by simp only [okey_eqb_spec]; exact hk)]
            have hvvf : expr_eqb (lit_strip e).1 (lit_strip e').1 = false := by
              cases hv : expr_eqb (lit_strip e).1 (lit_strip e').1 with
              | false => rfl
              | true => exact absurd (by simp only [vkey_of, p_expr_eqb_eq _ _ hv]) hk
            rw [ih]
            cases hE : expr_eqb e e' with
            | true => exact absurd (by rw [p_expr_eqb_eq e e' hE]) hk
            | false =>
                simp only [hvvf, Bool.false_eq_true, ite_false]
                cases e <;> rfl
      | KWord a w v => simp only [mk_ri, find_range, ih]
      | KZero a n => simp only [mk_ri, find_range, ih]
      | KBlob a n k => simp only [mk_ri, find_range, ih]
      | KImg lo hi => simp only [mk_ri, find_range, ih]
      | KAlign ex m => simp only [mk_ri, find_range, ih]
      | KWr a n => simp only [mk_ri, find_range, ih]
      | KDisj a1 n1 a2 n2 => simp only [mk_ri, find_range, ih]
      | KFill a n c => simp only [mk_ri, find_range, ih]
      | KUnk a n => simp only [mk_ri, find_range, ih]

/-! ### The block context -/

/-- PERF: the block context.  Everything the reference functions would
    re-derive on every call, computed once:
    - `bc_fk`  the knowledge list the context was made from (what the
      reference functions get);
    - `bc_ffk` `facts_of bc_fk`;
    - `bc_fs`  `sum_facts bc_fk bc_fk`;
    - `bc_ri`  `mk_ri bc_ffk`. -/
structure bctx where
  /-- the knowledge list the context was made from -/
  bc_fk : List kentry
  /-- `facts_of bc_fk` -/
  bc_ffk : List kentry
  /-- `sum_facts bc_fk bc_fk` -/
  bc_fs : List sfact
  /-- `mk_ri bc_ffk` -/
  bc_ri : rindex
  deriving DecidableEq, Repr

/-- `BC` — the record constructor. -/
abbrev BC (fk ffk : List kentry) (fs : List sfact) (ri : rindex) : bctx :=
  ⟨fk, ffk, fs, ri⟩

/-- The context WITHOUT the sum-facts digest (used to compute the digest
    itself). -/
def mkbc0 (fk : List kentry) (fs : List sfact) : bctx :=
  BC fk (facts_of fk) fs (mk_ri (facts_of fk))

/-- `erange_fB`: the interval domain, by fuel, with the block context
    threaded through.  Textually the reference `erange_f` with `find_range kn`
    replaced by the indexed `find_rangeI bc.bc_ri`; the recursion carries
    `bc` (`erange_fB_eqf0` proves it equal to the reference). -/
def erange_fB : Nat → bctx → expr → Option (Int × Int)
  | 0, _, _ => none
  | fuel + 1, bc, e =>
    let erange := erange_fB fuel bc
    match find_rangeI bc.bc_ri e with
    | some r => some (clampi r)
    | none =>
      match (let l := lin_of e
             if lin_trivial l then none
             else
               match lin_range erange l.1 l.2 with
               | some (lo, hi) =>
                   let q := zdiv64 lo
                   if q == zdiv64 hi then some (lo - q * two64, hi - q * two64) else none
               | none => none) with
      | some r => some r
      | none =>
        match e with
        | .ELit z => let v := zmod64 z; some (v, v)
        | .EVar _ => none
        | .EAlu op a b =>
            match op with
            | .ADD =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if ah + bh < two64 then some (al + bl, ah + bh)
                    else if two64 ≤ al + bl then some (al + bl - two64, ah + bh - two64)
                    else none
                | _, _ => none
            | .SUB =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if bh ≤ al then some (al - bh, ah - bl)
                    else if ah < bl then some (al - bh + two64, ah - bl + two64)
                    else none
                | _, _ => none
            | .AND =>
                -- mask 2^j-1 on a range that crosses no multiple of 2^j:
                -- exact residues; mask -2^j: both bounds rounded down to a
                -- multiple of 2^j (monotone)
                match (match b, erange a with
                       | .ELit m, some (al, ah) =>
                           let m' := m % two64
                           let j := zlog2 (m' + 1)
                           if (m' + 1 == zpow 2 j && al / zpow 2 j ≤ ah / zpow 2 j &&
                               al / zpow 2 j == ah / zpow 2 j)
                           then some (al % zpow 2 j, ah % zpow 2 j)
                           else
                             let jh := zlog2 (two64 - m')
                             if (two64 - m' == zpow 2 jh && jh < 64)
                             then some (al - al % zpow 2 jh, ah - ah % zpow 2 jh)
                             else none
                       | _, _ => none) with
                | some r => some r
                | none =>
                  match erange a, erange b with
                  | some (_, ah), some (_, bh) => some (0, min ah bh)
                  | some (_, ah), none => some (0, ah)
                  | none, some (_, bh) => some (0, bh)
                  | none, none => none
            | .OR =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) => some (max al bl, mask_cover (max ah bh))
                | _, _ => none
            | .XOR =>
                match erange a, erange b with
                | some (_, ah), some (_, bh) => some (0, mask_cover (max ah bh))
                | _, _ => none
            | .SRL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s => some (al / zpow 2 s, ah / zpow 2 s)
                | _, _ => none
            | .SRA =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    if ah < zpow 2 63 then some (al / zpow 2 s, ah / zpow 2 s) else none
                | _, _ => none
            | .SLL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    if ah * zpow 2 s < two64 then some (al * zpow 2 s, ah * zpow 2 s) else none
                | _, _ => none
            | .SLTU =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if ah < bl then some (1, 1)
                    else if bh ≤ al then some (0, 0) else some (0, 1)
                | _, _ => some (0, 1)
            | .SLT =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (ah < zpow 2 63 && bh < zpow 2 63) then
                      (if ah < bl then some (1, 1)
                       else if bh ≤ al then some (0, 0) else some (0, 1))
                    else some (0, 1)
                | _, _ => some (0, 1)
        | .EAluw op a b =>
            match op with
            | .ADD =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    let bl' := if bl == bh then zsigned64 bl else bl
                    let bh' := if bl == bh then zsigned64 bh else bh
                    if (0 ≤ al + bl' && ah + bh' < zpow 2 31)
                    then some (al + bl', ah + bh') else none
                | _, _ => none
            | .SUB =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (bh ≤ al && ah - bl < zpow 2 31) then some (al - bh, ah - bl) else none
                | _, _ => none
            | .SLL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if ah * zpow 2 s' < zpow 2 31 then some (al * zpow 2 s', ah * zpow 2 s')
                    else none
                | _, _ => none
            | .SRL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if (ah < zpow 2 32 && (0 < s' || ah < zpow 2 31))
                    then some (al / zpow 2 s', ah / zpow 2 s') else none
                | _, _ => none
            | .SRA =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if ah < zpow 2 31 then some (al / zpow 2 s', ah / zpow 2 s') else none
                | _, _ => none
            | _ => none
        | .EMd op a b =>
            match op with
            | .MUL =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (0 ≤ al && 0 ≤ bl && ah * bh < two64) then some (al * bl, ah * bh) else none
                | _, _ => none
            | .MULHU =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (0 ≤ al && 0 ≤ bl) then some (al * bl / two64, ah * bh / two64) else none
                | _, _ => none
            | .DIVU =>
                match erange a, b with
                | some (al, ah), .ELit d =>
                    let d' := d % two64
                    if 0 < d' then some (al / d', ah / d') else none
                | _, _ => none
            | .REMU =>
                match erange a, b with
                | some (al, ah), .ELit d =>
                    let d' := d % two64
                    if 0 < d' then some (0, min ah (d' - 1)) else none
                | _, _ => none
            | _ => none
        | .EMdw _ _ _ => none
        | .EExt sx lo n a =>
            let w := zpow 2 (8 * (n : Int))
            if sx then
              match lo, erange a with
              | 0, some (al, ah) =>
                  if (0 ≤ al && ah < w / 2) then some (al, ah)
                  else if (1 ≤ n && n ≤ 8 && w / 2 ≤ al && ah < w)
                       then some (two64 - w + al, two64 - w + ah) else none
              | _, _ => none
            else
              match lo, erange a with
              | 0, some (al, ah) =>
                  if (0 ≤ al && ah < w) then some (al, ah) else some (0, min (w - 1) two64m1)
              | _, _ => some (0, min (w - 1) two64m1)
        | .EBlob sx _ _ n =>
            -- a sign-extended blob slice is still a word
            if sx then some (0, two64m1)
            else some (0, min (zpow 2 (8 * (n : Int)) - 1) two64m1)

/-- `lin_range` only looks at the range function, pointwise. -/
theorem lin_range_ext {r1 r2 : expr → Option (Int × Int)} {c : Int}
    {ts : List (Int × expr)} (H : ∀ a, r1 a = r2 a) :
    lin_range r1 c ts = lin_range r2 c ts := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨k, a⟩ := t
      simp only [lin_range, H, ih]

/-! ### The block-context copies of the interval / alignment domain -/

/-- `erange0B`: the interval domain on the context's fact list. -/
def erange0B (bc : bctx) (e : expr) : Option (Int × Int) := erange_fB erange_fuel bc e

/-- `erangeB`: `erange0B` tightened by the align-down atoms (R4.2). -/
def erangeB (bc : bctx) (e : expr) : Option (Int × Int) :=
  let r := erange0B bc e
  let (e', s) := deand e
  if s == 0 then r
  else
    match erange0B bc (unlin (lin_of e')) with
    | some (lo', hi') =>
        if s ≤ lo' then
          match r with
          | some (lo, hi) => some (max lo (lo' - s), min hi hi')
          | none => some (lo' - s, hi')
        else r
    | none => r

/-- `base_rangeB`: a literal base needs no knowledge. -/
def base_rangeB (bc : bctx) (e : expr) : Option (Int × Int) :=
  match e with
  | .ELit z => let v := z % two64; some (v, v)
  | _ => erangeB bc e

/-- `ealignB`: the alignment domain (the fact-free half reads the digest). -/
def ealignB (bc : bctx) (e : expr) : Int :=
  max (ealign0 bc.bc_ffk e) (pageup_align e)

/-- `lin_nowrapB`. -/
def lin_nowrapB (bc : bctx) (e : expr) : Bool :=
  let l := lin_of e
  match lin_range (erangeB bc) l.1 l.2 with
  | some (lo, hi) => (0 ≤ lo && hi < two64)
  | none => false

/-- `srl_expandB`: expand SRL atoms (and high-AND atoms) of a term list. -/
def srl_expandB (bc : bctx) : List (Int × expr) → Int × List (Int × expr)
  | [] => (0, [])
  | (k, a) :: rest =>
      let (c, ts') := srl_expandB bc rest
      let keep := (c, lins_e k a ts')
      match a with
      | .EAlu .SRL e (.ELit s) =>
          let m := zpow 2 ((s % two64) % 64)
          if (k % m == 0 && lin_nowrapB bc e) then
            let q := k / m
            let le := lin_of e
            if (s % two64) % 64 ≤ ealignB bc e then
              -- exact: e is a multiple of m (J3e)
              (c + q * le.1, le.2.foldr (fun t acc => lins_e (q * t.1) t.2 acc) ts')
            else
              (c + q * le.1,
               lins_e (-q) (srl_rem e m) (le.2.foldr (fun t acc => lins_e (q * t.1) t.2 acc) ts'))
          else keep
      | .EAlu .AND e (.ELit mk) =>
          -- the align-down atom `e AND -2^s` = `e - (e AND (2^s-1))`
          -- exactly, for ANY coefficient — so that `2^s * SRL(e,s)` and
          -- `e AND -2^s` (two spellings of the same rounding,
          -- `and_high_split` produces the latter) expand to the same form
          -- and cancel
          match highmask_s mk with
          | some s =>
              if lin_nowrapB bc e then
                let le := lin_of e
                (c + k * le.1,
                 lins_e (-k) (srl_rem e (zpow 2 s))
                   (le.2.foldr (fun t acc => lins_e (k * t.1) t.2 acc) ts'))
              else keep
          | none => keep
      | _ => keep

/-- `fact_nowrapB`: a `KRange` fact pins the linear form when no other
    representative is possible (J3d). -/
def fact_nowrapB (bc : bctx) (e : expr) (hi : Int) : Bool :=
  let l := lin_of e
  match lin_range (erangeB bc) l.1 l.2 with
  | some (a, b) => (b < two64 && hi < a + two64)
  | none => false

/-- `sum_fact_xB`: the srl-expanded version of a digested fact (J3c). -/
def sum_fact_xB (bc : bctx) (ts : List (Int × expr)) (lo hi : Int) : List sfact :=
  let (c2, ts2) := srl_expandB bc ts
  match ts2 with
  | _ :: _ => if c2 == 0 then [] else [(ts2, (lo - c2, hi - c2))]
  | [] => []

/-- `sum_factsB`: the digested facts of the context's fact list. -/
def sum_factsB (bc : bctx) (kn : List kentry) : List sfact :=
  match kn with
  | [] => []
  | .KRange e lo hi :: rest =>
      match e with
      | .EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, ts@(_ :: _ :: _)) =>
            if fact_nowrapB bc e hi
            then (ts, (lo - c, hi - c)) ::
                 (sum_fact_xB bc ts (lo - c) (hi - c) ++ sum_factsB bc rest)
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
  | _ :: rest => sum_factsB bc rest

/-! ### The `..B` functions equal their references -/

theorem bc_fk_mkbc0 (fk : List kentry) (fs : List sfact) : (mkbc0 fk fs).bc_fk = fk := rfl

theorem bc_ffk_mkbc0 (fk : List kentry) (fs : List sfact) :
    (mkbc0 fk fs).bc_ffk = facts_of fk := rfl

theorem find_rangeI_mkbc0 (fk : List kentry) (fs : List sfact) :
    find_rangeI (mkbc0 fk fs).bc_ri = find_range (facts_of fk) := by
  funext e
  exact find_rangeI_eq (facts_of fk) e

/-- The fuel induction behind every `erange_fB`/`erange_f` comparison: with
    the same effective `find_range`, the two bodies are the same term (the
    residual goal after the rewrites is closed by conversion). -/
theorem erange_fB_eq_of (fuel : Nat) (bc : bctx) (kn : List kentry)
    (h : ∀ e, find_rangeI bc.bc_ri e = find_range kn e) :
    ∀ e, erange_fB fuel bc e = erange_f fuel kn e := by
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
      intro e
      have hlr : ∀ (c : Int) (ts : List (Int × expr)),
          lin_range (erange_fB fuel bc) c ts = lin_range (erange_f fuel kn) c ts :=
        fun c ts => lin_range_ext ih
      simp only [erange_fB, erange_f, h, ih, hlr]
      try exact rfl

theorem find_rangeI_mkbc0_pt (fk : List kentry) (fs : List sfact) :
    ∀ e, find_rangeI (mkbc0 fk fs).bc_ri e = find_range (facts_of fk) e :=
  fun e => congrFun (find_rangeI_mkbc0 fk fs) e

theorem erange_fB_eqf0 (fk : List kentry) (fs : List sfact) (fuel : Nat) :
    erange_fB fuel (mkbc0 fk fs) = erange_f fuel (facts_of fk) := by
  funext e
  exact erange_fB_eq_of fuel _ _ (find_rangeI_mkbc0_pt fk fs) e

theorem erange0B_eqf0 (fk : List kentry) (fs : List sfact) :
    erange0B (mkbc0 fk fs) = erange0 fk := by
  funext e
  simp only [erange0B, erange0, erange_fB_eqf0]

theorem erangeB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e) :
    erangeB bc = erange kn := by
  funext e
  simp only [erangeB, erange, erange0B, erange0, erange_fB_eq_of _ bc _ hri]
  try exact rfl

theorem erangeB_eqf0 (fk : List kentry) (fs : List sfact) :
    erangeB (mkbc0 fk fs) = erange fk :=
  erangeB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs)

theorem base_rangeB_eqf0 (fk : List kentry) (fs : List sfact) :
    base_rangeB (mkbc0 fk fs) = base_range fk := by
  funext e
  simp only [base_rangeB, base_range, erangeB_eqf0]
  try exact rfl

theorem ealignB_eq_of (bc : bctx) (kn : List kentry) (hffk : bc.bc_ffk = facts_of kn) :
    ealignB bc = ealign kn := by
  funext e
  simp only [ealignB, ealign, hffk]

theorem ealignB_eqf0 (fk : List kentry) (fs : List sfact) :
    ealignB (mkbc0 fk fs) = ealign fk :=
  ealignB_eq_of _ fk rfl

theorem lin_nowrapB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e) :
    lin_nowrapB bc = lin_nowrap kn := by
  funext e
  have h := erangeB_eq_of bc kn hri
  simp only [lin_nowrapB, lin_nowrap,
    lin_range_ext (r1 := erangeB bc) (r2 := erange kn) (fun a => congrFun h a)]
  try exact rfl

theorem lin_nowrapB_eqf0 (fk : List kentry) (fs : List sfact) :
    lin_nowrapB (mkbc0 fk fs) = lin_nowrap fk :=
  lin_nowrapB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs)

theorem srl_expandB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e)
    (hffk : bc.bc_ffk = facts_of kn) :
    ∀ ts, srl_expandB bc ts = srl_expand kn ts := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨k, a⟩ := t
      have hnw := lin_nowrapB_eq_of bc kn hri
      have hal := ealignB_eq_of bc kn hffk
      simp only [srl_expandB, srl_expand, ih, hnw, hal]
      try exact rfl

theorem srl_expandB_eqf0 (fk : List kentry) (fs : List sfact) (ts : List (Int × expr)) :
    srl_expandB (mkbc0 fk fs) ts = srl_expand fk ts :=
  srl_expandB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs) rfl ts

theorem fact_nowrapB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e) :
    fact_nowrapB bc = fact_nowrap kn := by
  funext e hi
  have h := erangeB_eq_of bc kn hri
  simp only [fact_nowrapB, fact_nowrap,
    lin_range_ext (r1 := erangeB bc) (r2 := erange kn) (fun a => congrFun h a)]
  try exact rfl

theorem fact_nowrapB_eqf0 (fk : List kentry) (fs : List sfact) :
    fact_nowrapB (mkbc0 fk fs) = fact_nowrap fk :=
  fact_nowrapB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs)

theorem sum_fact_xB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e)
    (hffk : bc.bc_ffk = facts_of kn) :
    sum_fact_xB bc = sum_fact_x kn := by
  funext ts lo hi
  have h := srl_expandB_eq_of bc kn hri hffk
  simp only [sum_fact_xB, sum_fact_x, h]
  try exact rfl

theorem sum_fact_xB_eqf0 (fk : List kentry) (fs : List sfact) :
    sum_fact_xB (mkbc0 fk fs) = sum_fact_x fk :=
  sum_fact_xB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs) rfl

theorem sum_factsB_eq_of (bc : bctx) (kn : List kentry)
    (hri : ∀ e, find_rangeI bc.bc_ri e = find_range (facts_of kn) e)
    (hffk : bc.bc_ffk = facts_of kn) :
    ∀ kn', sum_factsB bc kn' = sum_facts kn kn' := by
  intro kn'
  induction kn' with
  | nil => rfl
  | cons K rest ih =>
      have hfn := fact_nowrapB_eq_of bc kn hri
      have hfx := sum_fact_xB_eq_of bc kn hri hffk
      cases K with
      | KRange e lo hi =>
          cases e <;> simp only [sum_factsB, sum_facts, hfn, hfx, ih] <;> exact rfl
      | _ => simp only [sum_factsB, sum_facts, ih]

theorem sum_factsB_eqf0 (fk : List kentry) (fs : List sfact) :
    sum_factsB (mkbc0 fk fs) = sum_facts fk := by
  funext kn'
  exact sum_factsB_eq_of _ fk (find_rangeI_mkbc0_pt fk fs) rfl kn'


/-! #### The full block context

    The sum-facts digest is computed through the indexed functions. -/

/-- The full block context. -/
def mkbc (fk : List kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk []) fk)

theorem bc_fk_mkbc (fk : List kentry) : (mkbc fk).bc_fk = fk := rfl

theorem bc_ffk_mkbc (fk : List kentry) : (mkbc fk).bc_ffk = facts_of fk := rfl

theorem bc_fs_mkbc (fk : List kentry) : (mkbc fk).bc_fs = sum_facts fk fk := by
  simp only [mkbc, mkbc0]
  exact congrFun (sum_factsB_eqf0 fk []) fk

theorem find_rangeI_mkbc (fk : List kentry) :
    find_rangeI (mkbc fk).bc_ri = find_range (facts_of fk) :=
  find_rangeI_mkbc0 fk _

theorem find_rangeI_mkbc_pt (fk : List kentry) :
    ∀ e, find_rangeI (mkbc fk).bc_ri e = find_range (facts_of fk) e :=
  fun e => congrFun (find_rangeI_mkbc fk) e

theorem erange_fB_eqf (fk : List kentry) (fuel : Nat) :
    erange_fB fuel (mkbc fk) = erange_f fuel (facts_of fk) := by
  funext e
  exact erange_fB_eq_of fuel _ _ (find_rangeI_mkbc_pt fk) e

theorem erange0B_eqf (fk : List kentry) : erange0B (mkbc fk) = erange0 fk := by
  funext e
  simp only [erange0B, erange0, erange_fB_eqf]

theorem erangeB_eqf (fk : List kentry) : erangeB (mkbc fk) = erange fk :=
  erangeB_eq_of _ fk (find_rangeI_mkbc_pt fk)

theorem base_rangeB_eqf (fk : List kentry) : base_rangeB (mkbc fk) = base_range fk := by
  funext e
  simp only [base_rangeB, base_range, erangeB_eqf]
  try exact rfl

theorem ealignB_eqf (fk : List kentry) : ealignB (mkbc fk) = ealign fk :=
  ealignB_eq_of _ fk rfl

theorem lin_nowrapB_eqf (fk : List kentry) : lin_nowrapB (mkbc fk) = lin_nowrap fk :=
  lin_nowrapB_eq_of _ fk (find_rangeI_mkbc_pt fk)

theorem srl_expandB_eqf (fk : List kentry) (ts : List (Int × expr)) :
    srl_expandB (mkbc fk) ts = srl_expand fk ts :=
  srl_expandB_eq_of _ fk (find_rangeI_mkbc_pt fk) rfl ts

theorem fact_nowrapB_eqf (fk : List kentry) : fact_nowrapB (mkbc fk) = fact_nowrap fk :=
  fact_nowrapB_eq_of _ fk (find_rangeI_mkbc_pt fk)

theorem sum_fact_xB_eqf (fk : List kentry) : sum_fact_xB (mkbc fk) = sum_fact_x fk :=
  sum_fact_xB_eq_of _ fk (find_rangeI_mkbc_pt fk) rfl

theorem sum_factsB_eqf (fk : List kentry) : sum_factsB (mkbc fk) = sum_facts fk := by
  funext kn'
  exact sum_factsB_eq_of _ fk (find_rangeI_mkbc_pt fk) rfl kn'

/-! ### The facts layer: relational bounds, disjointness, symbolic lengths -/

/-- `lin_test_relB`: the relational retry of `lin_test`, against the
    context's digested facts (`bc_fs`). -/
def lin_test_relB (bc : bctx) (c : Int) (ts : List (Int × expr))
    (test : Int → Int → Bool) : Bool :=
  match bc.bc_fs with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) c ts' with
          | some (lo, hi) => test (lo + lo0) (hi + hi0)
          | none => false
      | _ => false

/-- `lin_testB`: per-atom interval first, then the relational retry. -/
def lin_testB (bc : bctx) (c : Int) (ts : List (Int × expr))
    (test : Int → Int → Bool) : Bool :=
  match lin_range (erangeB bc) c ts with
  | some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
  | none => lin_test_relB bc c ts test

/-- `lin_srangeB`: the scaled-interval bound of a linear form. -/
def lin_srangeB (bc : bctx) (e : expr) : Option (Int × Int) :=
  let l := lin_of e
  let j := srl_scale_need l.2
  if (0 ≤ j && j ≤ 24) then
    -- j = 0 too — the plain two-pass expansion interval
    let sc := zpow 2 j
    let ts := l.2.map (fun t => (sc * t.1, t.2))
    let (c2, t2) := srl_expandB bc ts
    let (c3, t3) := (if has_srl t2 then srl_expandB bc t2 else ((0 : Int), t2))
    match lin_range (erangeB bc) (sc * l.1 + c2 + c3) t3 with
    | some (lo', hi') =>
        let lo := zcdiv lo' sc
        let hi := hi' / sc
        if (0 ≤ lo && (lo ≤ hi && hi < two64)) then some (lo, hi) else none
    | none => none
  else none

/-- `lin_nowrapRB`: no-wrap of a linear form, with the relational step (J3). -/
def lin_nowrapRB (bc : bctx) (e : expr) : Bool :=
  let l := lin_of e
  let (c2, t2) := srl_expandB bc l.2   -- J3g: page-rounded forms
  if lin_testB bc (l.1 + c2) t2 (fun lo hi => (0 ≤ lo && hi < two64)) then true
  else -- the scaled two-pass expansion interval proves no-wrap too
    match lin_srangeB bc e with | some _ => true | none => false

/-- `lin_apart0B`: the exact difference of two ranges' starts, bounded away. -/
def lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
  (let l1 := lin_of b1
   let l2 := lin_of b2
   lin_testB bc (l2.1 + k2 - l1.1 - k1) (lsub_e l2.2 l1.2)
     (fun lo hi => (n1 ≤ lo || hi ≤ -n2)))

/-- `lin_apartB`, guarded by the shared-variable prefilter. -/
def lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false

/-- `lin_brangeB`: relational interval of a linear form (J3b). -/
def lin_brangeB (bc : bctx) (e : expr) : Option (Int × Int) :=
  let l := lin_of e
  match bc.bc_fs with
  | [] => none
  | fs =>
      match sum_subst fs l.2 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erangeB bc) l.1 ts' with
          | some (lo, hi) =>
              let lo' := lo + lo0
              let hi' := hi + hi0
              if (0 ≤ lo' && hi' < two64) then some (lo', hi') else none
          | none => none
      | _ => none

/-- `xloB`: lower numeric bound. -/
def xloB (bc : bctx) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
      match erangeB bc e with
      | some (lo, _) => some lo
      | none =>
          match lin_brangeB bc e with
          | some (lo, _) => some lo
          | none =>
              match lin_srangeB bc e with
              | some (lo, _) => some lo
              | none => none

/-- `xhiB`: upper numeric bound. -/
def xhiB (bc : bctx) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
      match erangeB bc e with
      | some (_, hi) => some hi
      | none =>
          match lin_brangeB bc e with
          | some (_, hi) => some hi
          | none =>
              match lin_srangeB bc e with
              | some (_, hi) => some hi
              | none => none

/-- `xt_nowrapB`: every term's base does not wrap. -/
def xt_nowrapB (bc : bctx) : xterms → Bool
  | [] => true
  | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r

/-- `lin_ge0_scaledB`: the form SCALED by `2^j` so every `k * SRL(_,s)`
    term becomes expandable, two expansion passes. -/
def lin_ge0_scaledB (bc : bctx) (c : Int) (ts : List (Int × expr)) : Bool :=
  let j := srl_scale_need ts
  if (0 < j && j ≤ 24) then
    let sc := zpow 2 j
    let ts' := ts.map (fun t => (sc * t.1, t.2))
    let (c2, t2) := srl_expandB bc ts'
    let (c3, t3) := (if has_srl t2 then srl_expandB bc t2 else ((0 : Int), t2))
    lin_testB bc (sc * c + c2 + c3) t3 (fun lo _ => 0 ≤ lo)
  else false

/-- `lin_ge0B`: `Σ pos - Σ neg >= 0` for every valuation satisfying the
    context's facts. -/
def lin_ge0B (bc : bctx) (pos neg : xterms) : Bool :=
  xt_nowrapB bc pos && xt_nowrapB bc neg &&
  (if lin_testB bc (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))
        (fun lo _ => 0 ≤ lo) then true
   else
     let (c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg))
     if lin_testB bc (xt_const pos - xt_const neg + c2) t2 (fun lo _ => 0 ≤ lo) then true
     else -- nested roundings — second expansion pass, only when atoms to
          -- expand remain
       if (if has_srl t2 then
             let (c3, t3) := srl_expandB bc t2
             lin_testB bc (xt_const pos - xt_const neg + c2 + c3) t3 (fun lo _ => 0 ≤ lo)
           else false) then true
       else -- scaled expansion
         lin_ge0_scaledB bc (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)))

/-- `xinside0B`: containment of `b1+k1, +n1` in `b2+k2, +n2`, symbolic. -/
def xinside0B (bc : bctx) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  if lin_ge0B bc [(b1, k1)] [(b2, k2)]
  then lin_ge0B bc [(b2, k2), (n2, 0)] [(b1, k1), (n1, 0)]
  else false

/-- `xinside_numB`: numeric containment (literal-based container). -/
def xinside_numB (bc : bctx) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match xloB bc b2, xhiB bc b2 with
  | some lo2, some hi2 =>
      if lo2 == hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | some (lo1, hi1), some h1, some l2 =>
            (lo2 + k2 ≤ lo1 + k1) && (hi1 + k1 + h1 ≤ lo2 + k2 + l2)
        | _, _, _ => false
      else false
  | _, _ => false

/-- `xinsideB`: containment of symbolic ranges. -/
def xinsideB (bc : bctx) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_numB bc b1 k1 n1 b2 k2 n2 else false

/-- `sub_itvB`: `b+k, b+k+n` (n literal) inside `c, c + m` (`m` a length
    expression): against its lower bound, then the exact linear test. -/
def sub_itvB (bc : bctx) (b : expr) (k n : Int) (c : saddr) (m : expr) : Bool :=
  if (if (expr_eqb b c.a_base && c.a_off ≤ k) then
        match xloB bc m with
        | some ml => k + n ≤ c.a_off + ml
        | none => false
      else false)
  then true
  else -- other spelling of the base: exact linear containment
    if (0 ≤ n && n < two64) then xinsideB bc b k (.ELit n) c.a_base c.a_off m else false

/-- `kdisj_apartB`: a recorded `KDisj` fact separates the two ranges. -/
def kdisj_apartB (bc : bctx) (kn : List kentry) (b1 : expr) (k1 n1 : Int)
    (b2 : expr) (k2 n2 : Int) : Bool :=
  match kn with
  | [] => false
  | .KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2

/-- `ranges_apartB`: literal-length apartness. -/
def ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  if (match base_rangeB bc b1, base_rangeB bc b2 with
      | some (lo1, hi1), some (lo2, hi2) =>
          (hi1 + k1 + n1 ≤ lo2 + k2 || hi2 + k2 + n2 ≤ lo1 + k1)
      | _, _ => false) then true
  else if kdisj_apartB bc bc.bc_fk b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2

/-- `sub_itv_xB`: containment test of a symbolic length range in a `KDisj`
    side. -/
def sub_itv_xB (bc : bctx) (b : expr) (k : Int) (n : expr) (c : saddr) (m : expr) : Bool :=
  xinsideB bc b k n c.a_base c.a_off m

/-- `kdisj_apart_xB`: `kdisj_apart` with symbolic lengths. -/
def kdisj_apart_xB (bc : bctx) (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match kn with
  | [] => false
  | .KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2

/-- `end_hiB`: the END of a SYMBOLIC-length range `b+k, +n` through a JOINT
    fact `KRange (b + k + n) _ ehi` (as `mmap_null` records for a symbolic
    length: base + len <= CEIL — with only the separate ranges of base and
    length the bound `base_hi + len_hi` overshoots by the class width).
    Valid as an integer bound when the sum provably does not wrap. -/
def end_hiB (bc : bctx) (b : expr) (k : Int) (n : expr) (lo1 hi1 h1 : Int) : Option Int :=
  match n with
  | .ELit _ => none
  | _ =>
      if (if 0 ≤ lo1 + k then hi1 + k + h1 < two64 else false) then
        match find_rangeI bc.bc_ri (mkAlu .ADD (mkAlu .ADD b (.ELit k)) n) with
        | some (_, ehi) => some ehi
        | none => none
      else none

/-- `ranges_apart_xB`: apartness of `b1+k1, +n1` and `b2+k2, +n2` with
    symbolic lengths. -/
def ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
        | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
            if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
            else -- joint END facts of symbolic-length ranges
            if le_end (end_hiB bc b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
            else le_end (end_hiB bc b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
        | _, _, _, _ => false) then true
    else if kdisj_apart_xB bc bc.bc_fk b1 k1 n1 b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2), (n2, 0)]

/-- `disj_sidesB`: the `KDisj` partners of the sides that contain the
    store. -/
def disj_sidesB (bc : bctx) (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : Int) :
    List (saddr × expr) :=
  match kn with
  | [] => []
  | .KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB bc rest b1 k1 n1
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB bc rest b1 k1 n1

/-- `disj_sides_xB`: the same with symbolic lengths. -/
def disj_sides_xB (bc : bctx) (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) :
    List (saddr × expr) :=
  match kn with
  | [] => []
  | .KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1

/-- `in_sidesB`: does one of the prepared sides contain the other range? -/
def in_sidesB (bc : bctx) (D : List (saddr × expr)) (b2 : expr) (k2 n2 : Int) : Bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2

/-- `in_sides_xB`: the symbolic-length variant. -/
def in_sides_xB (bc : bctx) (D : List (saddr × expr)) (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2

/-- `mk_sprepB`: prepare the store-side facts once per store. -/
def mk_sprepB (bc : bctx) (b1 : expr) (k1 : Int) (n1 : expr) : sprep :=
  SPrep (base_rangeB bc b1) (xhiB bc n1)
        (match n1 with | .ELit z1 => disj_sidesB bc bc.bc_fk b1 k1 (zlit64 z1) | _ => [])
        (disj_sides_xB bc bc.bc_fk b1 k1 n1)

/-- `ranges_apart_pB`: `ranges_apart_xB` with the store-side facts
    precomputed (see `mk_sprepB`). -/
def ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 =>
      let m1 := zlit64 z1
      let m2 := zlit64 z2
      if (match sp.sp_rng, base_rangeB bc b2 with
          | some (lo1, hi1), some (lo2, hi2) =>
              (hi1 + k1 + m1 ≤ lo2 + k2 || hi2 + k2 + m2 ≤ lo1 + k1)
          | _, _ => false) then true
      else if in_sidesB bc sp.sp_D b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp.sp_rng, base_rangeB bc b2, sp.sp_h1, xhiB bc n2 with
        | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
            if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
            else -- joint END facts of symbolic-length ranges
            if le_end (end_hiB bc b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
            else le_end (end_hiB bc b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
        | _, _, _, _ => false) then true
    else if in_sides_xB bc sp.sp_Dx b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2), (n2, 0)]

/-! #### The facts layer equals its reference -/

theorem lin_test_relB_eqf (fk : List kentry) :
    lin_test_relB (mkbc fk) = lin_test_rel fk := by
  funext c ts test
  simp only [lin_test_relB, lin_test_rel, bc_fs_mkbc, erangeB_eqf]
  try exact rfl

theorem lin_testB_eqf (fk : List kentry) : lin_testB (mkbc fk) = lin_test fk := by
  funext c ts test
  simp only [lin_testB, lin_test, erangeB_eqf, lin_test_relB_eqf]
  try exact rfl

theorem lin_srangeB_eqf (fk : List kentry) : lin_srangeB (mkbc fk) = lin_srange fk := by
  funext e
  simp only [lin_srangeB, lin_srange, srl_expandB_eqf, erangeB_eqf]
  try exact rfl

theorem lin_nowrapRB_eqf (fk : List kentry) : lin_nowrapRB (mkbc fk) = lin_nowrapR fk := by
  funext e
  simp only [lin_nowrapRB, lin_nowrapR, srl_expandB_eqf, lin_testB_eqf, lin_srangeB_eqf]
  try exact rfl

theorem lin_apart0B_eqf (fk : List kentry) : lin_apart0B (mkbc fk) = lin_apart0 fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [lin_apart0B, lin_apart0, lin_nowrapRB_eqf, lin_testB_eqf]
  try exact rfl

theorem lin_apartB_eqf (fk : List kentry) : lin_apartB (mkbc fk) = lin_apart fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [lin_apartB, lin_apart, lin_apart0B_eqf]
  try exact rfl

theorem lin_brangeB_eqf (fk : List kentry) : lin_brangeB (mkbc fk) = lin_brange fk := by
  funext e
  simp only [lin_brangeB, lin_brange, bc_fs_mkbc, erangeB_eqf]
  try exact rfl

theorem xloB_eqf (fk : List kentry) : xloB (mkbc fk) = xlo fk := by
  funext e
  simp only [xloB, xlo, erangeB_eqf, lin_brangeB_eqf, lin_srangeB_eqf]
  try exact rfl

theorem xhiB_eqf (fk : List kentry) : xhiB (mkbc fk) = xhi fk := by
  funext e
  simp only [xhiB, xhi, erangeB_eqf, lin_brangeB_eqf, lin_srangeB_eqf]
  try exact rfl

theorem xt_nowrapB_eqf (fk : List kentry) : xt_nowrapB (mkbc fk) = xt_nowrap fk := by
  funext ts
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨e, k⟩ := t
      simp only [xt_nowrapB, xt_nowrap, lin_nowrapRB_eqf, ih]
      try exact rfl

theorem lin_ge0_scaledB_eqf (fk : List kentry) :
    lin_ge0_scaledB (mkbc fk) = lin_ge0_scaled fk := by
  funext c ts
  simp only [lin_ge0_scaledB, lin_ge0_scaled, srl_expandB_eqf, lin_testB_eqf]
  try exact rfl

theorem lin_ge0B_eqf (fk : List kentry) : lin_ge0B (mkbc fk) = lin_ge0 fk := by
  funext pos neg
  simp only [lin_ge0B, lin_ge0, xt_nowrapB_eqf, lin_testB_eqf, srl_expandB_eqf,
    lin_ge0_scaledB_eqf]
  try exact rfl

theorem xinside0B_eqf (fk : List kentry) : xinside0B (mkbc fk) = xinside0 fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [xinside0B, xinside0, lin_ge0B_eqf]
  try exact rfl

theorem xinside_numB_eqf (fk : List kentry) :
    xinside_numB (mkbc fk) = xinside_num fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [xinside_numB, xinside_num, xloB_eqf, xhiB_eqf, base_rangeB_eqf]
  try exact rfl

theorem xinsideB_eqf (fk : List kentry) : xinsideB (mkbc fk) = xinside fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [xinsideB, xinside, xinside0B_eqf, xinside_numB_eqf]
  try exact rfl

theorem sub_itvB_eqf (fk : List kentry) : sub_itvB (mkbc fk) = sub_itv fk := by
  funext b k n c m
  simp only [sub_itvB, sub_itv, xloB_eqf, xinsideB_eqf]
  try exact rfl

theorem kdisj_apartB_eqf (fk : List kentry) : kdisj_apartB (mkbc fk) = kdisj_apart fk := by
  funext kn b1 k1 n1 b2 k2 n2
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KDisj c1 m1 c2 m2 =>
          simp only [kdisj_apartB, kdisj_apart, sub_itvB_eqf, ih]
          try exact rfl
      | _ => simp only [kdisj_apartB, kdisj_apart, ih]

theorem ranges_apartB_eqf (fk : List kentry) : ranges_apartB (mkbc fk) = ranges_apart fk := by
  funext b1 k1 n1 b2 k2 n2
  simp only [ranges_apartB, ranges_apart, base_rangeB_eqf, kdisj_apartB_eqf,
    lin_apartB_eqf, bc_fk_mkbc]
  try exact rfl

theorem sub_itv_xB_eqf (fk : List kentry) : sub_itv_xB (mkbc fk) = sub_itv_x fk := by
  funext b k n c m
  simp only [sub_itv_xB, sub_itv_x, xinsideB_eqf]
  try exact rfl

theorem kdisj_apart_xB_eqf (fk : List kentry) :
    kdisj_apart_xB (mkbc fk) = kdisj_apart_x fk := by
  funext kn b1 k1 n1 b2 k2 n2
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KDisj c1 m1 c2 m2 =>
          simp only [kdisj_apart_xB, kdisj_apart_x, sub_itv_xB_eqf, ih]
          try exact rfl
      | _ => simp only [kdisj_apart_xB, kdisj_apart_x, ih]

theorem end_hiB_eqf (fk : List kentry) : end_hiB (mkbc fk) = end_hi fk := by
  funext b k n lo1 hi1 h1
  simp only [end_hiB, end_hi, find_rangeI_mkbc]
  try exact rfl

theorem ranges_apart_xB_eqf (fk : List kentry) :
    ranges_apart_xB (mkbc fk) = ranges_apart_x fk := by
  funext b1 k1 n1 b2 k2 n2
  cases n1 <;> cases n2 <;>
    simp only [ranges_apart_xB, ranges_apart_x, ranges_apartB_eqf, base_rangeB_eqf,
      xhiB_eqf, end_hiB_eqf, kdisj_apart_xB_eqf, lin_ge0B_eqf, bc_fk_mkbc] <;>
    try exact rfl

theorem disj_sidesB_eqf (fk : List kentry) : disj_sidesB (mkbc fk) = disj_sides fk := by
  funext kn b1 k1 n1
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KDisj c1 m1 c2 m2 =>
          simp only [disj_sidesB, disj_sides, sub_itvB_eqf, ih]
          try exact rfl
      | _ => simp only [disj_sidesB, disj_sides, ih]

theorem disj_sides_xB_eqf (fk : List kentry) :
    disj_sides_xB (mkbc fk) = disj_sides_x fk := by
  funext kn b1 k1 n1
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KDisj c1 m1 c2 m2 =>
          simp only [disj_sides_xB, disj_sides_x, sub_itv_xB_eqf, ih]
          try exact rfl
      | _ => simp only [disj_sides_xB, disj_sides_x, ih]

theorem in_sidesB_eqf (fk : List kentry) : in_sidesB (mkbc fk) = in_sides fk := by
  funext D b2 k2 n2
  induction D with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨c, m⟩ := t
      simp only [in_sidesB, in_sides, sub_itvB_eqf, ih]
      try exact rfl

theorem in_sides_xB_eqf (fk : List kentry) : in_sides_xB (mkbc fk) = in_sides_x fk := by
  funext D b2 k2 n2
  induction D with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨c, m⟩ := t
      simp only [in_sides_xB, in_sides_x, sub_itv_xB_eqf, ih]
      try exact rfl

theorem mk_sprepB_eqf (fk : List kentry) : mk_sprepB (mkbc fk) = mk_sprep fk := by
  funext b1 k1 n1
  cases n1 <;>
    simp only [mk_sprepB, mk_sprep, base_rangeB_eqf, xhiB_eqf, disj_sidesB_eqf,
      disj_sides_xB_eqf, bc_fk_mkbc] <;>
    try exact rfl

theorem ranges_apart_pB_eqf (fk : List kentry) :
    ranges_apart_pB (mkbc fk) = ranges_apart_p fk := by
  funext sp b1 k1 n1 b2 k2 n2
  cases n1 <;> cases n2 <;>
    simp only [ranges_apart_pB, ranges_apart_p, base_rangeB_eqf, xhiB_eqf, end_hiB_eqf,
      in_sidesB_eqf, in_sides_xB_eqf, lin_apartB_eqf, lin_ge0B_eqf] <;>
    try exact rfl

/-! ## B2: the expression simplifiers -/

/-- `coeffs_divkB`: every coefficient is a multiple of `m` (`0` when the
    atom is `2^k`-aligned). -/
def coeffs_divkB (bc : bctx) (m : Int) : List (Int × expr) → Bool
  | [] => true
  | (k, a) :: rest =>
      ((k % m == 0 || (k * zpow 2 (ealignB bc a)) % m == 0) && coeffs_divkB bc m rest)

/-- `lin_lowbits_knB`: the low `k` bits of `e` under the context's facts. -/
def lin_lowbits_knB (bc : bctx) (e : expr) (k : Int) : Option Int :=
  let l := lin_of e
  if coeffs_divkB bc (zpow 2 k) l.2 then some (l.1 % zpow 2 k)
  else pageup_low e (zpow 2 k)

/-- `lin_nowrap_lB`: `lin_nowrap` of a linear form given directly. -/
def lin_nowrap_lB (bc : bctx) (c : Int) (ts : List (Int × expr)) : Bool :=
  match lin_range (erangeB bc) c ts with
  | some (lo, hi) => (0 ≤ lo && hi < two64)
  | none => false

/-- `mkSrlB`: right shift of a symbolic value, kept linear where possible. -/
def mkSrlB (bc : bctx) (a : expr) (s : Int) : expr :=
  let l := lin_of a
  let m := zpow 2 s
  if (!(lin_trivial l) && coeffs_div m l.2 && lin_nowrapB bc a)
  then unlin (l.1 / m, ldiv_terms m l.2) -- any constant: floor
  else
    match (if (!(lin_trivial l) && lin_nowrapB bc a) then lsplit_divc m l.2 else ([], [])) with
    | (dts@(_ :: _), rts@(_ :: _)) =>
        match (if lin_nowrap_lB bc l.1 rts then erangeB bc (unlin (l.1, rts)) else none) with
        | some (lo, hi) =>
            if lo / m == hi / m then unlin (lo / m, ldiv_terms m dts)
            else mkAlu .SRL a (.ELit s)
        | none => mkAlu .SRL a (.ELit s)
    | _ => mkAlu .SRL a (.ELit s)

/-- `lowbitsB`: the low `j` bits of the value of `e` (P-c). -/
def lowbitsB (bc : bctx) (e : expr) (j : Int) : Option Int :=
  let m := zpow 2 j
  let dflt := if j ≤ ealignB bc e then some 0 else lin_lowbits_knB bc e j
  match e with
  | .ELit z => some ((z % two64) % m)
  | .EAlu .AND a (.ELit c) =>
      if (c % two64) % m == 0 then some 0
      else
        match lowbitsB bc a j with
        | some v => some (zland v ((c % two64) % m))
        | none => dflt
  | .EAlu .OR a (.ELit c) =>
      match lowbitsB bc a j with
      | some v => some (zlor v ((c % two64) % m))
      | none => dflt
  | .EAlu .XOR a (.ELit c) =>
      match lowbitsB bc a j with
      | some v => some (zlxor v ((c % two64) % m))
      | none => dflt
  | .EAlu .ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with
      | some x, some y => some ((x + y) % m)
      | _, _ => dflt
  | .EAlu .SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with
      | some x, some y => some ((x - y) % m)
      | _, _ => dflt
  | .EMd .MUL (.ELit c) a =>
      if (c % two64) % m == 0 then some 0
      else
        match lowbitsB bc a j with
        | some v => some ((c * v) % m)
        | none => dflt
  | _ => dflt

/-- `lsplit_divB`: split a term list by divisibility (task 5). -/
def lsplit_divB (bc : bctx) (m : Int) :
    List (Int × expr) → List (Int × expr) × List (Int × expr)
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest
      if (k % m == 0 || (k * zpow 2 (ealignB bc a)) % m == 0)
      then ((k, a) :: d, r) else (d, (k, a) :: r)

/-- `and_high_splitB`: `a AND -2^j` for `a` = A + R. -/
def and_high_splitB (bc : bctx) (bk : expr) (j c : Int)
    (dts rts : List (Int × expr)) : expr :=
  let m := zpow 2 j
  let cA := c - c % m
  let r := unlin (c % m, rts)
  match erangeB bc r with
  | some (lo, hi) =>
      if lo / m == hi / m then unlin (cA + (lo / m) * m, dts)
      else mkAlu .ADD (unlin (cA, dts)) (mkAlu .AND r bk)
  | none => mkAlu .ADD (unlin (cA, dts)) (mkAlu .AND r bk)

/-- `and_low_splitB`: the `2^j - 1` half of the split. -/
def and_low_splitB (bc : bctx) (bk : expr) (j c : Int)
    (rts : List (Int × expr)) : expr :=
  let m := zpow 2 j
  let r := unlin (c % m, rts)
  match erangeB bc r with
  | some (lo, hi) =>
      if lo / m == hi / m then unlin (c % m - (lo / m) * m, rts)
      else mkAlu .AND r bk
  | none => mkAlu .AND r bk

/-- `narrow_maskB`: masks of the form `2^j - 2^i` narrowed through `xhiB`. -/
def narrow_maskB (bc : bctx) (a : expr) (k' : Int) : Option Int :=
  let i := ctz64 k'
  let m := k' + zpow 2 i
  let j := zlog2 m
  if (0 < k' && m == zpow 2 j && j < 64) then
    match xhiB bc a with
    | some h => if h < zpow 2 j then some (two64 - zpow 2 i) else none
    | none => none
  else none

/-- `mkAnd0B`: AND with an alignment mask on a value known to be aligned. -/
def mkAnd0B (bc : bctx) (a b : expr) : expr :=
  match b with
  | .ELit k =>
      let k' := k % two64
      let j := zlog2 (two64 - k')
      if (two64 - k' == zpow 2 j && j < 64) then
        (if j ≤ ealignB bc a then a
         else
           let l := lin_of a
           if (!(lin_trivial l) && coeffs_divkB bc (zpow 2 j) l.2)
           then unlin (l.1 - l.1 % zpow 2 j, l.2)
           else
             match (if lin_trivial l then ([], l.2) else lsplit_divB bc (zpow 2 j) l.2) with
             | (dts@(_ :: _), rts@(_ :: _)) => and_high_splitB bc b j l.1 dts rts
             | _ => mkMd .MUL (.ELit (zpow 2 j)) (mkSrlB bc a j))
      else
        let j2 := zlog2 (k' + 1)
        if (k' + 1 == zpow 2 j2 && j2 < 64) then
          (if j2 ≤ ealignB bc a then .ELit 0
           else
             match lowbitsB bc a j2 with -- P-c
             | some v => .ELit v
             | none =>
               if lin_trivial (lin_of a) then mkAlu .AND a b
               else
                 match lin_lowbits_knB bc a j2 with
                 | some v => .ELit v
                 | none =>
                     match lsplit_divB bc (zpow 2 j2) (lin_of a).2 with
                     | (_ :: _, rts@(_ :: _)) => and_low_splitB bc b j2 (lin_of a).1 rts
                     | _ => mkAlu .AND a b)
        else
          let j3 := zlog2 k' + 1
          if (0 < k' && j3 ≤ 64 && !(lin_trivial (lin_of a))) then
            match lin_lowbits_knB bc a j3 with
            | some v => .ELit (zland v k')
            | none => mkAlu .AND a b
          else mkAlu .AND a b
  | _ => mkAlu .AND a b

/-- `mkAndB`: mask merge `(x & m1) & k = x & (m1 & k)` (R1'). -/
def mkAndB (bc : bctx) (a b : expr) : expr :=
  match b with
  | .ELit k =>
      match narrow_maskB bc a (k % two64) with
      | some m => mkAnd0B bc a (.ELit m)
      | none => mkAnd0B bc a b
  | _ => mkAnd0B bc a b

/-- `mkAndKB`: mask merge with the R6 spelling of `x & -2^i`. -/
def mkAndKB (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | .EAlu .AND x (.ELit m1), .ELit k =>
      mkAndB bc x (.ELit (zland (m1 % two64) (k % two64)))
  | .EMd .MUL (.ELit m) (.EAlu .SRL x (.ELit i)), .ELit k =>
      let i' := (i % two64) % 64
      if m % two64 == zpow 2 i' then
        mkAndB bc x (.ELit (zland (two64 - zpow 2 i') (k % two64)))
      else mkAndB bc a b
  | _, _ => mkAndB bc a b

/-- `or_disjointB`: OR of bit-disjoint operands is addition. -/
def or_disjointB (bc : bctx) (a b : expr) : Bool :=
  match erangeB bc b with
  | some (lo, hi) => (0 ≤ lo && hi < zpow 2 (ealignB bc a))
  | none => false

/-- `mkOrB`: the smart OR constructor. -/
def mkOrB (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zalu .OR x y)
  | _, _ =>
      if or_disjointB bc a b then mkAlu .ADD a b
      else if or_disjointB bc b a then mkAlu .ADD a b
      else
        match b with
        | .ELit c => mkAlu .ADD (mkAndKB bc a (.ELit (zlnot (c % two64)))) (.ELit c)
        | _ =>
            match a with
            | .ELit c => mkAlu .ADD (mkAndKB bc b (.ELit (zlnot (c % two64)))) (.ELit c)
            | _ => .EAlu .OR a b

theorem coeffs_divkB_eqf (fk : List kentry) : coeffs_divkB (mkbc fk) = coeffs_divk fk := by
  funext m ts
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨k, a⟩ := t
      simp only [coeffs_divkB, coeffs_divk, ealignB_eqf, ih]
      try exact rfl

theorem lin_lowbits_knB_eqf (fk : List kentry) :
    lin_lowbits_knB (mkbc fk) = lin_lowbits_kn fk := by
  funext e k
  simp only [lin_lowbits_knB, lin_lowbits_kn, coeffs_divkB_eqf]
  try exact rfl

theorem lin_nowrap_lB_eqf (fk : List kentry) :
    lin_nowrap_lB (mkbc fk) = lin_nowrap_l fk := by
  funext c ts
  simp only [lin_nowrap_lB, lin_nowrap_l, erangeB_eqf]
  try exact rfl

theorem mkSrlB_eqf (fk : List kentry) : mkSrlB (mkbc fk) = mkSrl fk := by
  funext a s
  simp only [mkSrlB, mkSrl, lin_nowrapB_eqf, lin_nowrap_lB_eqf, erangeB_eqf]
  try exact rfl

theorem lowbitsB_eqf (fk : List kentry) : lowbitsB (mkbc fk) = lowbits fk := by
  funext e j
  induction e with
  | ELit z => simp only [lowbitsB, lowbits]
  | EVar n =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      simp only [ealignB_eqf, lin_lowbits_knB_eqf]
  | EAlu op a b iha ihb =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      cases op <;> cases b <;>
        dsimp only <;>
        (try rw [ealignB_eqf]) <;> (try rw [lin_lowbits_knB_eqf]) <;>
        (try rw [iha]) <;> (try rw [ihb]) <;> (try exact rfl)
  | EAluw op a b iha ihb =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      simp only [ealignB_eqf, lin_lowbits_knB_eqf]
  | EMd op a b iha ihb =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      cases op <;> cases a <;> cases b <;>
        dsimp only <;>
        (try rw [ealignB_eqf]) <;> (try rw [lin_lowbits_knB_eqf]) <;>
        (try rw [iha]) <;> (try rw [ihb]) <;> (try exact rfl)
  | EMdw op a b iha ihb =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      simp only [ealignB_eqf, lin_lowbits_knB_eqf]
  | EExt sx lo n a ih =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      simp only [ealignB_eqf, lin_lowbits_knB_eqf]
  | EBlob sx k i n =>
      rw [lowbitsB.eq_def, lowbits.eq_def]
      simp only [ealignB_eqf, lin_lowbits_knB_eqf]

theorem lsplit_divB_eqf (fk : List kentry) : lsplit_divB (mkbc fk) = lsplit_div fk := by
  funext m ts
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨k, a⟩ := t
      simp only [lsplit_divB, lsplit_div, ealignB_eqf, ih]
      try exact rfl

theorem and_high_splitB_eqf (fk : List kentry) :
    and_high_splitB (mkbc fk) = and_high_split fk := by
  funext bk j c dts rts
  simp only [and_high_splitB, and_high_split, erangeB_eqf]
  try exact rfl

theorem and_low_splitB_eqf (fk : List kentry) :
    and_low_splitB (mkbc fk) = and_low_split fk := by
  funext bk j c rts
  simp only [and_low_splitB, and_low_split, erangeB_eqf]
  try exact rfl

theorem narrow_maskB_eqf (fk : List kentry) : narrow_maskB (mkbc fk) = narrow_mask fk := by
  funext a k'
  simp only [narrow_maskB, narrow_mask, xhiB_eqf]
  try exact rfl

theorem mkAnd0B_eqf (fk : List kentry) : mkAnd0B (mkbc fk) = mkAnd0 fk := by
  funext a b
  cases b with
  | ELit k =>
      simp only [mkAnd0B, mkAnd0, ealignB_eqf, coeffs_divkB_eqf, lsplit_divB_eqf,
        and_high_splitB_eqf, and_low_splitB_eqf, mkSrlB_eqf, lowbitsB_eqf,
        lin_lowbits_knB_eqf]
      try exact rfl
  | _ => simp only [mkAnd0B, mkAnd0]

theorem mkAndB_eqf (fk : List kentry) : mkAndB (mkbc fk) = mkAnd fk := by
  funext a b
  cases b with
  | ELit k =>
      simp only [mkAndB, mkAnd, narrow_maskB_eqf, mkAnd0B_eqf]
      try exact rfl
  | _ => simp only [mkAndB, mkAnd, mkAnd0B_eqf]

theorem mkAndKB_eqf (fk : List kentry) : mkAndKB (mkbc fk) = mkAndK fk := by
  funext a b
  cases a <;> cases b <;>
    simp only [mkAndKB, mkAndK, mkAndB_eqf] <;>
    try exact rfl

theorem or_disjointB_eqf (fk : List kentry) : or_disjointB (mkbc fk) = or_disjoint fk := by
  funext a b
  simp only [or_disjointB, or_disjoint, erangeB_eqf, ealignB_eqf]
  try exact rfl

theorem mkOrB_eqf (fk : List kentry) : mkOrB (mkbc fk) = mkOr fk := by
  funext a b
  cases a <;> cases b <;>
    simp only [mkOrB, mkOr, is_lit, or_disjointB_eqf, mkAndKB_eqf] <;>
    try exact rfl

/-! ### Sanity checks on the index plumbing (decidable, `by decide`) -/

/-- `lset`/`lget` round trip: the inserted element heads its bucket. -/
theorem lget_lset_check :
    lget (lset [[1, 2], [3]] 1 9 : List (List Nat)) 1 = [9, 3] := by decide

/-- ... and the other buckets are untouched. -/
theorem lget_lset_check_other :
    lget (lset [[1, 2], [3]] 1 9 : List (List Nat)) 0 = [1, 2] := by decide

/-- A bucket beyond the end reads as `[]`. -/
theorem lget_oob_check : lget ([[1], [2]] : List (List Nat)) 5 = [] := by decide

/-- `okey_eqb` is key equality on bucket keys. -/
theorem okey_eqb_check :
    okey_eqb (some 3) (some 3) = true ∧ okey_eqb (some 3) (some 4) = false ∧
      okey_eqb none none = true ∧ okey_eqb (some 0) none = false := by decide

/-- The range index of a two-fact list answers from the right bucket: the
    second `KRange` on `EVar 1` shadows nothing (the first hit wins), and a
    query on `EVar 0` never sees a fact about `EVar 1`. -/
theorem find_rangeI_check :
    find_rangeI (mk_ri [.KRange (.EVar 1) 10 20, .KRange (.EVar 0) 1 2]) (.EVar 1)
      = some (10, 20) ∧
    find_rangeI (mk_ri [.KRange (.EVar 1) 10 20]) (.EVar 0) = none := by decide

/-- The indexed scan and the linear scan agree on the same (empty) list. -/
theorem find_rangeI_nil_check (e : expr) :
    find_rangeI (mk_ri []) e = find_range [] e := find_rangeI_eq [] e

/-! ## B2 (second half): the concretizer, branch decision, smart constructors

     -/

/-- `conc_tryB`: the concretization sweep on the context's fact list. -/
def conc_tryB (bc : bctx) (e : expr) (cands : List expr) : Option Int :=
  match cands with
  | [] => none
  | s :: rest =>
      if closedb s then conc_tryB bc e rest
      else if !(evalS_def s e) then conc_tryB bc e rest
      else
        match erangeB bc s with
        | some (lo, hi) =>
            if hi - lo ≤ conc_limit then
              match evalS s (wrap64 lo) e with
              | some v =>
                  if (if hi < lo then true
                      else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2) else false) then
                    if all_eval_toS s e v lo (hi - lo + 1).toNat then some v
                    else conc_tryB bc e rest
                  else conc_tryB bc e rest
              | none => conc_tryB bc e rest
            else conc_tryB bc e rest
        | none => conc_tryB bc e rest

/-- `concretizeB`: the small-range sweep. -/
def concretizeB (bc : bctx) (e : expr) : Option Int :=
  if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e))

/-- `foldKB`: a value whose range is provably a single point IS that
    literal. -/
def foldKB (bc : bctx) (e : expr) : expr :=
  match e with
  | .ELit _ => e
  | _ =>
      match erangeB bc e with
      | some (lo, hi) =>
          if lo == hi then .ELit lo
          else match concretizeB bc e with | some v => .ELit v | none => e
      | none => match concretizeB bc e with | some v => .ELit v | none => e

/-- `lin_branchB`: (P-a) exact linear arithmetic on the difference. -/
def lin_branchB (bc : bctx) (c : BranchCond) (a b : expr) : Option Bool :=
  let ltu := if lin_ge0B bc [(b, -1)] [(a, 0)] then some true
             else if lin_ge0B bc [(a, 0)] [(b, 0)] then some false else none
  match c with
  | .LTU => ltu
  | .GEU => ltu.map (!·)
  | .LT | .GE =>
      match erangeB bc a, erangeB bc b with
      | some (_, ah), some (_, bh) =>
          if (ah < zpow 2 63 && bh < zpow 2 63)
          then match c with | .LT => ltu | _ => ltu.map (!·)
          else none
      | _, _ => none
  | .EQ | .NE =>
      if (lin_ge0B bc [(b, -1)] [(a, 0)] || lin_ge0B bc [(a, -1)] [(b, 0)])
      then some (match c with | .EQ => false | _ => true)
      else
        if (if lin_ge0B bc [(a, 0)] [(b, 0)] then lin_ge0B bc [(b, 0)] [(a, 0)] else false)
        then some (match c with | .EQ => true | _ => false)
        else none

/-- `decide_branchB`. -/
def decide_branchB (bc : bctx) (c : BranchCond) (a b : expr) : Option Bool :=
  match a, b with
  | .ELit x, .ELit y => some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then some (cond_on_eq c)
      else
        match diff_branch c a b with
        | some t => some t
        | none =>
            match (match erangeB bc a, erangeB bc b with
                   | some (al, ah), some (bl, bh) => range_branch c al ah bl bh
                   | _, _ => none) with
            | some t => some t
            | none => lin_branchB bc c a b

/-- `mkSltB`: SLT/SLTU as instructions decided like branches. -/
def mkSltB (bc : bctx) (c : BranchCond) (op : AluOp) (a b : expr) : expr :=
  match a, b with
  | .ELit _, .ELit _ => mkAlu op a b
  | _, _ =>
      match decide_branchB bc c a b with
      | some true => .ELit 1
      | some false => .ELit 0
      | none => mkAlu op a b

/-- `mkAluK0B`: the knowledge-aware smart ALU constructor. -/
def mkAluK0B (bc : bctx) (op : AluOp) (a b : expr) : expr :=
  match op with
  | .SLTU => mkSltB bc .LTU .SLTU a b
  | .SLT => mkSltB bc .LT .SLT a b
  | .AND =>
      match a, b with
      | .ELit _, .ELit _ => mkAndB bc a b
      | .ELit _, _ => mkAndKB bc b a -- literal mask on the right
      | _, _ => mkAndKB bc a b
  | .OR => if expr_eqb a b then a else mkOrB bc a b
  | .XOR =>
      if expr_eqb a b then .ELit 0
      else
        match is_lit a, b with
        | none, .ELit k =>
            if k % two64 == two64 - 1 then mkAlu .SUB (.ELit (two64 - 1)) a
            else mkAlu op a b
        | _, _ => mkAlu op a b
  | .SRL =>
      match is_lit a, shamt_of b 6 with
      | none, some s => mkSrlB bc a s
      | _, _ => mkAlu op a b
  | _ => mkAlu op a b

/-- `mkAluKB`. -/
def mkAluKB (bc : bctx) (op : AluOp) (a b : expr) : expr :=
  foldKB bc (mkAluK0B bc op a b)

/-- `mkMdKB`: unsigned division / remainder by a literal power of two. -/
def mkMdKB (bc : bctx) (op : MulOp) (a b : expr) : expr :=
  match is_lit a, op, b with
  | none, .REMU, .ELit m =>
      match pow2_log m with
      | some k => mkAluKB bc .AND a (.ELit (zpow 2 k - 1))
      | none => mkMd op a b
  | none, .DIVU, .ELit m =>
      match pow2_log m with
      | some k => mkAluKB bc .SRL a (.ELit k)
      | none => mkMd op a b
  | _, _, _ => mkMd op a b

/-- `zband32B`: the INTEGER linear form of `d` lies in `(-2^31, 2^31)`. -/
def zband32B (bc : bctx) (d : expr) : Bool :=
  let l := lin_of d
  match lin_range (erangeB bc) l.1 l.2 with
  | some (lo, hi) => (-(zpow 2 31) < lo && hi < zpow 2 31)
  | none => false

/-- `mkAluwK0B`: the knowledge-aware smart 32-bit ALU constructor. -/
def mkAluwK0B (bc : bctx) (op : AluOp) (a b : expr) : expr :=
  match op with
  | .ADD | .SUB =>
      let d := mkAlu op a b
      match is_lit d with
      | some v => .ELit (zsx32 v)
      | none =>
          match erangeB bc d with
          | some (lo, hi) =>
              if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
          | none => if zband32B bc d then d else mkAluw op a b
  | _ => mkAluw op a b

/-- `mkAluwKB`. -/
def mkAluwKB (bc : bctx) (op : AluOp) (a b : expr) : expr :=
  foldKB bc (mkAluwK0B bc op a b)

/-- `extK0B`: a zero/sign-extended low slice of a value provably below the
    slice's (signed) capacity is the value itself. -/
def extK0B (bc : bctx) (v : expr) : expr :=
  match v with
  | .EExt sx 0 n e =>
      if n ≤ 7 then
        match erangeB bc e with
        | some (lo, hi) =>
            if hi < (if sx then zpow 2 (8 * (n : Int)) / 2 else zpow 2 (8 * (n : Int))) then e else v
        | none => v
      else v
  | _ => v

/-- `extKB`. -/
def extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v)

/-- `flat_scB`: flatness obligation for an `n`-byte access at `a`, unless the
    known interval bounds already decide it. -/
def flat_scB (bc : bctx) (a : saddr) (n : Nat) : List sidecond :=
  match base_rangeB bc a.a_base with
  | some (lo, hi) =>
      if (0 ≤ lo + a.a_off && hi + a.a_off + (n : Int) ≤ 2 ^ 64)
      then [] else [.SCFlat a (elen n)]
  | none => [.SCFlat a (elen n)]

/-- `wr_coveredB`: writability obligation, unless a `KWr` window covers the
    range (the window's length may be symbolic: its lower bound is used). -/
def wr_coveredB (bc : bctx) (kn : List kentry) (a : saddr) (n : Nat) : Bool :=
  match kn with
  | [] => false
  | .KWr ⟨kb, kk⟩ len :: rest =>
      if (if (expr_eqb a.a_base kb && kk ≤ a.a_off) then
            match xloB bc len with
            | some l => a.a_off + (n : Int) ≤ kk + l
            | none => false
          else false)
      then true
      else if xinsideB bc a.a_base a.a_off (.ELit (n : Int)) kb kk len then true
      else wr_coveredB bc rest a n
  | _ :: rest => wr_coveredB bc rest a n

/-- `storeok_scB`: the store-ok obligation list. -/
def storeok_scB (bc : bctx) (a : saddr) (n : Nat) : List sidecond :=
  if wr_coveredB bc bc.bc_fk a n then [] else [.SCStoreOk a n]

/-- `conc_exprB`: a register value replaced by its literal, when provable. -/
def conc_exprB (bc : bctx) (e : expr) : expr :=
  match e with
  | .ELit _ => e
  | _ => match concretizeB bc e with | some v => .ELit v | none => e

/-- `enum_branchB`: decide a branch by enumeration. -/
def enum_branchB (bc : bctx) (c : BranchCond) (a b : expr) : Option Bool :=
  let (e, pos) := cond_probe c a b
  match concretizeB bc e with
  | some v =>
      let z := (v % two64 == 0)
      some (if pos then !z else z)
  | none => none

/-- `to_saddrKB`: address formation with concretization of a non-literal
    base. -/
def to_saddrKB (bc : bctx) (e : expr) (imm : Int) : saddr :=
  match split_lit e with
  | (.ELit _, _) => to_saddr e imm
  | _ =>
      match concretizeB bc (mkAlu .ADD e (.ELit imm)) with
      | some v => SA (.ELit 0) v
      | none => to_saddr e imm

/-- `amo_alignedbB`: the ISA's `amo_aligned wd a` decided from the linear
    form / alignment facts of the address expression. -/
def amo_alignedbB (bc : bctx) (e : expr) (wd : AWidth) : Bool :=
  match lin_lowbits_knB bc e (match wd with | .W => 2 | .D => 3) with
  | some r => r == 0
  | none => false

/-- `amo_newvalB`: the value an AMO stores. -/
def amo_newvalB (bc : bctx) (wd : AWidth) (aop : Option AluOp) (old src : expr) : expr :=
  match aop with
  | none => src
  | some o => match wd with | .W => mkAluwKB bc o old src | .D => mkAluKB bc o old src

/-! #### Bridge for the `implicit_reducible` match auxiliaries

    A recursive definition's compiled matcher is `implicit_reducible`, so
    `rfl` cannot see through it.  `erange_fB`'s (shared by every `match
    erangeB .. with some (lo, hi)`) and the reference `erange_f`'s are the
    same function; this equation says so once. -/

theorem erange_fB_match_1 (motive : Option (Int × Int) → Sort u) (x : Option (Int × Int))
    (h1 : (lo hi : Int) → motive (some (lo, hi))) (h2 : Unit → motive none) :
    @erange_fB.match_1 motive x h1 h2 = @erange_f.match_1 motive x h1 h2 := by
  cases x with
  | none => rfl
  | some p =>
      obtain ⟨lo, hi⟩ := p
      rfl

/-! #### The second half of B2 equals its reference -/

theorem conc_tryB_eqf (fk : List kentry) : conc_tryB (mkbc fk) = conc_try fk := by
  funext e cands
  induction cands with
  | nil => rfl
  | cons s rest ih =>
      simp only [conc_tryB, conc_try, erangeB_eqf, ih]
      try exact rfl

theorem concretizeB_eqf (fk : List kentry) : concretizeB (mkbc fk) = concretize fk := by
  funext e
  simp only [concretizeB, concretize, conc_tryB_eqf]
  try exact rfl

theorem foldKB_eqf (fk : List kentry) : foldKB (mkbc fk) = foldK fk := by
  funext e
  simp only [foldKB, foldK, erangeB_eqf, concretizeB_eqf]
  try exact rfl

theorem lin_branchB_eqf (fk : List kentry) : lin_branchB (mkbc fk) = lin_branch fk := by
  funext c a b
  simp only [lin_branchB, lin_branch, lin_ge0B_eqf, erangeB_eqf]
  try exact rfl

theorem decide_branchB_eqf (fk : List kentry) :
    decide_branchB (mkbc fk) = decide_branch fk := by
  funext c a b
  cases a <;> cases b <;>
    simp only [decide_branchB, decide_branch, erangeB_eqf] <;>
    simp only [lin_branchB_eqf] <;>
    try exact rfl

theorem mkSltB_eqf (fk : List kentry) : mkSltB (mkbc fk) = mkSlt fk := by
  funext c op a b
  cases a <;> cases b <;>
    simp only [mkSltB, mkSlt, decide_branchB_eqf] <;>
    try exact rfl

theorem mkAluK0B_eqf (fk : List kentry) : mkAluK0B (mkbc fk) = mkAluK0 fk := by
  funext op a b
  cases op <;> cases a <;> cases b <;>
    simp only [mkAluK0B, mkAluK0, mkSltB_eqf, mkAndB_eqf, mkAndKB_eqf, mkOrB_eqf,
      mkSrlB_eqf] <;>
    try exact rfl

theorem mkAluKB_eqf (fk : List kentry) : mkAluKB (mkbc fk) = mkAluK fk := by
  funext op a b
  simp only [mkAluKB, mkAluK, mkAluK0B_eqf, foldKB_eqf]
  try exact rfl

theorem mkMdKB_eqf (fk : List kentry) : mkMdKB (mkbc fk) = mkMdK fk := by
  funext op a b
  cases op <;> cases a <;> cases b <;>
    simp only [mkMdKB, mkMdK, mkAluKB_eqf] <;>
    try exact rfl

theorem zband32B_eqf (fk : List kentry) : zband32B (mkbc fk) = zband32 fk := by
  funext d
  have h : ∀ c ts,
      lin_range (erangeB (mkbc fk)) c ts = lin_range (erange fk) c ts :=
    fun c ts => lin_range_ext (fun a => congrFun (erangeB_eqf fk) a)
  simp only [zband32B, zband32, h, erange_fB_match_1]

theorem mkAluwK0B_eqf (fk : List kentry) : mkAluwK0B (mkbc fk) = mkAluwK0 fk := by
  funext op a b
  cases op <;>
    simp only [mkAluwK0B, mkAluwK0, erangeB_eqf, zband32B_eqf] <;>
    try exact rfl

theorem mkAluwKB_eqf (fk : List kentry) : mkAluwKB (mkbc fk) = mkAluwK fk := by
  funext op a b
  simp only [mkAluwKB, mkAluwK, mkAluwK0B_eqf, foldKB_eqf]
  try exact rfl

theorem extK0B_eqf (fk : List kentry) : extK0B (mkbc fk) = extK0 fk := by
  funext v
  cases v <;> simp only [extK0B, extK0, erangeB_eqf] <;> try exact rfl

theorem extKB_eqf (fk : List kentry) : extKB (mkbc fk) = extK fk := by
  funext v
  simp only [extKB, extK, extK0B_eqf, foldKB_eqf]
  try exact rfl

theorem flat_scB_eqf (fk : List kentry) : flat_scB (mkbc fk) = flat_sc fk := by
  funext a n
  simp only [flat_scB, flat_sc, base_rangeB_eqf]
  try exact rfl

theorem wr_coveredB_eqf (fk : List kentry) : wr_coveredB (mkbc fk) = wr_covered fk := by
  funext kn a n
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      cases K with
      | KWr sa len =>
          obtain ⟨kb, kk⟩ := sa
          simp only [wr_coveredB, wr_covered, xloB_eqf, xinsideB_eqf, ih]
          try exact rfl
      | _ => simp only [wr_coveredB, wr_covered, ih]

theorem storeok_scB_eqf (fk : List kentry) : storeok_scB (mkbc fk) = storeok_sc fk := by
  funext a n
  simp only [storeok_scB, storeok_sc, wr_coveredB_eqf, bc_fk_mkbc]
  try exact rfl

theorem conc_exprB_eqf (fk : List kentry) : conc_exprB (mkbc fk) = conc_expr fk := by
  funext e
  cases e <;> simp only [conc_exprB, conc_expr, concretizeB_eqf] <;> try exact rfl

theorem enum_branchB_eqf (fk : List kentry) : enum_branchB (mkbc fk) = enum_branch fk := by
  funext c a b
  simp only [enum_branchB, enum_branch, concretizeB_eqf]
  try exact rfl

theorem to_saddrKB_eqf (fk : List kentry) : to_saddrKB (mkbc fk) = to_saddrK fk := by
  funext e imm
  simp only [to_saddrKB, to_saddrK, concretizeB_eqf]
  try exact rfl

theorem amo_alignedbB_eqf (fk : List kentry) : amo_alignedbB (mkbc fk) = amo_alignedb fk := by
  funext e wd
  cases wd <;> simp only [amo_alignedbB, amo_alignedb, lin_lowbits_knB_eqf] <;> try exact rfl

theorem amo_newvalB_eqf (fk : List kentry) : amo_newvalB (mkbc fk) = amo_newval fk := by
  funext wd aop old src
  cases wd <;> cases aop <;>
    simp only [amo_newvalB, amo_newval, mkAluKB_eqf, mkAluwKB_eqf] <;>
    try exact rfl

/-! ## B3: the read paths (`log_lookupB`, `know_lookupA0B`, `sym_readB`,
    `sym_stepB`) —  -/

/-- `log_lookupB`: the store-log walk on the context's fact list. -/
def log_lookupB (bc : bctx) (log : List sentry) (rb : expr) (rk : Int) (n : Nat) (sx : Bool)
    (hints : List Bool) (acc : List sidecond) : lres :=
  match log with
  | [] => .LMiss acc hints
  | ⟨⟨kb, kk⟩, w, v⟩ :: rest =>
      match rel_lit rb rk (n : Int) kb kk (w : Int) with
      | .RInside d => .LHit (mkExt sx d.toNat n v) acc hints
      | .RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | .RPartial =>
          match log_bytes_lit log rb rk n with
          | some bs => .LHit (lit_of_bytes sx n bs) acc hints
          | none => .LStuck
      | .RUnknown =>
          if ranges_apartB bc rb rk (n : Int) kb kk (w : Int)
          then log_lookupB bc rest rb rk n sx hints acc
          else
            match hints with
            | false :: _ => .LStuck
            | _ => log_lookupB bc rest rb rk n sx hints.tail
                     (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)

/-- `know_lookupA0B`: consult the knowledge list (order = priority). -/
def know_lookupA0B (bc : bctx) (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  match kn with
  | [] => .LMiss acc hints
  | K :: rest =>
      match K with
      | .KWord ⟨kb, kk⟩ w v =>
          match rel_lit rb rk (n : Int) kb kk (w : Int) with
          | .RInside d => .LHit (mkExt sx d.toNat n v) acc hints
          | _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KZero ⟨kb, kk⟩ len =>
          match len with
          | .ELit l0 =>
              match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
              | .RInside _ => .LHit (.ELit 0) acc hints
              | .RDisjoint | .RPartial => know_lookupA0B bc segs rest rb rk n sx hints acc
              | .RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then .LHit (.ELit 0) acc hints
                  else
                    match hints with
                    | true :: hs => .LHit (.ELit 0) (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0B bc segs rest rb rk n sx hs acc
                    | [] => know_lookupA0B bc segs rest rb rk n sx [] acc
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then .LHit (.ELit 0) acc hints
              else
                match hints with
                | true :: hs => .LHit (.ELit 0) (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                | false :: hs => know_lookupA0B bc segs rest rb rk n sx hs acc
                | [] => know_lookupA0B bc segs rest rb rk n sx [] acc
      | .KFill ⟨kb, kk⟩ len c =>
          let hit := fill_lit sx n c
          match len with
          | .ELit l0 =>
              match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
              | .RInside _ => .LHit hit acc hints
              | .RDisjoint | .RPartial => know_lookupA0B bc segs rest rb rk n sx hints acc
              | .RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then .LHit hit acc hints
                  else
                    match hints with
                    | true :: hs => .LHit hit (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0B bc segs rest rb rk n sx hs acc
                    | [] => know_lookupA0B bc segs rest rb rk n sx [] acc
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then .LHit hit acc hints
              else
                match hints with
                | true :: hs => .LHit hit (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                | false :: hs => know_lookupA0B bc segs rest rb rk n sx hs acc
                | [] => know_lookupA0B bc segs rest rb rk n sx [] acc
      | .KUnk _ _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KBlob ⟨kb, kk⟩ len k =>
          if expr_eqb rb kb then
            if kk ≤ rk then
              match len with
              | .ELit l0 =>
                  if rk + (n : Int) ≤ kk + (l0 % two64)
                  then .LHit (.EBlob sx k (rk - kk) n) acc hints
                  else if kk + (l0 % two64) ≤ rk then know_lookupA0B bc segs rest rb rk n sx hints acc
                  else .LStuck
              | _ =>
                  if (let ins : Bool := (match erangeB bc len with
                                         | some (lo, _) => rk + (n : Int) ≤ kk + lo
                                         | none => false)
                      ins) then .LHit (.EBlob sx k (rk - kk) n) acc hints
                  else
                    match hints with
                    | true :: hs => .LHit (.EBlob sx k (rk - kk) n)
                                      (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0B bc segs rest rb rk n sx hs acc
                    | [] => know_lookupA0B bc segs rest rb rk n sx [] acc
            else know_lookupA0B bc segs rest rb rk n sx hints acc
          else know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KImg lo hi =>
          match rb with
          | .ELit 0 =>
              if (lo ≤ rk && rk + (n : Int) ≤ hi) then
                match img_bytes segs rk n with
                | some bs => .LHit (lit_of_bytes sx n bs) acc hints
                | none => .LStuck
              else know_lookupA0B bc segs rest rb rk n sx hints acc
          | _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KAlign _ _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KRange _ _ _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KWr _ _ => know_lookupA0B bc segs rest rb rk n sx hints acc
      | .KDisj _ _ _ _ => know_lookupA0B bc segs rest rb rk n sx hints acc

/-- `know_lookupAB`: ... plus the bytewise literal composition. -/
def know_lookupAB (bc : bctx) (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  match know_lookupA0B bc segs kn rb rk n sx hints acc with
  | .LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | some bs => .LHit (lit_of_bytes sx n bs) acc' hints'
      | none => .LMiss acc' hints'
  | r => r

/-- `sym_readB`: log first, then knowledge, then the `SCReadBase` fallback. -/
def sym_readB (segs : List Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
    (a : saddr) (n : Nat) (sx' : Bool) :
    Option (expr × List sidecond × scripts × Nat) :=
  match log_lookupB bc ss.s_log a.a_base a.a_off n sx' scr.sc_hints [] with
  | .LStuck => none
  | .LHit v scs hints =>
      some (extKB bc v, flat_scB bc a n ++ scs, SCR scr.sc_dirs scr.sc_reads hints, ss.s_next)
  | .LMiss scs hints =>
      match know_lookupAB bc segs ss.s_know a.a_base a.a_off n sx' hints scs with
      | .LStuck => none
      | .LHit v scs' hints' =>
          some (extKB bc v, flat_scB bc a n ++ scs', SCR scr.sc_dirs scr.sc_reads hints', ss.s_next)
      | .LMiss scs' hints' =>
          let i := ss.s_next
          let rv := match scr.sc_reads with | [] => .EVar i | e :: _ => e
          let reads' := match scr.sc_reads with | [] => [] | _ :: t => t
          some (rv, flat_scB bc a n ++ .SCReadBase a n sx' rv :: scs',
                SCR scr.sc_dirs reads' hints', i + 1)

/-- `sym_stepB`: the symbolic stepper with the block context threaded
    through.  Instruction for instruction `sym_step`, with `..B` lookups. -/
def sym_stepB (bc : bctx) (segs : List Segment) (i : Instr) (ss : sym_state)
    (scr : scripts) : stepres :=
  let g r := sr_get ss.s_regs r
  let p := ss.s_pc
  match i with
  | .opImm op rd rs imm => .SOk (sset ss rd (mkAluKB bc op (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm op rd rs sh =>
      .SOk (sset ss rd (mkAluKB bc op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op op rd rs1 rs2 => .SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .opImm32 rd rs imm =>
      .SOk (sset ss rd (mkAluwKB bc .ADD (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm32 op rd rs sh =>
      .SOk (sset ss rd (mkAluw op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op32 op rd rs1 rs2 => .SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul op rd rs1 rs2 => .SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul32 op rd rs1 rs2 => .SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | .lui rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | .auipc rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | .jal rd imm =>
      .SOk (sset ss rd (.ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | .jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | .ELit z =>
          .SOk (sset ss rd (.ELit (p + 4)) (AxSymExec3.zland_m2 (bv_wrap 64 z + bv_signed imm) % 2 ^ 64)) [] scr
      | _ => .SStop
  | .branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm))
      let a := g rs1
      let b := g rs2
      match (match decide_branchB bc c a b with
             | some t => some t
             | none =>
                 match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                 | some t => some t
                 | none => enum_branchB bc c a b) with
      | some t => .SOk (sjump ss (if t then tk else p + 4)) [] scr
      | none =>
          match scr.sc_dirs with
          | [] => .SStop
          | t :: dirs' =>
              .SOk (sjump ss (if t then tk else p + 4)) [.SCBr t c a b]
                  (SCR dirs' scr.sc_reads scr.sc_hints)
  | .fence _ _ _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .fenceI _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .load sz sx rd rs imm =>
      let n := msize_bytes sz
      let sx' := match sz with | .SZ8 => false | _ => sx
      let a := to_saddrKB bc (g rs) (bv_signed imm)
      match sym_readB segs ss bc scr a n sx' with
      | none => .SStop
      | some (v, scs, scr', nx') =>
          .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                   ss.s_log, ss.s_know, nx', ss.s_resv⟩ scs scr'
  | .store sz rs1 rs2 imm =>
      let n := msize_bytes sz
      let a := to_saddrKB bc (g rs1) (bv_signed imm)
      match resv_inval ss.s_resv a with
      | none => .SStop
      | some r' =>
          .SOk ⟨p + 4, ss.s_regs, SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, r'⟩
              (flat_scB bc a n ++ storeok_scB bc a n) scr
  -- ---- A extension ----
  | .lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0
        match sym_readB segs ss bc scr a n (amo_sx wd) with
        | none => .SStop
        | some (v, scs, scr', nx') =>
            .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                     ss.s_log, ss.s_know, nx', some a⟩ scs scr'
      else .SStop
  | .sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs1
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0
        match ss.s_resv with
        | some r =>
            if saddr_eqb r a then
              .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs
                            else sr_upd ss.s_regs (ridx rd) (.ELit 0)),
                     SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, none⟩
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else .SStop
        | none => .SStop
      else .SStop
  | .amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | none => .SStop
      | some aop =>
          let n := msize_bytes (amo_sz wd)
          let e := g rs1
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0
            match resv_inval ss.s_resv a with
            | none => .SStop
            | some r' =>
                match sym_readB segs ss bc scr a n (amo_sx wd) with
                | none => .SStop
                | some (vold, scs, scr', nx') =>
                    .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) vold),
                             SE a n (amo_newvalB bc wd aop vold (g rs2)) :: ss.s_log,
                             ss.s_know, nx', r'⟩
                        (scs ++ storeok_scB bc a n) scr'
          else .SStop
  | _ => .SStop

/-- `know_lookupB`: the knowledge lookup on the context's own list. -/
def know_lookupB (segs : List Segment) (bc : bctx) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  know_lookupAB bc segs bc.bc_fk rb rk n sx hints acc

theorem log_lookupB_eqf (fk : List kentry) : log_lookupB (mkbc fk) = log_lookup fk := by
  funext log rb rk n sx hints acc
  induction log generalizing hints acc with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | mk a w v =>
        cases a with
        | mk kb kk =>
          cases rel_lit rb rk (n : Int) kb kk (w : Int) <;>
            simp only [log_lookupB, log_lookup, ranges_apartB_eqf, ih] <;>
            (try cases log_bytes_lit ({ e_addr := { a_base := kb, a_off := kk },
                                        e_width := w, e_val := v } :: rest) rb rk n) <;>
            (try cases hints with
             | nil => simp only [ih]
             | cons b t => (try cases b) <;> simp only [ih]) <;>
            try exact rfl

theorem know_lookupA0B_eqf (fk : List kentry) : know_lookupA0B (mkbc fk) = know_lookupA0 fk := by
  funext segs kn rb rk n sx hints acc
  induction kn generalizing hints acc with
  | nil => rfl
  | cons K rest ih =>
      cases K <;>
        simp only [know_lookupA0B, know_lookupA0, xinsideB_eqf, erangeB_eqf, ih] <;>
        try (with_unfolding_all exact rfl)

theorem know_lookupAB_eqf (fk : List kentry) : know_lookupAB (mkbc fk) = know_lookupA fk := by
  funext segs kn rb rk n sx hints acc
  simp only [know_lookupAB, know_lookupA, know_lookupA0B_eqf]
  try (with_unfolding_all exact rfl)

theorem sym_readB_eqf (fk : List kentry) (segs : List Segment) (ss : sym_state) :
    sym_readB segs ss (mkbc fk) = sym_read segs ss fk := by
  funext scr a n sx'
  simp only [sym_readB, sym_read, log_lookupB_eqf, know_lookupAB_eqf, extKB_eqf, flat_scB_eqf]
  try (with_unfolding_all exact rfl)

theorem know_lookupB_eqf (fk : List kentry) (segs : List Segment) :
    know_lookupB segs (mkbc fk) = know_lookup segs fk := by
  funext rb rk n sx hints acc
  simp only [know_lookupB, know_lookup, bc_fk_mkbc, know_lookupAB_eqf]
  try exact rfl

/-- `sym_stepB` is `sym_step` at the block context of the state's facts. -/
theorem sym_stepB_eq (segs : List Segment) (i : Instr) (ss : sym_state) (scr : scripts) :
    sym_stepB (mkbc (facts_of ss.s_know)) segs i ss scr = sym_step segs i ss scr := by
  simp only [sym_stepB, sym_step, mkAluKB_eqf, mkAluwK0B_eqf, mkAluwKB_eqf, mkMdKB_eqf,
    conc_exprB_eqf, decide_branchB_eqf, enum_branchB_eqf, sym_readB_eqf, to_saddrKB_eqf,
    amo_alignedbB_eqf, amo_newvalB_eqf, flat_scB_eqf, storeok_scB_eqf]
  try (with_unfolding_all exact rfl)

/-! ## B4: the knowledge load index (`kix`) — 

    `know_lookupA0B` walks the whole knowledge list for every load.  The
    index digests the list ONCE per block (entries tagged with their
    position): literal-address cells that fit in at most two 4 KiB granules
    go to a granule-keyed trie, the entries that are candidates for EVERY
    literal-address query form the "wide" list, and a literal query merges
    its granule's bucket with the wide list by position — exactly the
    sub-sequence of candidates, in the original order.  Hits, values and
    side conditions are unchanged (`know_lookupA0I_eq`, see the note on
    what is deferred at the end of this section). -/

/-- `gran`: the 4 KiB granule of an address. -/
def gran (a : Int) : Int := a / 4096

/-- Is the expression the literal zero (the absolute-address base)? -/
def is_lit0 (e : expr) : Bool := match e with | .ELit 0 => true | _ => false

/-- Literal extent `[s, e)` of a literal-address entry (`none`: not such an
    entry). -/
def lit0_extent (K : kentry) : Option (Int × Int) :=
  match K with
  | .KWord ⟨.ELit 0, kk⟩ w _ => some (kk, kk + (w : Int))
  | .KZero ⟨.ELit 0, kk⟩ (.ELit l0) => some (kk, kk + zmod64 l0)
  | .KFill ⟨.ELit 0, kk⟩ (.ELit l0) _ => some (kk, kk + zmod64 l0)
  | .KBlob ⟨.ELit 0, kk⟩ (.ELit l0) _ => some (kk, kk + zmod64 l0)
  | .KImg lo hi => some (lo, hi)
  | _ => none

/-- The extent is non-empty and spans at most two granules. -/
def ext_fits (s e : Int) : Bool := if s < e then gran (e - 1) - gran s ≤ 1 else false

/-- The extent touches granule `g`. -/
def ext_has (s e g : Int) : Bool := if g == gran s then true else g == gran (e - 1)

/-- Candidates for EVERY literal-address query. -/
def kx_wide0 (K : kentry) : Bool :=
  match lit0_extent K with
  | some (s, e) => !(ext_fits s e)
  | none =>
      match K with
      | .KZero ⟨kb, _⟩ _ | .KFill ⟨kb, _⟩ _ _ => true
      | .KBlob ⟨kb, _⟩ _ _ => is_lit0 kb
      | _ => false

/-- Candidates for a literal-address query in granule `g`. -/
def kx_cand0 (g : Int) (K : kentry) : Bool :=
  match lit0_extent K with
  | some (s, e) => if ext_fits s e then ext_has s e g else true
  | none => kx_wide0 K

/-- Candidates for a query with a non-literal base. -/
def kx_candf (K : kentry) : Bool :=
  match K with
  | .KWord ⟨kb, _⟩ _ _ | .KBlob ⟨kb, _⟩ _ _ => !(is_lit0 kb)
  | .KZero _ _ | .KFill _ _ _ => true
  | _ => false

/-- Trie key of a granule.  Injective. -/
def kx_gkey (g : Int) : Nat :=
  if g = 0 then 1 else if 0 < g then 2 * g.toNat else 2 * (-g).toNat + 1

/-- The knowledge load index. -/
structure kix where
  /-- the indexed list itself -/
  kx_kn : List kentry
  /-- wide entries (every literal query), tagged with their position -/
  kx_w0 : List (Nat × kentry)
  /-- granule -> fitting literal cells of that granule, tagged -/
  kx_gran : ptree (List (Nat × kentry))
  /-- candidates of a non-literal-base query -/
  kx_wf : List kentry

/-- `KX` — the record constructor. -/
abbrev KX (kn : List kentry) (w0 : List (Nat × kentry))
    (gr : ptree (List (Nat × kentry))) (wf : List kentry) : kix := ⟨kn, w0, gr, wf⟩

/-- The bucket of granule `g`. -/
def kx_bucket (t : ptree (List (Nat × kentry))) (g : Int) : List (Nat × kentry) :=
  match pt_get t (kx_gkey g) with | some b => b | none => []

/-- Push `x` onto the bucket of granule `g`. -/
def kx_add (g : Int) (x : Nat × kentry) (t : ptree (List (Nat × kentry))) :
    ptree (List (Nat × kentry)) :=
  pt_set (kx_gkey g) (x :: kx_bucket t g) t

/-- One digest pass. -/
def kx_build (kn : List kentry) (i : Nat) :
    List (Nat × kentry) × ptree (List (Nat × kentry)) × List kentry :=
  match kn with
  | [] => ([], .PTLeaf, [])
  | K :: rest =>
      let (w0, gr, wf) := kx_build rest (i + 1)
      let wf' := if kx_candf K then K :: wf else wf
      match lit0_extent K with
      | some (s, e) =>
          if ext_fits s e then
            let g1 := gran s
            let g2 := gran (e - 1)
            let gr1 := kx_add g1 (i, K) gr
            (w0, (if g1 == g2 then gr1 else kx_add g2 (i, K) gr1), wf')
          else ((i, K) :: w0, gr, wf')
      | none => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')

/-- `mk_kix`: the index of a knowledge list. -/
def mk_kix (kn : List kentry) : kix :=
  let r := kx_build kn 1
  ⟨kn, r.1, r.2.1, r.2.2⟩

/-- Merge by position (both lists strictly increasing), dropping the tags.
 Same
    function, same values. -/
def kx_merge : List (Nat × kentry) → List (Nat × kentry) → List kentry
  | [], l2 => l2.map Prod.snd
  | (p1, K1) :: r1, [] => K1 :: r1.map Prod.snd
  | (p1, K1) :: r1, (p2, K2) :: r2 =>
      if p1 < p2 then K1 :: kx_merge r1 ((p2, K2) :: r2)
      else K2 :: kx_merge ((p1, K1) :: r1) r2
termination_by l1 l2 => l1.length + l2.length
decreasing_by all_goals simp_wf

/-- The knowledge list, tagged with its positions (from `i`). -/
def tagged (kn : List kentry) (i : Nat) : List (Nat × kentry) :=
  match kn with
  | [] => []
  | K :: rest => (i, K) :: tagged rest (i + 1)

/-- Every tag in `l` is greater than `i` (: `Forall (fun t => i < fst t)`). -/
def all_gt (i : Nat) (l : List (Nat × kentry)) : Prop := ∀ t ∈ l, i < t.1

/-- Candidates for a literal-address query in granule `g` that are NOT wide. -/
def narrow_in (g : Int) (K : kentry) : Bool :=
  match lit0_extent K with
  | some (s, e) => if ext_fits s e then ext_has s e g else false
  | none => false

/-- The candidate sub-sequence for a query. -/
def kx_select (kx : kix) (rb : expr) (rk : Int) : List kentry :=
  if is_lit0 rb then kx_merge (kx_bucket kx.kx_gran (gran rk)) kx.kx_w0
  else kx.kx_wf

/-- `know_lookupA0I`: the reference walk on the index-selected candidates. -/
def know_lookupA0I (bc : bctx) (kx : kix) (segs : List Segment) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  match hints, n with
  | [], _ + 1 => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
  | _, _ => know_lookupA0B bc segs kx.kx_kn rb rk n sx hints acc

/-- `know_lookupABI`: ... plus the bytewise literal composition. -/
def know_lookupABI (bc : bctx) (kx : kix) (segs : List Segment) (kn : List kentry)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool)
    (acc : List sidecond) : lres :=
  match know_lookupA0I bc kx segs rb rk n sx hints acc with
  | .LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | some bs => .LHit (lit_of_bytes sx n bs) acc' hints'
      | none => .LMiss acc' hints'
  | r => r

/-- `sym_readBI`: `sym_readB` with the index. -/
def sym_readBI (segs : List Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
    (a : saddr) (n : Nat) (sx' : Bool) :
    Option (expr × List sidecond × scripts × Nat) :=
  match log_lookupB bc ss.s_log a.a_base a.a_off n sx' scr.sc_hints [] with
  | .LStuck => none
  | .LHit v scs hints =>
      some (extKB bc v, flat_scB bc a n ++ scs, SCR scr.sc_dirs scr.sc_reads hints, ss.s_next)
  | .LMiss scs hints =>
      match know_lookupABI bc kx segs ss.s_know a.a_base a.a_off n sx' hints scs with
      | .LStuck => none
      | .LHit v scs' hints' =>
          some (extKB bc v, flat_scB bc a n ++ scs', SCR scr.sc_dirs scr.sc_reads hints', ss.s_next)
      | .LMiss scs' hints' =>
          let i := ss.s_next
          let rv := match scr.sc_reads with | [] => .EVar i | e :: _ => e
          let reads' := match scr.sc_reads with | [] => [] | _ :: t => t
          some (rv, flat_scB bc a n ++ .SCReadBase a n sx' rv :: scs',
                SCR scr.sc_dirs reads' hints', i + 1)

/-- `sym_stepBI`: `sym_stepB` with the index. -/
def sym_stepBI (bc : bctx) (kx : kix) (segs : List Segment) (i : Instr) (ss : sym_state)
    (scr : scripts) : stepres :=
  let g r := sr_get ss.s_regs r
  let p := ss.s_pc
  match i with
  | .opImm op rd rs imm => .SOk (sset ss rd (mkAluKB bc op (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm op rd rs sh =>
      .SOk (sset ss rd (mkAluKB bc op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op op rd rs1 rs2 => .SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .opImm32 rd rs imm =>
      .SOk (sset ss rd (mkAluwKB bc .ADD (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm32 op rd rs sh =>
      .SOk (sset ss rd (mkAluw op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op32 op rd rs1 rs2 => .SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul op rd rs1 rs2 => .SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul32 op rd rs1 rs2 => .SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | .lui rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | .auipc rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | .jal rd imm =>
      .SOk (sset ss rd (.ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | .jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | .ELit z =>
          .SOk (sset ss rd (.ELit (p + 4)) (AxSymExec3.zland_m2 (bv_wrap 64 z + bv_signed imm) % 2 ^ 64)) [] scr
      | _ => .SStop
  | .branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm))
      let a := g rs1
      let b := g rs2
      match (match decide_branchB bc c a b with
             | some t => some t
             | none =>
                 match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                 | some t => some t
                 | none => enum_branchB bc c a b) with
      | some t => .SOk (sjump ss (if t then tk else p + 4)) [] scr
      | none =>
          match scr.sc_dirs with
          | [] => .SStop
          | t :: dirs' =>
              .SOk (sjump ss (if t then tk else p + 4)) [.SCBr t c a b]
                  (SCR dirs' scr.sc_reads scr.sc_hints)
  | .fence _ _ _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .fenceI _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .load sz sx rd rs imm =>
      let n := msize_bytes sz
      let sx' := match sz with | .SZ8 => false | _ => sx
      let a := to_saddrKB bc (g rs) (bv_signed imm)
      match sym_readBI segs ss bc kx scr a n sx' with
      | none => .SStop
      | some (v, scs, scr', nx') =>
          .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                   ss.s_log, ss.s_know, nx', ss.s_resv⟩ scs scr'
  | .store sz rs1 rs2 imm =>
      let n := msize_bytes sz
      let a := to_saddrKB bc (g rs1) (bv_signed imm)
      match resv_inval ss.s_resv a with
      | none => .SStop
      | some r' =>
          .SOk ⟨p + 4, ss.s_regs, SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, r'⟩
              (flat_scB bc a n ++ storeok_scB bc a n) scr
  | .lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0
        match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
        | none => .SStop
        | some (v, scs, scr', nx') =>
            .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                     ss.s_log, ss.s_know, nx', some a⟩ scs scr'
      else .SStop
  | .sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs1
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0
        match ss.s_resv with
        | some r =>
            if saddr_eqb r a then
              .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs
                            else sr_upd ss.s_regs (ridx rd) (.ELit 0)),
                     SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, none⟩
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else .SStop
        | none => .SStop
      else .SStop
  | .amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | none => .SStop
      | some aop =>
          let n := msize_bytes (amo_sz wd)
          let e := g rs1
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0
            match resv_inval ss.s_resv a with
            | none => .SStop
            | some r' =>
                match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
                | none => .SStop
                | some (vold, scs, scr', nx') =>
                    .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) vold),
                             SE a n (amo_newvalB bc wd aop vold (g rs2)) :: ss.s_log,
                             ss.s_know, nx', r'⟩
                        (scs ++ storeok_scB bc a n) scr'
          else .SStop
  | _ => .SStop

/-! ### B4: the index equals the reference walk — 

    The equality chain: the digest (`kx_build`) is a filter of the tagged
    list in three pieces (`kx_build_spec`), merging the two candidate lists
    by position gives the combined filter (`kx_merge_filters`), and the
    reference walk skips exactly the non-candidates
    (`know_lookupA0B_skip0` / `_skipf`), so `kx_select` is the plain
    `List.filter` (`kx_select_eq`) and `know_lookupA0I` the reference walk
    (`know_lookupA0I_eq`) — hence `sym_readBI_eqf` / `sym_stepBI_eq`. -/

/-- `gran_div`: the granule of `a` is `a / 4096`.   *proves* this
    from its `Z.shiftr a 12` definition of `gran`; here `gran` IS that
    division, so the lemma is definitional. -/
theorem gran_div (a : Int) : gran a = a / 4096 := rfl

theorem gran_mono {a b : Int} (h : a ≤ b) : gran a ≤ gran b := by
  unfold gran
  exact Int.ediv_le_ediv (by omega) h

theorem gran_between {s e x : Int} (hs : s ≤ x) (he : x < e) (hf : ext_fits s e = true) :
    ext_has s e (gran x) = true := by
  unfold ext_fits at hf
  have hse : s < e := by omega
  rw [ite_eq_left (by simp [hse])] at hf
  have hf' : gran (e - 1) - gran s ≤ 1 := by simpa using hf
  have hA : gran s ≤ gran x := gran_mono hs
  have hB : gran x ≤ gran (e - 1) := gran_mono (by omega)
  unfold ext_has
  by_cases h1 : gran x = gran s
  · simp [h1]
  · by_cases h2 : gran x = gran (e - 1)
    · simp [h1, h2]
    · omega

theorem kx_aluop_eqb_refl (a : AluOp) : aluop_eqb a a = true := by
  cases a <;> rfl

theorem kx_mulop_eqb_refl (a : MulOp) : mulop_eqb a a = true := by
  cases a <;> rfl

theorem kx_expr_eqb_refl (x : expr) : expr_eqb x x = true := by
  induction x with
  | ELit a => simp [expr_eqb]
  | EVar a => simp [expr_eqb]
  | EAlu o a b iha ihb => simp [expr_eqb, kx_aluop_eqb_refl, iha, ihb]
  | EAluw o a b iha ihb => simp [expr_eqb, kx_aluop_eqb_refl, iha, ihb]
  | EMd o a b iha ihb => simp [expr_eqb, kx_mulop_eqb_refl, iha, ihb]
  | EMdw o a b iha ihb => simp [expr_eqb, kx_mulop_eqb_refl, iha, ihb]
  | EExt s l n a ih => simp [expr_eqb, ih]
  | EBlob s k i n => simp [expr_eqb]

theorem rel_lit_same (rb : expr) (rk rn kk kl : Int) :
    rel_lit rb rk rn rb kk kl =
      (if (kk ≤ rk && rk + rn ≤ kk + kl) then .RInside (rk - kk)
       else if (rk + rn ≤ kk || kk + kl ≤ rk) then .RDisjoint else .RPartial) := by
  unfold rel_lit
  rw [kx_expr_eqb_refl]
  rfl

theorem rel_lit_other {rb : expr} {rk rn kk kl : Int} {kb : expr}
    (h : expr_eqb rb kb = false) : rel_lit rb rk rn kb kk kl = .RUnknown := by
  unfold rel_lit
  rw [h]
  rfl
theorem is_lit0_true {e : expr} (h : is_lit0 e = true) : e = .ELit 0 := by
  cases e with
  | ELit z =>
      simp only [is_lit0] at h
      split at h
      · rename_i hz
        rw [hz]
      · exact absurd h (by simp)
  | EVar n => simp [is_lit0] at h
  | EAlu o a b => simp [is_lit0] at h
  | EAluw o a b => simp [is_lit0] at h
  | EMd o a b => simp [is_lit0] at h
  | EMdw o a b => simp [is_lit0] at h
  | EExt s l n a => simp [is_lit0] at h
  | EBlob s k i n => simp [is_lit0] at h

theorem expr_eqb_lit0_l (kb : expr) : expr_eqb (.ELit 0) kb = is_lit0 kb := by
  cases kb with
  | ELit z =>
      simp only [expr_eqb, is_lit0]
      cases z with
      | ofNat n => cases n <;> rfl
      | negSucc n => rfl
  | EVar n => rfl
  | EAlu o a b => rfl
  | EAluw o a b => rfl
  | EMd o a b => rfl
  | EMdw o a b => rfl
  | EExt s l n a => rfl
  | EBlob s k i n => rfl

theorem expr_eqb_lit0_r (kb : expr) : expr_eqb kb (.ELit 0) = is_lit0 kb := by
  cases kb with
  | ELit z =>
      simp only [expr_eqb, is_lit0]
      cases z with
      | ofNat n => cases n <;> rfl
      | negSucc n => rfl
  | EVar n => rfl
  | EAlu o a b => rfl
  | EAluw o a b => rfl
  | EMd o a b => rfl
  | EMdw o a b => rfl
  | EExt s l n a => rfl
  | EBlob s k i n => rfl


theorem is_lit0_eqb {rb kb : expr} (h : is_lit0 kb = true) :
    expr_eqb rb kb = is_lit0 rb := by
  rw [is_lit0_true h]
  exact expr_eqb_lit0_r rb
theorem kx_gkey_inj {a b : Int} (h : kx_gkey a = kx_gkey b) : a = b := by
  unfold kx_gkey at h
  rcases Int.lt_trichotomy a 0 with ha | ha | ha
  · rcases Int.lt_trichotomy b 0 with hb | hb | hb
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_right (by omega : ¬ 0 < a)] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_right (by omega : ¬ 0 < b)] at h
      omega
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_right (by omega : ¬ 0 < a)] at h
      rw [ite_eq_left hb] at h
      omega
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_right (by omega : ¬ 0 < a)] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_left hb] at h
      omega
  · rcases Int.lt_trichotomy b 0 with hb | hb | hb
    · rw [ite_eq_left ha] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_right (by omega : ¬ 0 < b)] at h
      omega
    · omega
    · rw [ite_eq_left ha] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_left hb] at h
      omega
  · rcases Int.lt_trichotomy b 0 with hb | hb | hb
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_left ha] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_right (by omega : ¬ 0 < b)] at h
      omega
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_left ha] at h
      rw [ite_eq_left hb] at h
      omega
    · rw [ite_eq_right (by omega : ¬ a = 0), ite_eq_left ha] at h
      rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_left hb] at h
      omega

theorem kx_bucket_leaf (g : Int) : kx_bucket (ptree.PTLeaf : ptree (List (Nat × kentry))) g = [] := by
  unfold kx_bucket
  rw [pt_get_leaf]

theorem kx_bucket_add_same (g : Int) (x : Nat × kentry) (t : ptree (List (Nat × kentry))) :
    kx_bucket (kx_add g x t) g = x :: kx_bucket t g := by
  unfold kx_add
  unfold kx_bucket
  rw [pt_gss]

theorem kx_bucket_add_other (g g' : Int) (x : Nat × kentry)
    (t : ptree (List (Nat × kentry))) (H : g ≠ g') :
    kx_bucket (kx_add g' x t) g = kx_bucket t g := by
  have hk : kx_gkey g ≠ kx_gkey g' := fun h => H (kx_gkey_inj h)
  unfold kx_add
  unfold kx_bucket
  rw [pt_gso _ _ _ _ hk]

theorem kx_cand0_split (g : Int) (K : kentry) :
    kx_cand0 g K = (narrow_in g K || kx_wide0 K) := by
  unfold kx_cand0 narrow_in kx_wide0
  cases he : lit0_extent K with
  | none => rfl
  | some p =>
      obtain ⟨s, e⟩ := p
      cases hf : ext_fits s e <;> simp [hf]

theorem narrow_not_wide {g : Int} {K : kentry} (h : narrow_in g K = true) :
    kx_wide0 K = false := by
  unfold narrow_in at h
  unfold kx_wide0
  generalize hle : lit0_extent K = le at h ⊢
  cases le with
  | none =>
      with_unfolding_all dsimp only at h
      cases h
  | some p =>
      obtain ⟨s, e⟩ := p
      with_unfolding_all dsimp only at h ⊢
      cases hf : ext_fits s e with
      | false =>
          rw [hf] at h
          cases h
      | true => rfl
theorem filter_tagged_gt (P : kentry → Bool) (kn : List kentry) :
    ∀ (i j : Nat), j < i → all_gt j (List.filter (fun t => P t.2) (tagged kn i)) := by
  induction kn with
  | nil =>
      intro i j hj t ht
      simp [tagged] at ht
  | cons K rest ih =>
      intro i j hj t ht
      rw [tagged.eq_2, List.filter_cons] at ht
      split at ht
      · rcases List.mem_cons.mp ht with h | h
        · subst h
          exact hj
        · exact ih (i + 1) j (by omega) t h
      · exact ih (i + 1) j (by omega) t ht

theorem kx_merge_nil_l (l2 : List (Nat × kentry)) : kx_merge [] l2 = l2.map Prod.snd :=
  kx_merge.eq_1 l2

theorem kx_merge_nil_r (l1 : List (Nat × kentry)) : kx_merge l1 [] = l1.map Prod.snd := by
  cases l1 with
  | nil => rw [kx_merge.eq_1]
  | cons a l1 =>
      obtain ⟨p, K⟩ := a
      exact kx_merge.eq_2 p K l1

theorem kx_merge_cons_l {p : Nat} {K : kentry} {r1 : List (Nat × kentry)} :
    ∀ {l2 : List (Nat × kentry)}, all_gt p l2 →
      kx_merge ((p, K) :: r1) l2 = K :: kx_merge r1 l2 := by
  intro l2
  induction l2 with
  | nil =>
      intro _
      rw [kx_merge.eq_2, kx_merge_nil_r]
  | cons a l2 ih =>
      obtain ⟨p2, K2⟩ := a
      intro H
      have hp : p < p2 := H (p2, K2) (by simp)
      rw [kx_merge.eq_3]
      rw [ite_eq_left hp]

theorem kx_merge_cons_r {p : Nat} {K : kentry} {r2 : List (Nat × kentry)} :
    ∀ {l1 : List (Nat × kentry)}, all_gt p l1 →
      kx_merge l1 ((p, K) :: r2) = K :: kx_merge l1 r2 := by
  intro l1
  induction l1 with
  | nil => intro _; rw [kx_merge.eq_1, kx_merge.eq_1]; rfl
  | cons a l1 ih =>
      obtain ⟨p1, K1⟩ := a
      intro H
      have hp : p < p1 := H (p1, K1) (by simp)
      have hp' : ¬ p1 < p := by omega
      rw [kx_merge.eq_3]
      rw [ite_eq_right hp']

theorem kx_merge_filters (P Q : kentry → Bool) (kn : List kentry) :
    ∀ (i : Nat), (∀ K, P K = true → Q K = false) →
      kx_merge (List.filter (fun t => P t.2) (tagged kn i))
               (List.filter (fun t => Q t.2) (tagged kn i))
        = List.filter (fun K => P K || Q K) kn := by
  induction kn with
  | nil => intro i _; simp [tagged, kx_merge_nil_l]
  | cons K rest ih =>
      intro i HPQ
      rw [tagged.eq_2]
      cases HP : P K with
      | true =>
          have HQ : Q K = false := HPQ K HP
          rw [List.filter_cons_of_pos (by simp [HP]),
              List.filter_cons_of_neg (by simp [HQ]),
              List.filter_cons_of_pos (by simp [HP]),
              kx_merge_cons_l (filter_tagged_gt Q rest (i + 1) i (by omega)),
              ih (i + 1) HPQ]
      | false =>
          cases HQ : Q K with
          | true =>
              rw [List.filter_cons_of_neg (by simp [HP]),
                  List.filter_cons_of_pos (by simp [HQ]),
                  List.filter_cons_of_pos (by simp [HQ]),
                  kx_merge_cons_r (filter_tagged_gt P rest (i + 1) i (by omega)),
                  ih (i + 1) HPQ]
          | false =>
              rw [List.filter_cons_of_neg (by simp [HP]),
                  List.filter_cons_of_neg (by simp [HQ]),
                  List.filter_cons_of_neg (by simp [HP, HQ]),
                  ih (i + 1) HPQ]

/-! ### `lit0_extent` at the shapes the digest distinguishes -/

theorem lit0_extent_word_some (kk : Int) (w : Nat) (v : expr) :
    lit0_extent (.KWord ⟨.ELit 0, kk⟩ w v) = some (kk, kk + (w : Int)) := by
  with_unfolding_all exact rfl

theorem lit0_extent_word_none {kb : expr} (h : kb ≠ .ELit 0) (kk : Int) (w : Nat) (v : expr) :
    lit0_extent (.KWord ⟨kb, kk⟩ w v) = none := by
  cases kb <;> try (with_unfolding_all exact rfl)
  rename_i z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact absurd rfl h
      | succ m => with_unfolding_all exact rfl
  | negSucc n => with_unfolding_all exact rfl

theorem lit0_extent_zero_some (kk l0 : Int) :
    lit0_extent (.KZero ⟨.ELit 0, kk⟩ (.ELit l0)) = some (kk, kk + zmod64 l0) := by
  with_unfolding_all exact rfl

theorem lit0_extent_zero_none_base {kb : expr} (h : kb ≠ .ELit 0) (kk : Int) (len : expr) :
    lit0_extent (.KZero ⟨kb, kk⟩ len) = none := by
  cases kb <;> try (with_unfolding_all exact rfl)
  rename_i z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact absurd rfl h
      | succ m => with_unfolding_all exact rfl
  | negSucc n => with_unfolding_all exact rfl

theorem lit0_extent_zero_none_len {kk : Int} {len : expr} (h : ∀ l0, len ≠ .ELit l0) :
    lit0_extent (.KZero ⟨.ELit 0, kk⟩ len) = none := by
  cases len <;> try (with_unfolding_all exact rfl)
  rename_i l0
  exact absurd rfl (h l0)

theorem lit0_extent_fill_some (kk l0 c : Int) :
    lit0_extent (.KFill ⟨.ELit 0, kk⟩ (.ELit l0) c) = some (kk, kk + zmod64 l0) := by
  with_unfolding_all exact rfl

theorem lit0_extent_fill_none_base {kb : expr} (h : kb ≠ .ELit 0) (kk : Int) (len : expr)
    (c : Int) : lit0_extent (.KFill ⟨kb, kk⟩ len c) = none := by
  cases kb <;> try (with_unfolding_all exact rfl)
  rename_i z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact absurd rfl h
      | succ m => with_unfolding_all exact rfl
  | negSucc n => with_unfolding_all exact rfl

theorem lit0_extent_fill_none_len {kk c : Int} {len : expr} (h : ∀ l0, len ≠ .ELit l0) :
    lit0_extent (.KFill ⟨.ELit 0, kk⟩ len c) = none := by
  cases len <;> try (with_unfolding_all exact rfl)
  rename_i l0
  exact absurd rfl (h l0)

theorem lit0_extent_blob_some (kk l0 : Int) (k : Nat) :
    lit0_extent (.KBlob ⟨.ELit 0, kk⟩ (.ELit l0) k) = some (kk, kk + zmod64 l0) := by
  with_unfolding_all exact rfl

theorem lit0_extent_blob_none_base {kb : expr} (h : kb ≠ .ELit 0) (kk : Int) (len : expr)
    (k : Nat) : lit0_extent (.KBlob ⟨kb, kk⟩ len k) = none := by
  cases kb <;> try (with_unfolding_all exact rfl)
  rename_i z
  cases z with
  | ofNat n =>
      cases n with
      | zero => exact absurd rfl h
      | succ m => with_unfolding_all exact rfl
  | negSucc n => with_unfolding_all exact rfl

theorem lit0_extent_blob_none_len {kk : Int} {len : expr} (h : ∀ l0, len ≠ .ELit l0) (k : Nat) :
    lit0_extent (.KBlob ⟨.ELit 0, kk⟩ len k) = none := by
  cases len <;> try (with_unfolding_all exact rfl)
  rename_i l0
  exact absurd rfl (h l0)

theorem lit0_extent_img_some (lo hi : Int) :
    lit0_extent (.KImg lo hi) = some (lo, hi) := by
  with_unfolding_all exact rfl

theorem not_lit0_of_false {kb : expr} (h : is_lit0 kb = false) : kb ≠ .ELit 0 := by
  intro he
  rw [he] at h
  simp [is_lit0] at h

/-- The extent of a literal-base cell, as `kx_cand0` sees it. -/
theorem kx_cand0_some (g s e : Int) (K : kentry) (h : lit0_extent K = some (s, e)) :
    kx_cand0 g K = (if ext_fits s e = true then ext_has s e g else true) := by
  unfold kx_cand0
  rw [h]

theorem kx_cand0_none (g : Int) (K : kentry) (h : lit0_extent K = none) :
    kx_cand0 g K = kx_wide0 K := by
  unfold kx_cand0
  rw [h]

theorem kx_wide0_zero (a : saddr) (len : expr) (h : lit0_extent (.KZero a len) = none) :
    kx_wide0 (.KZero a len) = true := by
  unfold kx_wide0
  rw [h]

theorem kx_wide0_fill (a : saddr) (len : expr) (c : Int)
    (h : lit0_extent (.KFill a len c) = none) : kx_wide0 (.KFill a len c) = true := by
  unfold kx_wide0
  rw [h]

theorem kx_wide0_blob_lit {a : saddr} {len : expr} {k : Nat}
    (h : lit0_extent (.KBlob a len k) = none) (hb : a.a_base = .ELit 0) :
    kx_wide0 (.KBlob a len k) = true := by
  unfold kx_wide0
  rw [h]
  cases a with
  | mk b off =>
      simp only at hb
      subst hb
      rfl

/-- The walk skips one non-candidate entry (the `n >= 1`, `hints = []`,
    literal-base case of `know_lookupA0B`). -/
theorem know_lookupA0B_skip0 (bc : bctx) (segs : List Segment) (K : kentry)
    (rest : List kentry) (rk : Int) (n : Nat) (sx : Bool) (acc : List sidecond)
    (HC : kx_cand0 (gran rk) K = false) :
    know_lookupA0B bc segs (K :: rest) (.ELit 0) rk (n + 1) sx [] acc
      = know_lookupA0B bc segs rest (.ELit 0) rk (n + 1) sx [] acc := by
  cases K with
  | KWord sa w v =>
      obtain ⟨kb, kk⟩ := sa
      by_cases hL : is_lit0 kb = true
      · have hkb : kb = .ELit 0 := is_lit0_true hL
        subst hkb
        rw [kx_cand0_some _ _ _ _ (lit0_extent_word_some kk w v)] at HC
        simp only [know_lookupA0B]
        rw [rel_lit_same]
        by_cases hf : ext_fits kk (kk + (w : Int)) = true
        · rw [ite_eq_left hf] at HC
          by_cases hin : (decide (kk ≤ rk) && decide (rk + ((n + 1 : Nat) : Int) ≤ kk + (w : Int))) = true
          · rw [ite_eq_left hin]
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
            obtain ⟨h1, h2⟩ := hin
            exact absurd (gran_between (s := kk) (e := kk + (w : Int)) (x := rk) h1 (by omega) hf)
              (by rw [HC]; simp)
          · rw [ite_eq_right hin]
            by_cases hdj : (decide (rk + ((n + 1 : Nat) : Int) ≤ kk) ||
                decide (kk + (w : Int) ≤ rk)) = true
            · rw [ite_eq_left hdj]
            · rw [ite_eq_right hdj]
        · rw [ite_eq_right hf] at HC
          exact absurd HC (by simp)
      · have hLf : is_lit0 kb = false := by simpa using hL
        have hkb : kb ≠ .ELit 0 := not_lit0_of_false hLf
        simp only [know_lookupA0B]
        rw [rel_lit_other (by rw [expr_eqb_lit0_l, hLf])]
  | KZero sa len =>
      obtain ⟨kb, kk⟩ := sa
      by_cases hL : is_lit0 kb = true
      · have hkb : kb = .ELit 0 := is_lit0_true hL
        subst hkb
        by_cases hlit : ∃ l0, len = .ELit l0
        · obtain ⟨l0, rfl⟩ := hlit
          rw [kx_cand0_some _ _ _ _ (lit0_extent_zero_some kk l0)] at HC
          rw [zmod64_eq2] at HC
          simp only [know_lookupA0B]
          rw [rel_lit_same]
          by_cases hf : ext_fits kk (kk + l0 % two64) = true
          · rw [ite_eq_left hf] at HC
            by_cases hin : (decide (kk ≤ rk) &&
                decide (rk + ((n + 1 : Nat) : Int) ≤ kk + l0 % two64)) = true
            · rw [ite_eq_left hin]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
              obtain ⟨h1, h2⟩ := hin
              exact absurd (gran_between (s := kk) (e := kk + l0 % two64) (x := rk) h1 (by omega) hf)
                (by rw [HC]; simp)
            · rw [ite_eq_right hin]
              by_cases hdj : (decide (rk + ((n + 1 : Nat) : Int) ≤ kk) ||
                  decide (kk + l0 % two64 ≤ rk)) = true
              · rw [ite_eq_left hdj]
              · rw [ite_eq_right hdj]
          · rw [ite_eq_right hf] at HC
            exact absurd HC (by simp)
        · have hn : ∀ l0, len ≠ .ELit l0 := by
            intro l0 h; exact hlit ⟨l0, h⟩
          rw [kx_cand0_none _ _ (lit0_extent_zero_none_len hn),
            kx_wide0_zero _ _ (lit0_extent_zero_none_len hn)] at HC
          exact absurd HC (by simp)
      · have hLf : is_lit0 kb = false := by simpa using hL
        have hkb : kb ≠ .ELit 0 := not_lit0_of_false hLf
        rw [kx_cand0_none _ _ (lit0_extent_zero_none_base hkb kk len),
          kx_wide0_zero _ _ (lit0_extent_zero_none_base hkb kk len)] at HC
        exact absurd HC (by simp)
  | KFill sa len c =>
      obtain ⟨kb, kk⟩ := sa
      by_cases hL : is_lit0 kb = true
      · have hkb : kb = .ELit 0 := is_lit0_true hL
        subst hkb
        by_cases hlit : ∃ l0, len = .ELit l0
        · obtain ⟨l0, rfl⟩ := hlit
          rw [kx_cand0_some _ _ _ _ (lit0_extent_fill_some kk l0 c)] at HC
          rw [zmod64_eq2] at HC
          simp only [know_lookupA0B]
          rw [rel_lit_same]
          by_cases hf : ext_fits kk (kk + l0 % two64) = true
          · rw [ite_eq_left hf] at HC
            by_cases hin : (decide (kk ≤ rk) &&
                decide (rk + ((n + 1 : Nat) : Int) ≤ kk + l0 % two64)) = true
            · rw [ite_eq_left hin]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
              obtain ⟨h1, h2⟩ := hin
              exact absurd (gran_between (s := kk) (e := kk + l0 % two64) (x := rk) h1 (by omega) hf)
                (by rw [HC]; simp)
            · rw [ite_eq_right hin]
              by_cases hdj : (decide (rk + ((n + 1 : Nat) : Int) ≤ kk) ||
                  decide (kk + l0 % two64 ≤ rk)) = true
              · rw [ite_eq_left hdj]
              · rw [ite_eq_right hdj]
          · rw [ite_eq_right hf] at HC
            exact absurd HC (by simp)
        · have hn : ∀ l0, len ≠ .ELit l0 := by
            intro l0 h; exact hlit ⟨l0, h⟩
          rw [kx_cand0_none _ _ (lit0_extent_fill_none_len hn),
            kx_wide0_fill _ _ _ (lit0_extent_fill_none_len hn)] at HC
          exact absurd HC (by simp)
      · have hLf : is_lit0 kb = false := by simpa using hL
        have hkb : kb ≠ .ELit 0 := not_lit0_of_false hLf
        rw [kx_cand0_none _ _ (lit0_extent_fill_none_base hkb kk len c),
          kx_wide0_fill _ _ _ (lit0_extent_fill_none_base hkb kk len c)] at HC
        exact absurd HC (by simp)
  | KBlob sa len k =>
      obtain ⟨kb, kk⟩ := sa
      by_cases hL : is_lit0 kb = true
      · have hkb : kb = .ELit 0 := is_lit0_true hL
        subst hkb
        by_cases hlit : ∃ l0, len = .ELit l0
        · obtain ⟨l0, rfl⟩ := hlit
          rw [kx_cand0_some _ _ _ _ (lit0_extent_blob_some kk l0 k)] at HC
          rw [zmod64_eq2] at HC
          simp only [know_lookupA0B]
          simp only [kx_expr_eqb_refl, ite_eq_left rfl, ite_true]
          by_cases hf : ext_fits kk (kk + l0 % two64) = true
          · rw [ite_eq_left hf] at HC
            by_cases hkr : kk ≤ rk
            · rw [ite_eq_left hkr]
              by_cases hin : rk + ((n + 1 : Nat) : Int) ≤ kk + l0 % two64
              · rw [ite_eq_left hin]
                exact absurd (gran_between hkr (by omega) hf) (by rw [HC]; simp)
              · rw [ite_eq_right hin]
                by_cases hdj : kk + l0 % two64 ≤ rk
                · rw [ite_eq_left hdj]
                · rw [ite_eq_right hdj]
                  exact absurd (gran_between hkr (by omega) hf) (by rw [HC]; simp)
            · rw [ite_eq_right hkr]
          · rw [ite_eq_right hf] at HC
            exact absurd HC (by simp)
        · have hn : ∀ l0, len ≠ .ELit l0 := by
            intro l0 h; exact hlit ⟨l0, h⟩
          rw [kx_cand0_none _ _ (lit0_extent_blob_none_len hn k)] at HC
          have hw : kx_wide0 (.KBlob ⟨.ELit 0, kk⟩ len k) = true :=
            kx_wide0_blob_lit (lit0_extent_blob_none_len hn k) rfl
          rw [hw] at HC
          exact absurd HC (by simp)
      · have hLf : is_lit0 kb = false := by simpa using hL
        have hkb : kb ≠ .ELit 0 := not_lit0_of_false hLf
        simp only [know_lookupA0B]
        rw [expr_eqb_lit0_l, hLf]
        simp only [ite_false, Bool.false_eq_true]
  | KImg lo hi =>
      rw [kx_cand0_some _ _ _ _ (lit0_extent_img_some lo hi)] at HC
      simp only [know_lookupA0B]
      by_cases hf : ext_fits lo hi = true
      · rw [ite_eq_left hf] at HC
        by_cases hin : (decide (lo ≤ rk) && decide (rk + ((n + 1 : Nat) : Int) ≤ hi)) = true
        · rw [ite_eq_left hin]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
          obtain ⟨h1, h2⟩ := hin
          exact absurd (gran_between (s := lo) (e := hi) (x := rk) h1 (by omega) hf)
            (by rw [HC]; simp)
        · rw [ite_eq_right hin]
      · rw [ite_eq_right hf] at HC
        exact absurd HC (by simp)
  | KAlign e m => with_unfolding_all exact rfl
  | KRange e lo hi => with_unfolding_all exact rfl
  | KWr sa len => with_unfolding_all exact rfl
  | KDisj a1 n1 a2 n2 => with_unfolding_all exact rfl
  | KUnk sa len => with_unfolding_all exact rfl

theorem know_lookupA0B_skipf (bc : bctx) (segs : List Segment) (K : kentry) (rest : List kentry)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (acc : List sidecond)
    (Hrb : is_lit0 rb = false) (HC : kx_candf K = false) :
    know_lookupA0B bc segs (K :: rest) rb rk n sx [] acc
      = know_lookupA0B bc segs rest rb rk n sx [] acc := by
  cases K with
  | KWord sa w v =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kx_candf] at HC
      have hL : is_lit0 kb = true := by
        cases h : is_lit0 kb with
        | true => rfl
        | false => rw [h] at HC; simp at HC
      have hkb : kb = .ELit 0 := is_lit0_true hL
      subst hkb
      simp only [know_lookupA0B]
      rw [rel_lit_other (by rw [is_lit0_eqb hL]; exact Hrb)]
  | KBlob sa len k =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kx_candf] at HC
      have hL : is_lit0 kb = true := by
        cases h : is_lit0 kb with
        | true => rfl
        | false => rw [h] at HC; simp at HC
      have hkb : kb = .ELit 0 := is_lit0_true hL
      subst hkb
      simp only [know_lookupA0B]
      rw [is_lit0_eqb hL, Hrb]
      simp only [Bool.false_eq_true, ite_false]
  | KZero sa len =>
      simp only [kx_candf] at HC
      exact absurd HC (by simp)
  | KFill sa len c =>
      simp only [kx_candf] at HC
      exact absurd HC (by simp)
  | KImg lo hi =>
      simp only [know_lookupA0B]
      cases rb <;> try (with_unfolding_all exact rfl)
      rename_i z
      cases z with
      | ofNat m =>
          cases m with
          | zero => simp [is_lit0] at Hrb
          | succ j => with_unfolding_all exact rfl
      | negSucc j => with_unfolding_all exact rfl
  | KAlign e m => with_unfolding_all exact rfl
  | KRange e lo hi => with_unfolding_all exact rfl
  | KWr sa len => with_unfolding_all exact rfl
  | KDisj a1 n1 a2 n2 => with_unfolding_all exact rfl
  | KUnk sa len => with_unfolding_all exact rfl

theorem know_lookupA0B_filter0 (bc : bctx) (segs : List Segment) (l : List kentry) (rk : Int)
    (n : Nat) (sx : Bool) :
    ∀ (acc : List sidecond),
      know_lookupA0B bc segs (List.filter (kx_cand0 (gran rk)) l) (.ELit 0) rk (n + 1) sx [] acc
        = know_lookupA0B bc segs l (.ELit 0) rk (n + 1) sx [] acc := by
  induction l with
  | nil => intro acc; rfl
  | cons K rest ih =>
      intro acc
      rw [List.filter_cons]
      by_cases hc : kx_cand0 (gran rk) K = true
      · rw [ite_eq_left hc]
        simp only [know_lookupA0B]
        cases K <;> simp only [] <;>
          repeat (first | exact ih _ | rfl | split)
      · rw [ite_eq_right hc]
        have hc' : kx_cand0 (gran rk) K = false := by simpa using hc
        rw [know_lookupA0B_skip0 bc segs K rest rk n sx acc hc']
        exact ih acc


theorem know_lookupA0B_filterf (bc : bctx) (segs : List Segment) (l : List kentry) (rb : expr)
    (rk : Int) (n : Nat) (sx : Bool) (Hrb : is_lit0 rb = false) :
    ∀ (acc : List sidecond),
      know_lookupA0B bc segs (List.filter kx_candf l) rb rk n sx [] acc
        = know_lookupA0B bc segs l rb rk n sx [] acc := by
  induction l with
  | nil => intro acc; rfl
  | cons K rest ih =>
      intro acc
      rw [List.filter_cons]
      by_cases hc : kx_candf K = true
      · rw [ite_eq_left hc]
        simp only [know_lookupA0B]
        cases K <;> simp only [] <;>
          repeat (first | exact ih _ | rfl | split)
      · rw [ite_eq_right hc]
        have hc' : kx_candf K = false := by simpa using hc
        rw [know_lookupA0B_skipf bc segs K rest rb rk n sx acc Hrb hc']
        exact ih acc

/-- The bucket of an added cell: the digest's two-granule insertion, as
    `narrow_in` sees it. -/
theorem kx_add_bucket_step (i : Nat) (K : kentry) (s e : Int)
    (t : ptree (List (Nat × kentry))) (g : Int) :
    kx_bucket (if gran s == gran (e - 1) then kx_add (gran s) (i, K) t
               else kx_add (gran (e - 1)) (i, K) (kx_add (gran s) (i, K) t)) g
      = (if ext_has s e g then (i, K) :: kx_bucket t g else kx_bucket t g) := by
  by_cases h12 : (gran s == gran (e - 1)) = true
  · rw [ite_eq_left h12]
    have hg : gran s = gran (e - 1) := by simpa using h12
    by_cases h1 : (g == gran s) = true
    · have hext : ext_has s e g = true := by unfold ext_has; rw [ite_eq_left h1]
      simp only [hext]
      have hgs : g = gran s := by simpa using h1
      rw [hgs, kx_bucket_add_same]
      simp
    · have hne : g ≠ gran s := by simpa using h1
      have h1f : (g == gran s) = false := by simpa using h1
      have hext : ext_has s e g = false := by
        unfold ext_has
        rw [ite_eq_right h1]
        rw [← hg]
        simpa using h1f
      simp only [hext]
      rw [kx_bucket_add_other _ _ _ _ hne]
      simp
  · rw [ite_eq_right h12]
    have hg : gran s ≠ gran (e - 1) := by simpa using h12
    by_cases h1 : (g == gran s) = true
    · have hext : ext_has s e g = true := by unfold ext_has; rw [ite_eq_left h1]
      simp only [hext]
      have hgs : g = gran s := by simpa using h1
      rw [hgs, kx_bucket_add_other (gran s) (gran (e - 1)) _ _ hg, kx_bucket_add_same]
      simp
    · have hne : g ≠ gran s := by simpa using h1
      by_cases h2 : (g == gran (e - 1)) = true
      · have hext : ext_has s e g = true := by unfold ext_has; rw [ite_eq_right h1, h2]
        simp only [hext]
        have hge : g = gran (e - 1) := by simpa using h2
        rw [hge, kx_bucket_add_same, kx_bucket_add_other (gran (e - 1)) (gran s) _ _ hg.symm]
        simp
      · have h2f : (g == gran (e - 1)) = false := by simpa using h2
        have hne2 : g ≠ gran (e - 1) := by simpa using h2f
        have hext : ext_has s e g = false := by unfold ext_has; rw [ite_eq_right h1, h2f]
        simp only [hext]
        rw [kx_bucket_add_other _ _ _ _ hne2, kx_bucket_add_other _ _ _ _ hne]
        simp

/-- What one digest pass computes. -/
theorem kx_build_spec {kn : List kentry} {i : Nat} {w0 : List (Nat × kentry)}
    {gr : ptree (List (Nat × kentry))} {wf : List kentry}
    (H : kx_build kn i = (w0, (gr, wf))) :
    w0 = List.filter (fun t => kx_wide0 t.2) (tagged kn i) ∧
    (∀ g, kx_bucket gr g = List.filter (fun t => narrow_in g t.2) (tagged kn i)) ∧
    wf = List.filter kx_candf kn := by
  induction kn generalizing i w0 gr wf with
  | nil =>
      rw [kx_build] at H
      injection H with h1 h2
      injection h2 with h2a h2b
      subst h1; subst h2a; subst h2b
      refine ⟨?_, ?_, ?_⟩
      · simp [tagged]
      · intro g
        rw [kx_bucket_leaf]
        simp [tagged]
      · simp [tagged]
  | cons K rest ih =>
      rw [kx_build] at H
      generalize hb : kx_build rest (i + 1) = res at H
      obtain ⟨w0', gr', wf'⟩ := res
      dsimp only at H
      obtain ⟨A, B, C⟩ := ih (i := i + 1) (w0 := w0') (gr := gr') (wf := wf') hb
      generalize hwf2 : (if kx_candf K then K :: wf' else wf') = wf2 at H
      generalize hle : lit0_extent K = le at H
      cases le with
      | none =>
          have hnarrow : ∀ g, narrow_in g K = false := by
            intro g; simp only [narrow_in, hle]
          by_cases hw : kx_wide0 K = true
          · rw [ite_eq_left hw] at H
            injection H with h1 h2
            injection h2 with h2a h2b
            subst h1; subst h2a; subst h2b
            refine ⟨?_, ?_, ?_⟩
            · rw [tagged.eq_2, List.filter_cons_of_pos (by simpa using hw), A]
            · intro g
              rw [tagged.eq_2, List.filter_cons_of_neg (by rw [hnarrow]; simp)]
              exact B g
            · rw [← hwf2, List.filter_cons, C]
          · have hwf : kx_wide0 K = false := by simpa using hw
            rw [ite_eq_right hw] at H
            injection H with h1 h2
            injection h2 with h2a h2b
            subst h1; subst h2a; subst h2b
            refine ⟨?_, ?_, ?_⟩
            · rw [tagged.eq_2, List.filter_cons_of_neg (by simp [hwf]), A]
            · intro g
              rw [tagged.eq_2, List.filter_cons_of_neg (by rw [hnarrow]; simp)]
              exact B g
            · rw [← hwf2, List.filter_cons, C]
      | some p =>
          obtain ⟨s, e⟩ := p
          with_unfolding_all dsimp only at H
          by_cases hf : ext_fits s e = true
          · -- narrow: the cell fits in at most two granules
            have hnarrow : ∀ g, narrow_in g K = ext_has s e g := by
              intro g; simp [narrow_in, hle, hf]
            rw [ite_eq_left hf] at H
            injection H with h1 h2
            injection h2 with h2a h2b
            subst h1; subst h2a; subst h2b
            refine ⟨?_, ?_, ?_⟩
            · rw [tagged.eq_2, List.filter_cons_of_neg (by simp [kx_wide0, hle, hf]), A]
            · intro g
              rw [kx_add_bucket_step, tagged.eq_2, List.filter_cons, hnarrow g]
              by_cases he : ext_has s e g = true
              · rw [ite_eq_left he, ite_eq_left (by simp [he]), B]
              · rw [ite_eq_right he, ite_eq_right (by simpa using he), B]
            · rw [← hwf2, List.filter_cons, C]
          · -- wide literal cell
            have hnarrow : ∀ g, narrow_in g K = false := by
              intro g; simp [narrow_in, hle, hf]
            rw [ite_eq_right hf] at H
            injection H with h1 h2
            injection h2 with h2a h2b
            subst h1; subst h2a; subst h2b
            refine ⟨?_, ?_, ?_⟩
            · rw [tagged.eq_2, List.filter_cons_of_pos (by simp [kx_wide0, hle, hf]), A]
            · intro g
              rw [tagged.eq_2, List.filter_cons_of_neg (by rw [hnarrow]; simp)]
              exact B g
            · rw [← hwf2, List.filter_cons, C]


/-- The candidate sub-sequence is the plain filter. -/
theorem kx_select_eq (kn : List kentry) (rb : expr) (rk : Int) :
    kx_select (mk_kix kn) rb rk
      = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn := by
  unfold kx_select mk_kix
  generalize hb : kx_build kn 1 = res
  obtain ⟨w0, gr, wf⟩ := res
  dsimp only
  obtain ⟨A, B, C⟩ := kx_build_spec hb
  by_cases hL : is_lit0 rb = true
  · rw [ite_eq_left hL, ite_eq_left hL, B, A,
      kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1 (fun K h => narrow_not_wide h)]
    apply List.filter_congr
    intro K _
    exact (kx_cand0_split (gran rk) K).symm
  · rw [ite_eq_right hL, ite_eq_right hL]
    exact C

/-- The reference walk reads the same answer off the index . -/
theorem know_lookupA0I_eq (bc : bctx) (kn : List kentry) (segs : List Segment) (rb : expr)
    (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) :
    know_lookupA0I bc (mk_kix kn) segs rb rk n sx hints acc
      = know_lookupA0B bc segs kn rb rk n sx hints acc := by
  unfold know_lookupA0I
  cases hints with
  | nil =>
      cases n with
      | zero => with_unfolding_all exact rfl
      | succ m =>
          with_unfolding_all dsimp only
          rw [kx_select_eq]
          by_cases hL : is_lit0 rb = true
          · rw [ite_eq_left hL]
            have hrb : rb = .ELit 0 := is_lit0_true hL
            subst hrb
            exact know_lookupA0B_filter0 bc segs kn rk m sx acc
          · rw [ite_eq_right hL]
            have hLf : is_lit0 rb = false := by simpa using hL
            exact know_lookupA0B_filterf bc segs kn rb rk (m + 1) sx hLf acc
  | cons h hs => rfl

theorem know_lookupABI_eq (bc : bctx) (kn : List kentry) (segs : List Segment) :
    know_lookupABI bc (mk_kix kn) segs kn = know_lookupAB bc segs kn := by
  funext rb rk n sx hints acc
  unfold know_lookupABI know_lookupAB
  rw [know_lookupA0I_eq]

theorem sym_readBI_eqf (segs : List Segment) (ss : sym_state) (bc : bctx) :
    sym_readBI segs ss bc (mk_kix ss.s_know) = sym_readB segs ss bc := by
  funext scr a n sx'
  unfold sym_readBI sym_readB
  rw [know_lookupABI_eq]

theorem sym_stepBI_eq (bc : bctx) (segs : List Segment) (i : Instr) (ss : sym_state)
    (scr : scripts) :
    sym_stepBI bc (mk_kix ss.s_know) segs i ss scr = sym_stepB bc segs i ss scr := by
  simp only [sym_stepBI, sym_stepB, sym_readBI_eqf]
  try (with_unfolding_all exact rfl)

/-! ## B5: extension mode and the drivers — 

    The extension-mode lookups on the block context (`zf_coversB` ..
    `x_filterB`), the step `sym_stepXB`, and the table drivers
    `sym_execTXB` / `sym_execTXBI`.  `segs` is threaded explicitly (Lean
    has no section variables). -/

/-- `zf_coversB`: `rb+rk, +n` inside ONE entry, by offsets or by exact
    linear arithmetic. -/
def zf_coversB (bc : bctx) (rb : expr) (rk : Int) (n : Nat) (kb : expr) (kk : Int)
    (len : expr) : Bool :=
  (match len with
   | .ELit l0 =>
       match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
       | .RInside _ => true
       | _ => false
   | _ => false) || xinsideB bc rb rk (elen n) kb kk len

/-- `kentry_overlayB`: an entry proving the range OVERLAY-DEFINED. -/
def kentry_overlayB (bc : bctx) (rb : expr) (rk : Int) (n : Nat) (K : kentry) : Bool :=
  match K with
  | .KUnk ⟨kb, kk⟩ len | .KZero ⟨kb, kk⟩ len | .KFill ⟨kb, kk⟩ len _ | .KBlob ⟨kb, kk⟩ len _ =>
      zf_coversB bc rb rk n kb kk len
  | _ => false

/-- `kentry_readableB`: an entry proving the range READABLE. -/
def kentry_readableB (bc : bctx) (rb : expr) (rk : Int) (n : Nat) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨kb, kk⟩ w _ =>
      match rel_lit rb rk (n : Int) kb kk (w : Int) with
      | .RInside _ => true
      | _ => false
  | _ => kentry_overlayB bc rb rk n K

/-- `kn_readableB`: some entry (or the bytewise cover) proves readability. -/
def kn_readableB (segs : List Segment) (bc : bctx) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) : Bool :=
  kn.any (kentry_readableB bc rb rk n) || know_bytes_cov segs true kn rb rk n

/-- `kn_overlayB`: some entry (or the bytewise cover) proves overlay-definition. -/
def kn_overlayB (segs : List Segment) (bc : bctx) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) : Bool :=
  kn.any (kentry_overlayB bc rb rk n) || know_bytes_cov segs false kn rb rk n

/-- `x_dischargeableB`: the obligations extension mode discharges. -/
def x_dischargeableB (segs : List Segment) (bc : bctx) (ss ss' : sym_state)
    (rb : Option (saddr × Nat × Bool)) (sc : sidecond) : Bool :=
  let kn := ss.s_know
  match sc with
  | .SCReadBase a n sx (.EVar j) =>
      (match rb with
       | some (a', n', sx') => saddr_eqb a' a && (n' == n) && (sx' == sx)
       | none => false) &&
      (j == ss.s_next) && (j < ss'.s_next) && evars_lt ss.s_next a.a_base &&
      (1 ≤ n && n ≤ 8) && kn_readable segs bc.bc_fk kn a.a_base a.a_off n
  | .SCFlat a (.ELit z) =>
      (1 ≤ z && z ≤ 8) && kn_readable segs bc.bc_fk kn a.a_base a.a_off z.toNat
  | .SCStoreOk a n => (1 ≤ n && n ≤ 8) && kn_overlay segs bc.bc_fk kn a.a_base a.a_off n
  | _ => false

/-- `x_filterB`: filter the obligations extension mode discharges. -/
def x_filterB (segs : List Segment) (bc : bctx) (ss ss' : sym_state)
    (scs : List sidecond) : List sidecond :=
  match scs with
  | [] => []
  | _ =>
      let rb := find_readbase ss.s_next scs
      scs.filter (fun sc => !(x_dischargeableB segs bc ss ss' rb sc))

/-- `sym_stepXB`: the extension-mode step, obligations discharged,
    destination capped. -/
def sym_stepXB (segs : List Segment) (bc : bctx) (K : Nat) (i : Instr) (ss : sym_state)
    (scr : scripts) : stepres :=
  match sym_stepB bc segs i ss scr with
  | .SOk ss' scs scr' =>
      if ss.s_next ≤ ss'.s_next
      then .SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else .SStop
  | .SStop => .SStop

/-- `sym_stepXBI`: the extension-mode step with the knowledge index. -/
def sym_stepXBI (bc : bctx) (kx : kix) (segs : List Segment) (K : Nat) (i : Instr)
    (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI bc kx segs i ss scr with
  | .SOk ss' scs scr' =>
      if ss.s_next ≤ ss'.s_next
      then .SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else .SStop
  | .SStop => .SStop

/-- `sym_execTXB_go`: the extension-mode table driver on the block context. -/
def sym_execTXB_go (segs : List Segment) (bc : bctx) (t : itab) (K : Nat) (fuel : Nat)
    (first : Bool) (stops : List Int) (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match itab_lookup t ss.s_pc with
        | none => if s_clean ss then ss else ck
        | some i =>
            match sym_stepXB segs bc K i ss scr_nil with
            | .SOk ss' [] _ =>
                sym_execTXB_go segs bc t K f false stops ss' (if s_clean ss' then ss' else ck)
            | _ => if s_clean ss then ss else ck

/-- `sym_execTXB`. -/
def sym_execTXB (segs : List Segment) (bc : bctx) (t : itab) (K : Nat) (fuel : Nat)
    (first : Bool) (stops : List Int) (ss : sym_state) : sym_state :=
  sym_execTXB_go segs bc t K fuel first stops (clr ss) (clr ss)

/-- `sym_execTXBI_go`: ... with the knowledge index. -/
def sym_execTXBI_go (bc : bctx) (kx : kix) (segs : List Segment) (t : itab) (K : Nat)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (ck : sym_state) :
    sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match itab_lookup t ss.s_pc with
        | none => if s_clean ss then ss else ck
        | some i =>
            match sym_stepXBI bc kx segs K i ss scr_nil with
            | .SOk ss' [] _ => sym_execTXBI_go bc kx segs t K f false stops ss' (if s_clean ss' then ss' else ck)
            | _ => if s_clean ss then ss else ck

/-- `sym_execTXBI`. -/
def sym_execTXBI (segs : List Segment) (bc : bctx) (kx : kix) (t : itab) (K : Nat)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) : sym_state :=
  sym_execTXBI_go bc kx segs t K fuel first stops (clr ss) (clr ss)

/-! ### The extension-mode layer equals its reference -/

theorem zf_coversB_eqf (fk : List kentry) : zf_coversB (mkbc fk) = zf_covers fk := by
  funext rb rk n kb kk len
  simp only [zf_coversB, zf_covers, xinsideB_eqf]
  try (with_unfolding_all exact rfl)

theorem kentry_overlayB_eqf (fk : List kentry) :
    kentry_overlayB (mkbc fk) = kentry_overlay fk := by
  funext rb rk n K
  cases K <;> simp only [kentry_overlayB, kentry_overlay, zf_coversB_eqf] <;>
    try (with_unfolding_all exact rfl)

theorem kentry_readableB_eqf (fk : List kentry) :
    kentry_readableB (mkbc fk) = kentry_readable fk := by
  funext rb rk n K
  cases K <;> simp only [kentry_readableB, kentry_readable, kentry_overlayB_eqf] <;>
    try (with_unfolding_all exact rfl)

theorem kn_readableB_eqf (segs : List Segment) (fk : List kentry) :
    kn_readableB segs (mkbc fk) = kn_readable segs fk := by
  funext kn rb rk n
  simp only [kn_readableB, kn_readable, kentry_readableB_eqf]
  try exact rfl

theorem kn_overlayB_eqf (segs : List Segment) (fk : List kentry) :
    kn_overlayB segs (mkbc fk) = kn_overlay segs fk := by
  funext kn rb rk n
  simp only [kn_overlayB, kn_overlay, kentry_overlayB_eqf]
  try exact rfl

theorem x_dischargeableB_eq (segs : List Segment) (ss ss' : sym_state)
    (rb : Option (saddr × Nat × Bool)) (sc : sidecond) :
    x_dischargeableB segs (mkbc (facts_of ss.s_know)) ss ss' rb sc
      = x_dischargeable segs ss ss' rb sc := by
  simp only [x_dischargeableB, x_dischargeable, bc_fk_mkbc]
  try (with_unfolding_all exact rfl)

theorem x_filterB_eq (segs : List Segment) (ss ss' : sym_state) (scs : List sidecond) :
    x_filterB segs (mkbc (facts_of ss.s_know)) ss ss' scs
      = x_filter segs ss ss' scs := by
  simp only [x_filterB, x_filter, x_dischargeableB_eq]
  try (with_unfolding_all exact rfl)

theorem sym_stepXB_eq (segs : List Segment) (K : Nat) (i : Instr) (ss : sym_state)
    (scr : scripts) :
    sym_stepXB segs (mkbc (facts_of ss.s_know)) K i ss scr = sym_stepX segs K i ss scr := by
  rw [sym_stepXB, sym_stepX, sym_stepB_eq]
  rcases h : sym_step segs i ss scr with _ | ⟨ss', scs, scr'⟩
  · rfl
  · simp only [h, x_filterB_eq]

theorem sym_step_know (segs : List Segment) (i : Instr) (ss : sym_state) (scr : scripts)
    (ss' : sym_state) (scs : List sidecond) (scr' : scripts)
    (h : sym_step segs i ss scr = .SOk ss' scs scr') : ss'.s_know = ss.s_know := by
  -- every branch of `sym_step` writes `ss.s_know` (via `sset`/`sjump`/a record)
  simp only [sym_step] at h ⊢
  cases i <;> simp only [sset, sjump] at h ⊢ <;>
    repeat (first
      | (split at h)
      | (obtain ⟨rfl, -, -⟩ := h; rfl)
      | (injection h with h1 h2 h3; subst h1; rfl)
      | (simp at h)
      | rfl)

theorem cap_rd_know (K : Nat) (i : Instr) (ss : sym_state) :
    (cap_rd K i ss).s_know = ss.s_know := by
  unfold cap_rd
  repeat (first | rfl | split)

theorem sym_stepX_know (segs : List Segment) (K : Nat) (i : Instr) (ss : sym_state) (scr : scripts)
    (ss' : sym_state) (scs : List sidecond) (scr' : scripts)
    (h : sym_stepX segs K i ss scr = .SOk ss' scs scr') : ss'.s_know = ss.s_know := by
  simp only [sym_stepX] at h
  split at h
  · rename_i ss1 scs1 scr1 E
    split at h
    · injection h with h1 h2 h3
      subst h1
      rw [cap_rd_know]
      exact sym_step_know segs i ss scr ss1 scs1 scr1 E
    · cases h
  · cases h

theorem sym_execTX_go_know (segs : List Segment) (t : itab) (K : Nat) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      ck.s_know = ss.s_know →
      (sym_execTX_go segs t K fuel first stops ss ck).s_know = ss.s_know := by
  intro fuel
  induction fuel with
  | zero =>
      intro first stops ss ck hck
      simp only [sym_execTX_go]
      split
      · rfl
      · exact hck
  | succ f ih =>
      intro first stops ss ck hck
      simp only [sym_execTX_go]
      split
      · split
        · rfl
        · exact hck
      · split
        · split
          · rfl
          · exact hck
        · cases hh : sym_stepX segs K _ ss scr_nil with
          | SStop =>
              simp only [hh]
              split
              · rfl
              · exact hck
          | SOk ss1 scs1 scr1' =>
              cases scs1 with
              | nil =>
                  have hk : ss1.s_know = ss.s_know :=
                    sym_stepX_know segs K _ ss scr_nil ss1 [] scr1' hh
                  simp only [hh]
                  split
                  · rw [ih false stops ss1 ss1 rfl, hk]
                  · rw [ih false stops ss1 ck]
                    · exact hk
                    · rw [hck, hk]
              | cons sc rest =>
                  simp only [hh]
                  split
                  · rfl
                  · exact hck

theorem sym_execTX_know (segs : List Segment) (t : itab) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) :
    (sym_execTX segs t K fuel first stops ss).s_know = ss.s_know := by
  simp only [sym_execTX, clr]
  exact sym_execTX_go_know segs t K fuel first stops (clr ss) (clr ss) (by rfl)

/-! ### B5: the B-driver equals the reference driver

    The BRIDGE between the bounded (`..B`) and unbounded (reference)
    drivers: `sym_execTXB_go` with the block context BUILT FROM THE STATE'S
    OWN knowledge is `sym_execTX_go`, step for step. -/

theorem sym_execTXB_go_eq (segs : List Segment) (t : itab) (K : Nat) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execTXB_go segs (mkbc (facts_of ss.s_know)) t K fuel first stops ss ck
        = sym_execTX_go segs t K fuel first stops ss ck := by
  intro fuel
  induction fuel with
  | zero =>
      intro first stops ss ck
      simp only [sym_execTXB_go, sym_execTX_go]
  | succ f ih =>
      intro first stops ss ck
      simp only [sym_execTXB_go, sym_execTX_go]
      by_cases h1 : (!first && stops.any (fun x => x == ss.s_pc)) = true
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1]
        cases hlk : itab_lookup t ss.s_pc with
        | none => simp only [hlk]
        | some i =>
            simp only [hlk]
            rw [sym_stepXB_eq]
            cases hh : sym_stepX segs K i ss scr_nil with
            | SStop => simp only [hh]
            | SOk ss1 scs1 scr1 =>
                cases scs1 with
                | nil =>
                    have hk : ss1.s_know = ss.s_know :=
                      sym_stepX_know segs K i ss scr_nil ss1 [] scr1 hh
                    simp only [hh]
                    rw [← hk]
                    exact ih false stops ss1 _
                | cons sc rest => simp only [hh]

theorem sym_execTXB_eq (segs : List Segment) (kn0 : List kentry) (t : itab) (K : Nat)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (h : ss.s_know = kn0) :
    sym_execTXB segs (mkbc (facts_of kn0)) t K fuel first stops ss
      = sym_execTX segs t K fuel first stops ss := by
  subst h
  unfold sym_execTXB sym_execTX
  -- `clr ss` keeps `s_know`, so the state's context is the `clr`'d one's
  exact sym_execTXB_go_eq segs t K fuel first stops (clr ss) (clr ss)

/-! ### B5: the knowledge index does not change the driver's answer -/

theorem sym_stepXBI_eq (segs : List Segment) (K : Nat) (i : Instr) (ss : sym_state)
    (scr : scripts) :
    sym_stepXBI (mkbc (facts_of ss.s_know)) (mk_kix ss.s_know) segs K i ss scr
      = sym_stepX segs K i ss scr := by
  have hXB : sym_stepXBI (mkbc (facts_of ss.s_know)) (mk_kix ss.s_know) segs K i ss scr
      = sym_stepXB segs (mkbc (facts_of ss.s_know)) K i ss scr := by
    unfold sym_stepXBI
    rw [sym_stepBI_eq]
    with_unfolding_all exact rfl
  rw [hXB]
  exact sym_stepXB_eq segs K i ss scr

theorem sym_execTXBI_go_eq (segs : List Segment) (t : itab) (K : Nat) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execTXBI_go (mkbc (facts_of ss.s_know)) (mk_kix ss.s_know) segs t K fuel first stops ss ck
        = sym_execTX_go segs t K fuel first stops ss ck := by
  intro fuel
  induction fuel with
  | zero =>
      intro first stops ss ck
      simp only [sym_execTXBI_go, sym_execTX_go]
  | succ f ih =>
      intro first stops ss ck
      simp only [sym_execTXBI_go, sym_execTX_go]
      by_cases h1 : (!first && stops.any (fun x => x == ss.s_pc)) = true
      · rw [ite_eq_left h1, ite_eq_left h1]
      · rw [ite_eq_right h1, ite_eq_right h1]
        cases hlk : itab_lookup t ss.s_pc with
        | none => simp only [hlk]
        | some i =>
            simp only [hlk]
            rw [sym_stepXBI_eq]
            cases hh : sym_stepX segs K i ss scr_nil with
            | SStop => simp only [hh]
            | SOk ss1 scs1 scr1 =>
                cases scs1 with
                | nil =>
                    have hk : ss1.s_know = ss.s_know :=
                      sym_stepX_know segs K i ss scr_nil ss1 [] scr1 hh
                    simp only [hh]
                    rw [← hk]
                    exact ih false stops ss1 _
                | cons sc rest => simp only [hh]

theorem sym_execTXBI_eq (segs : List Segment) (kn0 : List kentry) (t : itab) (K : Nat)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (h : ss.s_know = kn0) :
    sym_execTXBI segs (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss
      = sym_execTX segs t K fuel first stops ss := by
  subst h
  unfold sym_execTXBI sym_execTX
  exact sym_execTXBI_go_eq segs t K fuel first stops (clr ss) (clr ss)

/-! ## B6: the prune layer (`kcutB` .. `prunepcB`) —  -/

/-- `kcutB`: exact split of a zero entry by a written range, modulo base
    spelling, decided by exact linear arithmetic on the context's facts. -/
def kcutB (bc : bctx) (mk : saddr → expr → kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr) : List kentry :=
  let ws := mkAlu .ADD wb (.ELit wk)
  let ks := mkAlu .ADD kb (.ELit kk)
  let lowc : Bool :=
    if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false
    else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk), (len, 0)] [(wb, wk)]
    else false
  let low := if lowc then [mk (SA kb kk) (mkAlu .SUB ws ks)] else []
  let highc : Bool :=
    if lin_ge0B bc [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)]
    then
      if lin_ge0B bc [(wb, wk), (wn, 0)] [(kb, kk)]
      then lin_ge0B bc [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)]
      else false
    else false
  let high :=
    if highc then
      let we := mkAlu .ADD ws wn
      let (hb, ho) := split_lit we
      let ha :=
        if (lin_ge0B bc [(hb, ho)] [(wb, wk), (wn, 0)] && lin_ge0B bc [(wb, wk), (wn, 0)] [(hb, ho)])
        then SA hb ho else SA we 0
      [mk ha (mkAlu .SUB (mkAlu .ADD ks len) we)]
    else []
  low ++ high

/-- `kcutB` at `KZero`. -/
def kzero_cutB (bc : bctx) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcutB bc .KZero wb wk wn kb kk len

/-- `kcutB` at `KFill c`. -/
def kfill_cutB (bc : bctx) (c : Int) (wb : expr) (wk : Int) (wn : expr) (kb : expr)
    (kk : Int) (len : expr) : List kentry :=
  kcutB bc (fun a n => .KFill a n c) wb wk wn kb kk len

/-- `kcutB` at `KUnk`. -/
def kunk_cutB (bc : bctx) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcutB bc .KUnk wb wk wn kb kk len

/-- `prune_zfB`: the same-base-or-not protocol shared by `KZero`/`KFill`/
    `KUnk`, against the store `wb+k, +w`.  `apart`/`diffbase` are thunks. -/
def prune_zfB (bc : bctx) (mk : saddr → expr → kentry) (wb : expr) (k : Int) (w : Nat)
    (K : kentry) (kb : expr) (kk : Int) (len : expr) (apart : Unit → Bool) (hints : List Bool)
    (diffbase : Unit → List kentry × List sidecond × List Bool) :
    List kentry × List sidecond × List Bool :=
  if expr_eqb kb wb then
    match len with
    | .ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ =>
        if k + (w : Int) ≤ kk then ([K], [], hints)
        else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
  else if apart () then ([K], [], hints)
  else
    match kcutB bc mk wb k (elen w) kb kk len with
    | [] => diffbase ()
    | cut => (cut, [], hints)

/-- `prune1pB`: one knowledge entry against a freshly written range
    `wa, wa+w`. -/
def prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) : List kentry × List sidecond × List Bool :=
  let k := wa.a_off
  let diffbase (ka : saddr) (kl : expr) : List kentry × List sidecond × List Bool :=
    let apart := ranges_apart_pB bc sp wa.a_base k (elen w) ka.a_base ka.a_off kl
    if apart then ([K], [], hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj wa (elen w) ka kl], hs)
      | false :: hs => ([], [], hs)
      | [] => ([], [], [])
  match K with
  | .KAlign _ _ => ([K], [], hints)
  | .KRange _ _ _ => ([K], [], hints)
  | .KWr _ _ => ([K], [], hints)
  | .KDisj _ _ _ _ => ([K], [], hints)
  | .KImg lo hi =>
      match wa.a_base with
      | .ELit 0 =>
          let r1 := if lo < min k hi then [.KImg lo (min k hi)] else []
          let lo2 := max lo (k + (w : Int))
          let r2 := if lo2 < hi then [.KImg lo2 hi] else []
          (r1 ++ r2, [], hints)
      | _ =>
          if hi - lo < 2 ^ 64 then diffbase (SA (.ELit 0) lo) (.ELit (hi - lo))
          else ([], [], hints)
  | .KZero ⟨kb, kk⟩ len =>
      prune_zfB bc .KZero wa.a_base k w K kb kk len
        (fun _ => ranges_apart_pB bc sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KFill ⟨kb, kk⟩ len c =>
      prune_zfB bc (fun a n => .KFill a n c) wa.a_base k w K kb kk len
        (fun _ => ranges_apart_pB bc sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KUnk ⟨kb, kk⟩ len =>
      prune_zfB bc .KUnk wa.a_base k w K kb kk len
        (fun _ => ranges_apart_pB bc sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KWord ⟨kb, kk⟩ w' v =>
      if expr_eqb kb wa.a_base then
        (if (kk + (w' : Int) ≤ k || k + (w : Int) ≤ kk)
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))
      else if ranges_apart_pB bc sp wa.a_base k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (w == 1 && w' == 1 && expr_eqb wv v)
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | .KBlob ⟨kb, kk⟩ len bk =>
      if expr_eqb kb wa.a_base then
        match len with
        | .ELit l0 =>
            let l := l0 % two64
            (if (kk + l ≤ k || k + (w : Int) ≤ kk) then ([K], [], hints) else ([], [], hints))
        | _ => if k + (w : Int) ≤ kk then ([K], [], hints) else ([], [], hints)
      else diffbase (SA kb kk) len

/-- `ranges_apart_pB`: `ranges_apart_p` with the entry-side base range
    supplied, on the context's facts. -/
def ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (br2 : Option (Int × Int)) (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 =>
      let m1 := zlit64 z1
      let m2 := zlit64 z2
      if (match sp.sp_rng, br2 with
          | some (lo1, hi1), some (lo2, hi2) =>
              (hi1 + k1 + m1 ≤ lo2 + k2 || hi2 + k2 + m2 ≤ lo1 + k1)
          | _, _ => false) then true
      else if in_sidesB bc sp.sp_D b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp.sp_rng, br2, sp.sp_h1, xhiB bc n2 with
        | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
            if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
            else if le_end (end_hiB bc b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
            else le_end (end_hiB bc b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
        | _, _, _, _ => false) then true
    else if in_sides_xB bc sp.sp_Dx b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2), (n2, 0)]

/-- `prune1pcB`: `prune1pB` with the entry-side base range `br2` supplied. -/
def prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) (br2 : Option (Int × Int)) :
    List kentry × List sidecond × List Bool :=
  let k := wa.a_off
  let diffbase (ka : saddr) (kl : expr) : List kentry × List sidecond × List Bool :=
    let apart := ranges_apart_pcB bc sp wa.a_base k (elen w) br2 ka.a_base ka.a_off kl
    if apart then ([K], [], hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj wa (elen w) ka kl], hs)
      | false :: hs => ([], [], hs)
      | [] => ([], [], [])
  match K with
  | .KAlign _ _ | .KRange _ _ _ | .KWr _ _ | .KDisj _ _ _ _ | .KImg _ _ =>
      prune1pB bc sp wa w wv K hints
  | .KZero ⟨kb, kk⟩ len =>
      if expr_eqb kb wa.a_base then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kzero_cutB bc wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KFill ⟨kb, kk⟩ len c =>
      if expr_eqb kb wa.a_base then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kfill_cutB bc c wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KUnk ⟨kb, kk⟩ len =>
      if expr_eqb kb wa.a_base then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kunk_cutB bc wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KWord ⟨kb, kk⟩ w' v =>
      if expr_eqb kb wa.a_base then prune1pB bc sp wa w wv K hints
      else if ranges_apart_pcB bc sp wa.a_base k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (w == 1 && w' == 1 && expr_eqb wv v)
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | .KBlob ⟨kb, kk⟩ len bk =>
      if expr_eqb kb wa.a_base then prune1pB bc sp wa w wv K hints
      else diffbase (SA kb kk) len

/-- `prunepcB`: `prune1pcB` over the knowledge list, with the entry-side
    base ranges cached. -/
def prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) (hints : List Bool) (cache : List (expr × Option (Int × Int))) :
    List kentry × List sidecond × List Bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let (br2, cache') :=
        match kbase K with
        | some kb =>
            match br_lookup cache kb with
            | some r => (r, cache)
            | none =>
                let r := base_rangeB bc kb
                (r, (kb, r) :: cache)
        | none => (none, cache)
      let (kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2
      let (r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache'
      (kept ++ r, scs1 ++ scs2, hs2)

/-! ### The prune layer equals its reference -/

theorem kcutB_eqf (fk : List kentry) : kcutB (mkbc fk) = fun mk => kcut mk fk := by
  funext mk wb wk wn kb kk len
  simp only [kcutB, kcut, lin_ge0B_eqf]
  try (with_unfolding_all exact rfl)

theorem kzero_cutB_eqf (fk : List kentry) : kzero_cutB (mkbc fk) = kzero_cut fk := by
  funext wb wk wn kb kk len
  simp only [kzero_cutB, kzero_cut, kcutB_eqf]
  try (with_unfolding_all exact rfl)

theorem kfill_cutB_eqf (fk : List kentry) :
    kfill_cutB (mkbc fk) = fun c => kfill_cut c fk := by
  funext c wb wk wn kb kk len
  simp only [kfill_cutB, kfill_cut, kcutB_eqf]
  try (with_unfolding_all exact rfl)

theorem kunk_cutB_eqf (fk : List kentry) : kunk_cutB (mkbc fk) = kunk_cut fk := by
  funext wb wk wn kb kk len
  simp only [kunk_cutB, kunk_cut, kcutB_eqf]
  try (with_unfolding_all exact rfl)

theorem prune_zfB_eqf (fk : List kentry) : prune_zfB (mkbc fk) = fun mk => prune_zf mk fk := by
  funext mk wb k w K kb kk len apart hints diffbase
  simp only [prune_zfB, prune_zf, kcutB_eqf]
  try (with_unfolding_all exact rfl)

theorem prune1pB_eqf (fk : List kentry) : prune1pB (mkbc fk) = prune1p fk := by
  funext sp wa w wv K hints
  cases K <;>
    simp only [prune1pB, prune1p, ranges_apart_pB_eqf, prune_zfB_eqf] <;>
    try (with_unfolding_all exact rfl)

theorem ranges_apart_pcB_eqf (fk : List kentry) :
    ranges_apart_pcB (mkbc fk) = ranges_apart_pc fk := by
  funext sp b1 k1 n1 br2 b2 k2 n2
  simp only [ranges_apart_pcB, ranges_apart_pc, in_sidesB_eqf, lin_apartB_eqf, xhiB_eqf,
    end_hiB_eqf, in_sides_xB_eqf, lin_ge0B_eqf]
  try (with_unfolding_all exact rfl)

theorem prune1pcB_eqf (fk : List kentry) : prune1pcB (mkbc fk) = prune1pc fk := by
  funext sp wa w wv K hints br2
  cases K <;>
    simp only [prune1pcB, prune1pc, prune1pB_eqf, ranges_apart_pcB_eqf, kzero_cutB_eqf,
      kfill_cutB_eqf, kunk_cutB_eqf] <;>
    try (with_unfolding_all exact rfl)

theorem prunepcB_eqf (fk : List kentry) : prunepcB (mkbc fk) = prunepc fk := by
  funext sp wa w wv kn hints cache
  induction kn generalizing hints cache with
  | nil => rfl
  | cons K rest ih =>
      simp only [prunepcB, prunepc, prune1pcB_eqf, ih, base_rangeB_eqf]
      try (with_unfolding_all exact rfl)


/-! ## B7 (entry point): the horizontal carry — 

    Knowledge about `mem_denot E base log` from knowledge about `base`:
    process the log oldest-first, each store pruning what it overlaps and
    then recording itself.  `carryB` is `carry` with the block context
    threaded through. -/

/-- `carryB`: the inter-block carry on the block context. -/
def carryB (bc : bctx) (log : List sentry) (kn : List kentry) (hints : List Bool) :
    List kentry × List sidecond × List Bool :=
  match log with
  | [] => (kn, [], hints)
  | ⟨a, w, v⟩ :: older =>
      let (kn1, scs1, hs1) := carryB bc older kn hints
      let (kn2, scs2, hs2) :=
        prunepcB bc (mk_sprepB bc a.a_base a.a_off (elen w)) a w v kn1 hs1 []
      (.KWord a w v :: kn2, scs1 ++ scs2, hs2)
/-! ## B7: the fact-invariance chain -/

theorem filter_nil_app (l1 l2 : List kentry) (H1 : l1.filter is_factb = [])
    (H2 : l2.filter is_factb = []) : (l1 ++ l2).filter is_factb = [] := by
  rw [List.filter_append, H1, H2]
  rfl

theorem filter_if_single (c : Bool) (K : kentry) (H : is_factb K = false) :
    (if c then [K] else []).filter is_factb = [] := by
  cases c <;> simp [H]

theorem filter_if_nofacts {p : Prop} [Decidable p] (l : List kentry)
    (H : ∀ K ∈ l, is_factb K = false) : (if p then l else []).filter is_factb = [] := by
  by_cases hp : p
  · rw [ite_eq_left hp, List.filter_eq_nil_iff]
    intro a ha
    rw [H a ha]
    simp
  · rw [ite_eq_right hp]
    rfl

theorem kcut_nofacts (mk : saddr → expr → kentry) (kn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (H : ∀ a n, is_factb (mk a n) = false) :
    (kcut mk kn wb wk wn kb kk len).filter is_factb = [] := by
  unfold kcut
  dsimp only
  apply filter_nil_app
  · apply filter_if_nofacts
    intro K hK
    simp only [List.mem_singleton] at hK
    subst hK
    exact H _ _
  · apply filter_if_nofacts
    intro K hK
    simp only [List.mem_singleton] at hK
    subst hK
    exact H _ _

theorem ktrim_nofacts (mk : saddr → expr → kentry) (kb : expr) (kk : Int) (l0 : Int)
    (k : Int) (w : Nat) (H : ∀ a n, is_factb (mk a n) = false) :
    (ktrim mk kb kk l0 k w).filter is_factb = [] := by
  unfold ktrim
  dsimp only
  apply filter_nil_app <;>
    (apply filter_if_nofacts; intro K hK; simp only [List.mem_singleton] at hK; subst hK; exact H _ _)

theorem kword_cut_nofacts (kb : expr) (kk : Int) (w' : Nat) (v : expr) (k : Int) (w : Nat) :
    (kword_cut kb kk w' v k w).filter is_factb = [] := by
  unfold kword_cut
  cases v <;> dsimp only
  · apply filter_nil_app <;>
      (apply filter_if_nofacts; intro K hK; simp only [List.mem_singleton] at hK; subst hK; rfl)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem prune_zf_nofacts {mk : saddr → expr → kentry} {allkn : List kentry} {wb : expr}
    {k : Int} {w : Nat} {K : kentry} {kb : expr} {kk : Int} {len : expr}
    {apart : Unit → Bool} {hints : List Bool}
    {diffbase : Unit → List kentry × List sidecond × List Bool}
    (Hm : ∀ a n, is_factb (mk a n) = false) (HK : is_factb K = false)
    (Hd : ((diffbase ()).1).filter is_factb = []) :
    ((prune_zf mk allkn wb k w K kb kk len apart hints diffbase).1).filter is_factb = [] := by
  unfold prune_zf
  split
  · split
    · exact ktrim_nofacts mk kb kk _ k w Hm
    · all_goals (repeat (first
        | exact kcut_nofacts mk allkn wb k (elen w) kb kk len Hm
        | split
        | simp [HK]))
  · split
    · simp [HK]
    · cases hh : kcut mk allkn wb k (elen w) kb kk len with
      | nil => exact Hd
      | cons c cs =>
          have hcut : (kcut mk allkn wb k (elen w) kb kk len).filter is_factb = [] :=
            kcut_nofacts mk allkn wb k (elen w) kb kk len Hm
          rw [hh] at hcut
          exact hcut

theorem prune1p_facts (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (hints : List Bool) :
    ((prune1p allkn sp wa w wv K hints).1).filter is_factb = [K].filter is_factb := by
  cases K with
  | KAlign e m => rfl
  | KRange e lo hi => rfl
  | KWr sa len => rfl
  | KDisj a1 n1 a2 n2 => rfl
  | KImg lo hi =>
      have hR : ([.KImg lo hi].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      cases hb : wa.a_base <;> (try dsimp only) <;>
        repeat (first | rfl | split | simp [is_factb])
  | KZero sa len =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KZero ⟨kb, kk⟩ len].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      refine prune_zf_nofacts (mk := .KZero) ?_ ?_ ?_
      · intro a n
        rfl
      · rfl
      · (try dsimp only)
        repeat (first | rfl | split | simp [is_factb])
  | KFill sa len c =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KFill ⟨kb, kk⟩ len c].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      refine prune_zf_nofacts (mk := fun a n => .KFill a n c) ?_ ?_ ?_
      · intro a n
        rfl
      · rfl
      · (try dsimp only)
        repeat (first | rfl | split | simp [is_factb])
  | KUnk sa len =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KUnk ⟨kb, kk⟩ len].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      refine prune_zf_nofacts (mk := .KUnk) ?_ ?_ ?_
      · intro a n
        rfl
      · rfl
      · (try dsimp only)
        repeat (first | rfl | split | simp [is_factb])
  | KWord sa w' v =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KWord ⟨kb, kk⟩ w' v].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      repeat (first
        | rfl
        | split
        | exact kword_cut_nofacts kb kk w' v _ w
        | simp [is_factb])
  | KBlob sa len bk =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KBlob ⟨kb, kk⟩ len bk].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1p]
      repeat (first | rfl | split | simp [is_factb])

theorem prune1pc_facts (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (hints : List Bool) (br2 : Option (Int × Int)) :
    ((prune1pc allkn sp wa w wv K hints br2).1).filter is_factb = [K].filter is_factb := by
  cases K with
  | KAlign e m => exact prune1p_facts allkn sp wa w wv _ hints
  | KRange e lo hi => exact prune1p_facts allkn sp wa w wv _ hints
  | KWr sa len => exact prune1p_facts allkn sp wa w wv _ hints
  | KDisj a1 n1 a2 n2 => exact prune1p_facts allkn sp wa w wv _ hints
  | KImg lo hi => exact prune1p_facts allkn sp wa w wv _ hints
  | KZero sa len =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KZero ⟨kb, kk⟩ len].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1pc]
      by_cases hb : expr_eqb kb wa.a_base = true
      · rw [ite_eq_left hb]
        exact prune1p_facts allkn sp wa w wv _ hints
      · rw [ite_eq_right hb]
        split
        · simp [is_factb]
        · cases hcut : kzero_cut allkn wa.a_base wa.a_off (elen w) kb kk len with
          | nil =>
              (try dsimp only)
              repeat (first | rfl | split | simp [is_factb])
          | cons c cs =>
              have hcut' : (kzero_cut allkn wa.a_base wa.a_off (elen w) kb kk len).filter is_factb
                  = [] := by
                unfold kzero_cut
                exact kcut_nofacts .KZero allkn wa.a_base wa.a_off (elen w) kb kk len (by intro a n; rfl)
              rw [hcut] at hcut'
              exact hcut'
  | KFill sa len c =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KFill ⟨kb, kk⟩ len c].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1pc]
      by_cases hb : expr_eqb kb wa.a_base = true
      · rw [ite_eq_left hb]
        exact prune1p_facts allkn sp wa w wv _ hints
      · rw [ite_eq_right hb]
        split
        · simp [is_factb]
        · cases hcut : kfill_cut c allkn wa.a_base wa.a_off (elen w) kb kk len with
          | nil =>
              (try dsimp only)
              repeat (first | rfl | split | simp [is_factb])
          | cons c' cs =>
              have hcut' : (kfill_cut c allkn wa.a_base wa.a_off (elen w) kb kk len).filter is_factb
                  = [] := by
                unfold kfill_cut
                exact kcut_nofacts (fun a n => .KFill a n c) allkn wa.a_base wa.a_off (elen w) kb kk len
                  (by intro a n; rfl)
              rw [hcut] at hcut'
              exact hcut'
  | KUnk sa len =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KUnk ⟨kb, kk⟩ len].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1pc]
      by_cases hb : expr_eqb kb wa.a_base = true
      · rw [ite_eq_left hb]
        exact prune1p_facts allkn sp wa w wv _ hints
      · rw [ite_eq_right hb]
        split
        · simp [is_factb]
        · cases hcut : kunk_cut allkn wa.a_base wa.a_off (elen w) kb kk len with
          | nil =>
              (try dsimp only)
              repeat (first | rfl | split | simp [is_factb])
          | cons c' cs =>
              have hcut' : (kunk_cut allkn wa.a_base wa.a_off (elen w) kb kk len).filter is_factb
                  = [] := by
                unfold kunk_cut
                exact kcut_nofacts .KUnk allkn wa.a_base wa.a_off (elen w) kb kk len (by intro a n; rfl)
              rw [hcut] at hcut'
              exact hcut'
  | KWord sa w' v =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KWord ⟨kb, kk⟩ w' v].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1pc]
      by_cases hb : expr_eqb kb wa.a_base = true
      · rw [ite_eq_left hb]
        exact prune1p_facts allkn sp wa w wv _ hints
      · rw [ite_eq_right hb]
        repeat (first | rfl | split | simp [is_factb])
  | KBlob sa len bk =>
      obtain ⟨kb, kk⟩ := sa
      have hR : ([.KBlob ⟨kb, kk⟩ len bk].filter is_factb) = ([] : List kentry) := by simp [is_factb]
      rw [hR]
      simp only [prune1pc]
      by_cases hb : expr_eqb kb wa.a_base = true
      · rw [ite_eq_left hb]
        exact prune1p_facts allkn sp wa w wv _ hints
      · rw [ite_eq_right hb]
        repeat (first | rfl | split | simp [is_factb])

theorem prunepc_facts (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) :
    ∀ (hints : List Bool) (cache : List (expr × Option (Int × Int))),
      ((prunepc allkn sp wa w wv kn hints cache).1).filter is_factb = kn.filter is_factb := by
  induction kn with
  | nil => intro hints cache; rfl
  | cons K rest ih =>
      intro hints cache
      simp only [prunepc]
      rw [List.filter_append, prune1pc_facts]
      rw [ih]
      cases hk : is_factb K <;> simp [hk]

theorem carry_facts (log : List sentry) (kn : List kentry) (hints : List Bool) :
    ((carry log kn hints).1).filter is_factb = kn.filter is_factb := by
  induction log with
  | nil => rfl
  | cons e older ih =>
      obtain ⟨a, w, v⟩ := e
      simp only [carry]
      generalize hc : carry older kn hints = c at *
      obtain ⟨kn1, scs1, hs1⟩ := c
      generalize hp : prunepc (facts_of kn1) (mk_sprep (facts_of kn1) a.a_base a.a_off (elen w))
        a w v kn1 hs1 [] = p at *
      obtain ⟨kn2, scs2, hs2⟩ := p
      (try dsimp only)
      rw [List.filter_cons_of_neg (by simp [is_factb])]
      have h2 : kn2.filter is_factb = kn1.filter is_factb := by
        have h := prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) a.a_base a.a_off (elen w))
          a w v kn1 hs1 []
        rw [hp] at h
        (try dsimp only at h)
        exact h
      rw [h2, ih]

theorem carryB_eq (log : List sentry) (kn : List kentry) (hints : List Bool) :
    carryB (mkbc (facts_of kn)) log kn hints = carry log kn hints := by
  induction log with
  | nil => rfl
  | cons e older ih =>
      obtain ⟨a, w, v⟩ := e
      simp only [carryB, carry]
      rw [ih]
      generalize hc : carry older kn hints = c at *
      obtain ⟨kn1, scs1, hs1⟩ := c
      have hcf : kn1.filter is_factb = kn.filter is_factb := by
        have h := carry_facts older kn hints
        rw [hc] at h
        exact h
      have hF : facts_of kn1 = facts_of kn := by
        rw [facts_of_filter, facts_of_filter, hcf]
      rw [hF, mk_sprepB_eqf, prunepcB_eqf]

/-! ## B7 (vertical carry): 

    The VERTICAL carry: every knowledge entry is pushed through all the
    stores of the block, each store pruning what it overlaps; the bases of
    the entries are INTERNED (equal bases get equal small ids) so that the
    dominant `same-base` test becomes an integer comparison. -/

/-! ### Hints `[]`: pruning is a `flat_map` -/

/-- `prune` with no hints, keeping only the kept entries. -/
def g1 (fk : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry) :
    List kentry :=
  (prune1p fk sp wa w wv K []).1

theorem prune1p_nil (fk : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) : prune1p fk sp wa w wv K [] = (g1 fk sp wa w wv K, [], []) := by
  cases K <;>
    simp only [g1, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut] <;>
    repeat (first | rfl | split)

theorem prunep_nil (fk : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) :
    prunep fk sp wa w wv kn [] = (kn.flatMap (g1 fk sp wa w wv), [], []) := by
  induction kn with
  | nil => rfl
  | cons K rest ih =>
      simp only [prunep, List.flatMap_cons, prune1p_nil, ih, List.nil_append]

/-! ### The `PKeep`/`PRepl` fast path: `prune1pc` that SAYS when the entry
    is kept unchanged -/

/-- The result of the fast path: kept unchanged, or replaced by a list. -/
inductive pk_res : Type
  /-- the entry survives unchanged -/
  | PKeep
  /-- the entry is replaced by this list -/
  | PRepl (l : List kentry)

/-- The entries a `pk_res` stands for. -/
def pk_list (K : kentry) : pk_res → List kentry
  | .PKeep => [K]
  | .PRepl l => l

/-- `prune1pc` specialised to no hints, with the same-base test supplied
    (`same`) and a result that SAYS when the entry is kept unchanged. -/
def prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (same : Bool) (br2 : Option (Int × Int)) : pk_res :=
  let k := wa.a_off
  let wb := wa.a_base
  let zfK (mk : saddr → expr → kentry) (kb : expr) (kk : Int) (len : expr) : pk_res :=
    if same then
      match len with
      | .ELit l0 => .PRepl (ktrim mk kb kk l0 k w)
      | _ => if k + (w : Int) ≤ kk then .PKeep else .PRepl (kcutB bc mk wb k (elen w) kb kk len)
    else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then .PKeep
    else
      match kcutB bc mk wb k (elen w) kb kk len with
      | [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then .PKeep else .PRepl []
      | cut => .PRepl cut
  match K with
  | .KAlign _ _ => .PKeep
  | .KRange _ _ _ => .PKeep
  | .KWr _ _ => .PKeep
  | .KDisj _ _ _ _ => .PKeep
  | .KImg lo hi =>
      match wb with
      | .ELit 0 =>
          let r1 := if lo < min k hi then [.KImg lo (min k hi)] else []
          let lo2 := max lo (k + (w : Int))
          let r2 := if lo2 < hi then [.KImg lo2 hi] else []
          .PRepl (r1 ++ r2)
      | _ =>
          if hi - lo < 2 ^ 64 then
            (if ranges_apart_pB bc sp wb k (elen w) (.ELit 0) lo (.ELit (hi - lo)) then .PKeep
             else .PRepl [])
          else .PRepl []
  | .KZero ⟨kb, kk⟩ len => zfK .KZero kb kk len
  | .KFill ⟨kb, kk⟩ len c => zfK (fun a n => .KFill a n c) kb kk len
  | .KUnk ⟨kb, kk⟩ len => zfK .KUnk kb kk len
  | .KWord ⟨kb, kk⟩ w' v =>
      if same then
        (if (kk + (w' : Int) ≤ k || k + (w : Int) ≤ kk) then .PKeep
         else .PRepl (kword_cut kb kk w' v k w))
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then .PKeep
      else if (w == 1 && w' == 1 && expr_eqb wv v) then .PKeep
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then .PKeep
      else .PRepl []
  | .KBlob ⟨kb, kk⟩ len bk =>
      if same then
        match len with
        | .ELit l0 =>
            let l := l0 % two64
            (if (kk + l ≤ k || k + (w : Int) ≤ kk) then .PKeep else .PRepl [])
        | _ => if k + (w : Int) ≤ kk then .PKeep else .PRepl []
      else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then .PKeep else .PRepl []

/-- The fast path on the SAME test as the reference: when `same` says
    "same base" exactly as `prune1pc` tests it, the entries agree. -/
theorem prune1pcK_eq (fk : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (br2 : Option (Int × Int)) (same : Bool)
    (H : match kbase K with
         | some kb => same = expr_eqb kb wa.a_base
         | none => True) :
    pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2)
      = (prune1pc fk sp wa w wv K [] br2).1 := by
  cases K with
  | KAlign e m => rfl
  | KRange e lo hi => rfl
  | KWr sa len => rfl
  | KDisj a1 n1 a2 n2 => rfl
  | KImg lo hi =>
      simp only [kbase] at H
      obtain ⟨wb, k⟩ := wa
      simp only [prune1pcK, prune1pc, prune1p, ranges_apart_pB_eqf]
      cases wb with
      | ELit a =>
          by_cases hz : a = 0
          · simp [hz]
            repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
          · simp [hz]
            repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EVar n => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EAlu o a b => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EAluw o a b => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EMd o a b => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EMdw o a b => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EExt s l n a => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
      | EBlob s kk i n => repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KZero sa len =>
      obtain ⟨kb, kk⟩ := sa
      obtain ⟨wb, k⟩ := wa
      simp only [kbase] at H
      subst same
      simp only [prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, ranges_apart_pcB_eqf,
        kcutB_eqf]
      cases hC : expr_eqb kb wb <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KFill sa len c =>
      obtain ⟨kb, kk⟩ := sa
      obtain ⟨wb, k⟩ := wa
      simp only [kbase] at H
      subst same
      simp only [prune1pcK, prune1pc, prune1p, prune_zf, kfill_cut, ranges_apart_pcB_eqf,
        kcutB_eqf]
      cases hC : expr_eqb kb wb <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KUnk sa len =>
      obtain ⟨kb, kk⟩ := sa
      obtain ⟨wb, k⟩ := wa
      simp only [kbase] at H
      subst same
      simp only [prune1pcK, prune1pc, prune1p, prune_zf, kunk_cut, ranges_apart_pcB_eqf,
        kcutB_eqf]
      cases hC : expr_eqb kb wb <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KWord sa w' v =>
      obtain ⟨kb, kk⟩ := sa
      obtain ⟨wb, k⟩ := wa
      simp only [kbase] at H
      subst same
      simp only [prune1pcK, prune1pc, prune1p, ranges_apart_pcB_eqf, kcutB_eqf]
      cases hC : expr_eqb kb wb <;> simp [hC] <;>
        repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KBlob sa len bk =>
      obtain ⟨kb, kk⟩ := sa
      obtain ⟨wb, k⟩ := wa
      simp only [kbase] at H
      subst same
      simp only [prune1pcK, prune1pc, prune1p, ranges_apart_pcB_eqf, kcutB_eqf]
      cases hC : expr_eqb kb wb <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)

/-! ### Relating the cached `prune1pc`/`prunepc` to the plain `prune1p`/`prunep`

    (copies of the `AxSymExec3Sound` lemmas the vertical carry needs) -/

/-- Substituting the entry's own base range makes the cached apartness test
    the plain one. -/
theorem ranges_apart_pc_base_range (allkn : List kentry) (sp : sprep) (b1 : expr) (k1 : Int)
    (n1 : expr) (b2 : expr) (k2 : Int) (n2 : expr) :
    ranges_apart_pc allkn sp b1 k1 n1 (base_range allkn b2) b2 k2 n2
      = ranges_apart_p allkn sp b1 k1 n1 b2 k2 n2 := by
  cases n1 <;> cases n2 <;>
    simp only [ranges_apart_pc, ranges_apart_p, num_apart_p] <;>
    try (with_unfolding_all exact rfl)

theorem p_prune1pc_eq (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (hints : List Bool) (br2 : Option (Int × Int))
    (Hb : match kbase K with
          | some kb => br2 = base_range allkn kb
          | none => True) :
    prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints := by
  cases K with
  | KAlign e m => rfl
  | KRange e lo hi => rfl
  | KWr sa len => rfl
  | KDisj a1 n1 a2 n2 => rfl
  | KImg lo hi => rfl
  | KZero sa len =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kbase] at Hb
      subst br2
      simp only [prune1pc, prune1p, prune_zf, kzero_cut, ranges_apart_pc_base_range]
      cases hC : expr_eqb kb wa.a_base <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KFill sa len c =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kbase] at Hb
      subst br2
      simp only [prune1pc, prune1p, prune_zf, kfill_cut, ranges_apart_pc_base_range]
      cases hC : expr_eqb kb wa.a_base <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KUnk sa len =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kbase] at Hb
      subst br2
      simp only [prune1pc, prune1p, prune_zf, kunk_cut, ranges_apart_pc_base_range]
      cases hC : expr_eqb kb wa.a_base <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KWord sa w' v =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kbase] at Hb
      subst br2
      simp only [prune1pc, prune1p, ranges_apart_pc_base_range]
      cases hC : expr_eqb kb wa.a_base <;> simp [hC] <;>
        repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)
  | KBlob sa len bk =>
      obtain ⟨kb, kk⟩ := sa
      simp only [kbase] at Hb
      subst br2
      simp only [prune1pc, prune1p, ranges_apart_pc_base_range]
      cases hC : expr_eqb kb wa.a_base <;> simp [hC] <;>
        cases len <;> repeat (first | rfl | split | (with_unfolding_all exact rfl) | simp_all | omega)

/-- A cache is sound when every entry's stored range is its base's range. -/
def p_br_cache_ok (allkn : List kentry) (c : List (expr × Option (Int × Int))) : Prop :=
  ∀ p ∈ c, p.2 = base_range allkn p.1

theorem p_br_lookup_ok (allkn : List kentry) (c : List (expr × Option (Int × Int)))
    (b : expr) (r : Option (Int × Int)) (Hc : p_br_cache_ok allkn c)
    (HL : br_lookup c b = some r) : r = base_range allkn b := by
  induction c with
  | nil => simp [br_lookup] at HL
  | cons p rest ih =>
      obtain ⟨b', r'⟩ := p
      simp only [br_lookup] at HL
      by_cases h : expr_eqb b b' = true
      · rw [ite_eq_left h] at HL
        injection HL with HL'
        subst HL'
        have h1 : (b', r') ∈ (b', r') :: rest := by simp
        have h2 := Hc _ h1
        simp only at h2
        rw [h2, p_expr_eqb_eq b b' h]
      · rw [ite_eq_right h] at HL
        exact ih (fun p hp => Hc p (List.mem_cons_of_mem _ hp)) HL

theorem p_prunepc_eq (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) :
    ∀ (hints : List Bool) (cache : List (expr × Option (Int × Int))),
      p_br_cache_ok allkn cache →
      prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints := by
  induction kn with
  | nil => intro hints cache Hc; rfl
  | cons K rest ih =>
      intro hints cache Hc
      simp only [prunepc, prunep]
      cases hk : kbase K with
      | none =>
          simp only [hk]
          rw [p_prune1pc_eq allkn sp wa w wv K hints none (by simp [hk])]
          generalize hp : prune1p allkn sp wa w wv K hints = p
          obtain ⟨kept, scs1, hs1⟩ := p
          simp only [hp]
          rw [ih hs1 cache Hc]
      | some kb =>
          cases hL : br_lookup cache kb with
          | none =>
              simp only [hk, hL]
              rw [p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb) (by simp [hk])]
              generalize hp : prune1p allkn sp wa w wv K hints = p
              obtain ⟨kept, scs1, hs1⟩ := p
              simp only [hp]
              rw [ih hs1 ((kb, base_range allkn kb) :: cache)]
              · intro p hp2
                simp only [List.mem_cons] at hp2
                rcases hp2 with h | h
                · rw [h]
                · exact Hc p h
          | some r =>
              simp only [hk, hL]
              rw [p_prune1pc_eq allkn sp wa w wv K hints r
                (by simp [hk]; exact p_br_lookup_ok allkn cache kb r Hc hL)]
              generalize hp : prune1p allkn sp wa w wv K hints = p
              obtain ⟨kept, scs1, hs1⟩ := p
              simp only [hp]
              rw [ih hs1 cache Hc]

/-! ### Base interning (per block): equal bases get equal small ids -/

/-- The bucket key of a base: its first variable. -/
def bkey (e : expr) : Option Nat := first_var e

/-- A base together with its (cached) range. -/
structure binfo where
  /-- the base expression -/
  bi_base : expr
  /-- `base_rangeB` of it -/
  bi_br : Option (Int × Int)

/-- `BI` — the record constructor. -/
abbrev BI (b : expr) (br : Option (Int × Int)) : binfo := ⟨b, br⟩

/-- The intern table: per-variable buckets, the bucket of bases with no
    variable, the next id, and the id -> info map. -/
structure ntab where
  /-- bucket `n`: bases whose first variable is `n` -/
  nt_vars : List (List (expr × Nat))
  /-- bases with no variable at all -/
  nt_other : List (expr × Nat)
  /-- the next fresh id -/
  nt_next : Nat
  /-- id -> interned info -/
  nt_info : ptree binfo

/-- The empty table. -/
def nt_empty : ntab := ⟨[], [], 0, .PTLeaf⟩

/-- Linear lookup in a bucket. -/
def alookupE : List (expr × Nat) → expr → Option Nat
  | [], _ => none
  | (b', id) :: rest, b => if expr_eqb b b' then some id else alookupE rest b

/-- The bucket a query with key `k` may be answered from. -/
def nt_bucket (t : ntab) (k : Option Nat) : List (expr × Nat) :=
  match k with
  | some n => lget t.nt_vars n
  | none => t.nt_other

/-- Insert a base (and its info) under a fresh id. -/
def nt_add (t : ntab) (k : Option Nat) (p : expr × Nat) (bi : binfo) : ntab :=
  match k with
  | some n => ⟨lset t.nt_vars n p, t.nt_other, t.nt_next + 1, pt_set t.nt_next bi t.nt_info⟩
  | none => ⟨t.nt_vars, p :: t.nt_other, t.nt_next + 1, pt_set t.nt_next bi t.nt_info⟩

/-- Intern a base: an equal base gets an equal id. -/
def intern (bc : bctx) (t : ntab) (b : expr) : (Nat × binfo) × ntab :=
  let k := bkey b
  match alookupE (nt_bucket t k) b with
  | some id =>
      ((id, match pt_get t.nt_info id with
            | some bi => bi
            | none => BI b (base_rangeB bc b)), t)
  | none =>
      let id := t.nt_next
      let bi : binfo := BI b (base_rangeB bc b)
      ((id, bi), nt_add t k (b, id) bi)

/-- The table invariant: every entry is in the bucket of its own key, has
    the right info under its id, ids grow, and a bucket has no duplicates. -/
def NTI (bc : bctx) (t : ntab) : Prop :=
  (∀ (k : Option Nat) (b : expr) (id : Nat), (b, id) ∈ nt_bucket t k →
      k = bkey b ∧ pt_get t.nt_info id = some (BI b (base_rangeB bc b))
        ∧ id < t.nt_next)
  ∧ (∀ (k : Option Nat) (b : expr) (id id' : Nat), (b, id) ∈ nt_bucket t k →
      (b, id') ∈ nt_bucket t k → id = id')

theorem nt_bucket_empty (k : Option Nat) : nt_bucket nt_empty k = [] := by
  cases k with
  | none => rfl
  | some n => simp [nt_bucket, nt_empty, lget]

theorem NTI_empty (bc : bctx) : NTI bc nt_empty := by
  constructor
  · intro k b id h
    rw [nt_bucket_empty] at h
    exact absurd h (List.not_mem_nil)
  · intro k b id id' h
    rw [nt_bucket_empty] at h
    exact absurd h (List.not_mem_nil)

theorem alookupE_Some (l : List (expr × Nat)) (b : expr) (id : Nat)
    (H : alookupE l b = some id) : (b, id) ∈ l := by
  induction l with
  | nil => simp [alookupE] at H
  | cons p rest ih =>
      obtain ⟨b', id'⟩ := p
      simp only [alookupE] at H
      by_cases h : expr_eqb b b' = true
      · rw [ite_eq_left h] at H
        injection H with H'
        subst H'
        rw [p_expr_eqb_eq b b' h]
        exact List.mem_cons_self ..
      · rw [ite_eq_right h] at H
        exact List.mem_cons_of_mem _ (ih H)

theorem alookupE_None (l : List (expr × Nat)) (b : expr) (id : Nat)
    (H : alookupE l b = none) : (b, id) ∉ l := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      obtain ⟨b', id'⟩ := p
      simp only [alookupE] at H
      by_cases h : expr_eqb b b' = true
      · rw [ite_eq_left h] at H
        exact absurd H (by simp)
      · rw [ite_eq_right h] at H
        intro hmem
        have hsplit : (b, id) = (b', id') ∨ (b, id) ∈ rest := by
          simpa using hmem
        rcases hsplit with heq | hmem2
        · injection heq with hb hid
          subst hb
          rw [kx_expr_eqb_refl] at h
          exact absurd rfl h
        · exact ih H hmem2

theorem nt_add_bucket (t : ntab) (k : Option Nat) (p : expr × Nat) (bi : binfo)
    (k' : Option Nat) :
    nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k' := by
  cases k with
  | none =>
      cases k' with
      | none => simp [nt_add, nt_bucket, okey_eqb]
      | some m => simp [nt_add, nt_bucket, okey_eqb]
  | some n =>
      cases k' with
      | none => simp [nt_add, nt_bucket, okey_eqb]
      | some m => simpa [nt_add, nt_bucket, okey_eqb] using lget_lset n t.nt_vars p m

theorem nt_add_next (t : ntab) (k : Option Nat) (p : expr × Nat) (bi : binfo) :
    (nt_add t k p bi).nt_next = t.nt_next + 1 := by
  cases k <;> rfl

theorem nt_add_info (t : ntab) (k : Option Nat) (p : expr × Nat) (bi : binfo) :
    (nt_add t k p bi).nt_info = pt_set t.nt_next bi t.nt_info := by
  cases k <;> rfl

theorem intern_ok (bc : bctx) (t : ntab) (b : expr) (id : Nat) (bi : binfo) (t' : ntab)
    (HT : NTI bc t) (H : intern bc t b = ((id, bi), t')) :
    NTI bc t' ∧ bi = BI b (base_rangeB bc b) ∧ (b, id) ∈ nt_bucket t' (bkey b)
      ∧ (∀ k p, p ∈ nt_bucket t k → p ∈ nt_bucket t' k) := by
  obtain ⟨HA, HB⟩ := HT
  simp only [intern] at H
  cases hL : alookupE (nt_bucket t (bkey b)) b with
  | some id0 =>
      simp only [hL] at H
      injection H with h1 h2
      injection h1 with hid hbi
      subst hid
      subst hbi
      subst h2
      have HIn : (b, id0) ∈ nt_bucket t (bkey b) := alookupE_Some _ b id0 hL
      obtain ⟨_, hinfo, _⟩ := HA _ b id0 HIn
      exact ⟨⟨HA, HB⟩, by simp only [hinfo], HIn, fun k p hp => hp⟩
  | none =>
      simp only [hL] at H
      injection H with h1 h2
      injection h1 with hid hbi
      subst hid
      subst hbi
      subst h2
      refine ⟨⟨?_, ?_⟩, rfl, ?_, ?_⟩
      · intro k b0 id0 HIn
        rw [nt_add_bucket] at HIn
        by_cases hkk : k = bkey b
        · rw [ite_eq_left ((okey_eqb_spec k (bkey b)).2 hkk)] at HIn
          rw [nt_add_info, nt_add_next]
          have hsplit : (b0, id0) = (b, t.nt_next) ∨ (b0, id0) ∈ nt_bucket t k := by
            simpa using HIn
          rcases hsplit with heq | hold
          · injection heq with hb0 hid0
            subst hb0
            subst hid0
            exact ⟨hkk, by rw [pt_gss], by omega⟩
          · obtain ⟨hk0, hinfo0, hlt0⟩ := HA _ _ _ hold
            exact ⟨hk0, by rw [pt_gso _ _ _ _ (by omega)]; exact hinfo0, by omega⟩
        · rw [ite_eq_right (by simp only [okey_eqb_spec]; exact hkk)] at HIn
          rw [nt_add_info, nt_add_next]
          obtain ⟨hk0, hinfo0, hlt0⟩ := HA _ _ _ HIn
          exact ⟨hk0, by rw [pt_gso _ _ _ _ (by omega)]; exact hinfo0, by omega⟩
      · intro k b0 id0 id0' H1 H2
        rw [nt_add_bucket] at H1 H2
        by_cases hkk : k = bkey b
        · rw [ite_eq_left ((okey_eqb_spec k (bkey b)).2 hkk)] at H1 H2
          have s1 : (b0, id0) = (b, t.nt_next) ∨ (b0, id0) ∈ nt_bucket t k := by simpa using H1
          have s2 : (b0, id0') = (b, t.nt_next) ∨ (b0, id0') ∈ nt_bucket t k := by simpa using H2
          rcases s1 with e1 | o1 <;> rcases s2 with e2 | o2
          · injection e1 with _ h1
            injection e2 with _ h2
            rw [h1, h2]
          · injection e1 with hb0 hid0
            rw [hb0, hkk] at o2
            exact absurd o2 (alookupE_None _ b id0' hL)
          · injection e2 with hb0 hid0
            rw [hb0, hkk] at o1
            exact absurd o1 (alookupE_None _ b id0 hL)
          · exact HB _ _ _ _ o1 o2
        · rw [ite_eq_right (by simp only [okey_eqb_spec]; exact hkk)] at H1 H2
          exact HB _ _ _ _ H1 H2
      · rw [nt_add_bucket, ite_eq_left ((okey_eqb_spec (bkey b) (bkey b)).2 rfl)]
        exact List.mem_cons_self ..
      · intro k p hp
        rw [nt_add_bucket]
        by_cases hkk : k = bkey b
        · rw [ite_eq_left ((okey_eqb_spec k (bkey b)).2 hkk)]
          exact List.mem_cons_of_mem _ hp
        · rw [ite_eq_right (by simp only [okey_eqb_spec]; exact hkk)]
          exact hp

theorem nt_same_eq (bc : bctx) (t : ntab) (b1 : expr) (id1 : Nat) (b2 : expr) (id2 : Nat)
    (HT : NTI bc t) (H1 : (b1, id1) ∈ nt_bucket t (bkey b1))
    (H2 : (b2, id2) ∈ nt_bucket t (bkey b2)) :
    (id1 == id2) = expr_eqb b1 b2 := by
  obtain ⟨HA, HB⟩ := HT
  obtain ⟨_, I1, _⟩ := HA _ _ _ H1
  obtain ⟨_, I2, _⟩ := HA _ _ _ H2
  cases hh : id1 == id2 with
  | false =>
      cases he : expr_eqb b1 b2 with
      | false => rfl
      | true =>
          exfalso
          have hb : b1 = b2 := p_expr_eqb_eq b1 b2 he
          subst hb
          have hid : id1 = id2 := HB _ _ _ _ H1 H2
          rw [hid] at hh
          simp at hh
  | true =>
      have hid : id1 = id2 := by simpa using hh
      subst hid
      rw [I1] at I2
      injection I2 with hb
      cases hb
      simp [kx_expr_eqb_refl]

/-! ### Store descriptors and the two chains -/

/-- A store of the block, with its interned base id and base range. -/
structure stx where
  /-- the address -/
  sx_a : saddr
  /-- the width -/
  sx_w : Nat
  /-- the stored value -/
  sx_v : expr
  /-- the prepared store-side facts -/
  sx_sp : sprep
  /-- the interned id of its base -/
  sx_bid : Nat
  /-- `base_rangeB` of its base -/
  sx_br : Option (Int × Int)

/-- `mk_stxs`: the log (newest first) as store descriptors (OLDEST first),
    interning every base on the way. -/
def mk_stxs (bc : bctx) (log : List sentry) (t : ntab) : List stx × ntab :=
  match log with
  | [] => ([], t)
  | ⟨a, w, v⟩ :: older =>
      let (sxs, t1) := mk_stxs bc older t
      let (r, t2) := intern bc t1 a.a_base
      let (bid, bi) := r
      (sxs ++ [⟨a, w, v, mk_sprepB bc a.a_base a.a_off (elen w), bid, bi.bi_br⟩], t2)

/-- The entry-side base range of an entry. -/
def obrB (bc : bctx) (K : kentry) : Option (Int × Int) :=
  match kbase K with
  | some kb => base_rangeB bc kb
  | none => none

/-- `prune1pB` with no hints, keeping only the kept entries. -/
def g1cB (bc : bctx) (sx : stx) (K : kentry) : List kentry :=
  (prune1pcB bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K [] (obrB bc K)).1

/-- The plain (slow) chain: every entry visits every store. -/
def chain_slow (bc : bctx) (sxs : List stx) (l : List kentry) : List kentry :=
  match sxs with
  | [] => l
  | sx :: rest => chain_slow bc rest (l.flatMap (g1cB bc sx))

/-- The fast chain: an entry kept unchanged skips the store. -/
def chainK (bc : bctx) (sxs : List stx) (K : kentry) (same_of : Nat → Bool)
    (br2 : Option (Int × Int)) : List kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K (same_of sx.sx_bid) br2 with
      | .PKeep => chainK bc rest K same_of br2
      | .PRepl l => chain_slow bc rest l

/-- The improved chain: pieces with the entry's own base stay on the fast
    path. -/
def chainK2 (bc : bctx) (sxs : List stx) (K : kentry) (okb : Option expr)
    (same_of : Nat → Bool) (br2 : Option (Int × Int)) : List kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K (same_of sx.sx_bid) br2 with
      | .PKeep => chainK2 bc rest K okb same_of br2
      | .PRepl l =>
          match okb with
          | some kb =>
              l.flatMap (fun K' =>
                match kbase K' with
                | some kb' =>
                    if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2
                    else chain_slow bc rest [K']
                | none => chain_slow bc rest [K'])
          | none => chain_slow bc rest l

/-- The knowledge entries, each pushed through the whole block. -/
def entriesV (bc : bctx) (sxs : List stx) (kn : List kentry) (t : ntab) : List kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      match kbase K with
      | some kb =>
          let (r, t') := intern bc t kb
          let (bid, bi) := r
          chainK2 bc sxs K (some kb) (fun i => bid == i) bi.bi_br
            ++ entriesV bc sxs rest t'
      | none =>
          chainK2 bc sxs K none (fun _ => false) none ++ entriesV bc sxs rest t

/-- The stores themselves, each pushed through the LATER stores. -/
def stores_part (bc : bctx) (sxs : List stx) : List kentry :=
  match sxs with
  | [] => []
  | sx :: newer =>
      stores_part bc newer
        ++ chainK2 bc newer (.KWord sx.sx_a sx.sx_w sx.sx_v) (some sx.sx_a.a_base)
            (fun i => sx.sx_bid == i) sx.sx_br

/-- The vertical carry: the stores and the entries, all pushed through the
    block. -/
def carryV (bc : bctx) (log : List sentry) (kn : List kentry) : List kentry :=
  let (sxs, t) := mk_stxs bc log nt_empty
  stores_part bc sxs ++ entriesV bc sxs kn t

/-- The carry used by the plan checker: no stores -> identity; no hints ->
    vertical; otherwise the horizontal `carryB`. -/
def carryK0 (bc : bctx) (log : List sentry) (kn : List kentry) (hints : List Bool) :
    List kentry × List sidecond × List Bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryV bc log kn, [], [])
  | _, _ => carryB bc log kn hints

/-! ### The reference vertical form over the ORIGINAL functions -/

/-- One store applied to a list of entries, in the reference world. -/
def FM (fk : List kentry) (s : sentry) (l : List kentry) : List kentry :=
  match s with
  | ⟨a, w, v⟩ => l.flatMap (g1 fk (mk_sprep fk a.a_base a.a_off (elen w)) a w v)

/-- The reference chain (stores OLDEST first). -/
def chainRo (fk : List kentry) (sxo : List sentry) (l : List kentry) : List kentry :=
  match sxo with
  | [] => l
  | s :: newer => chainRo fk newer (FM fk s l)

/-- The entry a store records. -/
def kw (s : sentry) : kentry :=
  match s with
  | ⟨a, w, v⟩ => .KWord a w v

/-- The stores' own entries, each pushed through the LATER stores. -/
def SPRo (fk : List kentry) (sxo : List sentry) : List kentry :=
  match sxo with
  | [] => []
  | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s]

theorem flat_map_app' {A B : Type} (f : A → List B) (l1 l2 : List A) :
    (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f := by
  induction l1 with
  | nil => rfl
  | cons x r ih => simp only [List.cons_append, List.flatMap_cons, ih, List.append_assoc]

theorem FM_app (fk : List kentry) (s : sentry) (l1 l2 : List kentry) :
    FM fk s (l1 ++ l2) = FM fk s l1 ++ FM fk s l2 := by
  obtain ⟨a, w, v⟩ := s
  simp only [FM]
  exact flat_map_app' _ l1 l2

theorem chainRo_snoc (fk : List kentry) (sxo : List sentry) (s : sentry) (l : List kentry) :
    chainRo fk (sxo ++ [s]) l = FM fk s (chainRo fk sxo l) := by
  induction sxo generalizing l with
  | nil => rfl
  | cons x rest ih => simp only [List.cons_append, chainRo, ih]

theorem chainRo_app (fk : List kentry) (sxo : List sentry) (l1 l2 : List kentry) :
    chainRo fk sxo (l1 ++ l2) = chainRo fk sxo l1 ++ chainRo fk sxo l2 := by
  induction sxo generalizing l1 l2 with
  | nil => rfl
  | cons x rest ih => simp only [chainRo, ih, FM_app]

theorem SPRo_snoc (fk : List kentry) (sxo : List sentry) (s : sentry) :
    SPRo fk (sxo ++ [s]) = kw s :: FM fk s (SPRo fk sxo) := by
  induction sxo with
  | nil => obtain ⟨a, w, v⟩ := s; simp only [List.nil_append]; rfl
  | cons x rest ih =>
      simp only [List.cons_append, SPRo, ih, chainRo_snoc, FM_app, List.singleton_append]

/-- `carry` with the reference functions: the vertical form. -/
theorem carry_vertical (log : List sentry) (kn : List kentry) :
    carry log kn [] = (SPRo (facts_of kn) (List.reverse log) ++ chainRo (facts_of kn) (List.reverse log) kn, [], []) := by
  induction log with
  | nil => rfl
  | cons e older ih =>
      obtain ⟨a, w, v⟩ := e
      have hF : (SPRo (facts_of kn) (List.reverse older) ++ chainRo (facts_of kn) (List.reverse older) kn).filter
            is_factb = kn.filter is_factb := by
        have h := carry_facts older kn []
        rw [ih] at h
        simpa using h
      have hF' : facts_of
            (SPRo (facts_of kn) (List.reverse older) ++ chainRo (facts_of kn) (List.reverse older) kn)
          = facts_of kn := by
        rw [facts_of_filter, hF, ← facts_of_filter]
      simp only [carry, List.reverse_cons, ih, hF']
      have hp := p_prunepc_eq (facts_of kn) (mk_sprep (facts_of kn) a.a_base a.a_off (elen w)) a w v
        (SPRo (facts_of kn) (List.reverse older) ++ chainRo (facts_of kn) (List.reverse older) kn) [] []
        (by intro p hp; simp at hp)
      simp only [hp, prunep_nil]
      rw [SPRo_snoc, chainRo_snoc]
      simp only [FM, kw, flat_map_app']
      rfl

/-! ### The computed side equals the reference -/

/-- The log entry a store descriptor stands for. -/
def strip (sx : stx) : sentry := ⟨sx.sx_a, sx.sx_w, sx.sx_v⟩

/-- A store descriptor is consistent with the intern table. -/
def SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
  (sx.sx_a.a_base, sx.sx_bid) ∈ nt_bucket t (bkey sx.sx_a.a_base)
  ∧ sx.sx_br = base_rangeB bc sx.sx_a.a_base
  ∧ sx.sx_sp = mk_sprepB bc sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w)

theorem FM_nil (fk : List kentry) (s : sentry) : FM fk s [] = [] := by
  obtain ⟨a, w, v⟩ := s
  rfl

theorem SX_OK_mono (bc : bctx) (t t' : ntab) (sx : stx)
    (Hm : ∀ k p, p ∈ nt_bucket t k → p ∈ nt_bucket t' k) (H : SX_OK bc t sx) :
    SX_OK bc t' sx :=
  ⟨Hm _ _ H.1, H.2.1, H.2.2⟩

theorem g1cB_eq (fk : List kentry) (sx : stx)
    (Hsp : sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w))
    (l : List kentry) : l.flatMap (g1cB (mkbc fk) sx) = FM fk (strip sx) l := by
  simp only [FM, strip]
  congr 1
  funext K
  simp only [g1cB, g1]
  rw [prune1pcB_eqf]
  rw [p_prune1pc_eq fk sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K [] (obrB (mkbc fk) K) ?_]
  · simp only [Hsp, mk_sprepB_eqf]
  · cases hk : kbase K with
    | none => simp [hk]
    | some kb => simp [hk, obrB, base_rangeB_eqf]

theorem chain_slow_eq (fk : List kentry) (sxs : List stx) (l : List kentry)
    (HF : ∀ sx ∈ sxs, sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w)) :
    chain_slow (mkbc fk) sxs l = chainRo fk (sxs.map strip) l := by
  induction sxs generalizing l with
  | nil => rfl
  | cons sx rest ih =>
      simp only [List.map_cons, chain_slow, chainRo]
      rw [g1cB_eq fk sx (HF sx (by simp)) l]
      exact ih (FM fk (strip sx) l) (fun s hs => HF s (by simp [hs]))

theorem chainK_eq (fk : List kentry) (sxs : List stx) (K : kentry) (same_of : Nat → Bool)
    (br2 : Option (Int × Int))
    (HS : ∀ sx ∈ sxs, sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w))
    (HK : match kbase K with
          | some kb => br2 = base_rangeB (mkbc fk) kb
              ∧ ∀ sx ∈ sxs, same_of sx.sx_bid = expr_eqb kb sx.sx_a.a_base
          | none => br2 = none) :
    chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K] := by
  induction sxs generalizing K same_of br2 with
  | nil => rfl
  | cons sx rest ih =>
      simp only [chainK, chain_slow]
      have HS' : ∀ s ∈ rest,
          s.sx_sp = mk_sprepB (mkbc fk) s.sx_a.a_base s.sx_a.a_off (elen s.sx_w) :=
        fun s hs => HS s (by simp [hs])
      have HK' : match kbase K with
          | some kb => br2 = base_rangeB (mkbc fk) kb
              ∧ ∀ s ∈ rest, same_of s.sx_bid = expr_eqb kb s.sx_a.a_base
          | none => br2 = none := by
        cases hb : kbase K with
        | none => rw [hb] at HK; exact HK
        | some kb => rw [hb] at HK; exact ⟨HK.1, fun s hs => HK.2 s (by simp [hs])⟩
      have hbr2 : obrB (mkbc fk) K = br2 := by
        simp only [obrB]
        cases hb : kbase K with
        | none => rw [hb] at HK; dsimp only; exact HK.symm
        | some kb => rw [hb] at HK; dsimp only; exact HK.1.symm
      have E : pk_list K (prune1pcK (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K
            (same_of sx.sx_bid) br2)
          = (prune1pcB (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K []
              (obrB (mkbc fk) K)).1 := by
        rw [prune1pcB_eqf, hbr2]
        refine prune1pcK_eq fk sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K br2 (same_of sx.sx_bid) ?_
        cases hb : kbase K with
        | none => simp
        | some kb =>
            rw [hb] at HK
            exact HK.2 sx (by simp)
      generalize hpk : prune1pcK (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K
        (same_of sx.sx_bid) br2 = pk at E
      cases pk with
      | PKeep =>
          simp only [pk_list] at E
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [show (g1cB (mkbc fk) sx K) = [K] from by
            simp only [g1cB]
            rw [← E]]
          exact ih K same_of br2 HS' HK'
      | PRepl l =>
          simp only [pk_list] at E
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, g1cB]
          rw [← E]

theorem flat_map_flat_map {A B C : Type} (f : A → List B) (g : B → List C) (l : List A) :
    (l.flatMap f).flatMap g = l.flatMap (fun x => (f x).flatMap g) := by
  induction l with
  | nil => rfl
  | cons x r ih => simp only [List.flatMap_cons, flat_map_app', ih]

theorem flatMap_singleton_id {A : Type} (l : List A) : l.flatMap (fun x => [x]) = l := by
  induction l with
  | nil => rfl
  | cons x r ih =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.singleton_append, ih]

theorem chain_slow_flat_map (bc : bctx) (sxs : List stx) (l : List kentry) :
    chain_slow bc sxs l = l.flatMap (fun K => chain_slow bc sxs [K]) := by
  induction sxs generalizing l with
  | nil =>
      induction l with
      | nil => rfl
      | cons x r ihm =>
          simp only [chain_slow, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.singleton_append, flatMap_singleton_id]
  | cons sx rest ih =>
      simp only [chain_slow]
      rw [ih]
      rw [flat_map_flat_map]
      congr 1
      funext K
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (ih (g1cB bc sx K)).symm

theorem chainK2_eq (fk : List kentry) (sxs : List stx) (K : kentry) (same_of : Nat → Bool)
    (br2 : Option (Int × Int))
    (HS : ∀ sx ∈ sxs, sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w))
    (HK : match kbase K with
          | some kb => br2 = base_rangeB (mkbc fk) kb
              ∧ ∀ sx ∈ sxs, same_of sx.sx_bid = expr_eqb kb sx.sx_a.a_base
          | none => br2 = none) :
    chainK2 (mkbc fk) sxs K (kbase K) same_of br2 = chain_slow (mkbc fk) sxs [K] := by
  induction sxs generalizing K same_of br2 with
  | nil => rfl
  | cons sx rest ih =>
      simp only [chainK2, chain_slow]
      have HS' : ∀ s ∈ rest,
          s.sx_sp = mk_sprepB (mkbc fk) s.sx_a.a_base s.sx_a.a_off (elen s.sx_w) :=
        fun s hs => HS s (by simp [hs])
      have HK' : match kbase K with
          | some kb => br2 = base_rangeB (mkbc fk) kb
              ∧ ∀ s ∈ rest, same_of s.sx_bid = expr_eqb kb s.sx_a.a_base
          | none => br2 = none := by
        cases hb : kbase K with
        | none => rw [hb] at HK; exact HK
        | some kb => rw [hb] at HK; exact ⟨HK.1, fun s hs => HK.2 s (by simp [hs])⟩
      have hbr2 : obrB (mkbc fk) K = br2 := by
        simp only [obrB]
        cases hb : kbase K with
        | none => rw [hb] at HK; dsimp only; exact HK.symm
        | some kb => rw [hb] at HK; dsimp only; exact HK.1.symm
      have E : pk_list K (prune1pcK (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K
            (same_of sx.sx_bid) br2)
          = (prune1pcB (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K []
              (obrB (mkbc fk) K)).1 := by
        rw [prune1pcB_eqf, hbr2]
        refine prune1pcK_eq fk sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K br2 (same_of sx.sx_bid) ?_
        cases hb : kbase K with
        | none => simp
        | some kb =>
            rw [hb] at HK
            exact HK.2 sx (by simp)
      generalize hpk : prune1pcK (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K
        (same_of sx.sx_bid) br2 = pk at E
      cases pk with
      | PKeep =>
          simp only [pk_list] at E
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [show (g1cB (mkbc fk) sx K) = [K] from by
            simp only [g1cB]
            rw [← E]]
          exact ih K same_of br2 HS' HK'
      | PRepl l =>
          simp only [pk_list] at E
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, g1cB]
          rw [← E]
          cases hb : kbase K with
          | none => rfl
          | some kb =>
              dsimp only
              rw [chain_slow_flat_map]
              congr 1
              funext K'
              cases hk' : kbase K' with
              | none => rfl
              | some kb' =>
                  dsimp only
                  cases hE2 : expr_eqb kb' kb with
                  | false => simp [hE2]
                  | true =>
                      simp only [hE2, ite_true]
                      have hsub : kb' = kb := p_expr_eqb_eq kb' kb hE2
                      rw [← hsub, ← hk']
                      rw [hb] at HK
                      exact ih K' same_of br2 HS' (by
                        rw [hk']
                        dsimp only
                        exact ⟨by rw [hsub]; exact HK.1,
                               fun s hs => by rw [hsub]; exact HK.2 s (by simp [hs])⟩)

theorem Forall_SX_sp (fk : List kentry) (t : ntab) (sxs : List stx)
    (H : ∀ sx ∈ sxs, SX_OK (mkbc fk) t sx) :
    ∀ sx ∈ sxs, sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w) :=
  fun sx hsx => (H sx hsx).2.2

theorem Forall_SX_same (fk : List kentry) (t : ntab) (sxs : List stx) (kb : expr) (bid : Nat)
    (HT : NTI (mkbc fk) t) (HIn : (kb, bid) ∈ nt_bucket t (bkey kb))
    (H : ∀ sx ∈ sxs, SX_OK (mkbc fk) t sx) :
    ∀ sx ∈ sxs, (bid == sx.sx_bid) = expr_eqb kb sx.sx_a.a_base :=
  fun sx hsx => nt_same_eq (mkbc fk) t kb bid sx.sx_a.a_base sx.sx_bid HT HIn (H sx hsx).1

theorem mk_stxs_ok (fk : List kentry) (log : List sentry) (t : ntab) (sxs : List stx) (t' : ntab)
    (HT : NTI (mkbc fk) t) (H : mk_stxs (mkbc fk) log t = (sxs, t')) :
    NTI (mkbc fk) t' ∧ (∀ sx ∈ sxs, SX_OK (mkbc fk) t' sx) ∧ sxs.map strip = List.reverse log
      ∧ (∀ k p, p ∈ nt_bucket t k → p ∈ nt_bucket t' k) := by
  induction log generalizing t sxs t' with
  | nil =>
      simp only [mk_stxs, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact ⟨HT, by simp, rfl, fun k p hp => hp⟩
  | cons e older ih =>
      obtain ⟨a, w, v⟩ := e
      simp only [mk_stxs] at H
      generalize hE : mk_stxs (mkbc fk) older t = c at H
      obtain ⟨sxs0, t1⟩ := c
      generalize hI : intern (mkbc fk) t1 a.a_base = q at H
      obtain ⟨⟨bid, bi⟩, t2⟩ := q
      simp only [Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      obtain ⟨HT1, HS0, Hmap, Hm1⟩ := ih t sxs0 t1 HT hE
      obtain ⟨HT2, Hbi, HIn, Hm2⟩ := intern_ok (mkbc fk) t1 a.a_base bid bi t2 HT1 hI
      refine ⟨HT2, ?_, ?_, ?_⟩
      · intro sx hsx
        simp only [List.mem_append, List.mem_singleton] at hsx
        rcases hsx with h | h
        · exact SX_OK_mono (mkbc fk) t1 t2 sx (fun k p hp => Hm2 k p hp) (HS0 sx h)
        · subst h
          refine ⟨HIn, ?_, rfl⟩
          rw [Hbi]
      · simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_cons, Hmap, strip]
      · intro k p hp
        exact Hm2 k p (Hm1 k p hp)

theorem entriesV_eq (fk : List kentry) (sxs : List stx) (kn : List kentry) (t : ntab)
    (HT : NTI (mkbc fk) t) (HS : ∀ sx ∈ sxs, SX_OK (mkbc fk) t sx) :
    entriesV (mkbc fk) sxs kn t = chainRo fk (sxs.map strip) kn := by
  induction kn generalizing t with
  | nil =>
      induction sxs with
      | nil => rfl
      | cons sx r ih2 =>
          simp only [entriesV, List.map_cons, chainRo, FM_nil]
          exact ih2 (fun s hs => HS s (by simp [hs]))
  | cons K rest ih =>
      cases hb : kbase K with
      | none =>
          simp only [entriesV, hb]
          rw [show K :: rest = [K] ++ rest from rfl, chainRo_app]
          rw [ih t HT HS]
          congr 1
          have h := chainK2_eq fk sxs K (fun _ => false) none (fun sx hsx => (HS sx hsx).2.2)
            (by rw [hb])
          rw [hb] at h
          exact h.trans (chain_slow_eq fk sxs [K] (fun sx hsx => (HS sx hsx).2.2))
      | some kb =>
          simp only [entriesV, hb]
          generalize hI : intern (mkbc fk) t kb = q at *
          obtain ⟨⟨bid, bi⟩, t2⟩ := q
          dsimp only at *
          rw [show K :: rest = [K] ++ rest from rfl, chainRo_app]
          obtain ⟨HT2, Hbi, HIn, Hm2⟩ := intern_ok (mkbc fk) t kb bid bi t2 HT hI
          have HS' : ∀ sx ∈ sxs, SX_OK (mkbc fk) t2 sx :=
            fun sx hsx => SX_OK_mono (mkbc fk) t t2 sx (fun k p hp => Hm2 k p hp) (HS sx hsx)
          rw [ih t2 HT2 HS']
          congr 1
          have h := chainK2_eq fk sxs K (fun i => bid == i) bi.bi_br
            (fun sx hsx => (HS sx hsx).2.2) (by
              rw [hb]
              dsimp only
              exact ⟨by rw [Hbi], Forall_SX_same fk t2 sxs kb bid HT2 HIn HS'⟩)
          rw [hb] at h
          exact h.trans (chain_slow_eq fk sxs [K] (fun sx hsx => (HS sx hsx).2.2))

theorem stores_part_eq (fk : List kentry) (t : ntab) (sxs : List stx)
    (HT : NTI (mkbc fk) t) (HS : ∀ sx ∈ sxs, SX_OK (mkbc fk) t sx) :
    stores_part (mkbc fk) sxs = SPRo fk (sxs.map strip) := by
  induction sxs with
  | nil => rfl
  | cons sx newer ih =>
      obtain ⟨HIn, Hbr, Hsp⟩ := HS sx (by simp)
      have HS' : ∀ s ∈ newer, SX_OK (mkbc fk) t s := fun s hs => HS s (by simp [hs])
      simp only [stores_part, SPRo, List.map_cons]
      rw [ih HS']
      congr 1
      exact (chainK2_eq fk newer (.KWord sx.sx_a sx.sx_w sx.sx_v) (fun i => sx.sx_bid == i)
        sx.sx_br (fun s hs => (HS' s hs).2.2) (by
          show sx.sx_br = base_rangeB (mkbc fk) sx.sx_a.a_base
              ∧ ∀ s ∈ newer, (sx.sx_bid == s.sx_bid) = expr_eqb sx.sx_a.a_base s.sx_a.a_base
          exact ⟨Hbr, fun s hs =>
            nt_same_eq (mkbc fk) t sx.sx_a.a_base sx.sx_bid s.sx_a.a_base s.sx_bid HT HIn
              (HS' s hs).1⟩)).trans
        (chain_slow_eq fk newer [.KWord sx.sx_a sx.sx_w sx.sx_v] (fun s hs => (HS' s hs).2.2))

/-- The plan checker's carry is the reference carry (the concluding theorem). -/
theorem carryK0_eq (log : List sentry) (kn : List kentry) (hints : List Bool) :
    carryK0 (mkbc (facts_of kn)) log kn hints = carry log kn hints := by
  cases log with
  | nil => rfl
  | cons e older =>
      cases hints with
      | nil =>
          simp only [carryK0, carryV]
          generalize hE : mk_stxs (mkbc (facts_of kn)) (e :: older) nt_empty = c at *
          obtain ⟨sxs, t⟩ := c
          obtain ⟨HT, HS, Hmap, _⟩ := mk_stxs_ok (facts_of kn) (e :: older) nt_empty sxs t
            (NTI_empty _) hE
          rw [stores_part_eq (facts_of kn) t sxs HT HS,
            entriesV_eq (facts_of kn) sxs kn t HT HS, Hmap, carry_vertical]
      | cons h hs =>
          simp only [carryK0]
          exact carryB_eq (e :: older) kn (h :: hs)

/-! -/

set_option autoImplicit false

/-! ### The trie map -/

/-- `pt_map`: map a function over every value of the trie. -/
def pt_map {A B : Type} (f : A → B) : ptree A → ptree B
  | .PTLeaf => .PTLeaf
  | .PTNode l o r => .PTNode (pt_map f l) (o.map f) (pt_map f r)

theorem pt_get_map {A B : Type} (f : A → B) (t : ptree A) (k : Nat) :
    pt_get (pt_map f t) k = (pt_get t k).map f := by
  induction t generalizing k with
  | PTLeaf =>
      simp only [pt_map, pt_get.eq_1]
      rfl
  | PTNode l o r ihl ihr =>
      cases k with
      | zero =>
          rw [pt_map, pt_get.eq_2, pt_get.eq_2]
      | succ n =>
          simp only [pt_map]
          rw [pt_get.eq_3, pt_get.eq_3]
          by_cases h : (n % 2 == 0) = true
          · rw [ite_eq_left h, ite_eq_left h]
            exact ihl (n / 2)
          · rw [ite_eq_right h, ite_eq_right h]
            exact ihr (n / 2)

/-! ### Entry descriptors and the group table -/

/-- `kdescr`: base, offset and (literal) byte length of an entry. -/
def kdescr (K : kentry) : Option (expr × Int × Option Int) :=
  match K with
  | .KWord ⟨kb, kk⟩ w _ => some (kb, kk, some (zlit64 (w : Int)))
  | .KZero ⟨kb, kk⟩ len => some (kb, kk, match len with | .ELit z => some (zlit64 z) | _ => none)
  | .KUnk ⟨kb, kk⟩ len => some (kb, kk, match len with | .ELit z => some (zlit64 z) | _ => none)
  | .KFill ⟨kb, kk⟩ len _ => some (kb, kk, match len with | .ELit z => some (zlit64 z) | _ => none)
  | .KBlob ⟨kb, kk⟩ len _ => some (kb, kk, match len with | .ELit z => some (zlit64 z) | _ => none)
  | .KImg lo hi => some (.ELit 0, lo, if hi - lo < 2 ^ 64 then some (zlit64 (hi - lo)) else none)
  | _ => none

/-- Per-entry info from pass 1: interned base id, group id, base, base range,
    offset and byte length. -/
structure einfo where
  /-- the interned id of the entry's base -/
  ei_bid : Nat
  /-- the group the entry was put in -/
  ei_gid : Nat
  /-- the entry's base -/
  ei_kb : expr
  /-- `base_rangeB` of the base -/
  ei_br : Option (Int × Int)
  /-- the entry's offset -/
  ei_k : Int
  /-- the entry's byte length, when literal -/
  ei_m : Option Int

/-- `EI` — the record constructor. -/
abbrev EI (bid gid : Nat) (kb : expr) (br : Option (Int × Int)) (k : Int) (m : Option Int) :
    einfo := ⟨bid, gid, kb, br, k, m⟩

/-- Groups = (interned base, 64 KiB granule of the offset); the group table
    maps a group id to (base id, base range, hull of the members' byte
    ranges).  Any grouping is correct (`inb` re-checks membership); this one
    keeps absolute entries of distant regions apart. -/
abbrev gval := Nat × Option (Int × Int) × (Int × Int)

/-- The group table. -/
abbrev gtab := ptree gval

/-- The pass-1 state: `base -> (granule -> group id)`, the next group id, and
    the group table. -/
structure gst where
  /-- base id -> (granule key -> group id) -/
  gs_gid : ptree (ptree Nat)
  /-- the next fresh group id -/
  gs_next : Nat
  /-- group id -> its descriptor -/
  gs_bnds : gtab

/-- `GST` — the record constructor. -/
abbrev GST (gid : ptree (ptree Nat)) (next : Nat) (bnds : gtab) : gst := ⟨gid, next, bnds⟩

/-- The empty pass-1 state.   -/
def gst_empty : gst := ⟨.PTLeaf, 0, .PTLeaf⟩

/-- `gkey`: the 64 KiB granule of an offset, as a trie key.  Nothing below inspects the encoding: grouping is an
    optimisation and `inb` re-checks membership.) -/
def gkey (kk : Int) : Nat :=
  let g := kk / 65536
  if 0 ≤ g then (2 * g + 1).toNat else (-(2 * g)).toNat

/-- Look the group of `(bid, granule of kk)` up, allocating a fresh id (and
    recording the base under it) when it is new. -/
def ggroup (gs : gst) (bid : Nat) (kk : Int) : Nat × gst :=
  let gk := gkey kk
  let inner : ptree Nat := match pt_get gs.gs_gid bid with | some i => i | none => .PTLeaf
  match pt_get inner gk with
  | some gid => (gid, gs)
  | none =>
      (gs.gs_next,
       ⟨pt_set bid (pt_set gk gs.gs_next inner) gs.gs_gid, gs.gs_next + 1, gs.gs_bnds⟩)

/-- Extend a group's hull by `[lo, hi)`. -/
def bnd_add (gs : gst) (gid bid : Nat) (obr : Option (Int × Int)) (lo hi : Int) : gst :=
  ⟨gs.gs_gid, gs.gs_next,
   match pt_get gs.gs_bnds gid with
   | some (b, o, (l, h)) => pt_set gid (b, o, (min l lo, max h hi)) gs.gs_bnds
   | none => pt_set gid (bid, obr, (lo, hi)) gs.gs_bnds⟩

/-- Pass 1: intern every entry's base, put it in a group, widen the group's
    hull, and describe it.  `none` for entries that are not about memory. -/
def scan_entries (bc : bctx) (kn : List kentry) (t : ntab) (gs : gst) :
    (List (Option einfo) × ntab) × gst :=
  match kn with
  | [] => (([], t), gs)
  | K :: rest =>
      match kdescr K with
      | some (kb, kk, om) =>
          let (r, t1) := intern bc t kb
          let (bid, bi) := r
          let (gid, gs1) :=
            match om with
            | some m =>
                let (gid, gs0) := ggroup gs bid kk
                (gid, bnd_add gs0 gid bid bi.bi_br kk (kk + m))
            | none => (0, gs)
          let r2 := scan_entries bc rest t1 gs1
          ((some (EI bid gid kb bi.bi_br kk om) :: r2.1.1, r2.1.2), r2.2)
      | none =>
          let r2 := scan_entries bc rest t gs
          ((none :: r2.1.1, r2.1.2), r2.2)

/-! ### `verdict`, `mk_fl`, `mk_gl` -/

/-- The literal byte length of a store. -/
def sx_m1 (sx : stx) : Int := zlit64 (sx.sx_w : Int)

/-- The store is numerically apart from the whole group (and has another
    base id). -/
def verdict (sx : stx) (g : gval) : Bool :=
  match g with
  | (b, obr, (glo, ghi)) =>
      if b == sx.sx_bid then false
      else
        match sx.sx_sp.sp_rng, obr with
        | some (lo1, hi1), some (lo2, hi2) =>
            (hi1 + sx.sx_a.a_off + sx_m1 sx - lo2 ≤ glo || ghi ≤ lo1 + sx.sx_a.a_off - hi2)
        | _, _ => false

/-- The stores a group's members must visit, each with the full remainder of
    the chain. -/
def mk_fl (g : gval) (sxs : List stx) : List (stx × List stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict sx g then mk_fl g rest else (sx, rest) :: mk_fl g rest

/-- A group with its filtered store list. -/
abbrev gfl := gval × List (stx × List stx)

/-- `mk_gl`: attach to every group the stores it must visit. -/
def mk_gl (bnds : gtab) (sxs : List stx) : ptree gfl :=
  pt_map (fun g => (g, mk_fl g sxs)) bnds

/-- Syntactic equality of optional ranges. -/
def obr_eqb (a b : Option (Int × Int)) : Bool :=
  match a, b with
  | some (x1, y1), some (x2, y2) => (x1 == x2) && (y1 == y2)
  | none, none => true
  | _, _ => false

/-- The entry belongs to the group and lies inside its hull. -/
def inb (g : gval) (ei : einfo) : Bool :=
  match ei.ei_m, g with
  | some m, (b, obr, (lo, hi)) =>
      b == ei.ei_bid && obr_eqb obr ei.ei_br && lo ≤ ei.ei_k && ei.ei_k + m ≤ hi
  | _, _ => false

/-! ### The grouped chains -/

/-- `chainKF`: an entry visits only the stores listed for its group. -/
def chainKF (bc : bctx) (fl : List (stx × List stx)) (K : kentry) (okb : Option expr)
    (same_of : Nat → Bool) (br2 : Option (Int × Int)) : List kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match prune1pcK bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K (same_of sx.sx_bid) br2 with
      | .PKeep => chainKF bc fl' K okb same_of br2
      | .PRepl l =>
          match okb with
          | some kb =>
              l.flatMap (fun K' =>
                match kbase K' with
                | some kb' =>
                    if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2
                    else chain_slow bc rest [K']
                | none => chain_slow bc rest [K'])
          | none => chain_slow bc rest l

/-- `entriesG`: pass 2 — every entry visits its group's stores, or the whole
    chain when it belongs to no group / does not fit the hull. -/
def entriesG (bc : bctx) (sxs : List stx) (gl : ptree gfl) (kn : List kentry)
    (infos : List (Option einfo)) : List kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | some ei =>
           let okb := kbase K
           let same_of : Nat → Bool :=
             match okb with | some _ => (fun i => ei.ei_bid == i) | none => fun _ => false
           let br2 := match okb with | some _ => ei.ei_br | none => none
           match pt_get gl ei.ei_gid with
           | some (g, fl) =>
               if inb g ei then chainKF bc fl K okb same_of br2
               else chainK2 bc sxs K okb same_of br2
           | none => chainK2 bc sxs K okb same_of br2
       | none => chainK2 bc sxs K none (fun _ => false) none) ++ entriesG bc sxs gl rest irest
  | _, _ => []

/-- The grouped vertical carry. -/
def carryG (bc : bctx) (log : List sentry) (kn : List kentry) : List kentry :=
  let (sxs, t0) := mk_stxs bc log nt_empty
  let (r, gs) := scan_entries bc kn t0 gst_empty
  let (infos, _) := r
  stores_part bc sxs ++ entriesG bc sxs (mk_gl gs.gs_bnds sxs) kn infos

/-- The carry the plan checker calls, with the grouped vertical path. -/
def carryK (bc : bctx) (log : List sentry) (kn : List kentry) (hints : List Bool) :
    List kentry × List sidecond × List Bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG bc log kn, [], [])
  | _, _ => carryB bc log kn hints

/-! ### The proofs of the grouped carry -/

/-- `zlit64` is idempotent. -/
theorem zlit64_idem (z : Int) : zlit64 (zlit64 z) = zlit64 z := by
  have hmod : ∀ z : Int, zlit64 z = if (0 ≤ z && z < two64) then z else z % two64 := fun _ => rfl
  cases h : (0 ≤ z && z < two64) with
  | true =>
      have e : zlit64 z = z := by rw [hmod, ite_eq_left h]
      rw [e, e]
  | false =>
      have e : zlit64 z = z % two64 := by rw [hmod, ite_eq_right (by rw [h]; simp)]
      rw [e, hmod]
      have h1 : 0 ≤ z % two64 := Int.emod_nonneg z (by unfold two64; decide)
      have h2 : z % two64 < two64 := Int.emod_lt_of_pos z (by unfold two64; decide)
      rw [ite_eq_left (by simp [h1, h2])]

/-- `kdescr`'s base is the entry's `kbase`, except for the image entry (which
    has no base). -/
theorem kdescr_kbase (K : kentry) (kb : expr) (kk : Int) (om : Option Int)
    (H : kdescr K = some (kb, kk, om)) :
    kbase K = some kb ∨ ∃ lo hi : Int, K = .KImg lo hi ∧ kb = .ELit 0 ∧ kk = lo := by
  cases K with
  | KWord sa w v =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inl H.1
  | KZero sa len =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inl H.1
  | KUnk sa len =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inl H.1
  | KFill sa len c =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inl H.1
  | KBlob sa len bk =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inl H.1
  | KImg lo hi =>
      simp only [kdescr, kbase, Option.some.injEq, Prod.mk.injEq] at H ⊢
      exact Or.inr ⟨lo, hi, rfl, H.1.symm, H.2.1.symm⟩
  | KAlign e m => simp only [kdescr] at H; cases H
  | KRange e lo hi => simp only [kdescr] at H; cases H
  | KWr sa n => simp only [kdescr] at H; cases H
  | KDisj a1 n1 a2 n2 => simp only [kdescr] at H; cases H

/-- An entry with no description has no base either. -/
theorem kdescr_None_kbase (K : kentry) (H : kdescr K = none) : kbase K = none := by
  cases K with
  | KWord sa w v => simp only [kdescr] at H; cases H
  | KZero sa len => simp only [kdescr] at H; cases H
  | KUnk sa len => simp only [kdescr] at H; cases H
  | KFill sa len c => simp only [kdescr] at H; cases H
  | KBlob sa len bk => simp only [kdescr] at H; cases H
  | KImg lo hi => simp only [kdescr] at H; cases H
  | KAlign e m => rfl
  | KRange e lo hi => rfl
  | KWr sa n => rfl
  | KDisj a1 n1 a2 n2 => rfl

/-- Pass 1 describes every entry faithfully. -/
def EINF (bc : bctx) (t : ntab) (K : kentry) (oi : Option einfo) : Prop :=
  match oi with
  | none => kdescr K = none
  | some ei =>
      kdescr K = some (ei.ei_kb, ei.ei_k, ei.ei_m)
      ∧ (ei.ei_kb, ei.ei_bid) ∈ nt_bucket t (bkey ei.ei_kb)
      ∧ ei.ei_br = base_rangeB bc ei.ei_kb

/-- `Forall2 (EINF …)` — spelled as an inductive because this core has no
    `List.Forall₂`. -/
inductive EINF2 (bc : bctx) (t : ntab) : List kentry → List (Option einfo) → Prop
  /-- the empty pairing -/
  | nil : EINF2 bc t [] []
  /-- the head entries are described, the tails paired -/
  | cons {K : kentry} {rest : List kentry} {oi : Option einfo} {irest : List (Option einfo)} :
      EINF bc t K oi → EINF2 bc t rest irest → EINF2 bc t (K :: rest) (oi :: irest)

theorem EINF_mono (bc : bctx) (t t' : ntab) (K : kentry) (oi : Option einfo)
    (Hm : ∀ (k : Option Nat) (p : expr × Nat), p ∈ nt_bucket t k → p ∈ nt_bucket t' k)
    (H : EINF bc t K oi) : EINF bc t' K oi := by
  cases oi with
  | none => simpa only [EINF] using H
  | some ei =>
      simp only [EINF] at H ⊢
      exact ⟨H.1, Hm _ _ H.2.1, H.2.2⟩

/-! ### The numeric core of the `PKeep` lemmas -/

/-- A literal-length store that is numerically apart from the entry's range
    passes the cached apartness test. -/
theorem ranges_apart_pcB_lit_true (bc : bctx) (sp : sprep) (wb : expr) (k : Int) (w : Nat)
    (br2 : Option (Int × Int)) (b2 : expr) (k2 : Int) (z2 m lo1 hi1 lo2 hi2 : Int)
    (Hsp : sp.sp_rng = some (lo1, hi1)) (Hbr : br2 = some (lo2, hi2)) (Hz : m = zlit64 z2)
    (Hnum : hi1 + k + zlit64 (w : Int) ≤ lo2 + k2 ∨ hi2 + k2 + m ≤ lo1 + k) :
    ranges_apart_pcB bc sp wb k (.ELit (w : Int)) br2 b2 k2 (.ELit z2) = true := by
  simp only [ranges_apart_pcB, elen, Hsp, Hbr, Hz]
  rw [ite_eq_left]
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← Hz]
  exact Hnum

/-- `kdescr`'s byte length is literal only for a literal length expression. -/
theorem kdescr_len_ELit (len : expr) (m : Int)
    (H : (match len with | .ELit z => some (zlit64 z) | _ => none) = some m) :
    ∃ z : Int, len = .ELit z ∧ m = zlit64 z := by
  cases len with
  | ELit z => exact ⟨z, rfl, by simpa using H.symm⟩
  | EVar n => simp at H
  | EAlu o a b => simp at H
  | EAluw o a b => simp at H
  | EMd o a b => simp at H
  | EMdw o a b => simp at H
  | EExt s l n a => simp at H
  | EBlob s k i n => simp at H

/-- An entry kept by the numeric apartness test (the `kbase` case). -/
theorem prune1pcK_keep_based (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (kb : expr) (kk m lo1 hi1 lo2 hi2 : Int)
    (HB : kbase K = some kb) (HD : kdescr K = some (kb, kk, some m))
    (Hsp : sp.sp_rng = some (lo1, hi1)) (Hbr : base_rangeB bc kb = some (lo2, hi2))
    (Hnum : hi1 + wa.a_off + zlit64 (w : Int) ≤ lo2 + kk ∨ hi2 + kk + m ≤ lo1 + wa.a_off) :
    prune1pcK bc sp wa w wv K false (base_rangeB bc kb) = .PKeep := by
  cases K with
  | KZero sa len =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kbase, kdescr, Option.some.injEq, Prod.mk.injEq] at HB HD
      obtain ⟨hb, hk, hlen⟩ := HD
      rw [hb, hk]
      obtain ⟨z, rfl, hm⟩ := kdescr_len_ELit len m hlen
      simp only [prune1pcK, Bool.false_eq_true]
      rw [ite_eq_right (by simp)]
      /- The lemma states the apartness test at `expr.ELit …` while the
         goal keeps `elen …`, so its conclusion is `have`n at the goal's
         own spelling: `simp only [elen]` rewrites the test inside the
         `if` but leaves the `Decidable` instance at the old spelling,
         and the result is a goal that no longer type-checks. -/
      have hra : ranges_apart_pcB bc sp wa.a_base wa.a_off (elen w) (base_rangeB bc kb)
          kb kk (expr.ELit z) = true :=
        ranges_apart_pcB_lit_true bc sp wa.a_base wa.a_off w (base_rangeB bc kb) kb kk z m lo1 hi1 lo2 hi2 Hsp Hbr hm Hnum
      rw [ite_eq_left hra]
  | KUnk sa len =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kbase, kdescr, Option.some.injEq, Prod.mk.injEq] at HB HD
      obtain ⟨hb, hk, hlen⟩ := HD
      rw [hb, hk]
      obtain ⟨z, rfl, hm⟩ := kdescr_len_ELit len m hlen
      simp only [prune1pcK, Bool.false_eq_true]
      rw [ite_eq_right (by simp)]
      /- Spelled at the goal's `elen …`, as in the first arm. -/
      have hra : ranges_apart_pcB bc sp wa.a_base wa.a_off (elen w) (base_rangeB bc kb)
          kb kk (expr.ELit z) = true :=
        ranges_apart_pcB_lit_true bc sp wa.a_base wa.a_off w (base_rangeB bc kb) kb kk z m lo1 hi1 lo2 hi2 Hsp Hbr hm Hnum
      rw [ite_eq_left hra]
  | KFill sa len c =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kbase, kdescr, Option.some.injEq, Prod.mk.injEq] at HB HD
      obtain ⟨hb, hk, hlen⟩ := HD
      rw [hb, hk]
      obtain ⟨z, rfl, hm⟩ := kdescr_len_ELit len m hlen
      simp only [prune1pcK, Bool.false_eq_true]
      rw [ite_eq_right (by simp)]
      /- Spelled at the goal's `elen …`, as in the first arm. -/
      have hra : ranges_apart_pcB bc sp wa.a_base wa.a_off (elen w) (base_rangeB bc kb)
          kb kk (expr.ELit z) = true :=
        ranges_apart_pcB_lit_true bc sp wa.a_base wa.a_off w (base_rangeB bc kb) kb kk z m lo1 hi1 lo2 hi2 Hsp Hbr hm Hnum
      rw [ite_eq_left hra]
  | KBlob sa len bk =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kbase, kdescr, Option.some.injEq, Prod.mk.injEq] at HB HD
      obtain ⟨hb, hk, hlen⟩ := HD
      rw [hb, hk]
      obtain ⟨z, rfl, hm⟩ := kdescr_len_ELit len m hlen
      simp only [prune1pcK, Bool.false_eq_true]
      rw [ite_eq_right (by simp)]
      /- Spelled at the goal's `elen …`, as in the first arm. -/
      have hra : ranges_apart_pcB bc sp wa.a_base wa.a_off (elen w) (base_rangeB bc kb)
          kb kk (expr.ELit z) = true :=
        ranges_apart_pcB_lit_true bc sp wa.a_base wa.a_off w (base_rangeB bc kb) kb kk z m lo1 hi1 lo2 hi2 Hsp Hbr hm Hnum
      rw [ite_eq_left hra]
  | KWord sa w' v =>
      obtain ⟨kb', kk'⟩ := sa
      simp only [kbase, kdescr, Option.some.injEq, Prod.mk.injEq] at HB HD
      obtain ⟨hb, hk, hm⟩ := HD
      rw [hb, hk]
      simp only [prune1pcK, Bool.false_eq_true]
      rw [ite_eq_right (by simp)]
      /- Spelled at the goal's `elen …`, as in the first arm. -/
      have hra : ranges_apart_pcB bc sp wa.a_base wa.a_off (elen w) (base_rangeB bc kb)
          kb kk (elen w') = true :=
        ranges_apart_pcB_lit_true bc sp wa.a_base wa.a_off w (base_rangeB bc kb) kb kk (w' : Int) m lo1 hi1 lo2 hi2 Hsp Hbr hm.symm Hnum
      rw [ite_eq_left hra]
  | KImg lo hi => simp only [kbase] at HB; cases HB
  | KAlign e m => simp only [kbase] at HB; cases HB
  | KRange e lo hi => simp only [kbase] at HB; cases HB
  | KWr sa n => simp only [kbase] at HB; cases HB
  | KDisj a1 n1 a2 n2 => simp only [kbase] at HB; cases HB

/-- A literal-length store that is numerically apart from the entry's range
    passes the plain apartness test (image entries). -/
theorem ranges_apart_pB_lit_true (bc : bctx) (sp : sprep) (wb : expr) (k : Int) (w : Nat)
    (b2 : expr) (k2 : Int) (z2 m lo1 hi1 lo2 hi2 : Int)
    (Hsp : sp.sp_rng = some (lo1, hi1)) (Hbr : base_rangeB bc b2 = some (lo2, hi2))
    (Hz : m = zlit64 z2)
    (Hnum : hi1 + k + zlit64 (w : Int) ≤ lo2 + k2 ∨ hi2 + k2 + m ≤ lo1 + k) :
    ranges_apart_pB bc sp wb k (.ELit (w : Int)) b2 k2 (.ELit z2) = true := by
  simp only [ranges_apart_pB, elen, Hsp, Hbr, Hz]
  rw [ite_eq_left]
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← Hz]
  exact Hnum

/-- An image entry kept by the numeric apartness test. -/
theorem prune1pcK_keep_img (bc : bctx) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (lo hi m lo1 hi1 lo2 hi2 : Int) (same : Bool) (br2 : Option (Int × Int))
    (HD : kdescr (.KImg lo hi) = some (.ELit 0, lo, some m))
    (Hne : expr_eqb (.ELit 0) wa.a_base = false)
    (Hsp : sp.sp_rng = some (lo1, hi1)) (Hbr : base_rangeB bc (.ELit 0) = some (lo2, hi2))
    (Hnum : hi1 + wa.a_off + zlit64 (w : Int) ≤ lo2 + lo ∨ hi2 + lo + m ≤ lo1 + wa.a_off) :
    prune1pcK bc sp wa w wv (.KImg lo hi) same br2 = .PKeep := by
  have hm : m = zlit64 (hi - lo) := by
    by_cases hlt : hi - lo < 2 ^ 64
    · simp only [kdescr, ite_eq_left hlt, Option.some.injEq, Prod.mk.injEq] at HD
      exact HD.2.2.symm
    · simp only [kdescr, ite_eq_right hlt] at HD
      simp at HD
  have hstep : ∀ wb : expr,
      (if ranges_apart_pB bc sp wb wa.a_off (.ELit (w : Int)) (.ELit 0) lo (.ELit (hi - lo))
        then pk_res.PKeep else pk_res.PRepl []) = pk_res.PKeep := by
    intro wb
    rw [ite_eq_left (ranges_apart_pB_lit_true bc sp wb wa.a_off w (.ELit 0) lo (hi - lo) m
      lo1 hi1 lo2 hi2 Hsp Hbr hm Hnum)]
  by_cases hlt : hi - lo < 2 ^ 64
  · cases hwb : wa.a_base with
    | ELit z =>
        cases z with
        | ofNat n =>
            cases n with
            | zero =>
                rw [hwb] at Hne
                simp [expr_eqb] at Hne
            | succ k =>
                simp only [prune1pcK, hwb, ite_eq_left hlt, elen]
                exact hstep _
        | negSucc n =>
            simp only [prune1pcK, hwb, ite_eq_left hlt, elen]
            exact hstep _
    | EVar n => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EAlu o a b => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EAluw o a b => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EMd o a b => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EMdw o a b => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EExt s l n a => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
    | EBlob s k i n => simp only [prune1pcK, hwb, ite_eq_left hlt, elen]; exact hstep _
  · simp only [kdescr, ite_eq_right hlt] at HD
    simp at HD

/-- Pass 1 keeps the table invariant, only grows the buckets, and describes
    every entry faithfully. -/
theorem scan_entries_ok (fk kn : List kentry) :
    ∀ (t : ntab) (gs : gst) (infos : List (Option einfo)) (t' : ntab) (gs' : gst),
      NTI (mkbc fk) t → scan_entries (mkbc fk) kn t gs = ((infos, t'), gs') →
      NTI (mkbc fk) t'
        ∧ (∀ (k : Option Nat) (p : expr × Nat), p ∈ nt_bucket t k → p ∈ nt_bucket t' k)
        ∧ EINF2 (mkbc fk) t' kn infos := by
  induction kn with
  | nil =>
      intro t gs infos t' gs' HT H
      simp only [scan_entries, Prod.mk.injEq] at H
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := H
      exact ⟨HT, fun k p hp => hp, EINF2.nil⟩
  | cons K rest ih =>
      intro t gs infos t' gs' HT H
      cases hd : kdescr K with
      | none =>
          simp only [scan_entries, hd] at H
          generalize hes : scan_entries (mkbc fk) rest t gs = r at H
          obtain ⟨⟨infos2, t2⟩, gs2⟩ := r
          simp only [Prod.mk.injEq] at H
          obtain ⟨⟨hinf, ht⟩, hgs⟩ := H
          rw [← hinf, ← ht]
          obtain ⟨HT2, Hm2, HF⟩ := ih t gs infos2 t2 gs2 HT hes
          exact ⟨HT2, fun k p hp => Hm2 k p hp,
            EINF2.cons (by simpa only [EINF] using hd) HF⟩
      | some p =>
          obtain ⟨kb, kk, om⟩ := p
          cases om with
          | none =>
              simp only [scan_entries, hd] at H
              generalize hi : intern (mkbc fk) t kb = q at H
              obtain ⟨⟨bid, bi⟩, t1⟩ := q
              generalize hes : scan_entries (mkbc fk) rest t1 gs = r at H
              obtain ⟨⟨infos2, t2⟩, gs2⟩ := r
              simp only [Prod.mk.injEq] at H
              obtain ⟨⟨hinf, ht⟩, hgs⟩ := H
              rw [← hinf, ← ht]
              obtain ⟨HT1, Hbi, HIn, Hm1⟩ := intern_ok (mkbc fk) t kb bid bi t1 HT hi
              obtain ⟨HT2, Hm2, HF⟩ := ih t1 gs infos2 t2 gs2 HT1 hes
              refine ⟨HT2, fun k p hp => Hm2 k p (Hm1 k p hp), ?_⟩
              refine EINF2.cons ?_ HF
              simp only [EINF]
              exact ⟨hd, Hm2 _ _ HIn, by rw [Hbi]⟩
          | some m =>
              simp only [scan_entries, hd] at H
              generalize hi : intern (mkbc fk) t kb = q at H
              obtain ⟨⟨bid, bi⟩, t1⟩ := q
              generalize hg : ggroup gs bid kk = gq at H
              obtain ⟨gid, gs0⟩ := gq
              generalize hes : scan_entries (mkbc fk) rest t1 (bnd_add gs0 gid bid bi.bi_br kk (kk + m)) = r at H
              obtain ⟨⟨infos2, t2⟩, gs2⟩ := r
              simp only [Prod.mk.injEq] at H
              obtain ⟨⟨hinf, ht⟩, hgs⟩ := H
              rw [← hinf, ← ht]
              obtain ⟨HT1, Hbi, HIn, Hm1⟩ := intern_ok (mkbc fk) t kb bid bi t1 HT hi
              obtain ⟨HT2, Hm2, HF⟩ := ih t1 _ infos2 t2 gs2 HT1 hes
              refine ⟨HT2, fun k p hp => Hm2 k p (Hm1 k p hp), ?_⟩
              refine EINF2.cons ?_ HF
              simp only [EINF]
              exact ⟨hd, Hm2 _ _ HIn, by rw [Hbi]⟩

/-- `chainKF` on the group's filtered stores is the plain fast chain, as long
    as every store the group did NOT filter out is kept by `prune1pcK`. -/
theorem chainKF_eq (bc : bctx) (g : gval) (sxs : List stx) (K : kentry) (okb : Option expr)
    (same_of : Nat → Bool) (br2 : Option (Int × Int))
    (Hf : ∀ sx ∈ sxs, verdict sx g = true →
      prune1pcK bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K (same_of sx.sx_bid) br2 = .PKeep) :
    chainKF bc (mk_fl g sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2 := by
  induction sxs with
  | nil => rfl
  | cons sx rest ih =>
      have ih' : chainKF bc (mk_fl g rest) K okb same_of br2
          = chainK2 bc rest K okb same_of br2 :=
        ih (fun s hs hv => Hf s (by simp [hs]) hv)
      simp only [mk_fl, chainK2]
      by_cases hv : verdict sx g = true
      · rw [ite_eq_left hv]
        rw [Hf sx (by simp) hv]
        exact ih'
      · rw [ite_eq_right hv]
        simp only [chainKF]
        cases hpk : prune1pcK bc sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K (same_of sx.sx_bid) br2 with
        | PKeep => exact ih'
        | PRepl l => rfl

/-- The verdict and the hull check imply the numeric apartness of the entry. -/
theorem verdict_inb_num (sx : stx) (g : gval) (ei : einfo) (m : Int)
    (Hv : verdict sx g = true) (Hi : inb g ei = true) (Hm : ei.ei_m = some m) :
    (ei.ei_bid == sx.sx_bid) = false ∧
      ∃ lo1 hi1 lo2 hi2 : Int,
        sx.sx_sp.sp_rng = some (lo1, hi1) ∧ ei.ei_br = some (lo2, hi2) ∧
          (hi1 + sx.sx_a.a_off + zlit64 (sx.sx_w : Int) ≤ lo2 + ei.ei_k
            ∨ hi2 + ei.ei_k + m ≤ lo1 + sx.sx_a.a_off) := by
  obtain ⟨b, obr, glo, ghi⟩ := g
  simp only [verdict, inb, Hm] at Hv Hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at Hi
  obtain ⟨⟨⟨hbid, hbr⟩, hlo⟩, hhi⟩ := Hi
  by_cases hsame : (b == sx.sx_bid) = true
  · rw [ite_eq_left hsame] at Hv
    exact absurd Hv (by simp)
  · have hne : (ei.ei_bid == sx.sx_bid) = false := by
      rw [← hbid]
      simpa using hsame
    refine ⟨hne, ?_⟩
    rw [ite_eq_right hsame] at Hv
    cases hrng : sx.sx_sp.sp_rng with
    | none =>
        rw [hrng] at Hv
        exact absurd Hv (by simp)
    | some p =>
        obtain ⟨lo1, hi1⟩ := p
        cases hobr : obr with
        | none =>
            rw [hrng, hobr] at Hv
            exact absurd Hv (by simp)
        | some q =>
            obtain ⟨lo2, hi2⟩ := q
            rw [hrng, hobr] at Hv
            cases hbr2 : ei.ei_br with
            | none => rw [hobr, hbr2] at hbr; simp only [obr_eqb] at hbr; cases hbr
            | some r =>
                obtain ⟨x2, y2⟩ := r
                rw [hobr, hbr2] at hbr
                simp only [obr_eqb, Bool.and_eq_true, beq_iff_eq] at hbr
                obtain ⟨hx, hy⟩ := hbr
                rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, sx_m1] at Hv
                refine ⟨lo1, hi1, lo2, hi2, rfl, ?_, ?_⟩
                · rw [← hx, ← hy]
                · generalize hm1 : zlit64 (sx.sx_w : Int) = m1 at Hv ⊢
                  omega

/-- Right cancellation for `List.append`, as an `↔` (this core has the
    implication only). -/
theorem append_cancel_right_iff {α : Type} (a b c : List α) :
    (a ++ c = b ++ c) ↔ a = b :=
  ⟨List.append_cancel_right, fun h => by rw [h]⟩

/-- Pass 2 equals the reference chain: every entry visits the stores of its
    group, and the stores it skips are numerically apart from it. -/
theorem entriesG_eq (fk : List kentry) (sxs : List stx) (bnds : gtab) (kn : List kentry)
    (infos : List (Option einfo)) (t1 : ntab)
    (HT : NTI (mkbc fk) t1) (HS : ∀ sx ∈ sxs, SX_OK (mkbc fk) t1 sx)
    (HF : EINF2 (mkbc fk) t1 kn infos) :
    entriesG (mkbc fk) sxs (mk_gl bnds sxs) kn infos = chainRo fk (sxs.map strip) kn := by
  revert infos
  induction kn with
  | nil =>
      intro infos HF
      cases HF with
      | nil =>
          induction sxs with
          | nil => rfl
          | cons sx r ih =>
              simp only [List.map_cons, chainRo, FM_nil]
              exact ih (fun s hs => HS s (by simp [hs]))
  | cons K rest ih =>
      intro infos HF
      cases HF with
      | cons HK HF =>
          rename_i oi irest
          have HSP : ∀ sx ∈ sxs,
              sx.sx_sp = mk_sprepB (mkbc fk) sx.sx_a.a_base sx.sx_a.a_off (elen sx.sx_w) :=
            Forall_SX_sp fk t1 sxs HS
          simp only [entriesG, List.map_cons]
          rw [show K :: rest = [K] ++ rest from rfl, chainRo_app, ih irest HF,
            ← chain_slow_eq fk sxs [K] HSP, append_cancel_right_iff]
          cases oi with
          | none =>
              dsimp only
              simp only [EINF] at HK
              have hk : kbase K = none := kdescr_None_kbase K HK
              rw [← hk]
              exact chainK2_eq fk sxs K (fun _ => false) none HSP (by rw [hk])
          | some ei =>
              dsimp only
              simp only [EINF] at HK
              obtain ⟨HD, HIn, Hbr⟩ := HK
              have FULL : ∀ okb : Option expr, okb = kbase K →
                  chainK2 (mkbc fk) sxs K okb
                    (match okb with | some _ => fun i => ei.ei_bid == i | none => fun _ => false)
                    (match okb with | some _ => ei.ei_br | none => none)
                  = chain_slow (mkbc fk) sxs [K] := by
                intro okb hokb
                rw [hokb]
                refine chainK2_eq fk sxs K _ _ HSP ?_
                cases hb : kbase K with
                | none => exact rfl
                | some kb =>
                    have hkbe : kb = ei.ei_kb := by
                      rcases kdescr_kbase K ei.ei_kb ei.ei_k ei.ei_m HD with h | ⟨lo, hi, hK, -, -⟩
                      · rw [hb] at h
                        injection h with h'
                      · rw [hK] at hb
                        exact absurd hb (by simp [kbase])
                    exact ⟨by dsimp only; rw [hkbe]; exact Hbr,
                      fun sx hsx => by
                        dsimp only
                        rw [hkbe]
                        exact Forall_SX_same fk t1 sxs ei.ei_kb ei.ei_bid HT HIn HS sx hsx⟩
              simp only [mk_gl, pt_get_map]
              cases hpg : pt_get bnds ei.ei_gid with
              | none => exact FULL (kbase K) rfl
              | some gv =>
                  by_cases hinb : inb gv ei = true
                  · simp only [Option.map]
                    rw [ite_eq_left hinb]
                    rw [← FULL (kbase K) rfl]
                    refine chainKF_eq (mkbc fk) gv sxs K (kbase K) _ _ ?_
                    intro sx hsx hv
                    have hm : ∃ m : Int, ei.ei_m = some m := by
                      cases hm' : ei.ei_m with
                      | none => simp [inb, hm'] at hinb
                      | some m => exact ⟨m, rfl⟩
                    obtain ⟨m, hm⟩ := hm
                    obtain ⟨hne, lo1, hi1, lo2, hi2, hsp, hbr2, hnum⟩ :=
                      verdict_inb_num sx gv ei m hv hinb hm
                    obtain ⟨sxin, sxbr, sxsp⟩ := HS sx hsx
                    rw [hm] at HD
                    rcases kdescr_kbase K ei.ei_kb ei.ei_k (some m) HD with hb | ⟨lo, hi, hK, hkb, hk⟩
                    · simp only [hb, hne, Hbr]
                      exact prune1pcK_keep_based (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v K
                        ei.ei_kb ei.ei_k m lo1 hi1 lo2 hi2 hb HD hsp (by rw [← Hbr]; exact hbr2) hnum
                    · rw [hK] at HD ⊢
                      rw [hkb] at HD
                      rw [hk] at HD hnum
                      simp only [kbase]
                      refine prune1pcK_keep_img (mkbc fk) sx.sx_sp sx.sx_a sx.sx_w sx.sx_v lo hi m
                        lo1 hi1 lo2 hi2 _ _ HD ?_ hsp ?_ hnum
                      · rw [← hkb]
                        rw [← nt_same_eq (mkbc fk) t1 ei.ei_kb ei.ei_bid sx.sx_a.a_base sx.sx_bid
                          HT HIn sxin]
                        exact hne
                      · rw [← hkb]
                        rw [← Hbr]
                        exact hbr2
                  · simp only [Option.map]
                    rw [ite_eq_right hinb]
                    exact FULL (kbase K) rfl

/-- The grouped vertical carry equals the reference vertical form. -/
theorem carryG_eq (log : List sentry) (kn : List kentry) :
    carryG (mkbc (facts_of kn)) log kn
      = SPRo (facts_of kn) (log.reverse) ++ chainRo (facts_of kn) (log.reverse) kn := by
  simp only [carryG]
  generalize hE : mk_stxs (mkbc (facts_of kn)) log nt_empty = c
  obtain ⟨sxs, t0⟩ := c
  obtain ⟨HT0, HS0, Hmap, -⟩ :=
    mk_stxs_ok (facts_of kn) log nt_empty sxs t0 (NTI_empty _) hE
  generalize hES : scan_entries (mkbc (facts_of kn)) kn t0 gst_empty = d
  obtain ⟨⟨infos, t1⟩, gs⟩ := d
  obtain ⟨HT1, Hm, HF⟩ := scan_entries_ok (facts_of kn) kn t0 gst_empty infos t1 gs HT0 hES
  have HS1 : ∀ sx ∈ sxs, SX_OK (mkbc (facts_of kn)) t1 sx :=
    fun sx hsx => SX_OK_mono (mkbc (facts_of kn)) t0 t1 sx Hm (HS0 sx hsx)
  rw [stores_part_eq (facts_of kn) t0 sxs HT0 HS0,
    entriesG_eq (facts_of kn) sxs gs.gs_bnds kn infos t1 HT1 HS1 HF, Hmap]

/-- The plan checker's carry is the reference carry (the concluding theorem,
    with the grouped vertical path). -/
theorem carryK_eq (log : List sentry) (kn : List kentry) (hints : List Bool) :
    carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints := by
  cases log with
  | nil => rfl
  | cons e older =>
      cases hints with
      | nil =>
          simp only [carryK, carryG_eq, carry_vertical]
      | cons h hs =>
          simp only [carryK]
          exact carryB_eq (e :: older) kn (h :: hs)

/-! B7 complete: the GROUPED vertical carry is above in
    full — `pt_map`/`pt_get_map`, `kdescr`/`einfo`/`EI`, `gval`/`gtab`/
    `gst`/`GST`/`gst_empty`, `gkey`/`ggroup`/`bnd_add`, `scan_entries`,
    `sx_m1`/`verdict`/`mk_fl`/`gfl`/`mk_gl`, `obr_eqb`/`inb`, `chainKF`/
    `entriesG`/`carryG`, the entry point `carryK`, and every lemma of the
    block, ending in `carryK_eq`:
    `carryK (mkbc (facts_of kn)) log kn hints = carry log kn hints`.

    Nothing in this file is deferred. -/
