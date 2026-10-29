/-
  * Common.AxSymExec3Sound — soundness of the reflective symbolic executor
  `AxSymExec3`.

  Image-INDEPENDENT.  Denotations (`edenot` lives with the syntax in
  `AxSymExec3`; here: `sc_denot`, `kentry_ok`/`know_ok`, `regs_ok`,
  `log_flat`, `st_ok`) and the theorems `sym_step_sound`,
  `sym_exec_sound`/`sym_exec_ex`, `carry_sound`.  Nothing is admitted.

  LR/SC/AMO + reservation tracking.  `st_ok` (block-boundary relation: the
  machine is an `mkst`, no reservation) is the relation of
  `sym_exec_sound/_ex`, `sym_execS_sound/_ex`, `sym_execT_sound/_ex`.
  `st_okR` is the general relation (machine = `SymStepR.mkstR` whose
  reservation is `resv_denot E (s_resv ss)`); `sym_step_soundR` (one step,
  st_okR → st_okR, all instruction classes incl. Lr/Sc/Amo), the general
  driver theorems `sym_exec_soundR`, `sym_execS_soundR`,
  `sym_execT_soundR` and the clean-exit facts `sym_exec_resv`,
  `sym_execS_resv`, `sym_execT_resv` (a driver never returns a state with
  a live reservation).  The per-class machine step lemmas are in
  `SymStepR` (generic in the reservation).

  `mkSrl` split condition; align-down atoms in `erange` (see
  `AxSymExec3`): `erange0_sound` (the basic interval), `deand_sound`,
  `erange_sound` over the tightened `erange`; `mkSrl_denot` for the
  block-restricted split.

  `KUnk`, EXTENSION MODE — see `AxSymExec3`'s header: `kentry_ok (KUnk a
  n)`; `zf_kind` generalised to a byte PREDICATE (KZero / KFill / KUnk
  share `kcut_sound`, `ktrim_sound`, `zf_frame`, `prune_zf_sound`);
  `kunk_cut_sound`; Part P5c (Section XSound): `eagree`, `eupd`,
  `edenot_evars_lt`, `st_okX`, coverage soundness (`zf_covers_sound`,
  `kentry_overlay_sound`, `kentry_readable_sound`,
  `know_byte(s)_cov_sound`, `kn_readable_sound`, `kn_overlay_sound`),
  `x_discharge_sound`, `cap_rd_sound`, `sym_stepX_sound`,
  `sym_execTX_go_sound`, `sym_execTX_sound`, `sym_execTX_ex`,
  `sym_execTX_resv`, `sym_execSX_*`; `mkSrl_denot` extended (partial
  split); node-side `know_ok_unk_intro(_pt)`, `kunk_of_zero|fill|blob`,
  `kentry_ok_unk_grows`, `kentry_ok_unk_frame`, `kunk_store_ok`.

  Knowledge byte composition, `KFill`, EQ/NE by linear arithmetic,
  aligned/residual split of `mkAnd` — see the header of `AxSymExec3`:
  `kentry_ok (KFill a n c)`; `know_lookupA0_sound` + `know_byte_lit_sound`
  / `know_bytes_lit_sound` => `know_lookupA_sound`; `zf_kind` /
  `kcut_sound` / `ktrim_sound` / `zf_frame` / `prune_zf_sound` (KZero and
  KFill share one proof), `kword_cut_sound`, `kzero_cut_sound` and
  `kfill_cut_sound` as instances; `lin_branch_sound` EQ/NE;
  `erange_f_sound` high-mask case (bit-mask lemmas before it);
  `lsplit_div_sound`, `and_high_split_denot`, `and_low_split_denot` for
  `mkAnd_denot`; `pageup_low_k_sound` (sign-generic J3e); node-side
  `know_ok_fill_intro`, `know_ok_fill_intro_pt`, `kentry_ok_frame_bytes`,
  `wbytes_nth`.

  The  file interleaves its definitions with long
  blocks of arithmetic lemmas (the first denotation, `kentry_ok`, only
  appears at line 688 — after 600 lines of `Int`/bitvector algebra).
  Because Lean checks strictly in order, this module collects the
  DEFINITIONS first , then restates the lemmas
  in  order (Part 1 onwards).  `segs`, which  introduces as a section variable of
  `Section StepSound` / `Section XSound` / `Section CarrySound`, is an
  explicit parameter here, exactly as `SymExec.sc_denot` does it.
  The low-bits /
  shift-amount / mask block.  `coeffs_div_sound`, `eqm_mod_pow2`,
  `lin_lowbits_sound`, `shamt_of_sound`, `w_shift_amt` (with the 32-bit
  `alu32_shift_amt` / `low32_and31` helpers), `and_lowmask_val`,
  `slice_mod` (Lean core has no `Z.bits_inj'`; the work is done over `Nat`
  exponents as `slice_mod_nat`, which is the form `ext_Z` uses, with
  `slice_mod` as the `Int` corollary), `ext_Z_range`, `ext_val_compose`,
  `wrap64_mod`, `land64_eq`, `land32_eq`, `land_63`, `land_31`,
  `zext_fast_eq`, `mkExt_denot`.  Local glue the proofs need:
  `two_pow_pos_int`, `int_pow_le_pow`, `zland_ones`
  (`Z.land_ones` for this tree's 64-bit-window `zland`), `mask_ones_toNat`,
  `and_ones_word`, `zshiftl_one`, `bv_swrap_lo`.
  DEVIATION (`zext_fast_eq`, `mkExt_denot`).  With the half modulus spelled
  `bv_modulus 0 / 2`, `bv_swrap 0 0 = 0`.  The two lemmas
  therefore carry `sx = false ∨ 1 ≤ n` (`n ≤ 8` additionally, for the
  64-bit window inside `zland`), which covers every executor call site
  (`mkExt` is used at byte widths `1 ≤ n ≤ 8`).  If
  `PropExec.bv_swrap` is ever respelled as `bv_modulus n / 2`, the extra
  hypotheses can be dropped.
 Local glue: `div_pow8_shiftRight` (the
  `Int.shiftRight`/division bridge the byte slices need),
  `Z_to_bv_unsigned`, `natCast_two_pow_pos`, `int_pow_toNat`,
  `acc_shift` (the accumulator step of `log_lookup_acc`).
  DEVIATION (`extz_0`).  Same `bv_swrap`-at-`0` cause as above:
  `bv_swrap 0 0 = -1` here, so `extz true 0 0 = -1 ≠ 0`; the lemma
  carries `sx = false ∨ 1 ≤ n`, which covers every call site (load
  widths are `1, 2, 4, 8` bytes).
— the same values, and
  definitionally the `↑(2 ^ …)` that `BitVec`/`Int.emod` lemmas produce.
  Local glue the block needed: `shiftmask64`, `emod64_toNat_eq`,
  `natCast_pow_two`, `two_pow31_lt_two64`, `shamt32_eq`, `two_pow_half`,
  `bv_swrap_small` , `emod_le_self`
  (`Z.mod_le`), `two_pow_ne`/`two64_ne`/`two64_pos`, `bmod_eq_swrap`
  (`Int.bmod` at `2 ^ m` IS `bv_swrap`, `1 ≤ m`), `two_pow_split64`,
  `two64_eq_natCast`, `or_shift256_mod`, `toNat_emod_mul256`.
  DEVIATION (`zbytes_map`).  `zlor` truncates at 64 bits per step, so the
  lemma is stated as
  `zbytes_le_to_Z (map bv_unsigned bs) = bytes_le_to_Z bs % two64`.  Every
  call site folds into `Z_to_bv 64`/`extz`, which truncate anyway, so the
  `% two64` is invisible there.  `sext64_small` carries `1 ≤ m` — the same
  `bv_swrap`-at-`0` deviation as `extz_0`/`zext_fast_eq`.
  DEVIATIONS in this block, all forced by this tree's vocabulary and all
  invisible at the call sites:
  * `lor_ge_l`/`lor_ge_r` carry `x < 2^64` (`y < 2^64`).  `lor_cover`/`lxor_cover` need
    no such hypothesis: they case on whether `h` reaches the window and
    fall back to `zlor < 2^64 <= mask_cover h`.
  Also stated ahead of its user: `erange_f_lin_sound`, the linear-form
  case of `erange_f_sound`, stated for a standalone
  `lin_range` result so the main proof only has to peel its match.  It is
  the one part of that proof that needs the `q = p` block argument, and
  it now typechecks, so only the per-operator case bash is left there.
  `erange_f_sound` itself; `facts_of_ok`, `erange0_sound`, `deand_zero`,
  `deand_sound`, `erange_sound`, `base_range_sound`, `zlit64_eq`;
  `lin_nowrap_sound`, `lins_e_sound`, `lsub_e_sound`,
  `find_align_sound`; `zpow_int_add`, `ctz_fuel_sound`, `ctz64_sound`,
  `pow2_divide_le`, `divide_mod64`, `ealign0_sound`; the page-rounding
  atom finder `find_and_atom_k_some` / `find_and_atom_some`;
  `u_and_mask`, `fold_lins_e_sg_sound`, `fold_lins_e1_sound`,
  `pow2_of_zland_succ` / `nat_pow2_of_land_sub_one` (the `mm + 1 = 2^K`
  reconstruction that `pageup_low_k_sound` needs), and `u_srl_lit`,
  `fold_lins_e_sound`, `u_srl_rem`.
  FRAMEWORK for the alignment domain (`ealign0_sound`): a
  `Nat.testBit` divisibility calculus — `two_pow_dvd_iff_testbit`
  (`2^k ∣ n ↔ all bits below k vanish`), its `Int` bridge
  `zpow_two_dvd_nat_iff`, the `Nat`-level `bv_unsigned` of `AND`/`OR`
  (`u_and64_nat`, `u_or64_nat`), and the closure lemmas
  `dvd_and_of_dvd_left` / `dvd_and_of_dvd_right` / `dvd_or_of_dvd`,
  `dvd_mul_mul`, `ealign_zero_sound`, `ealign_nofact_sound`.  The
  `ADD`/`SUB`/`MUL`/`SLL` cases then reduce to `divide_mod64` +
  `pow2_divide_le` on `u_add64`/`u_sub64`/`u_mul64`/`u_sll64`.
  THE BLOCKER IS
  GONE: `pageup_low_k_sound` (sign-generic J3e) is proved from the
  `mm + 1 = 2^K` reconstruction `pow2_of_zland_succ` plus the modular
  bookkeeping described in the note below.  With it,
  `pageup_low_sound` (the `+1` idiom, then the dual `-1` one),
  `pageup_align_sound` (a recognised page-up form is a real alignment)
  and `ealign_sound` (`ealign0` and `pageup_align` combined by `max`)
  follow.  Then the J2-b/`srl_expand` block: `highmask_s_some` (a
  high-mask literal is `2^64 - 2^s`, `0 < s < 64`), `srl_expand_sound`
  (every SRL / high-AND atom the page-rounding expansion removes is
  replaced by a form with the SAME `tden`, using `u_srl_lit` for the SRL
  half and `land_highmask` for the `e AND -2^s = e - e mod 2^s` half),
  `mul_two64_eq_zero`, `sum_fact_x_sound`, `fact_nowrap_sound` and
  `sub_fact_sound`.
  The whole J2-b
  relational sum-fact block and the range/comparison layer on top of it:
  * `sum_facts_sound` + its four shape lemmas (`sum_facts_KRange_unfold`,
    `_cc`, `_one`, `_nil`).  The fix: factor the DEFINITIONAL
    unfolding into `sum_facts_KRange_unfold` (proved by `rfl`), which has
    `lin_of e` as the match scrutinee *syntactically*; then
    `rw [sum_facts_KRange_unfold, hle]` rewrites that scrutinee to the
    constructor `(c, t1 :: t2 :: tl)` BEFORE any `cases e` can unfold
    `lin_of` into `ladd …`, so the match reduces and the as-pattern is
    gone.  The three shapes of `ts` become three lemmas, and
    `sum_facts_sound` needs `key : ∀ c ts, lin_of e = (c, ts) → …` with
    `cases ts` (nil / singleton / cons-cons).  NB a `match ts` in a
    *statement* is elaborated DEPENDENTLY on any hypothesis that mentions
    `ts` (`match ts, hle with`), which is why one generic lemma does not
    work and there are three.
  * `sum_subst_sound` (`Int.mul_le_mul_of_nonneg_left` /
    `_nonpos_left` must be supplied by hand: `omega` cannot see
    `q * tden E fts` as monotone, and both directions are needed),
    `lin_test_rel_sound`, `lin_test_sound`, `lin_brange_sound`,
    `tden_map_scale` (`Int.mul_add` + `Int.mul_assoc`), `lin_srange_sound`,
    `lin_srange_exact`.
  * `xlo_sound` / `xhi_sound` (through the local fallback-chain
    lemmas `xlo_fallback` / `xhi_fallback`), `lin_nowrapR_sound`,
    `lin_apart_sound`.
  * the symbolic-length comparison layer: `xt_lin_sound`,
    `lin_ge0_scaled_sound` (`Int.nonneg_of_mul_nonneg_left` divides the
    positive factor back out), `lin_ge0_sound` (the four attempts; the
    common closing is the local `goal_of`), `xinside_sound`,
    `sub_itv_sound`, `if3_cases`, `kdisj_apart_sound_gen`,
    `kdisj_apart_sound`, `if3b` (local: the `Bool` sum of three
    attempts), `ranges_apart_sound`, `sub_itv_x_sound`,
    `kdisj_apart_x_sound`.
  2736 and 2743–2792, plus the P4d prefix and
  `know_lookupA0_sound`): the accumulator discipline
  `know_lookupA0_acc` / `know_lookupA_acc` / `know_lookup_acc`,
  `rel_lit_inside` / `rel_lit_disjoint`, the arithmetic prefix
  `u_lit0`, `Z_to_bv_emod64`, `bv_swrap_emod64`, `estart_lit0`,
  `adenot_shift`, `elenZ_lit`, `u8_lit`, `map_unsigned_repeat8`,
  `fill_lit_denot`, `fill_read`, and `ext_hit_value`,
  `know_lookupA0_sound`.
  DEVIATION (`fill_lit_denot`, `fill_read`): both carry `n ≤ 8`.  The
  cause is this tree's `zbytes_le_to_Z` truncating at 64 bits
  (`zbytes_map`), which the byte arithmetic of `bv_swrap` would see at
  `8n > 64`; every call site (the `KZero`/`KFill` cases of the lookup,
  where `n ≤ 8` is a hypothesis of the theorem) has it.
  `match rb with |.ELit 0 => A |
  _ => C` compiles to a matcher that does NOT iota-reduce for a variable
  or non-literal scrutinee, and the same fall-through form appears
  wherever the executor matches on `.ELit l0` with a `| _` default
  (`know_lookupA0`'s `KZero`/`KFill`/`KBlob`/`KImg` arms).  Two tools:
  (a) in a GOAL whose scrutinee is already the right constructor,
  `simp only []` reduces it after the `cases`; (b) `split` splits the
  stuck matcher and names the equation (`rename_i`), which is what the
  `KImg` case does (`split` then `injection` the equation to learn
  `z = 0`).  Careful: `split` on a goal whose OUTER `match` is the
  dependent result-match splits THAT first, so peel in the right order;
  and `rw` cannot rewrite a scrutinee that occurs in a dependent match's
  motive.  The two lemmas `match_elit0_pos`/`match_elit0_neg` state the
  reduction as rewrite rules for the non-dependent uses.
  GAP CLOSED` log block) and
  the bytewise knowledge lookups — the last two
  missing pieces of the LOAD PATH of `sym_step_sound`:
  * the log block: `rdn_inside_wbytes`, `word_byte_at` (+ `Z_to_bv8_mod`),
    `rdn_cons1` (+ `rdn_one`), `log_byte_lit_sound`,
    `log_bytes_lit_sound` (+ `flat_step`, `adenot_add_one`),
    `log_lookup_sound` (through the local predicate `log_hit_ok` and
    the one-layer transport `log_hit_ok_wbytes`);
  * the knowledge block: `know_byte_lit_sound` (the four covering arms —
    `KWord` literal, `KZero` literal, `KFill` literal, `KImg`),
    `know_bytes_lit_sound`, `know_lookupA_sound`, `know_lookup_sound`
    (all stated through the existing `hit_ok`).
  So BOTH halves of the load path (`log_lookup_sound` first, then
  `know_lookup_sound`) now have their soundness lemmas.
  `cases h :
  rel_lit … with | RInside d => …` followed by `simp only [h] at H` is
  what peels the executor's `rel_lit` match: the equation rewrites the
  scrutinee and `simp` iota-reduces the arms.  `generalize … at H` is NOT
  reliable here (it can leave the scrutinee in place), and neither
  `match_elit0_pos` nor `rw` on a literal-pattern matcher fires.  For the
  `KImg` arm's `match rb with | .ELit 0 => …`, `by_cases hz : z = 0`,
  `subst hz`, then `simp only [know_byte_lit] at H` reduces it (the
  scrutinee is a constructor); for `z ≠ 0`, `split at H` gives the
  equation plus the fall-through.
  `Z_to_bv64_u`, `Z_to_bv64_mod`, `to_saddr_denot` (+ the `Int` glue
  `Z_to_bv64_eq_of_emod`, `emod_add_mod`, `emod_add_emod_gen`).
  `to_saddr_denot` is the lemma every `to_saddr` call site in Part P5a
  uses, so the `sym_step_sound` block can start from it.
  3477 and the folding layer 3447–3570,
  3672–3726) — the alignment-mask block and the denotations of the smart
  ALU/M-extension constructors:
  * the alignment masks, on top of the existing `land_highmask` /
    `land_align_mask` / `land_lowmask` / `and_ones_word` /
    `and_lowmask_val`: `and_highmask_val` (a high mask rounds DOWN to a
    multiple of `2^j`), `and_mask_id` (an aligned value survives it) and
    `and_lowmask_zero` (a low mask clears a value whose low `j` bits
    vanish — one line from the already-proved `and_lowmask_val` plus
    `Int.emod_eq_zero_of_dvd`);
  * `coeffs_divk_sound` (the alignment-aware `coeffs_div_sound`: a term is
    a multiple of `m` judged by the coefficient alone OR by the coefficient
    times the atom's `ealign`) and `lin_lowbits_kn_sound` (the
    `lin_lowbits_kn` read, with the `pageup_low` fallback, through
    `pageup_low_sound`).  With `lin_lowbits_sound` from the earlier block,
    BOTH low-bits readers are now sound;
  * `ldiv_terms_sound`, `wrap64_range`, `Z_to_bv_wrap64`;
  * `zfast_eq` / `zfastm_eq`: the bit-sliced `zfast`/`zfastm` agree with
    the closed evaluation `zalu`/`zmd` on the canonical window, hence
    `zalu_l_eq` / `zmd_l_eq` for the literal folding of `mkAlu`/`mkMd`;
  * `mkAlu_denot` (through the standalone arm lemmas `mkAlu_sll_denot`,
    `mkAlu_sr_denot` and its `is_lit b = none` instance
    `mkAlu_sr_none_denot`), `mkMd_denot` and `mkMdw_denot`.
  `cases h : t`
  replaces the scrutinee `t` in the goal, but the goal's `match` is NOT
  iota-reduced by the following `exact`/`show` even when every discriminant
  is then a constructor (`exact` reports a type mismatch between
  `match some x, none with …` and the arm it should have reduced to).  The
  fix is an explicit `simp only []` (the empty simp set: only the
  iota/beta/zeta steps) right after the `cases`, and one more per branch
  when a SECOND `match` on the same scrutinee (`match op with …`) has just
  become constructors; a `tac <;> rfl` after it is harmless when `simp`
  already closed the goal, which is what the per-`op` dispatch lines in
  `mkAlu_denot`/`mkMd_denot` rely on.
  `Int.emod_nonneg` takes the
  NONZERO proof (`a ≠ 0`), so pass `Int.ne_of_gt (two_pow_pos_int …)`;
  `Int.emod_lt_of_pos` takes `0 < b`.  The `x mod 2^64` of a negative
  literal is `2^64 - a` via
  `Int.sub_emod` + `Int.emod_self` + `Int.sub_zero` + `Int.emod_emod`
  + `Int.emod_eq_of_lt` (a `h2 : x = (x - 2^64) + 1 * 2^64` rewrite is
  WRONG there: it also rewrites the `x` inside the other side's emod).
  `Int.toNat_lt_toNat` needs `0 < m`, so the `Nat`/`Int` comparison
  transfer for `SLTU` goes through `Int.lt_toNat` +
  `Int.toNat_of_nonneg`.  As always, state word bounds with
  `bv_unsigned v` and powers with `2 ^ 64` (not `two64`) for `omega`.

  `mkSrl_denot` (the `R3.3` split,
  through the local `lsplit_divc` permutation `SPLIT`),
  `and_highmask_srl` (R6), the mod-`2^j` bit lemmas `land_mod_pow2` /
  `lor_mod_pow2` / `lxor_mod_pow2` / `mod_pow2_mod_pow2` and
  `lowbits_sound` (P-c); then (3916–4026) `lsplit_div_sound`,
  `split_mod_core`, `and_high_split_denot`, `and_low_split_denot`; and
  (4232–4290) `itv_ltu_sound`, `bv_lts_eq_ltu_small` / `_hi`,
  `itv_lts_sound`, `range_branch_sound`, `cond_on_eq_sound`.
 Every use reads a
    `bv_unsigned` value or a nonnegative literal, so the conditions are
    discharged on the spot.
  * `and_highmask_srl` is stated at `zpow 2 j` (this tree's `Int` exponents
    are `Nat`).
  * `itv_lts_sound` needs the two `bv_lts = bv_ltu` bridges per half
    (local `bv_lts_eq_ltu_small` / `bv_lts_eq_ltu_hi`).
  HELPERS added with them: `alu_srl_div`, `edenot_unlin`,
  `unlin_val_of_nowrap_l` (a `lin_nowrap_l` form denotes its `Z` value, by
  the `q = 0` squeeze `Int.add_mul_ediv_right` + `Int.ediv_eq_zero_of_lt`
  — `omega` cannot do it: the atom `q * 2^64` is nonlinear),
  `int_pow_lt_pow`, `and_mod_pow2_nat_gen` / `or_mod_pow2_nat_gen` /
  `xor_mod_pow2_nat_gen`, `zop_mod_pow2`, `mul_mod_idem`, `zpow_two63`.
  The `mkAnd*` block and the exact linear
  comparison.  This is the block whose J3e arm needs `Nat.log2`/`Nat.land`
  bit reasoning (`Z.log2_spec`, `Z.bits_above_log2`, `Z.log2_land`) with no
  counterpart; the missing calculus is built here on the `Nat`
  representative and lifted at the `bv_unsigned` boundary:

  * the `Nat` bit lemmas `testbit_pow_sub` (the bits of `2^a - 2^i` are
    `i <= n < a`, from `Nat.testBit_two_pow_mul` + `testBit_two_pow_sub_one`)
    and `land_mask_narrow` (a value below `2^j` cannot tell the masks
    `2^j - 2^i` and `2^64 - 2^i` apart, by `Nat.eq_of_testBit_eq`), plus
    `zlog2_lt_pow_succ` (`k < 2^(log2 k + 1)` from `Nat.log2_eq_iff`) and
    `Z_to_bv64_two64_sub_pow` / `two64_sub_pow_natCast` / `zland_emod`;
  * `mkAnd0_denot`, through six local ARM lemmas so that the top-level
    case bash only peels the executor's `if`/`match` chain:
    `mkAnd0_high_id` (aligned operand is the identity), `mkAnd0_high_coeffs`
    (the constant's low bits are cleared), `mkAnd0_low_zero` / `_low_bits`
    (P-c via `lowbits_sound`) / `_low_kn` (`lin_lowbits_kn_sound`), and
    `mkAnd0_lit_mask` (J3e: the low `j3` bits decide a general literal
    mask — `v.toNat &&& k.toNat = ua.toNat &&& k.toNat` by bit
    extensionality, `Nat.testBit_mod_two_pow` below `j3` and
    `Nat.testBit_lt_two_pow` above it).  The two split arms reuse
    `and_high_split_denot` / `and_low_split_denot`, the R6 fallbacks
    `and_highmask_srl` / `and_highmask_val`;
  * `mkAnd_denot` (the `narrow_mask` pre-case) through
    `zland_mask_narrow` — the `Nat` `land_mask_narrow` lifted to `zland`,
    with `xhi_sound` giving the `x < 2^j` side condition;
  * `mkAndK_denot`, both mask-merge spellings, through one MERGE step
    (`mkAnd_denot` + the new `zland_assoc`) and the R6 value identity
    `r6_mul_srl_val` (`2^i * (x >> i) = x & -2^i`, from `u_mul_eqm`,
    `u_srl64`, `Int.ediv_mul_add_emod` and `land_highmask`);
  * `lin_branch_sound` (`EQ`/`NE` by two `lin_ge0_sound` calls, the
    unsigned comparisons, and `LT`/`GE` reduced to them by
    `bv_lts_eq_ltu_small` on the `erange` high bounds).
  The branch
  decision `decide_branch_sound` (through its `lit_branch` arm, the
  `diff_branch` literal-difference arm, `range_branch`/`erange` and
  `lin_branch`), then the whole 32-bit block that used to be deferred —
  `bv_swrap32_eq`, `sext32_val`, `u_swrap32`, `zfastw_eq`, `zaluw_l_eq`,
  `mkAluw_denot`.  (`land_aligned_small`, `zlor_eq_add_of_zland` and
  `or_disjoint_sound` belong to the OR block and are present below, with
  `foldK_denot`; they were NOT part of this block.)
  THE 32-BIT DEFERRAL IS GONE.  It was cheaper than the earlier notes
  feared: this tree's `zfastw` already speaks `sx32`/`land32`, so the only
  missing calculus was `bv_swrap 32 u % 2^64 = sx32 u` (`bv_swrap32_eq`,
  two `Int.emod_eq_of_lt` cases on a shifted representative),
  `sext32_val`, and `bv_swrap`'s periodicity in `t mod 2^32` (`u_swrap32`).
  `zfastw_eq` then needs nothing else: `ADD`/`SUB`/`SLL`/`SRL` are
  `BitVec.toNat_*` + `low32_toNat` + the `Int.natCast_*` casts, and the
  other seven `AluOp`s are `rfl`.  `mkAluw_denot` follows , with
  the shift-amount half factored into one lemma generic in the residual
  expression (see its section note).
  THE `evalS_eq` BLOCKER IS GONE (it was a definition bug, not a proof
  problem).  `AxSymExec3.zext_fast`'s `n = 0` branch is now
  `wrap64 (u - 1)`, so the fast path yields `2^64 - 1` at width 0 and
  AGREES with `zext_lit` (`bv_swrap 0 0 = -1`, then `% 2^64`).  Nothing in
  THIS file needed to change for it; the `sx = false ∨ 1 ≤ n`
  hypotheses of `zext_fast_eq` / `extz_0` / `sext64_small` are still
  there but are no longer on the critical path.
  The whole `eval_closed` layer and the
  concretization layer.

  * `eval_closed_sound`, `esubst_sound`, `all_eval_to_sound`,
    `eval_closed_range` (4503–4554);
  * `zext_fast_eq_all`: `zext_fast = zext_lit` at EVERY width, with NO
    side condition.  The three regimes are `n = 0, sx = true` (both sides
    `2^64 - 1`: `zext_fast_zero` / `zext_lit_zero`), `1 ≤ n ≤ 8` (the old
    lemma), and `8n > 64` (both sides are the slice `x / 2^(8*lo)`:
    `zland_zones_ge` + `bv_swrap_emod_pow` + `two_pow_sub_two64`, where
    `zland w (zones m) = w` for `0 ≤ w < 2^64`, `m ≥ 64`, and
    `bv_swrap m z % 2^64 = z % 2^64` for `m ≥ 64`);
  * `evalS_eq`, `all_eval_toS_eq`, `probeS_eq`, `conc_try_sound`,
    `concretize_sound`, `foldK_denot` (4554–4632).

  Now ONE-LINE downstream facts: `concretize` is sound at any expression,
  `foldK` preserves the denotation, and the enumeration sweep
  `all_eval_to` is the reference sweep.
  THE WHOLE `zlnot`/OR BLOCK, and with it the blocker that stopped the
  `mk*K*` family.
  * `land_aligned_small`, `or_disjoint_sound`, plus the local
    no-carry calculus (`nat_or_eq_add_of_and_zero`, `two_mul_or`,
    `or_or_or_swap`, `and_mod_two_zero`, `zlor_eq_add_of_zland`).
  * the ALL-ONES COMPLEMENT primitive: `testBit_ones_sub`,
    `land_ones_sub_eq_zero`, `lor_ones_sub`, `lxor_all_ones_sub`,
    `nat_or_eq_and_ones_sub_add`.
  * `or_as_and_not_plus`, `zlnot_emod_pow`/`zlnot_emod_toNat`,
    `or_R1`, `mkOr_denot`, `lxor_ones64`.
  THE COMPLEMENT PRIMITIVE — how it was actually done (the route the
  earlier notes planned was unnecessary).  Lean core has no
  `Nat.testBit_sub`, but it HAS the bit-level complement fact:
  `Nat.testBit_two_pow_sub_succ`
  (`testBit (2^n - (x+1)) i = (decide (i < n) && ! testBit x i)`,
  `Init/Data/Nat/Bitwise/Lemmas.lean`).  With `2^k - 1 - x` written as
  `2^k - (x+1)`, the three identities (`&&&` is `0`, `|||` and `^^^`
  are `2^k - 1`) are three `Nat.eq_of_testBit_eq` proofs of four lines
  each (`testBit_ones_sub` + `Nat.testBit_and/or/xor` +
  `Nat.testBit_two_pow_sub_one`).  The halving induction sketched in the
  previous version of this header is NOT needed and is recorded in the
  section note only as history.
  `or_as_and_not_plus` then follows the plan that WAS right: with
  `M = 2^64-1-C`, `(X &&& M) &&& C = 0` gives
  `(X &&& M) + C = (X &&& M) ||| C`, and
  `Nat.or_and_distrib_right` + `Nat.and_two_pow_sub_one_of_lt_two_pow`
  turn that into `X ||| C`.  `lxor_ones64` is `lxor_all_ones_sub` at the
  `Nat` level lifted through the window.
  The smart-constructor denotations
  `mkSlt_denot`, `mkAluK0_denot`, `mkAluK_denot`, `pow2_log_sound`,
  `mkMdK_denot`, `swrap32_neg`.  Local helpers added for them:
  `zpow2_bounds` (`0 < 2^k < 2^64` for `0 ≤ k < 64`), `zpow2_toNat`,
  `zpow2_sub_one_toNat`, `zpow2_sub_one_mod_toNat`,
  `zpow2_sub_one_mod_mod_toNat`, `zlor_comm_int`, `zland_comm_int`.
  `mkAluK0_denot`'s XOR-by-all-ones case is where `lxor_ones64` is
  consumed; its OR case is `mkOr_denot`.
  The 32-bit ALU denotations through the
  AMO helpers, i.e. everything up to the `sym_step_sound` block:
  * the two 32-bit prerequisites this tree owed: `sx32_stable_sound` and
    `zband32_sound`, both stated as "the denotation is a fixed point of
    `bv_swrap 32`" so `mkAluwK0`'s two arms are one `rw`. the
    load path of every `sym_step_sound` arm;
  * `wr_covered_sound`, `storeok_sc_sound`, `resv_inval_sound` (5045–5102);
  * `amo_alignedb_sound` (+ `amo_alignedb_gen`), `amo_val_alu32`,
    `amo_val_alu64`, `amo_val_swap` (5103–5130).
  THE WHOLE STEP BLOCK, i.e. everything
  the executor's soundness needs:
  * `amo_store_bytes_newval` (5131): the `.W` arm is `mkAluwK_denot` +
    `low32 ∘ sext 64 = id` + `amo_val_alu32`, the `.D` arm `mkAluK_denot` +
    `amo_val_alu64`, the `SWAP` arm `amo_val_swap` + `store_bytes_low32`;
  * `sym_step_sound_{load,store,lr,sc,amo}` (5160/5193/5231/5280/5308) —
    the five memory classes.
  Local helpers this block needed: `st_okR_sset` / `st_okR_sjump` (the
  `st_okR` half of every register-writing / pc-only arm: the state is a
  structure literal, so the machine equality is projection reduction and
  the only content is `regs_ok_upd`), `sext_lit_denot`, `zext_lit_denot`,
  and `zshiftl_bridge` (the tree has TWO `zshiftl`s, `AxSymExec3`'s and
  `PropExec`'s; `zland_m2` is textually identical in both, so `show` with
  one spelling suffices there).
  5863 — THE WHOLE `ExecSound` SECTION, Part 2
  below): the scripted-loop induction `sym_exec_go_sound` (with
  `sym_exec_acc`), the general drivers `sym_exec_soundR`, `sym_exec_sound`
  and `sym_exec_ex`, the strict drivers `sym_execS_go_sound`,
  `sym_execS_soundR`, `sym_execS_sound`, `sym_execS_ex`, the table-driven
  `sym_execT_go_sound`, `sym_execT_soundR`, `sym_execT_sound`,
  `sym_execT_ex`, and the clean-exit facts `sym_exec_resv`,
  `sym_execS_resv`, `sym_execT_resv`.  `sym_exec_ex` is the theorem
  `AxSymRun3.run_sound` consumes (one application, plus `st_ok_entry`).
  THE TWO JOINT-BOUND LEMMAS the carry
  chain needs: `end_hi_sound` (`b+k,+n` ends before `e` when the joint
  `KRange (b+k+n)` fact and the no-wrap premisses are recorded) with
  `le_end_sound` / `num_apart_sound` as its extraction helpers, and
  `ranges_apart_x_sound` (apartness of two SYMBOLIC-length ranges).
  THE WHOLE `Section XSound`:
  `find_readbase_In`, `x_filter_nil`; `sym_stepX_sound` (the extension-mode
  step) with `x_dischargeable_read_base` (the obligation's consequences),
  `cap_rd_next_ge` and `sym_stepX_next_ge`; then the drivers —
  `sgoX_ok` / `sgoX_stop_ok` (the extension-mode invariant, a named
  predicate like `go_ok`/`sgo_ok`), `sym_execTX_go_sound`,
  `sym_execTX_sound`, **`sym_execTX_ex`** (the theorem
  `AxSymRun3.runTX_sound` consumes), `sym_execTX_resv`,
  `sym_execSX_go_sound`, `sym_execSX_sound`, `sym_execSX_resv`.
  `wbytes_out` (local union of the two
  `CatExec` halves), `kentry_ok_frame`, `zf_piece` (+ `kzero_piece` as its
  instance) and `kimg_piece`; `kcut_sound` with `kzero_cut_sound` /
  `kfill_cut_sound` / `kunk_cut_sound`, `kcut_store` and
  `kzero_cut_store`; the prepared/cached prune equations `in_sides_eq`,
  `in_sides_x_eq`, `num_apart_p_eq`, `ranges_apart_p_eq`, `prune1p_eq`,
  `prunep_eq`, `ranges_apart_pc_eq`, `prune1pc_eq`, `prunepc_eq`; and
  `zf_frame`, `ktrim_sound`, `prune_zf_sound`.
  `Section CarrySound` is COMPLETE:
  `word_slice_bytes` and the four theorems after it, `kword_cut_sound`,
  `prune1_sound`, `prune_sound`, `carry_sound` (7262) — the theorem
  `AxSymRun3.carry_after` consumes.  Nothing  in this file is
  missing any more.
  `word_slice_bytes` then keeps the RHS in `Z_to_le_bytes n (bv_unsigned V /
  2^(8d))` shape (`skipn_Z_to_le_bytes` + `firstn_Z_to_le_bytes` put it
  there, and `firstn` introduces NO modulus), and the LHS is reduced to it
  through `ext_Z_range` + `Z_to_le_bytes_mod_nat`.
 ONE TRAP, paid for twice: the
  "shape" hypothesis of `kentry_ok_frame` is a `match` on the entry, and
  Lean generalises a `match` in a type over EVERY local hypothesis whose
  type mentions the scrutinee — so the same source text elaborates to
  `match K, HK with` in `kentry_ok_frame` but to `match K, HK, Hm with` in
  a lemma that also carries a hypothesis mentioning `[K]`, and the two are
  NOT definitionally equal.  Hence the split: only `prune1_keep_piece`
  takes the shape (its context has `K` and `HK` only), `prune1_dbfun` is a
  `def` for the hint-list table (so no `match` on the hint list is ever
  elaborated among hypotheses that mention it), and the plumbing takes the
  two "keep" cases as hypotheses.  Also: in the `¬same base` arms the entry
  keeps its OWN address (`SA kb kk`), so `HK` must NOT be rewritten to
  `wb` there; and `prune1`'s `KBlob` literal branch spells its length
  modulus `two64`, so `rw [two64_eq] at hc` is the bridge before `omega`
  can see `2 ^ 64`.
  Three
  traps, each one paid for:
  * `know_byte_cov` is `List.brecOn`-compiled and its OR-pattern arms
    (`.KZero ⟨kb,kk⟩ (.ELit l0) | .KFill …`) do NOT reduce under
    `simp only []`, and `cases K` leaves a hypothesis alone once it has
    been UNFOLDED (its type is then a `match` on `K`), after which
    `split at H` splits the WRONG arm.  The idiom: keep
    `H : know_byte_cov … = true` FOLDED, `cases K`, then rewrite with the
    per-shape `rfl` equation (`know_byte_cov_zero` … `know_byte_cov_img`);
    the four `.ELit`-pattern ones need `cases len <;> rfl` (plain `rfl`
    does not see through the shared decision tree).
  * `kentry_ok`'s statement spells an entry's address as the DESTRUCTURED
    record while `rel_lit_inside`/`estart` goals spell it `SA …`: the two
    are convertible but not syntactically equal, and `omega` then sees two
    atoms.  Keep the entry's address whole (`sa`) and carry
    `hsa : SA sa.a_base sa.a_off = sa`; rewrite `hst` with it before any
    `omega`.
  * `store_ok_of_all` states its bound at `((2^64 : Nat) : Int)`, so
    `rw [← two64_eq_natCast, two64_eq]` is the bridge — NOT `push_cast`,
    which blows `maxRecDepth` on these terms.
  * `cases h : len` does not rewrite the hypothesis's length match either:
    follow it with `simp only [h] at H` (one step does rewrite + iota) and
    `rw [h] at hfl hz` for the `elenZ` hypotheses.
  `split at Hs`
  peels the next nested `match`/`if` of `Hs`, and the goal order follows the
  SOURCE arm order (`| some r => … | none => …` gives `some` first; the
  reverse spelling gives `none` first); `rename_i` names the payload then
  the equation, in that order.  An `if C then … else SStop` in `Hs` is
  better peeled with `by_cases h : C = true` + `rw [ite_eq_left h] at Hs` /
  `rw [ite_eq_right h] at Hs` than with `split` (split turns the false arm into a
  `¬(if … = …)` side goal).  `cases h : ss.s_resv` does NOT work (it leaves
  an unsolved dependent-elimination goal); `split at Hs` does.  In the
  branch arm, `cases hdb : decide_branch …` does NOT rewrite `Hs` (the
  documented `cases`-vs-`match`-hypothesis trap): `generalize hdb : … = d1
  at Hs` then `cases d1`, once per decision level.  The `SStop` classes
  (`ecall`, `ebreak`, `csr`, `csrI` and the 15 FP arms) need
  `exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs)
  (by simp)` — a bare `absurd Hs (by simp)` reports "simp made no progress"
  because `Hs` is only DEFINITIONALLY in the `SStop` shape.
  * Extracting ONE conjunct from a long `&&`-chain (`x_dischargeable`): do
    not depend on the chain's association (`Bool.and_eq_true` peeling hands
    you a grouping you then have to guess).  CASE-SPLIT the wanted Boolean to
    `false`:
    `cases h : <conjunct> with | false => rw [h] at H; exact absurd H (by simp) | true => rfl`
    — whatever the nesting, `X && false` collapses the whole chain.  That is
    `x_dischargeable_read_base`.
  * `sym_stepX` peels like `sym_step`: `unfold sym_stepX at Hs`,
    `generalize hst : sym_step segs i ss scr_nil = r at Hs`, `cases r`, then
    `dsimp only at Hs` (dsimp, NOT `simp only []`, which errors when it makes
    no progress) to iota-reduce the arm; a `Bool` `if` is then peeled with
    `by_cases h : … = true` + `rw [ite_eq_left h] at Hs`.  `stepres.SOk.injEq` is
    the injection lemma for `SOk = SOk`.
  * `Z_to_bv` is an `abbrev`, so `st_ok`'s `mkst … (BitVec.ofInt 64 pc)` and
    `sym_execTX_ex`'s `mkst … (Z_to_bv 64 pc)` are only DEFINITIONALLY equal
    — `rw` will not fire.  Bridge once with
    `have hEq : <Z_to_bv form> = <BitVec.ofInt form> := rfl`.
  * `Int.add_emod_emod (m n k) : (m + n % k) % k = (m + n) % k` is this
    development's `Zplus_mod_idemp_r`; it plus two `Int.emod_eq_of_lt`
    collapses the `u_add64` muck in `end_hi_sound`.
  * `omega` and `bv_unsigned`: `u64_range` states its bound as `↑(w.toNat)`
    while the goals of this block are spelled `bv_unsigned w`, and `omega`
    treats the two as DIFFERENT atoms.  Restate in the goal's spelling
    (`have hb0 : 0 ≤ bv_unsigned (edenot E b) := (u64_range _).1` typechecks
    by defeq and keeps the atoms identical); likewise restate an
    `end_hi_sound` conclusion UNFOLDED
    (`have HE : bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1) ≤ e := …`)
    before an `omega` whose goal is unfolded.
  * `split at H` peels the redex of a `match`/`if` HYPOTHESIS in SOURCE
    order, and `rename_i` names payload, then equation(s), then the `if`
    condition.  `end_hi` = (match on `n`, `0 ≤ lo1 + k`,
    `hi1 + k + h1 < two64`, the `find_range` match); `num_apart` = (the
    four-way option match — 6 payloads + 4 equations, then the `||`
    condition, then two `if`s).  Peeling with `split` is what makes these
    work at all: a `match`-hypothesis is NOT rewritten by `cases`.
  * `split` on a goal whose term is a `match a, b with | .ELit k, … | …`
    (the shape every `mkAnd*`-style constructor has) gives ONE GOAL PER
    ARM with the constructor form already substituted, plus one fallback
    goal carrying the negative equations.  That is the cheap way into
    `mkAndK`, and the fallback is one `mkAnd_denot`.
  * `split` on `if (if C then D else false) then X else Y` splits the
    CONDITION's inner if FIRST (the traversal reaches it before the outer
    one), so a two-level `EQ`/`NE` condition needs three splits — or, much
    better, `by_cases hC : C = true` + `rw [ite_eq_left/ite_eq_right hC] at H`.
  * `split at H` on an `Option`-valued H whose arm holds a `match c with`
    splits THAT match first: `try simp only [] at H` before the split
    reduces it (the scrutinee is a constructor by then).
  * `omega` does NOT know `two64 = 2 ^ 64`, so it treats `k % two64` and
    `k % 2 ^ 64` as different atoms (`two64_eq` is `rfl`, but `omega`
    will not unfold it).  Pick ONE spelling per proof; a
    `rw [two64_eq] at *` is only safe when it is applied consistently.
  * `rw [h]` where `h` rewrites a subterm that ALSO occurs inside a
    `zlog2 …`/`ctz64 …` argument rewrites both, destroying the match with
    a lemma stated at the old form.  Use `conv => lhs; rw [h]` or
    `conv => rhs; rw [h]` (both exist; the `conv_lhs` tactic does not).
  * `rw [u_lit64]` rewrites every `bv_unsigned (Z_to_bv 64 _)`, the goal's
    own LHS included — order the rewrites (or `conv`) so the intended
    occurrence is the one that gets hit.
  * `(bv_unsigned (edenot E a)).toNat` needs the parentheses: `bv_unsigned
    (edenot E a).toNat` parses as `bv_unsigned ((edenot E a).toNat)` and
    fails on the implicit width.
  * `two_pow_pos_int`'s statement is about `2 ^ k`, so a goal printed with
    `zpow 2 k` needs `unfold zpow` first.
  * the `Int`/`Nat` bridges this block uses: `Int.toNat_le_toNat`,
    `Int.toNat_lt` (its argument is the nonneg of the LEFT side),
    `Int.toNat_sub''` (its second operand must be a `natCast`),
    `Int.natCast_sub`, `Int.toNat_of_nonneg`, `Nat.log2_eq_iff`,
    `Nat.testBit_two_pow_mul` / `_two_pow_sub_one` / `_mod_two_pow` /
    `Nat.testBit_lt_two_pow` / `Nat.and_lt_two_pow` / `Nat.and_assoc`.
  This tree's `Forall` convention is the membership predicate
  `∀ f ∈ l, P f` (core Lean has no `List.Forall`); `Forall_app_intro` /
  `Forall_one` are the composition helpers.
  (the working idiom for `let`/`match`-heavy `Option`- and
  `Bool`-valued definitions — `lin_srange`, `lin_ge0`, `lin_ge0_scaled`,
  `xlo`, `sub_itv`, `ranges_apart`).  `unfold f at H`, then
  `try simp only [] at H` (the `try` is essential: bare `simp only []`
  ERRORS when it makes no progress) zeta-reduces the `let`s; then
  `generalize h : <scrutinee> = x at H` + `cases x` + `try simp only [] at
  H` peels one match at a time (a `match`-scrutinee CAN be generalised
  this way, unlike a `cases h : t` on it).  A hypothesis whose term the
  unfold produced zeta-reduced (`(srl_expand kn (lin_of e).2).fst`) must
  be generalized at the UNREDUCED form: `by_cases h : <the printed
  term>` does NOT rewrite the `if` inside `H` when the two terms were
  elaborated with different `Decidable` instances, so prefer
  `split at H` (which also splits matches inside an `if`-condition) or
  state the case on the projections of the unreduced term.
  `split at H` names its hypotheses inaccessibly: `rename_i` them.
  `omega` is
  unreliable as soon as a term of the shape `q * 2 ^ 64` (a variable
  times the numeral) is in the context or the goal: it reports a bogus
  counterexample.  Do the additive steps BEFORE such a term enters the
  context, keep the multiple as a single atom, and finish with
  `mul_two64_eq_zero` (a squeeze into `(-2^64, 2^64)`), which works on
  `2 ^ 64 * (1 - q)` via `Int.pos_of_mul_pos_right`.  Two related
  traps: `omega` treats `(-k) * t` as a DIFFERENT atom from `-(k * t)`
  (pass `Int.neg_mul` as a hypothesis), and it will not distribute
  `(a + b) * c` (pass `Int.add_mul` / `Int.mul_sub`).
  `cases h : t` does not
  rewrite a hypothesis whose type is a `match` on `t`; use
  `generalize h : t = x at H` and then `obtain`.  Conversely, after a
  `cases` the branch match in the hypothesis is NOT iota-reduced:
  follow it with `simp only [] at H` (which errors when it makes no
  progress, so it cannot be sprinkled blindly).  Both traps are visible
  in `pageup_low_k_sound`.
  (a hypothesis that mentions the scrutinee cannot be REUSED
  after the goal's `cases`).  `cases ha : is_lit a` rewrites the GOAL but
  leaves every other hypothesis mentioning `is_lit a` alone, so a local
  lemma whose statement contains `match is_lit a with …` no longer
  matches the (reduced) goal — `exact H` reports a type mismatch between
  the two `match`es.  Either `generalize` the hypothesis over the value,
  or (what `mkAluw_denot` does) state it parametrically in the residual
  expression and pass the three branch instances in.
  `Int.natCast_emod` / `_add` / `_mul` / `_pow` / `_ediv` leave a
  `↑4294967296 : Int` (an `Int.ofNat` of the `Nat` literal) in the goal
  while the same numeral written on the other side is the `Int` literal;
  the two ARE the same term, so `exact rfl` / `rfl` closes the goal, but
  `rw`/`simp` will NOT match them and will report a `did not find the
  pattern` / unused-simp-argument.  `zfastw_eq` ends every case with a
  bare `rfl` for this reason.  Likewise `decide_eq_false` (not `simp`) is
  the way to turn `h : t ≠ 0` into a `Bool` equation when the numeral
  spellings differ.
  OPERATIONAL.  `lake env lean <file>` does NOT refresh the module's
  `.olean`; a scratch file importing the module then sees the STALE
  interface (`Unknown identifier` for the theorem just added).  Either
  iterate inside this file (≈8 s per check) or emit the olean explicitly
  — `lake env lean -o .lake/build/lib/lean/LinuxSem/Common/AxSymExec3Sound.olean
  LinuxSem/Common/AxSymExec3Sound.lean` (≈8 s once) and then
  check scratch files in ≈0.7 s each.
  TACTIC AVAILABILITY (core Lean 4.31 only; no Mathlib in this repo):
  `set`, `nth_rewrite`, `conv_lhs`, `norm_num`, `ring`, `push_neg`,
  `by_contra`, `positivity` and unqualified `le_refl` do NOT exist.
  Use `generalize h : e = x at H`, `conv => lhs; rw [..]`, `by decide`,
  `Int.le_refl`, `by_cases` + `absurd`, `push_cast` / `exact_mod_cast`
  (these two do exist), `ac_rfl` and `omega`.  A `cases x with`
  alternative MAY contain nested `cases` (this is fine).  `omega` does
  not unfold abbreviations: state hypotheses with `2 ^ 64` rather than
  `two64`, and with `bv_unsigned _` rather than `(·.toNat : Int)`.
  `2 ^ k` needs a `Nat` exponent — use `zpow 2 k` for `k : Int`.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.SymExec
import LinuxSem.Common.SymStepR
import LinuxSem.Common.AxSymExec3

namespace LinuxSem.Common.AxSymExec3Sound

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SymStepR
open LinuxSem.Common.StoreOk
open LinuxSem.Common.AxSymExec3

local instance axsymexec3sound_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! ## Part 0: the denotation layer

    Every definition of `AxSymExec3Sound`, in  order.  The
    lemmas that follow in Part 1 use them; see the file header for why
    they are collected here rather than interleaved. -/

/-! ### 0.1 Modular equality of `Z` values (`eqm`)

    `eqm a b` says `a` and `b` agree modulo `2^64`, which is exactly the
    relation `Z_to_bv 64` cannot see.  Every linear-form lemma
    (`lin_of_sound`, `unlin_sound`, …) is stated with it. -/
def eqm (a b : Int) : Prop := ∃ q, a = b + q * 2 ^ 64

/-! ### 0.2 Linear forms: denotation (`Section LinDenot`) -/

/-- `bv_unsigned` of the denotation, as an `Int`. -/
def uE (E : env) (e : expr) : Int := bv_unsigned (edenot E e)

/-- The constant + scaled-atom total of a linear form's term list. -/
def tden (E : env) : List (Int × expr) → Int
  | [] => 0
  | (k, a) :: r => k * uE E a + tden E r

/-- Denotation of a whole linear form `(constant, terms)`. -/
def lden (E : env) (x : lin) : Int := x.1 + tden E x.2

/-! ### 0.3 The register file -/

/-- The concrete register file agrees with the symbolic one under `E`. -/
def regs_ok (E : env) (sr : List expr) (regs : BvMap word) : Prop :=
  ∀ r : reg, getr regs r = edenot E (sr_get sr r)

/-- The IDENTITY valuation on registers: `EVar n` for `n < 32` is `x_n`. -/
def reg_ev (regs : BvMap word) (rest : Nat → word) : Nat → word :=
  fun n => if n < 32 then getr regs (BitVec.ofInt 5 (n : Int)) else rest n

/-! ### 0.4 Memory denotation, flatness, byte arithmetic

    Part P4a . -/

/-- The log denotes a fold of `wbytes` over the base memory: the OLDEST
    entry is applied first, so the head of the list is the outermost. -/
def mem_denot (E : env) (base : word → Option byte) :
    List sentry → word → Option byte
  | [] => base
  | ⟨a, w, v⟩ :: rest =>
      wbytes (mem_denot E base rest) (adenot E a)
        (word_to_le_bytes w (edenot E v))

/-- The Z-address of an `saddr` (base value + literal offset, NOT wrapped
    yet). -/
def estart (E : env) (a : saddr) : Int := bv_unsigned (edenot E a.a_base) + a.a_off

/-- The Z-value of a length expression. -/
def elenZ (E : env) (n : expr) : Int := bv_unsigned (edenot E n)

/-- `a, a+n` fits in the 64-bit address space without wrapping. -/
def flat (E : env) (a : saddr) (n : Int) : Prop :=
  0 ≤ estart E a ∧ estart E a < 2 ^ 64 ∧ 0 ≤ n ∧ estart E a + n ≤ 2 ^ 64

/-- Every logged store is flat (its width is at most 8 bytes). -/
def log_flat (E : env) : List sentry → Prop
  | [] => True
  | ⟨a, w, _⟩ :: rest => w ≤ 8 ∧ flat E a (w : Int) ∧ log_flat E rest

/-- Sign-extend the `8*n`-bit reading of `u` when `sx`, else keep it. -/
def extz (sx : Bool) (n : Nat) (u : Int) : Int :=
  if sx then bv_swrap (8 * n) u else u

/-! ### 0.5 Knowledge and side conditions -/

/-- **Knowledge denotation.**  What one `kentry` asserts about the BASE
    memory `base` (the memory the block started from: the image plus
    whatever the caller's overlay already held). -/
def kentry_ok (segs : List Segment) (E : env) (base : word → Option byte)
    (K : kentry) : Prop :=
  match K with
  | .KWord a w v =>
      w ≤ 8 ∧ flat E a (w : Int) ∧
        rdn segs base (adenot E a) w = some (word_to_le_bytes w (edenot E v))
  | .KZero a n =>
      flat E a (elenZ E n) ∧
        ∀ i, 0 ≤ i → i < elenZ E n →
          base (BitVec.ofInt 64 (estart E a + i)) = some (BitVec.ofInt 8 0)
  | .KBlob a n k =>
      flat E a (elenZ E n) ∧ ((E.eb k).length : Int) = elenZ E n ∧
        ∀ i, 0 ≤ i → i < elenZ E n →
          base (BitVec.ofInt 64 (estart E a + i))
            = some ((E.eb k).getD i.toNat (BitVec.ofInt 8 0))
  | .KImg lo hi =>
      0 ≤ lo ∧ hi ≤ 2 ^ 64 ∧ ∀ i, lo ≤ i → i < hi → base (BitVec.ofInt 64 i) = none
  | .KAlign e m => 0 < m ∧ bv_unsigned (edenot E e) % m = 0
  | .KRange e lo hi => lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi
  | .KWr a n =>
      flat E a (elenZ E n) ∧
        ∀ (d : Int) (m : Nat), 0 ≤ d → d + (m : Int) ≤ elenZ E n →
          store_ok segs base (BitVec.ofInt 64 (estart E a + d)) m = true
  | .KDisj a1 n1 a2 n2 =>
      estart E a1 + elenZ E n1 ≤ estart E a2 ∨
        estart E a2 + elenZ E n2 ≤ estart E a1
  | .KFill a n c =>
      flat E a (elenZ E n) ∧
        ∀ i, 0 ≤ i → i < elenZ E n →
          base (BitVec.ofInt 64 (estart E a + i)) = some (BitVec.ofInt 8 c)
  | .KUnk a n =>
      flat E a (elenZ E n) ∧
        ∀ i, 0 ≤ i → i < elenZ E n →
          base (BitVec.ofInt 64 (estart E a + i)) ≠ none

/-- A whole knowledge list. -/
def know_ok (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) : Prop :=
  ∀ K ∈ kn, kentry_ok segs E base K

/-- **Side-condition denotation.** -/
def sc_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (s : sidecond) : Prop :=
  match s with
  | .SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | .SCFlat a n => flat E a (elenZ E n)
  | .SCDisj a1 n1 a2 n2 =>
      flat E a1 (elenZ E n1) ∧ flat E a2 (elenZ E n2) ∧
        (estart E a1 + elenZ E n1 ≤ estart E a2 ∨
         estart E a2 + elenZ E n2 ≤ estart E a1)
  | .SCInside a1 n1 a2 n2 =>
      flat E a2 (elenZ E n2) ∧ 0 ≤ elenZ E n1 ∧
        estart E a2 ≤ estart E a1 ∧
        estart E a1 + elenZ E n1 ≤ estart E a2 + elenZ E n2
  | .SCStoreOk a n => store_ok segs base (adenot E a) n = true
  | .SCReadBase a n sx e =>
      ∃ bs, rdn segs base (adenot E a) n = some bs ∧
        BitVec.ofInt 64 (extz sx n (bytes_le_to_Z bs)) = edenot E e
  | .SCEq a b => edenot E a = edenot E b

/-- A whole batch of side conditions. -/
def scs_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (l : List sidecond) : Prop :=
  ∀ s ∈ l, sc_denot segs base E s

/-! ### 0.6 Relational sum-fact bounds (J2-b) -/

/-- A sum fact `(terms, (lo, hi))` is true when the terms denote a value in
    `[lo, hi]`. -/
def sfact_ok (E : env) (f : sfact) : Prop := f.2.1 ≤ tden E f.1 ∧ tden E f.1 ≤ f.2.2

/-- Denotation of a symbolic-length sum term list. -/
def xt_den (E : env) : xterms → Int
  | [] => 0
  | (e, k) :: r => bv_unsigned (edenot E e) + k + xt_den E r

/-! ### 0.7 The state relations (`Section StepSound`) -/

/-- **Block-boundary relation** (independent of the reservation extension):
    the machine is an `mkst` (no live reservation); the symbolic `s_resv`
    field is not consulted (the drivers clear it on entry, `clr`). -/
def st_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) : Prop :=
  ∃ regs, ms = mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom ∧
    regs_ok E ss.s_regs regs ∧
    log_flat E ss.s_log ∧
    know_ok segs E base ss.s_know

/-- Denotation of the tracked reservation. -/
def resv_denot (E : env) (r : Option saddr) : Option word :=
  match r with
  | some a => some (adenot E a)
  | none => none

/-- **General relation** (inside a block): the machine is an `mkstR` whose
    reservation is the denotation of `s_resv`. -/
def st_okR (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) : Prop :=
  ∃ regs, ms = mkstR regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
      (resv_denot E ss.s_resv) ∧
    regs_ok E ss.s_regs regs ∧
    log_flat E ss.s_log ∧
    know_ok segs E base ss.s_know

/-! ### 0.8 Extension mode (`Section XSound`) -/

/-- Valuations agreeing below a bound, and on the byte strings. -/
def eagree (b : Nat) (E E' : env) : Prop :=
  (∀ n, n < b → E.ev n = E'.ev n) ∧ E.eb = E'.eb

/-- Update one word variable. -/
def eupd (E : env) (i : Nat) (v : word) : env :=
  ⟨fun n => if n == i then v else E.ev n, E.eb⟩

/-- `ss` describes `ms` under EVERY valuation that agrees with `E` below
    `s_next ss`: the symbolic objects are (semantically) closed below the
    fresh-variable counter, so the counter can be used to name new
    values. -/
def st_okX (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) : Prop :=
  ∀ E', eagree ss.s_next E E' → st_okR segs E' base rom ss ms

/-- One byte as a LOAD sees it: the overlay if defined, else the image. -/
def rd1 (segs : List Segment) (mem : word → Option byte) (x : word) : Option byte :=
  match mem x with
  | some b => some b
  | none => seg_rom segs x

/-! ### 0.9 The `KZero`/`KFill`/`KUnk` generic frame -/

/-- The entry kinds `kcut`/`ktrim`/`prune_zf` are generic in: an entry
    constructor whose meaning is "flat, and every byte of the range is
    `byteof`" — `KZero` (byte 0) and `KFill _ _ c` (byte `Z_to_bv 8 c`). -/
def zf_kind (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) : Prop :=
  ∀ E M a n,
    kentry_ok segs E M (mk a n) ↔
      (flat E a (elenZ E n) ∧
       ∀ i, 0 ≤ i → i < elenZ E n → byteof (M (BitVec.ofInt 64 (estart E a + i))))

/-- A `base_range` cache: every entry stores the right answer. -/
def br_cache_ok (allkn : List kentry)
    (c : List (expr × Option (Int × Int))) : Prop :=
  ∀ p ∈ c, p.2 = base_range allkn p.1

/-- Every `KWord` in the list has width at most 8 bytes. -/
def kn_words_le8 : List kentry → Prop
  | [] => True
  | .KWord _ w _ :: r => w ≤ 8 ∧ kn_words_le8 r
  | _ :: r => kn_words_le8 r

/-! ## Part 1: soundness lemmas, in  order

    Part P1: syntactic equality, smart-constructor denotations. -/

/-- `aluop_eqb` reflects equality. -/
theorem aluop_eqb_eq {a b : AluOp} (H : aluop_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp [aluop_eqb] at H ⊢

/-- `mulop_eqb` reflects equality. -/
theorem mulop_eqb_eq {a b : MulOp} (H : mulop_eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp [mulop_eqb] at H ⊢

/-- `expr_eqb` reflects equality: the executor's syntactic checks are
    exactly semantic equality of the symbolic syntax. -/
theorem expr_eqb_eq : ∀ x y : expr, expr_eqb x y = true → x = y := by
  intro x
  induction x with
  | ELit a =>
    intro y H; cases y <;> simp_all [expr_eqb]
  | EVar a =>
    intro y H; cases y <;> simp_all [expr_eqb]
  | EAlu o a b iha ihb =>
    intro y H
    cases y with
    | EAlu o' a' b' =>
      simp only [expr_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨h1, h2⟩, h3⟩ := H
      rw [aluop_eqb_eq h1, iha _ h2, ihb _ h3]
    | _ => simp_all [expr_eqb]
  | EAluw o a b iha ihb =>
    intro y H
    cases y with
    | EAluw o' a' b' =>
      simp only [expr_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨h1, h2⟩, h3⟩ := H
      rw [aluop_eqb_eq h1, iha _ h2, ihb _ h3]
    | _ => simp_all [expr_eqb]
  | EMd o a b iha ihb =>
    intro y H
    cases y with
    | EMd o' a' b' =>
      simp only [expr_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨h1, h2⟩, h3⟩ := H
      rw [mulop_eqb_eq h1, iha _ h2, ihb _ h3]
    | _ => simp_all [expr_eqb]
  | EMdw o a b iha ihb =>
    intro y H
    cases y with
    | EMdw o' a' b' =>
      simp only [expr_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨h1, h2⟩, h3⟩ := H
      rw [mulop_eqb_eq h1, iha _ h2, ihb _ h3]
    | _ => simp_all [expr_eqb]
  | EExt sx lo n a iha =>
    intro y H
    cases y with
    | EExt sx' lo' n' a' =>
      simp only [expr_eqb, Bool.and_eq_true, beq_iff_eq] at H
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
      rw [h1, h2, h3, iha _ h4]
    | _ => simp_all [expr_eqb]
  | EBlob sx k i n =>
    intro y H
    cases y with
    | EBlob sx' k' i' n' =>
      simp only [expr_eqb, Bool.and_eq_true, beq_iff_eq] at H
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
      rw [h1, h2, h3, h4]
    | _ => simp_all [expr_eqb]

/-- `saddr_eqb` reflects equality of addresses. -/
theorem saddr_eqb_eq {a b : saddr} (H : saddr_eqb a b = true) : a = b := by
  obtain ⟨ab, ak⟩ := a
  obtain ⟨bb, bk⟩ := b
  simp only [saddr_eqb, Bool.and_eq_true, beq_iff_eq] at H
  obtain ⟨H1, H2⟩ := H
  rw [expr_eqb_eq ab bb H1, H2]

/-- The literal's denotation. -/
theorem edenot_lit (E : env) (z : Int) : edenot E (.ELit z) = Z_to_bv 64 z := rfl

/-- `v + 0 = v` at the ISA's `ALU_ADD`. -/
theorem alu64_add_0_r (v : word) : alu64 .ADD v (Z_to_bv 64 0) = v := by
  show v + BitVec.ofInt 64 0 = v
  bv_omega

/-- `ALU_ADD` is commutative. -/
theorem alu64_add_comm (a b : word) : alu64 .ADD a b = alu64 .ADD b a := by
  show a + b = b + a
  bv_omega

/-- Subtraction by a literal is addition of its negation. -/
theorem alu64_sub_as_add (v : word) (y : Int) :
    alu64 .SUB v (Z_to_bv 64 y) = alu64 .ADD v (Z_to_bv 64 (- y)) := by
  show v - BitVec.ofInt 64 y = v + BitVec.ofInt 64 (- y)
  bv_omega

/-! ### `eqm`: modular equality of `Int` values

    All of the linear-form reasoning below is congruence modulo `2^64`,
    which is exactly what `Z_to_bv 64` cannot see. -/

theorem eqm_refl (a : Int) : eqm a a := ⟨0, by omega⟩

theorem eqm_sym {a b : Int} (H : eqm a b) : eqm b a := by
  obtain ⟨q, hq⟩ := H
  exact ⟨-q, by omega⟩

theorem eqm_trans {a b c : Int} (H1 : eqm a b) (H2 : eqm b c) : eqm a c := by
  obtain ⟨q, hq⟩ := H1
  obtain ⟨r, hr⟩ := H2
  exact ⟨q + r, by omega⟩

theorem eqm_add {a b c d : Int} (H1 : eqm a b) (H2 : eqm c d) : eqm (a + c) (b + d) := by
  obtain ⟨q, hq⟩ := H1
  obtain ⟨r, hr⟩ := H2
  exact ⟨q + r, by omega⟩

theorem eqm_mul_l (k : Int) {a b : Int} (H : eqm a b) : eqm (k * a) (k * b) := by
  obtain ⟨q, hq⟩ := H
  refine ⟨k * q, ?_⟩
  rw [hq, Int.mul_add, Int.mul_assoc]

theorem eqm_mul_r (k : Int) {a b : Int} (H : eqm a b) : eqm (a * k) (b * k) := by
  obtain ⟨q, hq⟩ := H
  refine ⟨q * k, ?_⟩
  rw [hq, Int.add_mul, Int.mul_assoc, Int.mul_left_comm q (2 ^ 64) k,
    Int.mul_comm (2 ^ 64) (q * k)]

theorem eqm_mod (a : Int) : eqm (a % 2 ^ 64) a :=
  ⟨-(a / 2 ^ 64), by omega⟩

theorem two64z_eq : two64z = 2 ^ 64 := rfl

/-- `snorm` only moves a value by a multiple of `2^64`. -/
theorem snorm_hi (k : Int) (h : (2 : Int) ^ 63 ≤ k % 2 ^ 64) :
    snorm k = k % 2 ^ 64 - 2 ^ 64 := by
  rw [snorm_eq]
  /- `two64z` is NOT rewritten here: doing so rewrites the `if`'s
     condition but leaves the instance behind it at `k % two64z`, and
     the result is a goal that is no longer type-correct (this toolchain
     reports the mismatch instead of repairing it).  Leaving `two64z`
     alone keeps the definitional equality — `two64z_eq` is `rfl` — so
     `h` still matches the guard, and `ite_eq_left` closes the goal. -/
  simp only [snorm_ref]
  exact ite_eq_left h

theorem snorm_lo (k : Int) (h : ¬ ((2 : Int) ^ 63 ≤ k % 2 ^ 64)) :
    snorm k = k % 2 ^ 64 := by
  rw [snorm_eq]
  simp only [snorm_ref]
  exact ite_eq_right h

theorem eqm_snorm (k : Int) : eqm (snorm k) k := by
  by_cases h : (2 : Int) ^ 63 ≤ k % 2 ^ 64
  · rw [snorm_hi k h]; exact ⟨-(k / 2 ^ 64) - 1, by omega⟩
  · rw [snorm_lo k h]; exact ⟨-(k / 2 ^ 64), by omega⟩

theorem eqm_Z_to_bv {a b : Int} (H : eqm a b) : Z_to_bv 64 a = Z_to_bv 64 b := by
  obtain ⟨q, hq⟩ := H
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 64 a).toNat = (BitVec.ofInt 64 b).toNat
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, hq]
  have h : (b + q * 2 ^ 64) % ((2 ^ 64 : Nat) : Int) = b % ((2 ^ 64 : Nat) : Int) := by
    omega
  rw [h]

/-- `bv_unsigned` of a literal is the literal modulo `2^64`. -/
theorem u_lit64a (z : Int) : bv_unsigned (Z_to_bv 64 z) = z % 2 ^ 64 := by
  show ((BitVec.ofInt 64 z).toNat : Int) = z % 2 ^ 64
  rw [BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem eqm_u_lit (z : Int) : eqm (bv_unsigned (Z_to_bv 64 z)) z := by
  rw [u_lit64a]
  exact eqm_mod z

/-! ### Linear-form denotations (`Section LinDenot`)

    `eqm` congruence toolkit plus the 17  denotation lemmas.
    Everything reduces to congruences modulo `2^64`; the arithmetic is done
    with `Int.mul_add`/`Int.mul_assoc` rewrites (no `ring` tactic is
    available in this repository) and closed with `omega` over atoms. -/

/-- Equality implies `eqm`. -/
theorem eqm_of_eq {a b : Int} (h : a = b) : eqm a b := ⟨0, by rw [h]; simp⟩

theorem eqm_snorm_comm (k : Int) : eqm k (snorm k) := eqm_sym (eqm_snorm k)

/-- `snorm` scaled. -/
theorem eqm_snorm_mul (k u : Int) : eqm (snorm k * u) (k * u) :=
  eqm_sym (eqm_mul_r u (eqm_snorm_comm k))

/-- A vanishing `snorm` scaled. -/
theorem eqm_zero_mul_of_snorm (k u : Int) (h : snorm k = 0) : eqm 0 (k * u) := by
  have h1 : eqm (k * u) (snorm k * u) := eqm_mul_r u (eqm_snorm_comm k)
  rw [h] at h1
  simpa using eqm_sym h1

/-- `(k + k') * u = k*u + k'*u` under `eqm`. -/
theorem eqm_mul_add' (k k' u : Int) : eqm ((k + k') * u) (k * u + k' * u) :=
  eqm_of_eq (Int.add_mul k k' u)

theorem tden_nil (E : env) : tden E [] = 0 := rfl

theorem tden_cons (E : env) (k : Int) (a : expr) (r : List (Int × expr)) :
    tden E ((k, a) :: r) = k * uE E a + tden E r := rfl

theorem lins_sound (E : env) (k : Int) (a : expr) (ts : List (Int × expr)) :
    eqm (tden E (lins k a ts)) (k * uE E a + tden E ts) := by
  induction ts with
  | nil =>
    by_cases hz : (snorm k == 0) = true
    · rw [lins, ite_eq_left hz]
      have hs : snorm k = 0 := beq_iff_eq.mp hz
      simpa [tden_nil] using eqm_zero_mul_of_snorm k (uE E a) hs
    · rw [lins, ite_eq_right hz, tden_cons, tden_nil]
      simpa using eqm_snorm_mul k (uE E a)
  | cons hd rest ih =>
    obtain ⟨k', a'⟩ := hd
    by_cases he : (expr_eqb a a') = true
    · have ha : a = a' := expr_eqb_eq a a' he
      subst ha
      simp only [lins, ite_eq_left he]
      by_cases hz : (snorm (k + k') == 0) = true
      · rw [ite_eq_left hz]
        have hs : snorm (k + k') = 0 := beq_iff_eq.mp hz
        have h0 : eqm 0 ((k + k') * uE E a) := eqm_zero_mul_of_snorm (k + k') _ hs
        have h1 : eqm (k * uE E a + k' * uE E a) 0 :=
          eqm_trans (eqm_sym (eqm_mul_add' k k' (uE E a))) (eqm_sym h0)
        have h2 : eqm ((k * uE E a + k' * uE E a) + tden E rest) (tden E rest) := by
          have h := eqm_add h1 (eqm_refl (tden E rest))
          simpa using h
        refine eqm_trans (eqm_sym h2) ?_
        exact eqm_of_eq (by rw [Int.add_assoc, tden_cons])
      · rw [ite_eq_right hz, tden_cons]
        refine eqm_trans (eqm_add (eqm_snorm_mul (k + k') (uE E a)) (eqm_refl _)) ?_
        refine eqm_trans (eqm_add (eqm_mul_add' k k' (uE E a)) (eqm_refl _)) ?_
        exact eqm_of_eq (by rw [Int.add_assoc, tden_cons])
    · rw [lins, ite_eq_right he]
      cases hc : expr_cmp a a' with
      | lt =>
        simp only [hc]
        by_cases hz : (snorm k == 0) = true
        · rw [ite_eq_left hz, tden_cons]
          have hs : snorm k = 0 := beq_iff_eq.mp hz
          have h0 : eqm 0 (k * uE E a) := eqm_zero_mul_of_snorm k _ hs
          have h := eqm_add h0 (eqm_refl (k' * uE E a' + tden E rest))
          simpa using h
        · rw [ite_eq_right hz, tden_cons, tden_cons]
          exact eqm_add (eqm_snorm_mul k _) (eqm_refl _)
      | eq =>
        simp only [hc, tden_cons]
        have h2 := eqm_add (eqm_refl (k' * uE E a')) ih
        refine eqm_trans h2 (eqm_of_eq (by omega))
      | gt =>
        simp only [hc, tden_cons]
        have h2 := eqm_add (eqm_refl (k' * uE E a')) ih
        refine eqm_trans h2 (eqm_of_eq (by omega))

theorem ladd_sound (E : env) (x y : lin) : eqm (lden E (ladd x y)) (lden E x + lden E y) := by
  obtain ⟨c, ts⟩ := x
  obtain ⟨d, us⟩ := y
  have Hf : ∀ (l : List (Int × expr)) (acc : List (Int × expr)),
      eqm (tden E (l.foldr (fun t acc => lins t.1 t.2 acc) acc)) (tden E l + tden E acc) := by
    intro l
    induction l with
    | nil => intro acc; rw [List.foldr_nil, tden_nil]; exact eqm_of_eq (by simp)
    | cons hd tl ih =>
      intro acc
      obtain ⟨k, a⟩ := hd
      rw [List.foldr_cons]
      refine eqm_trans (lins_sound E k a _) ?_
      refine eqm_trans (eqm_add (eqm_refl _) (ih acc)) ?_
      exact eqm_of_eq (by rw [tden_cons, Int.add_assoc])
  simp only [lden, ladd]
  refine eqm_trans (eqm_add (eqm_snorm (c + d)) (Hf ts us)) ?_
  exact eqm_of_eq (by omega)

theorem eqm_mul_assoc (m k u : Int) : eqm ((m * k) * u) (m * (k * u)) :=
  eqm_of_eq (Int.mul_assoc m k u)

theorem lscale_terms_sound (E : env) (m : Int) (ts : List (Int × expr)) :
    eqm (tden E (lscale_terms m ts)) (m * tden E ts) := by
  induction ts with
  | nil => rw [lscale_terms, tden_nil]; exact eqm_of_eq (by simp)
  | cons hd rest ih =>
    obtain ⟨k, a⟩ := hd
    by_cases hz : (snorm (m * k) == 0) = true
    · rw [lscale_terms, ite_eq_left hz, tden_cons]
      have hs : snorm (m * k) = 0 := beq_iff_eq.mp hz
      have h0 : eqm 0 (m * k) := by
        have h := eqm_zero_mul_of_snorm (m * k) 1 hs
        simpa using h
      have h1 : eqm 0 ((m * k) * uE E a) := by
        have h := eqm_mul_r (uE E a) h0
        simpa using h
      have h2 : eqm 0 (m * (k * uE E a)) := by
        have h := eqm_mul_assoc m k (uE E a)
        exact eqm_trans h1 h
      refine eqm_trans ih ?_
      have h3 : eqm (m * tden E rest) (m * tden E rest + m * (k * uE E a)) := by
        have h := eqm_add (eqm_refl (m * tden E rest)) h2
        simpa using h
      refine eqm_trans h3 ?_
      exact eqm_of_eq (by rw [Int.mul_add]; omega)
    · rw [lscale_terms, ite_eq_right hz, tden_cons]
      refine eqm_trans (eqm_add (eqm_snorm_mul (m * k) (uE E a)) ih) ?_
      exact eqm_of_eq (by rw [tden_cons, Int.mul_add, Int.mul_assoc])

theorem lscale_sound (E : env) (m : Int) (x : lin) : eqm (lden E (lscale m x)) (m * lden E x) := by
  obtain ⟨c, ts⟩ := x
  simp only [lden, lscale]
  refine eqm_trans (eqm_add (eqm_snorm (m * c)) (lscale_terms_sound E m ts)) ?_
  exact eqm_of_eq (by rw [Int.mul_add])

theorem u_add64 (x y : word) : bv_unsigned (x + y) = (bv_unsigned x + bv_unsigned y) % 2 ^ 64 := by
  unfold bv_unsigned
  rw [BitVec.toNat_add]
  simp

theorem u_sub64 (x y : word) : bv_unsigned (x - y) = (bv_unsigned x - bv_unsigned y) % 2 ^ 64 := by
  unfold bv_unsigned
  rw [BitVec.toNat_sub, Int.natCast_emod]
  have hy : y.toNat ≤ 2 ^ 64 := by have := y.isLt; omega
  have hp : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := (Int.natCast_pow 2 64).symm
  rw [Int.natCast_add, Int.natCast_sub hy, hp]
  have hN : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  rw [hN]
  rw [show 18446744073709551616 - (y.toNat : Int) + (x.toNat : Int)
      = ((x.toNat : Int) - (y.toNat : Int)) + 1 * 18446744073709551616 from by omega]
  rw [Int.add_mul_emod_self_right]

theorem u_mul64 (x y : word) : bv_unsigned (x * y) = (bv_unsigned x * bv_unsigned y) % 2 ^ 64 := by
  unfold bv_unsigned
  rw [BitVec.toNat_mul]
  simp

theorem u_add_eqm (x y : word) :
    eqm (bv_unsigned (alu64 .ADD x y)) (bv_unsigned x + bv_unsigned y) := by
  show eqm (bv_unsigned (x + y)) _
  rw [u_add64]
  exact eqm_mod _

theorem u_sub_eqm (x y : word) :
    eqm (bv_unsigned (alu64 .SUB x y)) (bv_unsigned x - bv_unsigned y) := by
  show eqm (bv_unsigned (x - y)) _
  rw [u_sub64]
  exact eqm_mod _

theorem u_mul_eqm (x y : word) :
    eqm (bv_unsigned (mul_div .MUL x y)) (bv_unsigned x * bv_unsigned y) := by
  show eqm (bv_unsigned (x * y)) _
  rw [u_mul64]
  exact eqm_mod _

theorem lterm_sound (E : env) (t : Int × expr) : eqm (uE E (lterm t)) (t.1 * uE E t.2) := by
  obtain ⟨k, a⟩ := t
  by_cases hk : (k == 1) = true
  · rw [lterm, ite_eq_left hk]
    have hk1 : k = 1 := beq_iff_eq.mp hk
    subst hk1
    simpa [uE] using eqm_refl (uE E a)
  · rw [lterm, ite_eq_right hk]
    show eqm (bv_unsigned (mul_div .MUL (Z_to_bv 64 k) (edenot E a))) (k * uE E a)
    refine eqm_trans (u_mul_eqm (Z_to_bv 64 k) (edenot E a)) ?_
    exact eqm_mul_r (uE E a) (eqm_u_lit k)

theorem lterms_nil : lterms [] = .ELit 0 := rfl
theorem lterms_single (t : Int × expr) : lterms [t] = lterm t := rfl
theorem lterms_cons_cons (t t' : Int × expr) (r : List (Int × expr)) :
    lterms (t :: t' :: r) = .EAlu .ADD (lterm t) (lterms (t' :: r)) := rfl

theorem lterms_sound (E : env) (ts : List (Int × expr)) : eqm (uE E (lterms ts)) (tden E ts) := by
  induction ts with
  | nil =>
    rw [lterms_nil, tden_nil]
    exact eqm_of_eq (by simp [uE, edenot, Z_to_bv, BitVec.toNat_ofInt])
  | cons hd rest ih =>
    obtain ⟨k, a⟩ := hd
    cases rest with
    | nil =>
      rw [lterms_single, tden_cons, tden_nil]
      simpa using lterm_sound E (k, a)
    | cons hd' rest' =>
      obtain ⟨k', a'⟩ := hd'
      rw [lterms_cons_cons, tden_cons]
      refine eqm_trans (u_add_eqm (edenot E (lterm (k, a)))
        (edenot E (lterms ((k', a') :: rest')))) ?_
      exact eqm_add (lterm_sound E (k, a)) ih

theorem unlin_sound (E : env) (x : lin) : eqm (uE E (unlin x)) (lden E x) := by
  obtain ⟨c, ts⟩ := x
  cases ts with
  | nil =>
    simp only [unlin, lden, tden_nil]
    simpa [uE, edenot, Z_to_bv] using eqm_u_lit c
  | cons hd rest =>
    obtain ⟨k, a⟩ := hd
    by_cases hc : (c == 0) = true
    · rw [unlin, ite_eq_left hc]
      have hc0 : c = 0 := beq_iff_eq.mp hc
      subst hc0
      simp only [lden, tden_cons]
      refine eqm_trans (lterms_sound E ((k, a) :: rest)) ?_
      exact eqm_of_eq (by rw [Int.zero_add, tden_cons])
    · rw [unlin, ite_eq_right hc]
      simp only [lden, tden_cons]
      show eqm (bv_unsigned (alu64 .ADD (edenot E (lterms ((k, a) :: rest)))
        (edenot E (.ELit c)))) (c + (k * uE E a + tden E rest))
      refine eqm_trans (u_add_eqm _ _) ?_
      refine eqm_trans (eqm_add (lterms_sound E ((k, a) :: rest)) (eqm_u_lit c)) ?_
      exact eqm_of_eq (by rw [Int.add_comm, tden_cons])

theorem u_sll64 (x y : word) :
    bv_unsigned (alu64 .SLL x y)
      = (bv_unsigned x * 2 ^ (bv_unsigned y % 64).toNat) % 2 ^ 64 := by
  have hm : (y &&& BitVec.ofInt 64 63).toNat = y.toNat % 64 := by
    rw [BitVec.toNat_and]
    have h63 : (BitVec.ofInt 64 63).toNat = 63 := by decide
    rw [h63, show (63 : Nat) = 2 ^ 6 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_eq_mod y.toNat 6
  show bv_unsigned (x <<< (y &&& BitVec.ofInt 64 63).toNat) = _
  unfold bv_unsigned
  rw [hm, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.natCast_emod]
  have hp : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := (Int.natCast_pow 2 64).symm
  rw [hp, Int.natCast_mul, Int.natCast_pow]
  have hk : ((y.toNat : Int) % 64).toNat = y.toNat % 64 := by
    rw [Int.toNat_emod (by omega) (by decide), Int.toNat_natCast]
    rfl
  rw [hk]
  rfl

theorem u_sll_eqm (x : word) (s : Int) :
    eqm (bv_unsigned (alu64 .SLL x (Z_to_bv 64 s))) (zpow 2 (s % 64) * bv_unsigned x) := by
  rw [u_sll64]
  have hdvd : (64 : Int) ∣ ((2 ^ 64 : Nat) : Int) := ⟨((2 ^ 58 : Nat) : Int), by decide⟩
  have hy : bv_unsigned (Z_to_bv 64 s) % 64 = s % 64 := by
    rw [u_lit64a]
    exact Int.emod_emod_of_dvd s hdvd
  rw [hy]
  refine eqm_trans (eqm_mod _) ?_
  exact eqm_of_eq (Int.mul_comm (bv_unsigned x) ((2 : Int) ^ (s % 64).toNat))

theorem lin_of_triv (E : env) (e : expr) : eqm (lden E (0, [(1, e)])) (uE E e) := by
  simp only [lden, tden_cons, tden_nil, Int.zero_add, Int.one_mul, Int.add_zero]
  exact eqm_refl _

/-- `lin_of` at the second `MUL` shape (a not a literal). -/
theorem lin_of_mul_lit_r (a : expr) (k : Int) (h : ∀ j, a ≠ .ELit j) :
    lin_of (.EMd .MUL a (.ELit k)) = lscale k (lin_of a) := by
  cases a with
  | ELit j => exact absurd rfl (h j)
  | EVar n => rfl
  | EAlu o x y => rfl
  | EAluw o x y => rfl
  | EMd o x y => rfl
  | EMdw o x y => rfl
  | EExt sx l n e => rfl
  | EBlob sx kk i n => rfl

/-- `lin_of` at an unspecialised `MUL`. -/
theorem lin_of_mul_default (a b : expr) (ha : ∀ j, a ≠ .ELit j) (hb : ∀ j, b ≠ .ELit j) :
    lin_of (.EMd .MUL a b) = (0, [(1, .EMd .MUL a b)]) := by
  cases a with
  | ELit j => exact absurd rfl (ha j)
  | _ =>
    cases b with
    | ELit j => exact absurd rfl (hb j)
    | _ => rfl

/-- `lin_of` at a shift by a non-literal. -/
theorem lin_of_sll_default (a b : expr) (hb : ∀ s, b ≠ .ELit s) :
    lin_of (.EAlu .SLL a b) = (0, [(1, .EAlu .SLL a b)]) := by
  cases b with
  | ELit j => exact absurd rfl (hb j)
  | _ => rfl

theorem lin_of_sound (E : env) (e : expr) : eqm (lden E (lin_of e)) (uE E e) := by
  induction e with
  | ELit z =>
    show eqm (lden E (snorm z, [])) (bv_unsigned (Z_to_bv 64 z))
    simp only [lden, tden_nil, Int.add_zero, u_lit64a]
    refine eqm_trans (eqm_snorm z) ?_
    exact eqm_sym (eqm_mod z)
  | EVar n => exact lin_of_triv E _
  | EAlu op a b iha ihb =>
    cases op with
    | ADD =>
      show eqm (lden E (ladd (lin_of a) (lin_of b)))
        (bv_unsigned (alu64 .ADD (edenot E a) (edenot E b)))
      refine eqm_trans (ladd_sound E (lin_of a) (lin_of b)) ?_
      refine eqm_trans (eqm_add iha ihb) ?_
      exact eqm_sym (u_add_eqm (edenot E a) (edenot E b))
    | SUB =>
      show eqm (lden E (ladd (lin_of a) (lscale (-1) (lin_of b))))
        (bv_unsigned (alu64 .SUB (edenot E a) (edenot E b)))
      have hb : eqm (lden E (lscale (-1) (lin_of b))) (-1 * uE E b) :=
        eqm_trans (lscale_sound E (-1) (lin_of b)) (eqm_mul_l (-1) ihb)
      refine eqm_trans (ladd_sound E (lin_of a) (lscale (-1) (lin_of b))) ?_
      refine eqm_trans (eqm_add iha hb) ?_
      have hstep : eqm (uE E a + -1 * uE E b) (uE E a - uE E b) := by
        refine ⟨0, ?_⟩
        rw [Int.neg_one_mul, Int.sub_eq_add_neg]
        simp
      exact eqm_trans hstep (eqm_sym (u_sub_eqm (edenot E a) (edenot E b)))
    | SLL =>
      by_cases hb : ∃ s, b = .ELit s
      · obtain ⟨s, rfl⟩ := hb
        show eqm (lden E (lscale (zpow 2 (s % 64)) (lin_of a)))
          (bv_unsigned (alu64 .SLL (edenot E a) (Z_to_bv 64 s)))
        refine eqm_trans (lscale_sound E (zpow 2 (s % 64)) (lin_of a)) ?_
        refine eqm_trans (eqm_mul_l (zpow 2 (s % 64)) iha) ?_
        exact eqm_sym (u_sll_eqm (edenot E a) s)
      · have hb' : ∀ s, b ≠ .ELit s := fun s hs => hb ⟨s, hs⟩
        rw [lin_of_sll_default a b hb']
        exact lin_of_triv E _
    | SLT => exact lin_of_triv E _
    | SLTU => exact lin_of_triv E _
    | XOR => exact lin_of_triv E _
    | SRL => exact lin_of_triv E _
    | SRA => exact lin_of_triv E _
    | OR => exact lin_of_triv E _
    | AND => exact lin_of_triv E _
  | EAluw op a b iha ihb => exact lin_of_triv E _
  | EMd op a b iha ihb =>
    cases op with
    | MUL =>
      by_cases ha : ∃ j, a = .ELit j
      · obtain ⟨k, rfl⟩ := ha
        show eqm (lden E (lscale k (lin_of b)))
          (bv_unsigned (mul_div .MUL (Z_to_bv 64 k) (edenot E b)))
        refine eqm_trans (lscale_sound E k (lin_of b)) ?_
        refine eqm_trans (eqm_mul_l k ihb) ?_
        refine eqm_trans (eqm_sym (eqm_mul_r (uE E b) (eqm_u_lit k))) ?_
        exact eqm_sym (u_mul_eqm (Z_to_bv 64 k) (edenot E b))
      · have ha' : ∀ j, a ≠ .ELit j := fun j hj => ha ⟨j, hj⟩
        by_cases hb : ∃ j, b = .ELit j
        · obtain ⟨k, rfl⟩ := hb
          rw [lin_of_mul_lit_r a k ha']
          show eqm (lden E (lscale k (lin_of a)))
            (bv_unsigned (mul_div .MUL (edenot E a) (Z_to_bv 64 k)))
          refine eqm_trans (lscale_sound E k (lin_of a)) ?_
          refine eqm_trans (eqm_mul_l k iha) ?_
          have hstep : eqm (k * uE E a) (uE E a * bv_unsigned (Z_to_bv 64 k)) := by
            refine eqm_trans (eqm_of_eq (Int.mul_comm k (uE E a))) ?_
            exact eqm_sym (eqm_mul_l (uE E a) (eqm_u_lit k))
          refine eqm_trans hstep ?_
          exact eqm_sym (u_mul_eqm (edenot E a) (Z_to_bv 64 k))
        · have hb' : ∀ j, b ≠ .ELit j := fun j hj => hb ⟨j, hj⟩
          rw [lin_of_mul_default a b ha' hb']
          exact lin_of_triv E _
    | MULH => exact lin_of_triv E _
    | MULHSU => exact lin_of_triv E _
    | MULHU => exact lin_of_triv E _
    | DIV => exact lin_of_triv E _
    | DIVU => exact lin_of_triv E _
    | REM => exact lin_of_triv E _
    | REMU => exact lin_of_triv E _
  | EMdw op a b iha ihb => exact lin_of_triv E _
  | EExt sx lo n a iha => exact lin_of_triv E _
  | EBlob sx k i n => exact lin_of_triv E _

theorem ofInt_toNat (w : word) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

theorem unlin_ladd (E : env) (a b : expr) :
    edenot E (unlin (ladd (lin_of a) (lin_of b))) = alu64 .ADD (edenot E a) (edenot E b) := by
  rw [← ofInt_toNat (edenot E (unlin (ladd (lin_of a) (lin_of b)))),
    ← ofInt_toNat (alu64 .ADD (edenot E a) (edenot E b))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E _) ?_
  refine eqm_trans (ladd_sound E _ _) ?_
  refine eqm_trans (eqm_add (lin_of_sound E a) (lin_of_sound E b)) ?_
  exact eqm_sym (u_add_eqm (edenot E a) (edenot E b))

theorem unlin_lsub (E : env) (a b : expr) :
    edenot E (unlin (ladd (lin_of a) (lscale (-1) (lin_of b))))
      = alu64 .SUB (edenot E a) (edenot E b) := by
  rw [← ofInt_toNat (edenot E (unlin (ladd (lin_of a) (lscale (-1) (lin_of b))))),
    ← ofInt_toNat (alu64 .SUB (edenot E a) (edenot E b))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E _) ?_
  refine eqm_trans (ladd_sound E _ _) ?_
  have hb : eqm (lden E (lscale (-1) (lin_of b))) (-1 * uE E b) :=
    eqm_trans (lscale_sound E (-1) (lin_of b)) (eqm_mul_l (-1) (lin_of_sound E b))
  refine eqm_trans (eqm_add (lin_of_sound E a) hb) ?_
  show eqm (uE E a + -1 * uE E b) (bv_unsigned (alu64 .SUB (edenot E a) (edenot E b)))
  have hstep : eqm (uE E a + -1 * uE E b) (uE E a - uE E b) := by
    refine ⟨0, ?_⟩
    rw [Int.neg_one_mul, Int.sub_eq_add_neg]
    simp
  exact eqm_trans hstep (eqm_sym (u_sub_eqm (edenot E a) (edenot E b)))

theorem unlin_lsll (E : env) (a : expr) (s : Int) :
    edenot E (unlin (lscale (zpow 2 (s % 64)) (lin_of a)))
      = alu64 .SLL (edenot E a) (Z_to_bv 64 s) := by
  rw [← ofInt_toNat (edenot E (unlin (lscale (zpow 2 (s % 64)) (lin_of a)))),
    ← ofInt_toNat (alu64 .SLL (edenot E a) (Z_to_bv 64 s))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E _) ?_
  refine eqm_trans (lscale_sound E (zpow 2 (s % 64)) (lin_of a)) ?_
  refine eqm_trans (eqm_mul_l (zpow 2 (s % 64)) (lin_of_sound E a)) ?_
  exact eqm_sym (u_sll_eqm (edenot E a) s)

theorem unlin_lmul_l (E : env) (x : Int) (b : expr) :
    edenot E (unlin (lscale x (lin_of b))) = mul_div .MUL (Z_to_bv 64 x) (edenot E b) := by
  rw [← ofInt_toNat (edenot E (unlin (lscale x (lin_of b)))),
    ← ofInt_toNat (mul_div .MUL (Z_to_bv 64 x) (edenot E b))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E _) ?_
  refine eqm_trans (lscale_sound E x (lin_of b)) ?_
  refine eqm_trans (eqm_mul_l x (lin_of_sound E b)) ?_
  refine eqm_trans (eqm_mul_r (uE E b) (eqm_sym (eqm_mod x))) ?_
  rw [← u_lit64a]
  exact eqm_sym (u_mul_eqm (Z_to_bv 64 x) (edenot E b))

theorem unlin_lmul_r (E : env) (a : expr) (y : Int) :
    edenot E (unlin (lscale y (lin_of a))) = mul_div .MUL (edenot E a) (Z_to_bv 64 y) := by
  rw [← ofInt_toNat (edenot E (unlin (lscale y (lin_of a)))),
    ← ofInt_toNat (mul_div .MUL (edenot E a) (Z_to_bv 64 y))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E _) ?_
  refine eqm_trans (lscale_sound E y (lin_of a)) ?_
  refine eqm_trans (eqm_mul_l y (lin_of_sound E a)) ?_
  refine eqm_trans (eqm_of_eq (Int.mul_comm y (uE E a))) ?_
  refine eqm_trans (eqm_mul_l (uE E a) (eqm_sym (eqm_mod y))) ?_
  rw [← u_lit64a]
  exact eqm_sym (u_mul_eqm (edenot E a) (Z_to_bv 64 y))


/-! -/

theorem ridx_eq_toNat (r : reg) : ridx r = r.toNat := by
  unfold ridx bv_unsigned
  omega

theorem ridx_inj {r r' : reg} (H : ridx r = ridx r') : r = r' := by
  apply BitVec.eq_of_toNat_eq
  rw [ridx_eq_toNat, ridx_eq_toNat] at H
  exact H

theorem nth_sr_upd (n : Nat) (sr : List expr) (e : expr) (i : Nat) :
    (sr_upd sr n e).getD i (.ELit 0) = if i = n then e else sr.getD i (.ELit 0) := by
  induction n generalizing sr i with
  | zero =>
    cases sr with
    | nil => cases i <;> simp [sr_upd]
    | cons h t => cases i <;> simp [sr_upd]
  | succ n ih =>
    cases sr with
    | nil =>
      cases i with
      | zero => simp [sr_upd]
      | succ i => simp only [sr_upd, List.getD_cons_succ, Nat.succ.injEq, ih, List.getD_nil,
          ite_true]
    | cons h t =>
      cases i with
      | zero => simp [sr_upd]
      | succ i => simp only [sr_upd, List.getD_cons_succ, Nat.succ.injEq, ih]

/-- Writing register `rd` keeps the register file describing the machine. -/
theorem regs_ok_upd (E : env) (sr : List expr) (regs : BvMap word) (rd : reg)
    (v : word) (e : expr) (Hr : regs_ok E sr regs) (Hv : edenot E e = v) :
    regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
      (if bv_eqb rd 0 then regs else regupd regs rd v) := by
  by_cases hrd : bv_eqb rd 0 = true
  · rw [ite_eq_left hrd, ite_eq_left hrd]; exact Hr
  · rw [ite_eq_right hrd, ite_eq_right hrd]
    have Hne : rd ≠ 0 := by
      intro h; subst h; exact hrd (bv_eqb_refl 0)
    intro r
    by_cases hr0 : bv_eqb r 0 = true
    · have h0 : r = 0 := beq_iff_eq.mp hr0
      subst h0
      show getr (regupd regs rd v) 0 = edenot E (.ELit 0)
      rw [show getr (regupd regs rd v) 0 = 0 from by simp [getr, bv_eqb_refl]]
      show (0 : word) = BitVec.ofInt 64 0
      decide
    · have Hrr : getr regs r = edenot E (sr.getD (ridx r) (.ELit 0)) := by
        have h := Hr r
        unfold sr_get at h
        rw [ite_eq_right hr0] at h
        exact h
      unfold sr_get
      rw [ite_eq_right hr0, nth_sr_upd]
      by_cases hi : ridx r = ridx rd
      · rw [ite_eq_left hi]
        have hrr : r = rd := ridx_inj hi
        subst hrr
        rw [getr_same _ _ _ Hne]
        exact Hv.symm
      · rw [ite_eq_right hi]
        have hrr : r ≠ rd := by intro h; subst h; exact hi rfl
        rw [getr_other _ _ _ _ hrr]
        exact Hrr

/-- Pin one register to a symbolic expression, given that the concrete
    file already agrees. -/
theorem regs_ok_pin (E : env) (sr : List expr) (regs : BvMap word) (r : reg) (e : expr)
    (Hr : regs_ok E sr regs) (Hv : getr regs r = edenot E e) :
    regs_ok E (sr_upd sr (ridx r) e) regs := by
  intro r'
  by_cases hr0 : bv_eqb r' 0 = true
  · have h0 : r' = 0 := beq_iff_eq.mp hr0
    subst h0
    show getr regs 0 = edenot E (sr_get (sr_upd sr (ridx r) e) 0)
    rw [show getr regs 0 = 0 from by simp [getr, bv_eqb_refl]]
    unfold sr_get
    rw [ite_eq_left (bv_eqb_refl (0 : reg))]
    show (0 : word) = BitVec.ofInt 64 0
    decide
  · have Hrr : getr regs r' = edenot E (sr.getD (ridx r') (.ELit 0)) := by
      have h := Hr r'
      unfold sr_get at h
      rw [ite_eq_right hr0] at h
      exact h
    unfold sr_get
    rw [ite_eq_right hr0, nth_sr_upd]
    by_cases hi : ridx r' = ridx r
    · rw [ite_eq_left hi]
      have hrr : r' = r := ridx_inj hi
      subst hrr
      exact Hv
    · rw [ite_eq_right hi]
      exact Hrr

theorem ridx_range (r : reg) : ridx r < 32 := by
  unfold ridx bv_unsigned
  have := u5_range r
  omega

theorem ridx_roundtrip (r : reg) : Z_to_bv 5 (ridx r : Int) = r := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 5 (ridx r : Int)).toNat = r.toNat
  rw [BitVec.toNat_ofInt, ridx_eq_toNat]
  have h := u5_range r
  have h2 : (r.toNat : Int) % ((2 ^ 5 : Nat) : Int) = (r.toNat : Int) := by omega
  rw [h2, Int.toNat_natCast]

/-- The explicit 32-entry `sr_id` is the range map, so `getD` is available
    on it. -/
theorem sr_id_eq_range : sr_id = (List.range 32).map (fun n => .EVar n) := by decide

theorem sr_id_getD (n : Nat) (hn : n < 32) : sr_id.getD n (.ELit 0) = .EVar n := by
  rw [sr_id_eq_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using hn)]
  simp only [List.getElem_map, List.getElem_range]
  rfl

/-- The identity valuation on registers: `EVar n` for `n < 32` is `x_n`. -/
theorem regs_ok_id (regs : BvMap word) (rest : Nat → word) (ebs : Nat → List byte) :
    regs_ok ⟨reg_ev regs rest, ebs⟩ sr_id regs := by
  intro r
  by_cases hr0 : bv_eqb r 0 = true
  · have h0 : r = 0 := beq_iff_eq.mp hr0
    subst h0
    show getr regs 0 = edenot ⟨reg_ev regs rest, ebs⟩ (sr_get sr_id 0)
    rw [show getr regs 0 = 0 from by simp [getr, bv_eqb_refl]]
    unfold sr_get
    rw [ite_eq_left (bv_eqb_refl (0 : reg))]
    show (0 : word) = BitVec.ofInt 64 0
    decide
  · have hget : sr_id.getD (ridx r) (.ELit 0) = .EVar (ridx r) :=
      sr_id_getD (ridx r) (ridx_range r)
    unfold sr_get
    rw [ite_eq_right hr0, hget]
    show getr regs r = reg_ev regs rest (ridx r)
    unfold reg_ev
    rw [ite_eq_left (ridx_range r)]
    rw [show BitVec.ofInt 5 (ridx r : Int) = r from ridx_roundtrip r]

/-! ### Memory denotation: growth and one-`cons` shapes -/

theorem mem_denot_grows (E : env) (base : word → Option byte) (log : List sentry) :
    mem_grows base (mem_denot E base log) := by
  induction log with
  | nil => exact mem_grows_refl base
  | cons hd rest ih =>
    obtain ⟨a, w, v⟩ := hd
    exact mem_grows_trans ih
      (wbytes_grows (word_to_le_bytes w (edenot E v)) (mem_denot E base rest) (adenot E a))

theorem mem_denot_cons (E : env) (base : word → Option byte) (a : saddr) (w : Nat)
    (v : expr) (rest : List sentry) :
    mem_denot E base (SE a w v :: rest)
      = wbytes (mem_denot E base rest) (adenot E a)
          (word_to_le_bytes w (edenot E v)) := rfl

/-- A literal in range reads back as itself. -/
theorem u_small {z : Int} (Hz : 0 ≤ z ∧ z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z := by
  rw [u_lit64a]
  exact Int.emod_eq_of_lt Hz.1 Hz.2

/-- A flat address denotes exactly its Z-address. -/
theorem flat_u (E : env) (a : saddr) (n : Int) (H : flat E a n) :
    bv_unsigned (adenot E a) = estart E a := by
  obtain ⟨H1, H2, _, _⟩ := H
  show bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E a.a_base) + a.a_off)) = estart E a
  exact u_small ⟨H1, H2⟩

/-- Flatness is monotone in the length. -/
theorem flat_mono (E : env) (a : saddr) (n m : Int) (H : flat E a n) (Hm : 0 ≤ m ∧ m ≤ n) :
    flat E a m := by
  obtain ⟨H1, H2, H3, H4⟩ := H
  obtain ⟨Hm1, Hm2⟩ := Hm
  exact ⟨H1, H2, Hm1, by omega⟩

theorem log_flat_cons (E : env) (a : saddr) (w : Nat) (v : expr) (rest : List sentry) :
    log_flat E (SE a w v :: rest) = (w ≤ 8 ∧ flat E a (w : Int) ∧ log_flat E rest) := rfl

theorem scs_denot_cons (segs : List Segment) (base : word → Option byte) (E : env)
    (s : sidecond) (l : List sidecond) :
    scs_denot segs base E (s :: l) ↔ sc_denot segs base E s ∧ scs_denot segs base E l := by
  unfold scs_denot
  constructor
  · intro H
    exact ⟨H s (List.mem_cons_self ..), fun x hx => H x (List.mem_cons_of_mem _ hx)⟩
  · intro ⟨A, B⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact A
    · exact B x hx

theorem scs_denot_app (segs : List Segment) (base : word → Option byte) (E : env)
    (l1 l2 : List sidecond) :
    scs_denot segs base E (l1 ++ l2) ↔
      scs_denot segs base E l1 ∧ scs_denot segs base E l2 := by
  unfold scs_denot
  constructor
  · intro H
    exact ⟨fun x hx => H x (List.mem_append_left _ hx),
           fun x hx => H x (List.mem_append_right _ hx)⟩
  · intro ⟨A, B⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact A x hx
    · exact B x hx

/-- Subtracting from a remainder: the outer `%` is idempotent. -/
theorem emod_sub_emod_right (a b M : Int) : (a % M - b) % M = (a - b) % M := by
  have h : a % M = a - M * (a / M) := Int.emod_def a M
  rw [h, show a - M * (a / M) - b = (a - b) - (a / M) * M from by rw [Int.mul_comm]; omega]
  rw [Int.sub_mul_emod_self_right]

/-- `bv_wrap` cannot see the signed wrap. -/
theorem wrap_swrap (n : Nat) (z : Int) : bv_wrap n (bv_swrap n z) = bv_wrap n z := by
  unfold bv_wrap bv_swrap
  rw [emod_sub_emod_right]
  congr 1
  omega

/-- The low 32 bits of a sign extension are the value again. -/
theorem low32_sext64_32 (v : BitVec 32) : low32 (sext 64 v) = v := by
  apply BitVec.eq_of_toNat_eq
  unfold low32 sext bits
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth_of_le (by decide)]
  by_cases hm : v.msb = true
  · rw [ite_eq_left hm]
    have hsplit : 2 ^ 64 - 2 ^ 32 = 2 ^ 32 * (2 ^ 32 - 1) := by decide
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
  · rw [ite_eq_right hm, Nat.add_zero, Nat.mod_eq_of_lt v.isLt]

/-- Adding a `Nat` to a word. -/
theorem w_add_nat (a : word) (n : Nat) :
    a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + (n : Int)) := by
  have hsum : bv_unsigned a + (n : Int) = ((a.toNat + n : Nat) : Int) := by
    show ((a.toNat : Int)) + (n : Int) = ((a.toNat + n : Nat) : Int)
    push_cast
    rfl
  rw [hsum]
  show a + BitVec.ofNat 64 n = BitVec.ofNat 64 (a.toNat + n)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_mod]

/-- Adding one. -/
theorem w_add_1 (a : word) : a + 1 = Z_to_bv 64 (bv_unsigned a + 1) := by
  have h := w_add_nat a 1
  simpa [nat_to_word] using h

/-! ### Small arithmetic -/

/-- A literal in range reads back as itself, spelled as the small-arithmetic
    section does. -/
theorem u_small' (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z :=
  u_small Hz

theorem v_addi_0 (x : word) : v_addi x 0 = x := by
  show BitVec.ofInt 64 ((x.toNat : Int) + 0) = x
  bv_omega

/-! ### `Section StepSound`: the two state relations -/

theorem st_ok_R (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (H : st_ok segs E base rom ss ms) :
    st_okR segs E base rom (clr ss) ms := by
  obtain ⟨regs, hms, HR, HL, HK⟩ := H
  subst hms
  refine ⟨regs, ?_, HR, HL, HK⟩
  show mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
      = mkstR regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E (clr ss).s_resv)
  show mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
      = mkstR regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E none)
  simp only [resv_denot, mkstR_None]

theorem st_okR_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (H : st_okR segs E base rom ss ms)
    (Hr : ss.s_resv = none) : st_ok segs E base rom ss ms := by
  obtain ⟨regs, hms, HR, HL, HK⟩ := H
  refine ⟨regs, ?_, HR, HL, HK⟩
  rw [hms, Hr]
  show mkstR regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom none = _
  rw [mkstR_None]

theorem s_clean_None (ss : sym_state) : s_clean ss = true ↔ ss.s_resv = none := by
  unfold s_clean
  cases ss.s_resv <;> simp

theorem s_resv_clr (ss : sym_state) : (clr ss).s_resv = none := rfl

theorem msize_bytes_range (sz : MSize) :
    1 ≤ AxSymExec3.msize_bytes sz ∧ AxSymExec3.msize_bytes sz ≤ 8 := by
  cases sz <;> decide

theorem msize_bytes_R (sz : MSize) : SymStepR.msize_bytes sz = AxSymExec3.msize_bytes sz := by
  cases sz <;> rfl

theorem amo_msize_sz (wd : AWidth) : SymStepR.amo_msize wd = AxSymExec3.amo_sz wd := by
  cases wd <;> rfl

theorem amo_nbytes_sz (wd : AWidth) : SymStepR.amo_nbytes wd = AxSymExec3.msize_bytes (amo_sz wd) := by
  cases wd <;> rfl

theorem st_okR_parts (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (H : st_okR segs E base rom ss ms) :
    regs_ok E ss.s_regs ms.ms_regs ∧ ms.ms_mem = mem_denot E base ss.s_log ∧
      log_flat E ss.s_log ∧ know_ok segs E base ss.s_know ∧
      ms = mkstR ms.ms_regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
        (resv_denot E ss.s_resv) := by
  obtain ⟨regs, hms, HR, HL, HK⟩ := H
  subst hms
  exact ⟨HR, rfl, HL, HK, rfl⟩

/-! ### `Section XSound`: extension mode -/

theorem eagree_refl (b : Nat) (E : env) : eagree b E E :=
  ⟨fun _ _ => rfl, rfl⟩

theorem eagree_sym {b : Nat} {E E' : env} (H : eagree b E E') : eagree b E' E :=
  ⟨fun n hn => (H.1 n hn).symm, H.2.symm⟩

theorem eagree_trans {b : Nat} {E1 E2 E3 : env}
    (H1 : eagree b E1 E2) (H2 : eagree b E2 E3) : eagree b E1 E3 :=
  ⟨fun n hn => by rw [H1.1 n hn, H2.1 n hn], by rw [H1.2, H2.2]⟩

theorem eagree_le {b b' : Nat} {E E' : env} (H : eagree b' E E') (Hle : b ≤ b') :
    eagree b E E' :=
  ⟨fun n hn => H.1 n (by omega), H.2⟩

theorem eagree_upd (E : env) (i : Nat) (v : word) : eagree i E (eupd E i v) := by
  refine ⟨fun n hn => ?_, rfl⟩
  have h : (n == i) = false := by
    rw [Bool.eq_false_iff]
    intro h; rw [beq_iff_eq] at h; omega
  show E.ev n = (if n == i then v else E.ev n)
  rw [h]
  rfl

theorem eupd_at (E : env) (i : Nat) (v : word) : (eupd E i v).ev i = v := by
  show (if i == i then v else E.ev i) = v
  rw [ite_eq_left (beq_iff_eq.mpr rfl)]

theorem edenot_evars_lt {b : Nat} {E E' : env} {e : expr}
    (H : eagree b E E') (He : evars_lt b e = true) : edenot E e = edenot E' e := by
  induction e with
  | ELit z => rfl
  | EVar n =>
    simp only [evars_lt] at He
    exact H.1 n (by simpa using He)
  | EAlu o a c iha ihc =>
    simp only [evars_lt, Bool.and_eq_true] at He
    simp only [edenot, iha He.1, ihc He.2]
  | EAluw o a c iha ihc =>
    simp only [evars_lt, Bool.and_eq_true] at He
    simp only [edenot, iha He.1, ihc He.2]
  | EMd o a c iha ihc =>
    simp only [evars_lt, Bool.and_eq_true] at He
    simp only [edenot, iha He.1, ihc He.2]
  | EMdw o a c iha ihc =>
    simp only [evars_lt, Bool.and_eq_true] at He
    simp only [edenot, iha He.1, ihc He.2]
  | EExt sx lo n a iha =>
    simp only [evars_lt] at He
    simp only [edenot, iha He]
  | EBlob sx k i n =>
    simp only [edenot, H.2]

theorem st_okX_R (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (H : st_okX segs E base rom ss ms) :
    st_okR segs E base rom ss ms :=
  H E (eagree_refl _ _)

theorem st_okX_agree (segs : List Segment) (E E' : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (H : st_okX segs E base rom ss ms)
    (Ha : eagree ss.s_next E E') : st_okX segs E' base rom ss ms :=
  fun E'' Ha'' => H E'' (eagree_trans Ha Ha'')

theorem st_okX_clr (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state)
    (H : ∀ E', eagree ss.s_next E E' → st_ok segs E' base rom ss ms) :
    st_okX segs E base rom (clr ss) ms :=
  fun E' Ha => st_ok_R segs E' base rom ss ms (H E' Ha)

/-! ### `Section CarrySound`: generic `Forall` helpers and the `zf` frame -/

/-- Two `Forall`s compose over an append (this tree states the `Forall`s as
    membership predicates, `List.Forall` not being part of core Lean). -/
theorem Forall_app_intro {A : Type} (P : A → Prop) (l1 l2 : List A)
    (H1 : ∀ x ∈ l1, P x) (H2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact H1 x hx
  · exact H2 x hx

/-- A singleton `Forall`. -/
theorem Forall_one {A : Type} (P : A → Prop) (x : A) (H : P x) : ∀ y ∈ [x], P y := by
  intro y hy
  rcases List.mem_singleton.mp hy with rfl
  exact H

theorem zf_kind_zero (segs : List Segment) :
    zf_kind segs .KZero (fun x => x = some (BitVec.ofInt 8 0)) := by
  intro E M a n
  rfl

theorem zf_kind_fill (segs : List Segment) (c : Int) :
    zf_kind segs (fun a n => .KFill a n c) (fun x => x = some (BitVec.ofInt 8 c)) := by
  intro E M a n
  rfl

theorem zf_kind_unk (segs : List Segment) :
    zf_kind segs .KUnk (fun x => x ≠ none) := by
  intro E M a n
  rfl

theorem br_lookup_ok (allkn : List kentry) (c : List (expr × Option (Int × Int)))
    (b : expr) (r : Option (Int × Int)) (Hc : br_cache_ok allkn c)
    (Hl : br_lookup c b = some r) : r = base_range allkn b := by
  induction c with
  | nil => simp [br_lookup] at Hl
  | cons hd rest ih =>
    obtain ⟨b', r'⟩ := hd
    have H1 : r' = base_range allkn b' := Hc _ (List.mem_cons_self ..)
    have Hc' : br_cache_ok allkn rest := fun p hp => Hc p (List.mem_cons_of_mem _ hp)
    simp only [br_lookup] at Hl
    by_cases h : expr_eqb b b' = true
    · rw [ite_eq_left h] at Hl
      rw [Option.some.injEq] at Hl
      rw [← Hl, H1, expr_eqb_eq _ _ h]
    · rw [ite_eq_right h] at Hl
      exact ih Hc' Hl

theorem know_ok_words_le8 (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (H : know_ok segs E M kn) : kn_words_le8 kn := by
  induction kn with
  | nil => trivial
  | cons K r ih =>
    have HK : kentry_ok segs E M K := H K (List.mem_cons_self ..)
    have Hr : know_ok segs E M r := fun p hp => H p (List.mem_cons_of_mem _ hp)
    have := ih Hr
    cases K with
    | KWord a w v =>
      simp only [kentry_ok] at HK
      exact ⟨HK.1, this⟩
    | _ => simpa [kn_words_le8] using this

/-! ### `is_lit`, small address arithmetic, side-condition membership -/

theorem is_lit_some {e : expr} {z : Int} (H : is_lit e = some z) : e = .ELit z := by
  cases e <;> simp_all [is_lit]

theorem elenZ_elen (E : env) (n : Nat) (hn : n ≤ 8) : elenZ E (elen n) = (n : Int) := by
  show bv_unsigned (edenot E (.ELit (n : Int))) = (n : Int)
  show bv_unsigned (Z_to_bv 64 (n : Int)) = (n : Int)
  exact u_small ⟨by omega, by omega⟩

theorem sidecond_eqb_eq : ∀ x y : sidecond, sidecond_eqb x y = true → x = y := by
  intro x y H
  cases x with
  | SCFlat a n =>
    cases y with
    | SCFlat a' n' =>
      simp only [sidecond_eqb, Bool.and_eq_true] at H
      rw [saddr_eqb_eq H.1, expr_eqb_eq _ _ H.2]
    | _ => simp [sidecond_eqb] at H
  | SCStoreOk a n =>
    cases y with
    | SCStoreOk a' n' =>
      simp only [sidecond_eqb, Bool.and_eq_true, beq_iff_eq] at H
      rw [saddr_eqb_eq H.1, H.2]
    | _ => simp [sidecond_eqb] at H
  | SCDisj a1 n1 a2 n2 =>
    cases y with
    | SCDisj a1' n1' a2' n2' =>
      simp only [sidecond_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
      rw [saddr_eqb_eq h1, expr_eqb_eq _ _ h2, saddr_eqb_eq h3, expr_eqb_eq _ _ h4]
    | _ => simp [sidecond_eqb] at H
  | SCInside a1 n1 a2 n2 =>
    cases y with
    | SCInside a1' n1' a2' n2' =>
      simp only [sidecond_eqb, Bool.and_eq_true] at H
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := H
      rw [saddr_eqb_eq h1, expr_eqb_eq _ _ h2, saddr_eqb_eq h3, expr_eqb_eq _ _ h4]
    | _ => simp [sidecond_eqb] at H
  | SCBr t c a b => cases y <;> simp [sidecond_eqb] at H
  | SCReadBase a n sx e => cases y <;> simp [sidecond_eqb] at H
  | SCEq a b => cases y <;> simp [sidecond_eqb] at H

theorem sc_mem_In (x : sidecond) (l : List sidecond) (H : sc_mem x l = true) :
    x ∈ l := by
  induction l with
  | nil => simp [sc_mem] at H
  | cons y t ih =>
    simp only [sc_mem, Bool.or_eq_true] at H
    rcases H with H | H
    · exact List.mem_cons.mpr (Or.inl (sidecond_eqb_eq _ _ H))
    · exact List.mem_cons.mpr (Or.inr (ih H))

theorem sc_add_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (news acc : List sidecond) (H : scs_denot segs base E (sc_add news acc)) :
    scs_denot segs base E news ∧ scs_denot segs base E acc := by
  induction news generalizing acc with
  | nil =>
    exact ⟨fun x hx => absurd hx (by simp), by simpa [sc_add] using H⟩
  | cons x t ih =>
    simp only [sc_add] at H
    by_cases hm : sc_mem x acc = true
    · rw [ite_eq_left hm] at H
      obtain ⟨Ht, Hacc⟩ := ih acc H
      refine ⟨?_, Hacc⟩
      intro y hy
      rcases List.mem_cons.mp hy with h | hy
      · rw [h]; exact Hacc x (sc_mem_In x acc hm)
      · exact Ht y hy
    · rw [ite_eq_right hm] at H
      obtain ⟨Ht, Hxa⟩ := ih (x :: acc) H
      obtain ⟨Hx, Hacc⟩ := (scs_denot_cons segs base E x acc).mp Hxa
      refine ⟨?_, Hacc⟩
      intro y hy
      rcases List.mem_cons.mp hy with h | hy
      · rw [h]; exact Hx
      · exact Ht y hy

/-! ### The ISA ops as `Int` congruences -/

/-! ### Node-side `KUnk` introduction

    A `KZero` / `KFill` / `KBlob` entry says what the bytes ARE, so it also
    says they are DEFINED: each layer can widen to `KUnk` when a later
    pass only needs readability. -/

/-- Pointwise form: every byte of the range is defined in `M`.
 -/
theorem know_ok_unk_intro_pt (segs : List Segment) (E : env) (M : word → Option byte)
    (a : saddr) (n : expr) (Hfl : flat E a (elenZ E n))
    (H : ∀ i, 0 ≤ i → i < elenZ E n →
      M (BitVec.ofInt 64 (estart E a + i)) ≠ none) :
    kentry_ok segs E M (.KUnk a n) :=
  ⟨Hfl, H⟩

theorem kunk_of_zero (segs : List Segment) (E : env) (M : word → Option byte)
    (a : saddr) (n : expr) (H : kentry_ok segs E M (.KZero a n)) :
    kentry_ok segs E M (.KUnk a n) := by
  obtain ⟨hf, hb⟩ := H
  refine ⟨hf, fun i h0 hi => ?_⟩
  rw [hb i h0 hi]
  simp

theorem kunk_of_fill (segs : List Segment) (E : env) (M : word → Option byte)
    (a : saddr) (n : expr) (c : Int) (H : kentry_ok segs E M (.KFill a n c)) :
    kentry_ok segs E M (.KUnk a n) := by
  obtain ⟨hf, hb⟩ := H
  refine ⟨hf, fun i h0 hi => ?_⟩
  rw [hb i h0 hi]
  simp

theorem kunk_of_blob (segs : List Segment) (E : env) (M : word → Option byte)
    (a : saddr) (n : expr) (k : Nat) (H : kentry_ok segs E M (.KBlob a n k)) :
    kentry_ok segs E M (.KUnk a n) := by
  obtain ⟨hf, _, hb⟩ := H
  refine ⟨hf, fun i h0 hi => ?_⟩
  rw [hb i h0 hi]
  simp

/-! ### Shifts, masks, and `Nat`/`Int` casts  -/



theorem pow2_div_64 (k : Int) (Hk : 0 ≤ k ∧ k ≤ 64) : zpow 2 k ∣ (2 : Int) ^ 64 := by
  have hk : k.toNat ≤ 64 := by omega
  refine ⟨(2 : Int) ^ (64 - k.toNat), ?_⟩
  unfold zpow
  rw [← Int.pow_add, Nat.add_sub_cancel' hk]

theorem u_lit_mod (s m : Int) (Hs : 0 ≤ s ∧ s < 2 ^ 6) (Hm : m = 64 ∨ m = 32) (Hsm : s < m) :
    bv_unsigned (Z_to_bv 64 s) % m = s := by
  rw [u_small ⟨Hs.1, by omega⟩]
  exact Int.emod_eq_of_lt Hs.1 Hsm

theorem and63_toNat (y : word) : (y &&& BitVec.ofInt 64 63).toNat = y.toNat % 64 := by
  rw [BitVec.toNat_and]
  have h63 : (BitVec.ofInt 64 63).toNat = 63 := by decide
  rw [h63, show (63 : Nat) = 2 ^ 6 - 1 from by decide]
  exact Nat.and_two_pow_sub_one_eq_mod y.toNat 6

theorem bv_unsigned_toNat (y : word) : (bv_unsigned y).toNat = y.toNat := rfl

theorem bv_unsigned_nonneg (y : word) : 0 ≤ bv_unsigned y := Int.natCast_nonneg _

theorem emod64_toNat (z : Int) (hz : 0 ≤ z) : (z % 64).toNat = z.toNat % 64 := by
  rw [Int.toNat_emod hz (by decide)]
  rfl

theorem intTwo64_toNat : ((2 : Int) ^ 64).toNat = 2 ^ 64 := by
  rw [Int.toNat_pow_of_nonneg (by omega)]
  rfl

theorem natCast_two64_toNat : ((↑(2 ^ 64) : Int)).toNat = 2 ^ 64 := intTwo64_toNat

theorem and63_amt (y y' : word) (H : bv_unsigned y % 64 = bv_unsigned y' % 64) :
    (y &&& BitVec.ofInt 64 63).toNat = (y' &&& BitVec.ofInt 64 63).toNat := by
  rw [and63_toNat, and63_toNat]
  have h : ((y.toNat % 64 : Nat) : Int) = ((y'.toNat % 64 : Nat) : Int) := by
    rw [Int.natCast_emod (y.toNat) 64, Int.natCast_emod (y'.toNat) 64]
    exact H
  omega

theorem alu_srl_amt (x y y' : word) (H : bv_unsigned y % 64 = bv_unsigned y' % 64) :
    alu64 .SRL x y = alu64 .SRL x y' := by
  show (x >>> (y &&& BitVec.ofInt 64 63).toNat) = (x >>> (y' &&& BitVec.ofInt 64 63).toNat)
  rw [and63_amt y y' H]

theorem alu_sra_amt (x y y' : word) (H : bv_unsigned y % 64 = bv_unsigned y' % 64) :
    alu64 .SRA x y = alu64 .SRA x y' := by
  show (x.sshiftRight (y &&& BitVec.ofInt 64 63).toNat)
     = (x.sshiftRight (y' &&& BitVec.ofInt 64 63).toNat)
  rw [and63_amt y y' H]

theorem alu_sll_amt (x y : word) (s : Int) (Hs : bv_unsigned y % 64 = s) :
    alu64 .SLL x y = Z_to_bv 64 (bv_unsigned x * zpow 2 s) := by
  have hzpos : 0 < zpow 2 s := by
    unfold zpow
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hsN : s.toNat = y.toNat % 64 := by
    rw [← Hs, emod64_toNat (bv_unsigned y) (bv_unsigned_nonneg y), bv_unsigned_toNat]
  have hzx : (zpow 2 s).toNat = 2 ^ s.toNat := by
    unfold zpow
    rw [Int.toNat_pow_of_nonneg (by omega)]
    rfl
  apply BitVec.eq_of_toNat_eq
  show (x <<< (y &&& BitVec.ofInt 64 63).toNat).toNat
     = (BitVec.ofInt 64 (bv_unsigned x * zpow 2 s)).toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, and63_toNat, BitVec.toNat_ofInt,
    Int.toNat_emod (Int.mul_nonneg (bv_unsigned_nonneg x) (by omega)) (by decide),
    Int.toNat_mul (bv_unsigned_nonneg x) (by omega), hzx, bv_unsigned_toNat x, ← hsN]
  simp only [Int.toNat_natCast]

theorem alu_sll_amt_eq (x y y' : word) (H : bv_unsigned y % 64 = bv_unsigned y' % 64) :
    alu64 .SLL x y = alu64 .SLL x y' := by
  show (x <<< (y &&& BitVec.ofInt 64 63).toNat)
     = (x <<< (y' &&& BitVec.ofInt 64 63).toNat)
  rw [and63_amt y y' H]

theorem unlin_lsll_amt (E : env) (a : expr) (y : word) (s : Int)
    (Hs : bv_unsigned y % 64 = s) :
    edenot E (unlin (lscale (zpow 2 s) (lin_of a))) = alu64 .SLL (edenot E a) y := by
  have hs0 : 0 ≤ s := by rw [← Hs]; exact Int.emod_nonneg _ (by decide)
  have hs1 : s < 64 := by rw [← Hs]; exact Int.emod_lt_of_pos _ (by decide)
  have he : s % 64 = s := Int.emod_eq_of_lt hs0 hs1
  have h : zpow 2 s = zpow 2 (s % 64) := by rw [he]
  have hdvd : (64 : Int) ∣ ((2 ^ 64 : Nat) : Int) := ⟨((2 ^ 58 : Nat) : Int), by decide⟩
  have hb : bv_unsigned (Z_to_bv 64 s) % 64 = s % 64 := by
    rw [u_lit64a]
    rw [show ((2 : Int) ^ 64) = ((2 ^ 64 : Nat) : Int) from (Int.natCast_pow 2 64).symm]
    exact Int.emod_emod_of_dvd s hdvd
  calc edenot E (unlin (lscale (zpow 2 s) (lin_of a)))
      = edenot E (unlin (lscale (zpow 2 (s % 64)) (lin_of a))) := by rw [h]
    _ = alu64 .SLL (edenot E a) (Z_to_bv 64 s) := unlin_lsll E a s
    _ = alu64 .SLL (edenot E a) y := alu_sll_amt_eq _ _ _ (by rw [hb, he]; exact Hs.symm)

theorem Z_to_bv64_swrap64 (u : Int) : Z_to_bv 64 (bv_swrap 64 u) = Z_to_bv 64 u := by
  apply eqm_Z_to_bv
  have h63 : ((2 ^ (64 - 1) : Nat) : Int) = 9223372036854775808 := by decide
  have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  refine ⟨-((u + 9223372036854775808) / 18446744073709551616), ?_⟩
  unfold bv_swrap
  rw [h63, h64, Int.emod_def]
  omega


/-! ### Byte-slice extraction (`ext_Z`/`ext_val`) -/

theorem ext_Z_0_8 (sx : Bool) (z : Int) :
    ext_Z sx 0 8 z = if sx then bv_swrap 64 (z % 2 ^ 64) else z % 2 ^ 64 := by
  dsimp only [ext_Z]
  have h88 : (8 * 8 : Nat) = 64 := by decide
  rw [h88]
  simp only [Nat.mul_zero, Int.reducePow, Int.reduceDiv, Int.ediv_one, Bool.false_eq_true,
    ite_false, ite_true]

theorem ext_val_full (sx : Bool) (v : word) : ext_val sx 0 8 v = v := by
  unfold ext_val
  rw [ext_Z_0_8]
  have h1 : Z_to_bv 64 (bv_unsigned v % 2 ^ 64) = Z_to_bv 64 (bv_unsigned v) :=
    eqm_Z_to_bv (eqm_mod (bv_unsigned v))
  cases sx with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact h1.trans (ofInt_toNat v)
  | true =>
    simp only [Bool.true_eq_false, ite_true]
    rw [Z_to_bv64_swrap64]
    exact h1.trans (ofInt_toNat v)

/-! ### Low bits of linear forms, shift amounts, and the `Int`-level mask
    arithmetic (`coeffs_div_sound` … `and_lowmask_val`)

     order resumes here: `coeffs_div_sound`, `eqm_mod_pow2`,
    `lin_lowbits_sound`, `shamt_of_sound`, `w_shift_amt`,
    `and_lowmask_val`, `slice_mod`, `ext_Z_range`, `ext_val_compose`,
    `wrap64_mod`, `land64_eq`, `land32_eq`, `land_63`, `land_31`,
    `zext_fast_eq`, `mkExt_denot`. -/

/-- `2 ^ n` is positive, as an `Int`. -/
theorem two_pow_pos_int (n : Nat) : (0 : Int) < (2 : Int) ^ n := by
  have h : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := Int.natCast_pow 2 n
  rw [← h]
  exact Int.natCast_pos.mpr (Nat.two_pow_pos n)

/-- `2 ^ k ≤ 2 ^ j` for `k ≤ j` (`Int` spelling of `Z.pow_le_mono_r`). -/
theorem int_pow_le_pow (k j : Nat) (h : k ≤ j) : (2 : Int) ^ k ≤ (2 : Int) ^ j := by
  have h1 : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h
  have h2 : ((2 ^ k : Nat) : Int) ≤ ((2 ^ j : Nat) : Int) := Int.ofNat_le.mpr h1
  rwa [Int.natCast_pow, Int.natCast_pow] at h2

/-- `Z.land y (2^k - 1) = y mod 2^k` (`Z.land_ones`) for this tree's
    `zland`, every `y`, and `k ≤ 64`. -/
theorem zland_ones (y : Int) (k : Nat) (hk : k ≤ 64) :
    AxSymExec3.zland y ((2 : Int) ^ k - 1) = y % (2 : Int) ^ k := by
  have hk64 : (2 : Int) ^ k ≤ (2 : Int) ^ 64 := by
    have h1 : ((2 ^ k : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hk)
    rwa [Int.natCast_pow, Int.natCast_pow] at h1
  have htwo : two64 = (2 : Int) ^ 64 := rfl
  have hone : (1 : Int) ≤ (2 : Int) ^ k := by
    have h : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
    rw [← h]
    exact Int.ofNat_le.mpr (Nat.one_le_two_pow)
  have hlt : (2 : Int) ^ k - 1 < two64 := by
    rw [htwo]
    exact Int.lt_of_lt_of_le (Int.sub_lt_self _ (by decide)) hk64
  have hmask : ((2 : Int) ^ k - 1) % two64 = (2 : Int) ^ k - 1 :=
    Int.emod_eq_of_lt (Int.sub_nonneg_of_le hone) hlt
  have hmaskNat : (((2 : Int) ^ k - 1) % two64).toNat = 2 ^ k - 1 := by
    rw [hmask]
    have hcast : (2 : Int) ^ k - 1 = ((2 ^ k - 1 : Nat) : Int) := by
      rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) from (Int.natCast_pow 2 k).symm]
      exact (Int.natCast_sub (Nat.one_le_two_pow)).symm
    rw [hcast, Int.toNat_natCast]
  have hm : 0 ≤ y % two64 := Int.emod_nonneg _ (by rw [htwo]; decide)
  unfold AxSymExec3.zland
  rw [hmaskNat, Nat.and_two_pow_sub_one_eq_mod]
  have hcast2 : ((((y % two64).toNat % 2 ^ k : Nat)) : Int)
      = ((y % two64).toNat : Int) % (2 : Int) ^ k := by
    rw [Int.natCast_emod, Int.natCast_pow]
    rfl
  rw [hcast2, Int.toNat_of_nonneg hm]
  refine Int.emod_emod_of_dvd y ⟨(2 : Int) ^ (64 - k), ?_⟩
  rw [htwo, ← Int.pow_add, Nat.add_sub_cancel' hk]

/-- `coeffs_div`: every coefficient is a multiple of `m`, so the term list
    denotes a multiple of `m`. -/
theorem coeffs_div_sound (E : env) (m : Int) (ts : List (Int × expr))
    (Hm : 0 < m) (H : coeffs_div m ts = true) : tden E ts % m = 0 := by
  induction ts with
  | nil => rw [tden_nil]; exact Int.zero_emod m
  | cons hd rest ih =>
    obtain ⟨k, a⟩ := hd
    rw [coeffs_div, Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (beq_iff_eq.mp H1)
    have hmul : m ∣ k * uE E a := ⟨c * uE E a, by rw [hc, Int.mul_assoc]⟩
    have hrest : m ∣ tden E rest := Int.dvd_of_emod_eq_zero (ih H2)
    rw [tden_cons]
    exact Int.emod_eq_zero_of_dvd (Int.dvd_add hmul hrest)

/-- `eqm` is compatible with reducing modulo `2^k`, `k ≤ 64`. -/
theorem eqm_mod_pow2 (a b k : Int) (Hk : 0 ≤ k ∧ k ≤ 64) (H : eqm a b) :
    a % zpow 2 k = b % zpow 2 k := by
  obtain ⟨q, hq⟩ := H
  obtain ⟨r, hr⟩ := pow2_div_64 k Hk
  have heq : b + q * 2 ^ 64 = b + (q * r) * zpow 2 k := by
    rw [hr, Int.mul_left_comm, Int.mul_comm]
  rw [hq, heq, Int.add_mul_emod_self_right]

/-- The low `k` bits of a linear form that `coeffs_div` accepts: they are
    the literal `c mod 2^k`, and the value is in range. -/
theorem lin_lowbits_sound (E : env) (e : expr) (k v : Int) (Hk : 0 ≤ k ∧ k ≤ 64)
    (H : lin_lowbits e k = some v) :
    bv_unsigned (edenot E e) % zpow 2 k = v ∧ 0 ≤ v ∧ v < zpow 2 k := by
  have hp : 0 < zpow 2 k := by
    unfold zpow
    exact two_pow_pos_int k.toNat
  have hd : coeffs_div (zpow 2 k) (lin_of e).2 = true := by
    by_cases hh : coeffs_div (zpow 2 k) (lin_of e).2 = true
    · exact hh
    · simp only [lin_lowbits] at H
      rw [ite_eq_right hh] at H
      exact absurd H (by simp)
  have hv : v = (lin_of e).1 % zpow 2 k := by
    simp only [lin_lowbits] at H
    rw [ite_eq_left hd] at H
    exact (Option.some.inj H).symm
  have hcd : tden E (lin_of e).2 % zpow 2 k = 0 :=
    coeffs_div_sound E (zpow 2 k) (lin_of e).2 hp hd
  have hsplit : lden E (lin_of e) % zpow 2 k = (lin_of e).1 % zpow 2 k := by
    simp only [lden]
    rw [Int.add_emod, hcd, Int.add_zero, Int.emod_emod]
  have Hm := eqm_mod_pow2 (lden E (lin_of e)) (uE E e) k Hk (lin_of_sound E e)
  simp only [uE] at Hm
  have h1 : bv_unsigned (edenot E e) % zpow 2 k = (lin_of e).1 % zpow 2 k :=
    Hm.symm.trans hsplit
  refine ⟨?_, ?_, ?_⟩
  · rw [hv]; exact h1
  · rw [hv]; exact Int.emod_nonneg _ (by omega)
  · rw [hv]; exact Int.emod_lt_of_pos _ hp

/-- A shift amount is determined by the low `bits` bits of the value. -/
theorem shamt_of_sound (E : env) (e : expr) (bits s : Int) (Hb : 0 ≤ bits ∧ bits ≤ 64)
    (H : shamt_of e bits = some s) :
    bv_unsigned (edenot E e) % zpow 2 bits = s ∧ 0 ≤ s ∧ s < zpow 2 bits := by
  have hp : 0 < zpow 2 bits := by
    unfold zpow
    exact two_pow_pos_int bits.toNat
  unfold shamt_of at H
  cases e with
  | ELit z =>
    simp only at H
    have hs : s = z % zpow 2 bits := (Option.some.inj H).symm
    have h1 : bv_unsigned (Z_to_bv 64 z) % zpow 2 bits = z % zpow 2 bits := by
      rw [u_lit64a]
      exact Int.emod_emod_of_dvd z (pow2_div_64 bits Hb)
    refine ⟨?_, ?_, ?_⟩
    · rw [hs]; exact h1
    · rw [hs]; exact Int.emod_nonneg _ (by omega)
    · rw [hs]; exact Int.emod_lt_of_pos _ hp
  | _ => exact lin_lowbits_sound E _ bits s Hb H

/-- The low 5 bits of `low32 y` are `y mod 32`. -/
theorem low32_and31 (y : word) :
    ((low32 y) &&& BitVec.ofInt 32 31).toNat = y.toNat % 32 := by
  rw [BitVec.toNat_and]
  have h31 : (BitVec.ofInt 32 31).toNat = 31 := by decide
  have hl : (low32 y).toNat = y.toNat % 2 ^ 32 := by
    unfold low32 bits
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [h31, hl, show (31 : Nat) = 2 ^ 5 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd y.toNat (by decide : 32 ∣ 2 ^ 32)]

/-- `alu32` at a 32-bit shift only reads the masked amount. -/
theorem alu32_shift_amt (op : AluOp) (h : op = .SLL ∨ op = .SRL ∨ op = .SRA)
    (x y y' : BitVec 32)
    (H : (y &&& BitVec.ofInt 32 31).toNat = (y' &&& BitVec.ofInt 32 31).toNat) :
    alu32 op x y = alu32 op x y' := by
  rcases h with rfl | rfl | rfl <;> (simp only [alu32, alu]; rw [H])

/-- **Shifts depend on the amount register only through its low 5 bits.**
     `w_shift_amt`. -/
theorem w_shift_amt (op : AluOp) (x y y' : word)
    (Hop : op = .SLL ∨ op = .SRL ∨ op = .SRA)
    (H : bv_unsigned y % 32 = bv_unsigned y' % 32) :
    sext 64 (alu32 op (low32 x) (low32 y)) = sext 64 (alu32 op (low32 x) (low32 y')) := by
  congr 1
  apply alu32_shift_amt op Hop
  rw [low32_and31, low32_and31]
  have h2 : ((y.toNat % 32 : Nat) : Int) = ((y'.toNat % 32 : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_emod]
    exact H
  exact Int.ofNat.inj h2

/-- `Z.land y 63 = y mod 64`. -/
theorem land_63 (y : Int) : AxSymExec3.zland y 63 = y % 64 := by
  have h := zland_ones y 6 (by decide)
  simpa using h

/-- `Z.land y 31 = y mod 32`. -/
theorem land_31 (y : Int) : AxSymExec3.zland y 31 = y % 32 := by
  have h := zland_ones y 5 (by decide)
  simpa using h

/-- `land32 z = z mod 2^32`. -/
theorem land32_eq (z : Int) : land32 z = z % 4294967296 := by
  have h32 : (4294967296 : Int) = (2 : Int) ^ 32 := by decide
  unfold land32 two32z
  by_cases h : (0 ≤ z && z < (2 : Int) ^ 32) = true
  · rw [ite_eq_left h, h32]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact (Int.emod_eq_of_lt h.1 h.2).symm
  · rw [ite_eq_right h, h32]
    have hz := zland_ones z 32 (by decide)
    unfold ones32z zones
    rw [hz]

/-- `land64 z = z mod 2^64` (`Z.land_ones`). -/
theorem land64_eq (z : Int) : land64 z = z % two64 := by
  unfold land64
  by_cases h : (0 ≤ z && z < two64) = true
  · rw [ite_eq_left h]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact (Int.emod_eq_of_lt h.1 h.2).symm
  · rw [ite_eq_right h]
    exact land_ones64z' z

/-- `wrap64 z = z mod 2^64`. -/
theorem wrap64_mod (z : Int) : wrap64 z = z % two64 := by
  unfold wrap64
  by_cases h : (0 ≤ z && z < two64) = true
  · rw [ite_eq_left h]
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact (Int.emod_eq_of_lt h.1 h.2).symm
  · rw [ite_eq_right h]

/--  name for the statement just proved (`AxSymExec3Sound:3457`,
    `wrap64_eq`): this tree had it as `wrap64_mod` only, so the
    name is restored here as an alias rather than re-proved. -/
theorem wrap64_eq (z : Int) : wrap64 z = z % two64 := wrap64_mod z

/-- The `64`-bit `toNat` of the `k`-bit all-ones mask. -/
theorem mask_ones_toNat (k : Nat) (hk : k ≤ 64) :
    (BitVec.ofInt 64 ((2 : Int) ^ k - 1)).toNat = 2 ^ k - 1 := by
  have hcast : (2 : Int) ^ k - 1 = ((2 ^ k - 1 : Nat) : Int) := by
    rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) from (Int.natCast_pow 2 k).symm]
    exact (Int.natCast_sub (Nat.one_le_two_pow)).symm
  rw [hcast, BitVec.toNat_ofInt, ← Int.natCast_emod, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (by
    have h2 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega)

/-- `v &&& (2^k - 1) = v mod 2^k` at `word` width (`bv` spelling of
    `Z.land_ones`). -/
theorem and_ones_word (v : word) (k : Nat) (hk : k ≤ 64) :
    v &&& BitVec.ofInt 64 ((2 : Int) ^ k - 1)
      = BitVec.ofInt 64 (((v.toNat % 2 ^ k : Nat)) : Int) := by
  have hrhs : (BitVec.ofInt 64 (((v.toNat % 2 ^ k : Nat)) : Int)).toNat = v.toNat % 2 ^ k := by
    rw [BitVec.toNat_ofInt, ← Int.natCast_emod, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt (by
      have h1 : v.toNat < 2 ^ 64 := v.isLt
      have h2 : v.toNat % 2 ^ k ≤ v.toNat := Nat.mod_le _ _
      omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, mask_ones_toNat k hk, Nat.and_two_pow_sub_one_eq_mod, hrhs]

/-- **`ALU_AND` with a low mask is a reduction modulo `2^j`.**
     `and_lowmask_val`. -/
theorem and_lowmask_val (v : word) (j : Int) (Hj : 0 ≤ j) (Hj64 : j ≤ 64) :
    alu64 .AND v (Z_to_bv 64 (zpow 2 j - 1))
      = Z_to_bv 64 (bv_unsigned v % zpow 2 j) := by
  have hk : j.toNat ≤ 64 := by omega
  have hz : zpow 2 j = (2 : Int) ^ j.toNat := rfl
  show v &&& BitVec.ofInt 64 (zpow 2 j - 1) = BitVec.ofInt 64 (bv_unsigned v % zpow 2 j)
  rw [hz]
  have hrhs : bv_unsigned v % (2 : Int) ^ j.toNat = ((v.toNat % 2 ^ j.toNat : Nat) : Int) := by
    show ((v.toNat : Int)) % (2 : Int) ^ j.toNat = ((v.toNat % 2 ^ j.toNat : Nat) : Int)
    rw [show (2 : Int) ^ j.toNat = ((2 ^ j.toNat : Nat) : Int)
        from (Int.natCast_pow 2 j.toNat).symm, ← Int.natCast_emod]
  rw [hrhs]
  exact and_ones_word v j.toNat hk

/-- **Byte-slice extraction is compositional**: taking `[lo, lo+n)` of the
    zero-extended `[lo', lo'+n')` window is taking the wide slice directly.
     `slice_mod` is the arithmetic core; it is stated here at the
    `Nat` exponents `ext_Z` actually uses (`2 ^ (8 * lo)`), with
    `slice_mod` as the `Int`-exponent corollary. -/
theorem slice_mod_nat (a : Int) (m k j : Nat) (H : k + j ≤ m) :
    (a % (2 : Int) ^ m / (2 : Int) ^ k) % (2 : Int) ^ j
      = (a / (2 : Int) ^ k) % (2 : Int) ^ j := by
  have hk : 0 < (2 : Int) ^ k := two_pow_pos_int k
  have hp : 0 < (2 : Int) ^ m := two_pow_pos_int m
  have hM : (2 : Int) ^ m = (2 : Int) ^ (m - k) * (2 : Int) ^ k := by
    rw [← Int.pow_add, Nat.sub_add_cancel (by omega : k ≤ m)]
  have hdef := Int.emod_def a ((2 : Int) ^ m)
  generalize hA : a % (2 : Int) ^ m = A at hdef ⊢
  generalize hq : a / (2 : Int) ^ m = q at hdef ⊢
  have hA0 : 0 ≤ A := by rw [← hA]; exact Int.emod_nonneg _ (by omega)
  have hAlt : A < (2 : Int) ^ m := by rw [← hA]; exact Int.emod_lt_of_pos _ hp
  have ha : a = A + (2 : Int) ^ m * q := by rw [hdef]; omega
  have hmq : (2 : Int) ^ m * q = ((2 : Int) ^ (m - k) * q) * (2 : Int) ^ k := by
    have hassoc : (2 : Int) ^ (m - k) * (2 : Int) ^ k * q
        = ((2 : Int) ^ (m - k) * q) * (2 : Int) ^ k := by
      rw [Int.mul_assoc, Int.mul_comm ((2 : Int) ^ k) q, ← Int.mul_assoc]
    rw [hM, hassoc]
  have hstep : a / (2 : Int) ^ k
      = A / (2 : Int) ^ k + (2 : Int) ^ (m - k) * q := by
    rw [ha, hmq, Int.add_mul_ediv_right _ _ (by omega)]
  have hjle : j ≤ m - k := by omega
  have hdvd : (2 : Int) ^ j ∣ (2 : Int) ^ (m - k) := by
    refine ⟨(2 : Int) ^ (m - k - j), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' hjle]
  obtain ⟨r, hr⟩ := hdvd
  have hsplit : (2 : Int) ^ (m - k) * q = (r * q) * (2 : Int) ^ j := by
    rw [hr, Int.mul_assoc, Int.mul_comm ((2 : Int) ^ j) (r * q)]
  have hAq0 : 0 ≤ A / (2 : Int) ^ k := Int.ediv_nonneg hA0 (by omega)
  have hAqlt : A / (2 : Int) ^ k < (2 : Int) ^ (m - k) := by
    rw [Int.ediv_lt_iff_lt_mul hk, ← hM]
    exact hAlt
  have hfinal : (a / (2 : Int) ^ k) % (2 : Int) ^ j
      = A / (2 : Int) ^ k % (2 : Int) ^ j := by
    rw [hstep, hsplit, Int.add_mul_emod_self_right]
  exact hfinal.symm

/-- `slice_mod`, at `Int` exponents. -/
theorem slice_mod (a m k j : Int) (Hk : 0 ≤ k) (Hj : 0 ≤ j) (Hm : k + j ≤ m) :
    (a % zpow 2 m / zpow 2 k) % zpow 2 j = (a / zpow 2 k) % zpow 2 j := by
  have hkj : (k + j).toNat = k.toNat + j.toNat := Int.toNat_add Hk Hj
  have hm0 : 0 ≤ m := by omega
  have hmm : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
  have hm : k.toNat + j.toNat ≤ m.toNat := by
    rw [← hkj]
    exact Int.toNat_le.mpr (by rw [hmm]; exact Hm)
  unfold zpow
  exact slice_mod_nat a m.toNat k.toNat j.toNat hm

/-- The zero-extended slice `[lo, lo+n)` of a `Z` is in `[0, 2^64)` for
    `n ≤ 8`.   `ext_Z_range`. -/
theorem ext_Z_range (lo n : Nat) (z : Int) (Hn : n ≤ 8) :
    0 ≤ ext_Z false lo n z ∧ ext_Z false lo n z < (2 : Int) ^ 64 := by
  have hp : 0 < (2 : Int) ^ (8 * n) := two_pow_pos_int _
  dsimp only [ext_Z]
  simp only [Bool.false_eq_true, ite_false]
  constructor
  · exact Int.emod_nonneg _ (by omega)
  · have h1 : z / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n) < (2 : Int) ^ (8 * n) :=
      Int.emod_lt_of_pos _ hp
    have h2 : (2 : Int) ^ (8 * n) ≤ (2 : Int) ^ 64 := int_pow_le_pow (8 * n) 64 (by omega)
    omega

/-- `ext_Z` at `sx = false` composes (the `Z` half of `ext_val_compose`). -/
theorem ext_Z_false_compose (lo n lo' n' : Nat) (z : Int) (Hle : lo + n ≤ n') :
    ext_Z false lo n (ext_Z false lo' n' z) = ext_Z false (lo' + lo) n z := by
  have hq : 0 ≤ (2 : Int) ^ (8 * lo') := by
    have := two_pow_pos_int (8 * lo'); omega
  dsimp only [ext_Z]
  simp only [Bool.false_eq_true, ite_false]
  calc ((z / (2 : Int) ^ (8 * lo')) % (2 : Int) ^ (8 * n') / (2 : Int) ^ (8 * lo))
        % (2 : Int) ^ (8 * n)
      = ((z / (2 : Int) ^ (8 * lo')) / (2 : Int) ^ (8 * lo)) % (2 : Int) ^ (8 * n) :=
        slice_mod_nat (z / (2 : Int) ^ (8 * lo')) (8 * n') (8 * lo) (8 * n) (by omega)
    _ = (z / (2 : Int) ^ (8 * lo' + 8 * lo)) % (2 : Int) ^ (8 * n) := by
        rw [Int.ediv_ediv_of_nonneg hq, ← Int.pow_add]
    _ = (z / (2 : Int) ^ (8 * (lo' + lo))) % (2 : Int) ^ (8 * n) := by
        rw [show 8 * lo' + 8 * lo = 8 * (lo' + lo) from by omega]

/-- **Slices compose.**   `ext_val_compose`. -/
theorem ext_val_compose (sx : Bool) (lo n lo' n' : Nat) (v : word)
    (Hle : lo + n ≤ n') (Hn' : n' ≤ 8) :
    ext_val sx lo n (ext_val false lo' n' v) = ext_val sx (lo' + lo) n v := by
  have hq : 0 ≤ (2 : Int) ^ (8 * lo') := by
    have := two_pow_pos_int (8 * lo'); omega
  have hslice : ((bv_unsigned v / (2 : Int) ^ (8 * lo')) % (2 : Int) ^ (8 * n')
        / (2 : Int) ^ (8 * lo)) % (2 : Int) ^ (8 * n)
      = bv_unsigned v / (2 : Int) ^ (8 * (lo' + lo)) % (2 : Int) ^ (8 * n) := by
    rw [slice_mod_nat (bv_unsigned v / (2 : Int) ^ (8 * lo')) (8 * n') (8 * lo) (8 * n)
      (by omega)]
    rw [Int.ediv_ediv_of_nonneg hq, ← Int.pow_add,
      show 8 * lo' + 8 * lo = 8 * (lo' + lo) from by omega]
  have hbv : bv_unsigned (Z_to_bv 64 (ext_Z false lo' n' (bv_unsigned v)))
      = ext_Z false lo' n' (bv_unsigned v) := by
    rw [u_lit64a]
    exact Int.emod_eq_of_lt (ext_Z_range lo' n' _ Hn').1 (ext_Z_range lo' n' _ Hn').2
  unfold ext_val
  rw [hbv]
  cases sx with
  | false =>
    dsimp only [ext_Z]
    simp only [Bool.false_eq_true, ite_false]
    rw [hslice]
  | true =>
    dsimp only [ext_Z]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [hslice]


/-! #### `zext_fast` = `zext_lit` (`zext_fast_eq`) and `mkExt` (`mkExt_denot`)

    With the half modulus spelled `bv_modulus 0 / 2`, `bv_swrap 0 0 = 0`, so
    `bv_swrap 0 0 = 0` and the degenerate `sx = true, n = 0` case holds.
    This tree's `PropExec.bv_swrap` uses `2 ^ (n - 1)` with `Nat`
    subtraction, so `2 ^ (0 - 1) = 1` and `bv_swrap 0 0 = -1`: hence
    `zext_fast true lo 0 x = 0` while `zext_lit true lo 0 x = 2^64-1`
    (both `by decide`).  The statement below therefore carries
    `sx = false ∨ 1 ≤ n`, which is the honest form here; every `mkExt`
    call site of the executor uses a byte width (`1 ≤ n ≤ 8`), where the
    two agree.  See the report for the exact counterexample. -/

/-- `zshiftl 1 s = 2^s`. -/
theorem zshiftl_one (s : Nat) : AxSymExec3.zshiftl 1 s = (2 : Int) ^ s := by
  unfold AxSymExec3.zshiftl
  rw [Int.one_mul]

/-- Below the half modulus the signed wrap is the identity (`Z.land`-free
    companion of `bv_swrap_hi`, which PropExec only states above it). -/
theorem bv_swrap_lo (n : Nat) (z : Int) (Hn : n ≠ 0)
    (Hlo : 0 ≤ z) (Hhi : z < ((2 ^ (n - 1) : Nat) : Int)) :
    bv_swrap n z = z := by
  unfold bv_swrap
  have hnm : n = (n - 1) + 1 := by omega
  have hmul : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    rw [hnm, Nat.pow_succ]
    push_cast
    rw [Int.mul_comm]
  have h1 : (z + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int)
      = z + ((2 ^ (n - 1) : Nat) : Int) := by
    apply Int.emod_eq_of_lt <;> omega
  rw [h1]
  omega

/-- **`zext_fast` is `zext_lit`** . -/
theorem zext_fast_eq (sx : Bool) (lo n : Nat) (x : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hn8 : n ≤ 8) (Hn : sx = false ∨ 1 ≤ n) :
    zext_fast sx lo n x = zext_lit sx lo n x := by
  have hk8 : 8 * n ≤ 64 := by omega
  have hpos : 0 < (2 : Int) ^ (8 * n) := two_pow_pos_int _
  have hu : AxSymExec3.zland (AxSymExec3.zshiftr x (8 * lo)) (zones (8 * n))
      = x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n) := by
    have h := zland_ones (x / (2 : Int) ^ (8 * lo)) (8 * n) hk8
    simpa [AxSymExec3.zshiftr, zones] using h
  have hu0 : 0 ≤ x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n) :=
    Int.emod_nonneg _ (by omega)
  have hukt : x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n) < (2 : Int) ^ (8 * n) :=
    Int.emod_lt_of_pos _ hpos
  have hbx : bv_unsigned (Z_to_bv 64 x) = x := by
    rw [u_lit64a]; exact Int.emod_eq_of_lt Hx.1 Hx.2
  have hlit : zext_lit sx lo n x = ext_Z sx lo n x % two64 := by
    unfold zext_lit ext_val
    rw [hbx]
    exact u_lit64a _
  cases sx with
  | false =>
    unfold zext_fast
    simp only [Bool.false_eq_true, ite_false]
    rw [hu, wrap64_mod, hlit]
    dsimp only [ext_Z]
    simp only [Bool.false_eq_true, ite_false]
  | true =>
    rcases Hn with h | hn
    · exact absurd h (by decide)
    cases n with
    | zero => omega
    | succ m =>
      have hkcast : (8 * (((m + 1 : Nat)) : Int)) = ((8 * (m + 1) : Nat) : Int) := by
        rw [Int.natCast_mul]; rfl
      have hk1 : (8 * (((m + 1 : Nat)) : Int) - 1).toNat = 8 * (m + 1) - 1 := by
        rw [hkcast]
        have hsub : ((8 * (m + 1) : Nat) : Int) - 1 = ((8 * (m + 1) - 1 : Nat) : Int) := by
          have h := Int.natCast_sub (n := 1) (m := 8 * (m + 1)) (by omega)
          simpa using h.symm
        rw [hsub, Int.toNat_natCast]
      have hk0 : (8 * (((m + 1 : Nat)) : Int)).toNat = 8 * (m + 1) := by
        rw [hkcast, Int.toNat_natCast]
      have hne : 8 * (m + 1) ≠ 0 := by omega
      unfold zext_fast
      dsimp only
      simp only [Bool.true_eq_false, ite_true]
      rw [hk1, hk0, zshiftl_one, zshiftl_one]
      rw [hu, hlit]
      dsimp only [ext_Z]
      simp only [Bool.true_eq_false, ite_true]
      by_cases hlt : x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * (m + 1))
          < (2 : Int) ^ (8 * (m + 1) - 1)
      · rw [ite_eq_left hlt, wrap64_mod,
          bv_swrap_lo (8 * (m + 1)) _ hne hu0 (by
            rw [show ((2 ^ (8 * (m+1) - 1) : Nat) : Int) = (2 : Int) ^ (8 * (m+1) - 1)
              from Int.natCast_pow 2 _]
            exact hlt)]
      · rw [ite_eq_right hlt, wrap64_mod,
          bv_swrap_hi (8 * (m + 1)) _ hne
            (by
              rw [show ((2 ^ (8 * (m+1) - 1) : Nat) : Int) = (2 : Int) ^ (8 * (m+1) - 1)
                from Int.natCast_pow 2 _]
              exact Int.not_lt.mp hlt)
            (by
              rw [show ((2 ^ (8 * (m+1)) : Nat) : Int) = (2 : Int) ^ (8 * (m+1))
                from Int.natCast_pow 2 _]
              exact hukt)]
        rw [show ((2 ^ (8 * (m+1)) : Nat) : Int) = (2 : Int) ^ (8 * (m + 1))
          from Int.natCast_pow 2 _]
        rw [show x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * (m + 1))
              - (2 : Int) ^ (8 * (m + 1)) + two64
            = (x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * (m + 1))
              - (2 : Int) ^ (8 * (m + 1))) + 1 * two64 from by rw [Int.one_mul]]
        rw [Int.add_mul_emod_self_right]

/-- `mkExt` on a non-literal: only `(0, 8)` and the zero-extended
    composition change the syntax.  One equation per constructor (the
    generic statement would need a dependent match on the constructor). -/
theorem mkExt_EVar (sx : Bool) (lo n : Nat) (v : Nat) :
    mkExt sx lo n (.EVar v)
      = (if (lo == 0 && n == 8) then .EVar v else .EExt sx lo n (.EVar v)) := rfl

theorem mkExt_EAlu (sx : Bool) (lo n : Nat) (o : AluOp) (a b : expr) :
    mkExt sx lo n (.EAlu o a b)
      = (if (lo == 0 && n == 8) then .EAlu o a b else .EExt sx lo n (.EAlu o a b)) := rfl

theorem mkExt_EAluw (sx : Bool) (lo n : Nat) (o : AluOp) (a b : expr) :
    mkExt sx lo n (.EAluw o a b)
      = (if (lo == 0 && n == 8) then .EAluw o a b else .EExt sx lo n (.EAluw o a b)) := rfl

theorem mkExt_EMd (sx : Bool) (lo n : Nat) (o : MulOp) (a b : expr) :
    mkExt sx lo n (.EMd o a b)
      = (if (lo == 0 && n == 8) then .EMd o a b else .EExt sx lo n (.EMd o a b)) := rfl

theorem mkExt_EMdw (sx : Bool) (lo n : Nat) (o : MulOp) (a b : expr) :
    mkExt sx lo n (.EMdw o a b)
      = (if (lo == 0 && n == 8) then .EMdw o a b else .EExt sx lo n (.EMdw o a b)) := rfl

theorem mkExt_EBlob (sx : Bool) (lo n : Nat) (sx' : Bool) (k : Nat) (i : Int) (n' : Nat) :
    mkExt sx lo n (.EBlob sx' k i n')
      = (if (lo == 0 && n == 8) then .EBlob sx' k i n'
         else .EExt sx lo n (.EBlob sx' k i n')) := rfl

theorem mkExt_EExt_true (sx : Bool) (lo n : Nat) (lo' n' : Nat) (e' : expr) :
    mkExt sx lo n (.EExt true lo' n' e')
      = (if (lo == 0 && n == 8) then .EExt true lo' n' e'
         else .EExt sx lo n (.EExt true lo' n' e')) := rfl

theorem mkExt_EExt_false (sx : Bool) (lo n : Nat) (lo' n' : Nat) (e' : expr) :
    mkExt sx lo n (.EExt false lo' n' e')
      = (if (lo == 0 && n == 8) then .EExt false lo' n' e'
         else if (lo + n ≤ n' && n' ≤ 8) then .EExt sx (lo' + lo) n e'
         else .EExt sx lo n (.EExt false lo' n' e')) := rfl

/-- **`mkExt` denotes the slice it names.**   `mkExt_denot`, with
    the `zext_fast_eq` caveat (`n ≤ 8` — the executor's byte widths — and
    `sx = false ∨ 1 ≤ n`). -/
theorem mkExt_denot (E : env) (sx : Bool) (lo n : Nat) (e : expr)
    (Hn8 : n ≤ 8) (Hn : sx = false ∨ 1 ≤ n) :
    edenot E (mkExt sx lo n e) = ext_val sx lo n (edenot E e) := by
  have full : ∀ (e : expr), (lo == 0 && n == 8) = true →
      edenot E e = ext_val sx lo n (edenot E e) := by
    intro e hf
    rw [Bool.and_eq_true] at hf
    obtain ⟨h1, h2⟩ := hf
    rw [beq_iff_eq] at h1 h2
    subst h1; subst h2
    exact (ext_val_full sx (edenot E e)).symm
  cases e with
  | ELit x =>
    have hwx : wrap64 x = x % (2 : Int) ^ 64 := by
      rw [wrap64_mod]
      rfl
    have hw0 : 0 ≤ wrap64 x := by
      rw [hwx]; exact Int.emod_nonneg _ (by decide)
    have hwt : wrap64 x < 2 ^ 64 := by
      rw [hwx]; exact Int.emod_lt_of_pos _ (by decide)
    have hzf := zext_fast_eq sx lo n (wrap64 x) ⟨hw0, hwt⟩ Hn8 Hn
    have hlit2 : zext_lit sx lo n (wrap64 x) = ext_Z sx lo n (x % (2 : Int) ^ 64) % 2 ^ 64 := by
      unfold zext_lit ext_val
      simp only [u_lit64a, hwx, Int.emod_emod]
    have hrhs : ext_val sx lo n (Z_to_bv 64 x) = Z_to_bv 64 (ext_Z sx lo n (x % (2 : Int) ^ 64)) := by
      unfold ext_val
      rw [u_lit64a]
    show Z_to_bv 64 (zext_fast sx lo n (wrap64 x)) = ext_val sx lo n (Z_to_bv 64 x)
    rw [hzf, hlit2, hrhs, eqm_Z_to_bv (eqm_mod (ext_Z sx lo n (x % (2 : Int) ^ 64)))]
  | EVar v =>
    rw [mkExt_EVar sx lo n v]
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl
  | EAlu o a b =>
    rw [mkExt_EAlu sx lo n o a b]
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl
  | EAluw o a b =>
    rw [mkExt_EAluw sx lo n o a b]
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl
  | EMd o a b =>
    rw [mkExt_EMd sx lo n o a b]
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl
  | EMdw o a b =>
    rw [mkExt_EMdw sx lo n o a b]
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl
  | EExt sx' lo' n' e' =>
    cases sx' with
    | true =>
      rw [mkExt_EExt_true sx lo n lo' n' e']
      by_cases hf : (lo == 0 && n == 8) = true
      · rw [ite_eq_left hf]
        exact full _ hf
      · rw [ite_eq_right hf]
        rfl
    | false =>
      rw [mkExt_EExt_false sx lo n lo' n' e']
      by_cases hf : (lo == 0 && n == 8) = true
      · rw [ite_eq_left hf]
        exact full _ hf
      · rw [ite_eq_right hf]
        by_cases hc : (lo + n ≤ n' && n' ≤ 8) = true
        · rw [ite_eq_left hc]
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          exact (ext_val_compose sx lo n lo' n' (edenot E e') hc1 hc2).symm
        · rw [ite_eq_right hc]
          rfl
  | EBlob sx' k i n' =>
    rw [mkExt_EBlob sx lo n sx' k i n']
    by_cases hf : (lo == 0 && n == 8) = true
    · rw [ite_eq_left hf]
      exact full _ hf
    · rw [ite_eq_right hf]
      rfl

/-! ## Part P4b-slices: byte-level slicing (`rdn` suffix / window)

     `rdn_skipn` … `bytes_le_to_Z_bound`.  The two `rdn` lemmas are
    the `skipn`/`firstn`-flavoured companions of `SeqExec.rdn_skipn` /
    `SeqExec.rdn_firstn` (same statements: Lean's `List.drop`/`List.take`
    are `skipn`/`firstn`), so they are instances of the generic lemmas
    proved with the executor.
-/

/-- A successful `n`-byte read, sliced at `k`: the read from `a+k` for
    `n-k` bytes yields the tail. -/
theorem rdn_skipn (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte) (k : Nat),
      rdn segs mem a n = some bs → k ≤ n →
      rdn segs mem (a + nat_to_word k) (n - k) = some (bs.drop k) :=
  SeqExec.rdn_skipn segs mem n

/-- A window of a successful read: `d, d+k` inside `n` reads back as
    `firstn k (skipn d bs)`. -/
theorem rdn_slice (segs : List Segment) (mem : word → Option byte) (n : Nat)
    (a : word) (bs : List byte) (d k : Nat)
    (H : rdn segs mem a n = some bs) (Hdk : d + k ≤ n) :
    rdn segs mem (a + nat_to_word d) k = some ((bs.drop d).take k) := by
  have H1 := SeqExec.rdn_skipn segs mem n a bs d H (by omega)
  exact SeqExec.rdn_firstn segs mem (n - d) (a + nat_to_word d) (bs.drop d) k H1 (by omega)

/-! ### `Z_to_le_bytes` slices -/

/-- `Int` division by `2 ^ (8d)` is the `d`-byte right shift . -/
theorem div_pow8_shiftRight (z : Int) (d : Nat) :
    z / 2 ^ (8 * d) = z >>> (8 * d) :=
  (Int.shiftRight_eq_div_pow z (8 * d)).symm

/-- `skipn` of a little-endian byte string is the byte string of the
    shifted value. -/
theorem skipn_Z_to_le_bytes (w d : Nat) (z : Int) (Hd : d ≤ w) :
    (Z_to_le_bytes w z).drop d = Z_to_le_bytes (w - d) (z / 2 ^ (8 * d)) := by
  induction w generalizing d z with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    rfl
  | succ w ih =>
    cases d with
    | zero =>
      show Z_to_le_bytes (w + 1) z = Z_to_le_bytes (w + 1 - 0) (z / 2 ^ (8 * 0))
      rw [Nat.mul_zero, Int.pow_zero, Int.ediv_one]
      rfl
    | succ d =>
      show (Z_to_le_bytes w (z >>> 8)).drop d
          = Z_to_le_bytes (w + 1 - (d + 1)) (z / 2 ^ (8 * (d + 1)))
      rw [ih d (z >>> 8) (by omega)]
      have hweq : w + 1 - (d + 1) = w - d := by omega
      rw [hweq]
      clear hweq
      congr 1
      rw [div_pow8_shiftRight, div_pow8_shiftRight, ← Int.shiftRight_add]
      rw [show 8 + 8 * d = 8 * (d + 1) from by omega]

/-- `firstn` of a little-endian byte string is the byte string of the
    window's width. -/
theorem firstn_Z_to_le_bytes (m n : Nat) (z : Int) (Hn : n ≤ m) :
    (Z_to_le_bytes m z).take n = Z_to_le_bytes n z := by
  induction m generalizing n z with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rfl
  | succ m ih =>
    cases n with
    | zero => rfl
    | succ n =>
      show BitVec.ofInt 8 z :: (Z_to_le_bytes m (z >>> 8)).take n
          = BitVec.ofInt 8 z :: Z_to_le_bytes n (z >>> 8)
      rw [ih n (z >>> 8) (by omega)]

/-- The value of a byte window of a word: exactly the shifted window.
 -/
theorem slice_word_bytes (w d n : Nat) (v : word) (H : d + n ≤ w) :
    bytes_le_to_Z ((word_to_le_bytes w v).drop d |>.take n)
      = bv_unsigned v / 2 ^ (8 * d) % 2 ^ (8 * n) := by
  unfold word_to_le_bytes
  rw [skipn_Z_to_le_bytes w d (v.toNat : Int) (by omega)]
  rw [firstn_Z_to_le_bytes (w - d) n _ (by omega)]
  have hz : 0 ≤ (v.toNat : Int) / 2 ^ (8 * d) :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (by have := two_pow_pos_int (8 * d); omega)
  rw [bytes_le_Z_to_le n _ hz]
  have htoNat : ((v.toNat : Int) / 2 ^ (8 * d)).toNat = v.toNat / 2 ^ (8 * d) := by
    rw [show ((v.toNat : Int) / 2 ^ (8 * d)) = ((v.toNat / 2 ^ (8 * d) : Nat) : Int) from
      (Int.natCast_ediv v.toNat (2 ^ (8 * d))).symm, Int.toNat_natCast]
  rw [htoNat, Int.natCast_emod]
  have hdiv : ((v.toNat / 2 ^ (8 * d) : Nat) : Int) = (v.toNat : Int) / 2 ^ (8 * d) :=
    Int.natCast_ediv v.toNat (2 ^ (8 * d))
  rw [hdiv]
  rfl

/-- The length of a window of a long-enough list.   -/
theorem length_firstn_skipn {A : Type} (l : List A) (d n : Nat)
    (H : d + n ≤ l.length) : ((l.drop d).take n).length = n := by
  rw [List.length_take, List.length_drop]
  omega

/-- Byte strings are bounded by their little-endian width.   -/
theorem bytes_le_to_Z_bound (bs : List byte) :
    0 ≤ bytes_le_to_Z bs ∧ bytes_le_to_Z bs < (2 : Int) ^ (8 * bs.length) := by
  constructor
  · unfold bytes_le_to_Z
    exact Int.natCast_nonneg _
  · exact PropExec.bytes_le_to_Z_bound bs

/-! ### `Z_to_bv` at word values, and pointwise/image reads -/

/-- The unsigned value, read back as a literal, is the word. -/
theorem Z_to_bv_unsigned (a : word) : Z_to_bv 64 (bv_unsigned a) = a := by
  show BitVec.ofInt 64 (a.toNat : Int) = a
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt a.isLt
theorem Z_to_bv_u_plus0 (a : word) : Z_to_bv 64 (bv_unsigned a + 0) = a := by
  rw [Int.add_zero]
  exact Z_to_bv_unsigned a

/-!  Lean
    checks in order and their proofs need `Z_to_bv_unsigned`/
    `Z_to_bv_u_plus0` (just above), so they sit here; `know_ok_unk_intro_pt`
    is up in the `KUnk` section. -/

/-- The `j`-th byte of a `wbytes` walk: a read inside the written range
    answers the written byte. -/
theorem wbytes_nth (bs : List byte) :
    ∀ (m : word → Option byte) (a : word) (j : Nat),
      (a.toNat : Int) + ((bs.length : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      j < bs.length →
      wbytes m a bs (Z_to_bv 64 ((a.toNat : Int) + ((j : Nat) : Int)))
        = some (bs.getD j (Z_to_bv 8 0)) := by
  induction bs with
  | nil => intro m a j _ hj; rw [List.length_nil] at hj; omega
  | cons b rest ih =>
    intro m a j Hnw hj
    cases rest with
    | nil =>
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have hx : Z_to_bv 64 ((a.toNat : Int) + (((0 : Nat)) : Int)) = a := by
        rw [Int.natCast_zero, Int.add_zero]; exact Z_to_bv_unsigned a
      simp only [wbytes, hx, List.getD_cons_zero]
      rw [ite_eq_left (bv_eqb_refl a)]
    | cons b' rest' =>
      have hlen : (((b :: b' :: rest').length : Nat) : Int)
          = (((b' :: rest').length : Nat) : Int) + 1 := by simp
      have hpos : (1 : Int) ≤ (((b' :: rest').length : Nat) : Int) := by
        have h : 1 ≤ (b' :: rest').length := by simp
        exact Int.ofNat_le.mpr h
      have hstep : wbytes m a (b :: b' :: rest')
          = wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) (b' :: rest') := rfl
      have hu1 : (a + 1).toNat = a.toNat + 1 := by
        apply toNat_add_one
        omega
      have hb2 : (((a + 1).toNat : Int) + (((b' :: rest').length : Nat) : Int))
          ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hu1]; omega
      cases j with
      | zero =>
        have hx : Z_to_bv 64 ((a.toNat : Int) + (((0 : Nat)) : Int)) = a := by
          rw [Int.natCast_zero, Int.add_zero]; exact Z_to_bv_unsigned a
        rw [hstep,
          wbytes_below (b' :: rest') _ (a + 1)
            (Z_to_bv 64 ((a.toNat : Int) + (((0 : Nat)) : Int)))]
        · rw [hx]
          rw [ite_eq_left (bv_eqb_refl a)]
          rfl
        · exact hb2
        · rw [hx, hu1]; omega
      | succ j' =>
        have hxj : Z_to_bv 64 ((a.toNat : Int) + (((j' + 1 : Nat)) : Int))
            = Z_to_bv 64 (((a + 1).toNat : Int) + ((j' : Nat) : Int)) := by
          rw [hu1]; congr 1; push_cast; omega
        rw [hstep, hxj,
          ih (fun x => if bv_eqb x a then some b else m x) (a + 1) j' hb2 (by omega),
          List.getD_cons_succ]

/-- After writing ANY `n` bytes there, the entry is a `KUnk`: the write
    makes every byte of the range defined.   -/
theorem know_ok_unk_intro (segs : List Segment) (E : env) (M : word → Option byte)
    (a : saddr) (bs : List byte) (ne : expr)
    (Hfl : flat E a (((bs.length : Nat)) : Int))
    (Hne : elenZ E ne = (((bs.length : Nat)) : Int)) :
    kentry_ok segs E (wbytes M (adenot E a) bs) (.KUnk a ne) := by
  have hfl' : flat E a (elenZ E ne) := by rw [Hne]; exact Hfl
  refine know_ok_unk_intro_pt segs E (wbytes M (adenot E a) bs) a ne hfl' ?_
  intro i h0 hi
  rw [Hne] at hi
  have hu : bv_unsigned (adenot E a) = estart E a := flat_u E a _ hfl'
  have hu' : ((adenot E a).toNat : Int) = estart E a := hu
  have h4 : estart E a + (((bs.length : Nat)) : Int) ≤ (2 : Int) ^ 64 := by
    obtain ⟨-, -, -, h4⟩ := Hfl
    exact h4
  have hnw : ((adenot E a).toNat : Int) + (((bs.length : Nat)) : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hu', Int.natCast_pow]
    exact h4
  have hi' : i.toNat < bs.length := by
    have h : (i.toNat : Int) < (((bs.length : Nat)) : Int) := by
      rw [Int.toNat_of_nonneg h0]; exact hi
    exact Int.ofNat_lt.mp h
  have hii : (((i.toNat : Nat)) : Int) = i := Int.toNat_of_nonneg h0
  have hz : BitVec.ofInt 64 (estart E a + i)
      = BitVec.ofInt 64 (((adenot E a).toNat : Int) + ((i.toNat : Nat) : Int)) := by
    rw [hu', hii]
  rw [hz, wbytes_nth bs M (adenot E a) i.toNat hnw hi']
  simp

/-- A read described pointwise at its bytes is the byte list.
 -/
theorem rdn_pointwise (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte), bs.length = n →
      bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      (∀ j : Nat, j < n →
        mem (Z_to_bv 64 (bv_unsigned a + (j : Int)))
          = some (bs.getD j (Z_to_bv 8 0))) →
      rdn segs mem a n = some bs := by
  induction n with
  | zero =>
    intro a bs hlen _ _
    cases bs with
    | nil => rfl
    | cons b bs' =>
      rw [List.length_cons] at hlen
      exact absurd hlen (by omega)
  | succ n ih =>
    intro a bs hlen hw hpt
    cases bs with
    | nil =>
      rw [List.length_nil] at hlen
      exact absurd hlen (by omega)
    | cons b bs' =>
      have hlen' : bs'.length = n := by
        rw [List.length_cons] at hlen
        omega
      have hmem0 : mem a = some b := by
        have h := hpt 0 (by omega)
        simpa [Z_to_bv_u_plus0, List.getD_cons_zero] using h
      cases n with
      | zero =>
        have hbs' : bs' = [] := List.eq_nil_of_length_eq_zero hlen'
        subst hbs'
        rw [SeqExec.rdn_succ segs mem a 0 b hmem0, SeqExec.rdn_zero]
        rfl
      | succ n' =>
        have hlt : bv_unsigned a + 1 < (2 : Int) ^ 64 := by
          have h2 := hw
          push_cast at h2
          have hn : (0 : Int) ≤ (n' : Int) := Int.natCast_nonneg n'
          omega
        have hsucc : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a hlt
        have hw' : bv_unsigned (a + 1) + ((n' + 1 : Nat) : Int) ≤ 2 ^ 64 := by
          rw [hsucc]
          have h2 := hw
          push_cast at h2 ⊢
          omega
        have hpt' : ∀ j : Nat, j < n' + 1 →
            mem (Z_to_bv 64 (bv_unsigned (a + 1) + (j : Int)))
              = some (bs'.getD j (Z_to_bv 8 0)) := by
          intro j hj
          have h := hpt (j + 1) (by omega)
          rw [hsucc]
          have hcast : bv_unsigned a + 1 + (j : Int) = bv_unsigned a + ((j + 1 : Nat) : Int) := by
            push_cast
            omega
          rw [hcast]
          simpa [List.getD_cons_succ] using h
        rw [SeqExec.rdn_succ segs mem a (n' + 1) b hmem0,
          ih (a + 1) bs' hlen' hw' hpt']
        rfl

/-- An image read whose bytes the overlay leaves alone is a `rdn` read of
    the image. -/
theorem rdn_img (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (zs : List Int),
      bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      (∀ j : Nat, j < n → mem (Z_to_bv 64 (bv_unsigned a + (j : Int))) = none) →
      img_bytes segs (bv_unsigned a) n = some zs →
      ∃ bs, rdn segs mem a n = some bs ∧ bs.map bv_unsigned = zs := by
  induction n with
  | zero =>
    intro a zs _ _ himg
    simp only [img_bytes, Option.some.injEq] at himg
    subst himg
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro a zs hw hpt himg
    simp only [img_bytes, Z_to_bv_unsigned] at himg
    cases hrom : seg_rom segs a with
    | none =>
      rw [hrom] at himg
      exact absurd himg (by simp)
    | some b =>
      rw [hrom] at himg
      cases hrest : img_bytes segs (bv_unsigned a + 1) n with
      | none =>
        rw [hrest] at himg
        exact absurd himg (by simp)
      | some zr =>
        rw [hrest] at himg
        rw [Option.some.injEq] at himg
        subst himg
        have hmem0 : mem a = none := by
          have h := hpt 0 (by omega)
          simpa [Z_to_bv_u_plus0] using h
        have hbyte : SeqExec.rdn_byte segs mem a = some b := by
          simp only [SeqExec.rdn_byte, hmem0, hrom]
        cases n with
        | zero =>
          simp only [img_bytes, Option.some.injEq] at hrest
          subst hrest
          refine ⟨[b], ?_, rfl⟩
          rw [SeqExec.rdn_succ_byte segs mem a 0 b hbyte, SeqExec.rdn_zero]
          rfl
        | succ n' =>
          have hlt : bv_unsigned a + 1 < (2 : Int) ^ 64 := by
            have h2 := hw
            push_cast at h2
            have hn : (0 : Int) ≤ (n' : Int) := Int.natCast_nonneg n'
            omega
          have hsucc : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a hlt
          have hrest' : img_bytes segs (bv_unsigned (a + 1)) (n' + 1) = some zr := by
            rw [hsucc]
            exact hrest
          have hw' : bv_unsigned (a + 1) + ((n' + 1 : Nat) : Int) ≤ 2 ^ 64 := by
            rw [hsucc]
            have h2 := hw
            push_cast at h2 ⊢
            omega
          have hpt' : ∀ j : Nat, j < n' + 1 →
              mem (Z_to_bv 64 (bv_unsigned (a + 1) + (j : Int))) = none := by
            intro j hj
            have h := hpt (j + 1) (by omega)
            rw [hsucc]
            have hcast : bv_unsigned a + 1 + (j : Int) = bv_unsigned a + ((j + 1 : Nat) : Int) := by
              push_cast
              omega
            rw [hcast]
            exact h
          obtain ⟨bs, hbs, hmap⟩ := ih (a + 1) zr hw' hpt' hrest'
          refine ⟨b :: bs, ?_, ?_⟩
          · rw [SeqExec.rdn_succ_byte segs mem a (n' + 1) b hbyte, hbs]
            rfl
          · simp only [List.map_cons, hmap]

/-! ### `zbytes_le_to_Z`, `extz`, extraction at literal values -/

/-- Byte strings of zeros denote zero.   -/
theorem bytes_le_to_Z_repeat0 (n : Nat) :
    bytes_le_to_Z (List.replicate n (Z_to_bv 8 0)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    show (((Z_to_bv 8 0).toNat
      ||| (bytes_le_to_Nat (List.replicate n (Z_to_bv 8 0)) <<< 8) : Nat) : Int) = 0
    have hz : (Z_to_bv 8 0).toNat = 0 := by decide
    have hrest : bytes_le_to_Nat (List.replicate n (Z_to_bv 8 0)) = 0 := by
      have h := ih
      unfold bytes_le_to_Z at h
      exact Int.ofNat.inj h
    rw [hz, hrest]
    rfl

/-- Sign-extending zero at a positive width is zero.   -/
theorem extz_0 (sx : Bool) (n : Nat) (Hn : sx = false ∨ 1 ≤ n) : extz sx n 0 = 0 := by
  unfold extz
  cases sx with
  | false => rfl
  | true =>
    rcases Hn with h | hn
    · exact absurd h (by simp)
    · show bv_swrap (8 * n) (0 : Int) = 0
      unfold bv_swrap
      rw [Int.zero_add]
      have hpos : (0 : Int) < ((2 ^ (8 * n - 1) : Nat) : Int) := by
        rw [Int.natCast_pow]
        exact two_pow_pos_int (8 * n - 1)
      have hlt : ((2 ^ (8 * n - 1) : Nat) : Int) < ((2 ^ (8 * n) : Nat) : Int) := by
        rw [Int.natCast_pow, Int.natCast_pow]
        exact Int.pow_lt_pow_of_lt (by decide) (by omega)
      rw [Int.emod_eq_of_lt (by omega) hlt]
      omega

/-- `bv_extract0_lit`: the extraction statement is only recorded
    (it is `True`). -/
theorem bv_extract0_lit (m : Nat) (u : Int)
    (H : bits 0 m (Z_to_bv 64 u) = Z_to_bv m u) : True := trivial

/-! ### Extraction and extension at literal values -/

/-- `2 ^ k` as a positive `Int` (the `Nat`-cast spelling `BitVec`/`Int.emod`
    lemmas produce). -/
theorem natCast_two_pow_pos (k : Nat) : (0 : Int) < ((2 ^ k : Nat) : Int) := by
  have h := two_pow_pos_int k
  simpa using h

/-- `(2 : Int) ^ k` as a `Nat`, for the byte arithmetic. -/
theorem int_pow_toNat (k : Nat) : ((2 : Int) ^ k).toNat = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Int.pow_succ, Int.toNat_mul (by have := two_pow_pos_int k; omega)
      (by omega), ih, show Int.toNat 2 = 2 from rfl, Nat.pow_succ]

/-- `t % 2^64 = t + 2^64` in the negative window `[-2^64, 0)`.   -/
theorem mod_wrap_neg (t : Int) (h1 : -((2 : Int) ^ 64) ≤ t) (h2 : t < 0) :
    t % (2 : Int) ^ 64 = t + (2 : Int) ^ 64 := by
  rw [← Int.add_mul_emod_self_right t 1 ((2 : Int) ^ 64), Int.one_mul]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Extracting the low `m` bits of a 64-bit literal.   -/
theorem extract0_Z_to_bv64 (m : Nat) (u : Int) (Hm : m ≤ 64) :
    bits 0 m (Z_to_bv 64 u) = Z_to_bv m u := by
  apply BitVec.eq_of_toNat_eq
  show ((BitVec.ofInt 64 u).extractLsb' 0 m).toNat = (BitVec.ofInt m u).toNat
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : ((2 : Int) ^ m) ∣ ((2 : Int) ^ 64) := by
    refine ⟨(2 : Int) ^ (64 - m), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' Hm]
  have hx0 : 0 ≤ u % ((2 ^ 64 : Nat) : Int) :=
    Int.emod_nonneg _ (by have h := natCast_two_pow_pos 64; omega)
  have h1 : ((u % ((2 ^ 64 : Nat) : Int)) % ((2 ^ m : Nat) : Int)).toNat
      = (u % ((2 ^ 64 : Nat) : Int)).toNat % 2 ^ m := by
    rw [Int.toNat_emod hx0 (by have h := natCast_two_pow_pos m; omega), Int.toNat_natCast]
  have h2 : (u % ((2 ^ 64 : Nat) : Int)) % ((2 ^ m : Nat) : Int)
      = u % ((2 ^ m : Nat) : Int) :=
    Int.emod_emod_of_dvd u (m := (2 : Int) ^ m) (k := (2 : Int) ^ 64) hdvd
  rw [← h2, h1]

/-- Zero-extending a literal already inside its width.   -/
theorem zext64_small (m : Nat) (u : Int) (Hm : m ≤ 64) (Hu : 0 ≤ u ∧ u < 2 ^ m) :
    zext 64 (Z_to_bv m u) = Z_to_bv 64 u := by
  apply BitVec.eq_of_toNat_eq
  unfold zext BitVec.zeroExtend
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hu : u % ((2 ^ m : Nat) : Int) = u := by
    rw [show (((2 ^ m : Nat)) : Int) = (2 : Int) ^ m from (Int.natCast_pow 2 m).symm]
    exact Int.emod_eq_of_lt Hu.1 Hu.2
  have h64 : (u % ((2 ^ 64 : Nat) : Int)).toNat = u.toNat % 2 ^ 64 := by
    rw [Int.toNat_emod Hu.1 (by have h := natCast_two_pow_pos 64; omega), Int.toNat_natCast]
  rw [hu, h64]

/-! ### The literal-offset split and the shifted bound -/

/-- Shifting an interval inside `[0, 2^64)` that already contains
    `(x + c') mod 2^64` down/up by `c - c'`. -/
theorem shifted_bound (x c c' lo hi : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64)
    (H : lo ≤ (x + c') % 2 ^ 64 ∧ (x + c') % 2 ^ 64 ≤ hi)
    (L0 : 0 ≤ lo) (LH : lo ≤ hi) (H64 : hi < 2 ^ 64)
    (D0 : 0 ≤ lo + (c - c')) (D64 : hi + (c - c') < 2 ^ 64) :
    lo + (c - c') ≤ (x + c) % 2 ^ 64 ∧ (x + c) % 2 ^ 64 ≤ hi + (c - c') := by
  have hsplit : (x + c) % 2 ^ 64 = ((x + c') % 2 ^ 64 + (c - c')) % 2 ^ 64 := by
    rw [show x + c = (x + c') + (c - c') from by omega,
      ← Int.emod_add_emod (x + c') ((2 : Int) ^ 64) (c - c')]
  have h1 : 0 ≤ (x + c') % 2 ^ 64 + (c - c') := by omega
  have h2 : (x + c') % 2 ^ 64 + (c - c') < (2 : Int) ^ 64 := by omega
  rw [hsplit, Int.emod_eq_of_lt h1 h2]
  omega

/-- The literal offset split: `lit_strip e = (v, c)` says that `e` denotes
    `v` plus the literal `c`, modulo 2^64. -/
theorem lit_strip_val (E : env) (e v : expr) (c : Int)
    (H : lit_strip e = (v, c)) :
    bv_unsigned (edenot E e) = (bv_unsigned (edenot E v) + c) % 2 ^ 64 := by
  have hD : (v = e ∧ c = 0) ∨ e = .EAlu .ADD v (.ELit c) := by
    cases e with
    | ELit z => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EVar n => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EAlu op a b =>
      cases op with
      | ADD =>
        cases b with
        | ELit z => right; simp only [lit_strip, Prod.mk.injEq] at H; rw [H.1, H.2]
        | EVar n => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EAlu o a' b' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EAluw o a' b' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EMd o a' b' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EMdw o a' b' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EExt sx lo n a' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
        | EBlob sx k i n => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SUB => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | AND => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | OR => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | XOR => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SLT => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SLTU => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SLL => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SRL => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
      | SRA => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EAluw op a b => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EMd op a b => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EMdw op a b => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EExt sx lo n e' => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
    | EBlob sx k i n => left; simp only [lit_strip, Prod.mk.injEq] at H; exact ⟨H.1.symm, H.2.symm⟩
  rcases hD with ⟨rfl, rfl⟩ | rfl
  · rw [Int.add_zero, Int.emod_eq_of_lt (u64_range _).1 (u64_range _).2]
  · show bv_unsigned (edenot E (.EAlu .ADD v (.ELit c)))
      = (bv_unsigned (edenot E v) + c) % 2 ^ 64
    rw [show edenot E (.EAlu .ADD v (.ELit c))
          = v_add (edenot E v) (edenot E (.ELit c)) from alu_add _ _]
    rw [show edenot E (.ELit c) = Z_to_bv 64 c from edenot_lit E c]
    show (bv_unsigned (edenot E v) + bv_unsigned (Z_to_bv 64 c)) % 2 ^ 64 = _
    rw [u_lit64a, Int.add_emod_emod]

/-- Shift a lookup's accumulator by one side condition (the `RUnknown`
    hint step of `log_lookup_acc`). -/
theorem acc_shift (acc : List sidecond) (s : sidecond) (res : lres) :
    (match res with
     | .LHit _ scs _ => ∃ pre, scs = pre ++ (s :: acc)
     | .LMiss scs _ => ∃ pre, scs = pre ++ (s :: acc)
     | .LStuck => True) →
    (match res with
     | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
     | .LMiss scs _ => ∃ pre, scs = pre ++ acc
     | .LStuck => True) := by
  cases res with
  | LHit v scs h =>
    intro hpre
    obtain ⟨pre, hp⟩ := hpre
    exact ⟨pre ++ [s], by rw [hp, List.append_assoc]; rfl⟩
  | LMiss scs h =>
    intro hpre
    obtain ⟨pre, hp⟩ := hpre
    exact ⟨pre ++ [s], by rw [hp, List.append_assoc]; rfl⟩
  | LStuck => intro _; exact trivial

/-- Accumulator monotonicity of the lookups: the side conditions a lookup
    returns are its accumulator with a prefix in front.   -/
theorem log_lookup_acc (kn : List kentry) (log : List sentry) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) :
    ∀ (hints : List Bool) (acc : List sidecond),
      (match log_lookup kn log rb rk n sx hints acc with
       | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
       | .LMiss scs _ => ∃ pre, scs = pre ++ acc
       | .LStuck => True) := by
  induction log with
  | nil =>
    intro hints acc
    exact ⟨[], by simp [log_lookup]⟩
  | cons hd rest ih =>
    intro hints acc
    obtain ⟨⟨kb, kk⟩, w, v⟩ := hd
    simp only [log_lookup]
    cases hrel : rel_lit rb rk (n : Int) kb kk (w : Int) with
    | RInside d =>
      exact ⟨[], by simp⟩
    | RDisjoint =>
      simpa using ih hints acc
    | RPartial =>
      cases hbl : log_bytes_lit (_ :: rest) rb rk n with
      | none => exact trivial
      | some bs => exact ⟨[], by simp [hbl]⟩
    | RUnknown =>
      cases hra : ranges_apart kn rb rk (n : Int) kb kk (w : Int) with
      | true =>
        simpa using ih hints acc
      | false =>
        cases hints with
        | nil =>
          exact acc_shift acc (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w))
            _ (ih [] (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc))
        | cons b bs =>
          cases b with
          | false => exact trivial
          | true =>
            exact acc_shift acc (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w))
              _ (ih bs (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc))

/-- **`find_range` is sound**: whatever interval a `KRange` fact (possibly
    shifted by a literal offset) bounds `e`, contains the denotation.
 -/
theorem find_range_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo hi : Int)
    (Hkn : know_ok segs E M kn) (H : find_range kn e = some (lo, hi)) :
    lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
  induction kn generalizing lo hi with
  | nil => simp [find_range] at H
  | cons K rest ih =>
    have HK : kentry_ok segs E M K := Hkn K (List.mem_cons_self ..)
    have Hrest : know_ok segs E M rest := fun K' h => Hkn K' (List.mem_cons_of_mem _ h)
    cases K with
    | KRange e' lo' hi' =>
      have HK' : lo' ≤ bv_unsigned (edenot E e') ∧ bv_unsigned (edenot E e') ≤ hi' := HK
      simp only [find_range] at H
      by_cases heq : expr_eqb e e' = true
      · rw [ite_eq_left heq] at H
        simp only [Option.some.injEq, Prod.mk.injEq] at H
        obtain ⟨hlo, hhi⟩ := H
        have he : e = e' := expr_eqb_eq e e' heq
        rw [← hlo, ← hhi, he]
        exact HK'
      · rw [ite_eq_right heq] at H
        obtain ⟨v', c', Hs'⟩ : ∃ v' c', lit_strip e' = (v', c') :=
          ⟨(lit_strip e').1, (lit_strip e').2, rfl⟩
        simp only [Hs'] at H
        have GO : ∀ (v : expr) (c : Int), lit_strip e = (v, c) →
            (if expr_eqb v v' then
               (if (0 ≤ lo' && lo' ≤ hi' && hi' < 2 ^ 64
                    && 0 ≤ lo' + (c - c') && hi' + (c - c') < 2 ^ 64)
                then some (lo' + (c - c'), hi' + (c - c')) else find_range rest e)
             else find_range rest e) = some (lo, hi) →
            lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
          intro v c Hs H0
          by_cases hv : expr_eqb v v' = true
          · rw [ite_eq_left hv] at H0
            split at H0
            · rename_i hcond
              have H0' := Option.some.inj H0
              have hlo : lo' + (c - c') = lo := by simpa using congrArg Prod.fst H0'
              have hhi : hi' + (c - c') = hi := by simpa using congrArg Prod.snd H0'
              rw [← hlo, ← hhi]
              obtain ⟨hA, hD64⟩ := (Bool.and_eq_true ..).mp hcond
              obtain ⟨hB, hD0⟩ := (Bool.and_eq_true ..).mp hA
              obtain ⟨hC, hH64⟩ := (Bool.and_eq_true ..).mp hB
              obtain ⟨hL0, hLH⟩ := (Bool.and_eq_true ..).mp hC
              have hvv : v = v' := expr_eqb_eq v v' hv
              have V1 := lit_strip_val E e v c Hs
              have V2 := lit_strip_val E e' v' c' Hs'
              have hbv : bv_unsigned (edenot E v') = bv_unsigned (edenot E v) := by rw [hvv]
              rw [hbv] at V2
              obtain ⟨HK1, HK2⟩ := HK'
              rw [V2] at HK1 HK2
              rw [V1]
              exact shifted_bound (bv_unsigned (edenot E v)) c c' lo' hi'
                ⟨(u64_range _).1, (u64_range _).2⟩ ⟨HK1, HK2⟩
                (of_decide_eq_true hL0) (of_decide_eq_true hLH) (of_decide_eq_true hH64)
                (of_decide_eq_true hD0) (of_decide_eq_true hD64)
            · exact ih lo hi Hrest H0
          · rw [ite_eq_right hv] at H0
            exact ih lo hi Hrest H0
        cases e with
        | ELit z => exact ih lo hi Hrest H
        | EVar n => exact GO _ _ rfl H
        | EAlu o a b => cases o <;> cases b <;> exact GO _ _ rfl H
        | EAluw o a b => exact GO _ _ rfl H
        | EMd o a b => exact GO _ _ rfl H
        | EMdw o a b => exact GO _ _ rfl H
        | EExt sx l n a => exact GO _ _ rfl H
        | EBlob sx k i n => exact GO _ _ rfl H
    | KWord a w v => exact ih lo hi Hrest H
    | KZero a n => exact ih lo hi Hrest H
    | KBlob a n k => exact ih lo hi Hrest H
    | KImg l h => exact ih lo hi Hrest H
    | KAlign e m => exact ih lo hi Hrest H
    | KWr a n => exact ih lo hi Hrest H
    | KDisj a1 n1 a2 n2 => exact ih lo hi Hrest H
    | KFill a n c => exact ih lo hi Hrest H
    | KUnk a n => exact ih lo hi Hrest H

/-! ## The `u_*` compute block

    Value lemmas for the ISA operations, used by `erange_sound`. -/
theorem two64_eq : two64 = (2 : Int) ^ 64 := rfl

/-- `u_lit64` (this tree's `u_lit64a`, restated at `two64`). -/
theorem u_lit64 (z : Int) : bv_unsigned (Z_to_bv 64 z) = z % two64 := u_lit64a z
theorem u_small_id (t : Int) (H : 0 ≤ t ∧ t < 2 ^ 64) : t % two64 = t := by
  rw [two64_eq]
  exact Int.emod_eq_of_lt H.1 H.2
theorem mod_wrap_hi (t : Int) (H : (2 : Int) ^ 64 ≤ t ∧ t < 2 ^ 64 + 2 ^ 64) :
    t % (2 : Int) ^ 64 = t - (2 : Int) ^ 64 := by
  have h1 : 0 ≤ t - (2 : Int) ^ 64 := by omega
  have h2 : t - (2 : Int) ^ 64 < (2 : Int) ^ 64 := by omega
  have ht : t = (t - (2 : Int) ^ 64) + 1 * ((2 : Int) ^ 64) := by
    rw [Int.one_mul]; omega
  rw [ht, Int.add_mul_emod_self_right, Int.one_mul, Int.emod_eq_of_lt h1 h2]
  omega
theorem mod32_of_mod64 (z : Int) : z % 64 % 32 = z % 32 :=
  Int.emod_emod_of_dvd z (m := 32) (k := 64) ⟨2, by rfl⟩
theorem swrap32_small (t : Int) (Ht : 0 ≤ t ∧ t < 2 ^ 31) : bv_swrap 32 t = t := by
  unfold bv_swrap
  rw [show ((2 ^ (32 - 1) : Nat) : Int) = ((2 ^ 31 : Nat) : Int) from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega
theorem swrap32_shift (t k : Int) : bv_swrap 32 (t + k * (2 : Int) ^ 32) = bv_swrap 32 t := by
  unfold bv_swrap
  rw [show t + k * (2 : Int) ^ 32 + ((2 ^ 31 : Nat) : Int)
      = (t + ((2 ^ 31 : Nat) : Int)) + k * ((2 ^ 32 : Nat) : Int) from by
        rw [Int.natCast_pow]; omega,
    Int.add_mul_emod_self_right]
theorem clampi_sound (v : word) (lo hi lo' hi' : Int)
    (H : lo ≤ bv_unsigned v ∧ bv_unsigned v ≤ hi)
    (Hc : clampi (lo, hi) = (lo', hi')) :
    lo' ≤ bv_unsigned v ∧ bv_unsigned v ≤ hi' := by
  unfold clampi at Hc
  simp only at Hc
  injection Hc with h1 h2
  rw [← h1, ← h2]
  obtain ⟨hlo, hhi⟩ := H
  obtain ⟨hv1, hv2⟩ := u64_range v
  constructor
  · exact Int.max_le.mpr ⟨hlo, hv1⟩
  · refine Int.le_min.mpr ⟨hhi, ?_⟩
    show (v.toNat : Int) ≤ two64 - 1
    unfold two64
    have hone : (1 : Int) ≤ (2 : Int) ^ 64 := by have := two_pow_pos_int 64; omega
    omega
theorem lit_shamt_sound (E : env) (b : expr) (s : Int) (H : lit_shamt b = some s) :
    bv_unsigned (edenot E b) % 64 = s ∧ 0 ≤ s ∧ s < 64 := by
  cases b with
  | ELit z =>
    simp only [lit_shamt, Option.some.injEq] at H
    subst H
    have hpos : (0 : Int) < 64 := by decide
    have hne : (64 : Int) ≠ 0 := by decide
    refine ⟨?_, Int.emod_nonneg z hne, Int.emod_lt_of_pos z hpos⟩
    rw [edenot_lit, u_lit64a]
    exact Int.emod_emod_of_dvd z (m := 64) (k := (2 : Int) ^ 64) ⟨(2 : Int) ^ 58, by decide⟩
  | EVar n =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EAlu o a b =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EAluw o a b =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EMd o a b =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EMdw o a b =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EExt sx l n a =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)
  | EBlob sx k i n =>
    simp only [lit_shamt] at H
    exact absurd H (by simp)

/-! ### Local glue for the compute block

    The `Nat`/`Int` shift-mask bridge, the `2^k` natural-cast bridge, and
    `bv_swrap_small`, which had to be added. -/

/-- The 64-bit shift mask as a `Nat` (the `sh` of `alu` at `n = 64`). -/
theorem shiftmask64 (y : word) :
    (y &&& BitVec.ofInt 64 63).toNat = y.toNat % 64 := by
  rw [BitVec.toNat_and]
  have h63 : (BitVec.ofInt 64 63).toNat = 63 := by decide
  rw [h63, show (63 : Nat) = 2 ^ 6 - 1 from by decide]
  exact Nat.and_two_pow_sub_one_eq_mod y.toNat 6

/-- The `64` in a shift amount, read back as a `Nat`. -/
theorem emod64_toNat_eq (y : word) : (bv_unsigned y % 64).toNat = y.toNat % 64 := by
  have h : bv_unsigned y % 64 = ((y.toNat % 64 : Nat) : Int) := by
    unfold bv_unsigned
    exact (Int.natCast_emod y.toNat 64).symm
  rw [h, Int.toNat_natCast]

/-- `2 ^ k` as a natural cast (the shape `zshiftl`/`zshiftr` produce). -/
theorem natCast_pow_two (k : Nat) : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) :=
  (Int.natCast_pow 2 k).symm

/-- A 31-bit value is a 64-bit value. -/
theorem two_pow31_lt_two64 (t : Int) (h : t < 2 ^ 31) : t < 2 ^ 64 :=
  Int.lt_of_lt_of_le h (int_pow_le_pow 31 64 (by decide))

/-- The 32-bit shift amount from the 64-bit one (`mod32_of_mod64`). -/
theorem shamt32_eq (y : word) (s : Int) (Hs : bv_unsigned y % 64 = s) :
    y.toNat % 32 = (s % 32).toNat := by
  have h1 : ((y.toNat % 32 : Nat) : Int) = (y.toNat : Int) % 32 := Int.natCast_emod _ _
  have h3 : ((y.toNat % 32 : Nat) : Int) = s % 32 := by
    rw [h1, ← mod32_of_mod64, Hs]
  have h4 : 0 ≤ s % 32 := Int.emod_nonneg _ (by decide)
  have h5 : ((y.toNat % 32 : Nat) : Int) = (((s % 32).toNat : Nat) : Int) := by
    rw [h3, Int.toNat_of_nonneg h4]
  exact Int.ofNat_inj.mp h5

/-- `2 ^ (n-1)` is half of `2 ^ n` (`n >= 1`). -/
theorem two_pow_half (n : Nat) (hn : 1 ≤ n) :
    ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
  have hn1 : n = (n - 1) + 1 := by omega
  rw [hn1, Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
  rfl

/-- `bv_swrap_small`: a value below the half modulus is fixed (at the
    bound `1 <= n`, the same `bv_swrap`-at-`0` deviation as `extz_0`). -/
theorem bv_swrap_small (n : Nat) (hn : 1 ≤ n) (z : Int)
    (h : 0 ≤ z ∧ z < ((2 ^ (n - 1) : Nat) : Int)) : bv_swrap n z = z := by
  unfold bv_swrap
  rw [two_pow_half n hn,
    Int.emod_eq_of_lt (by have := natCast_two_pow_pos (n - 1); omega)
      (by have := natCast_two_pow_pos (n - 1); omega)]
  omega

/-- `a mod b <= a` for `a >= 0`, `b > 0` (`Z.mod_le`). -/
theorem emod_le_self (a : Int) (b : Int) (h : 0 ≤ a) (hb : 0 < b) : a % b ≤ a := by
  have hq : 0 ≤ a / b := Int.ediv_nonneg h (Int.le_of_lt hb)
  have hq' : 0 ≤ a / b * b := Int.mul_nonneg hq (Int.le_of_lt hb)
  have he : a / b * b + a % b = a := Int.ediv_mul_add_emod a b
  omega

/-- `2 ^ k != 0`. -/
theorem two_pow_ne (k : Nat) : (2 : Int) ^ k ≠ 0 := by
  have h := two_pow_pos_int k
  intro h0
  rw [h0] at h
  exact (Int.lt_irrefl 0) h

/-- `two64 != 0`. -/
theorem two64_ne : two64 ≠ 0 := by
  rw [two64_eq]
  exact two_pow_ne 64

/-- `two64 > 0`. -/
theorem two64_pos : (0 : Int) < two64 := by
  rw [two64_eq]
  exact two_pow_pos_int 64

/-! ### The 64-bit ALU value lemmas -/
theorem u_and64 (x y : word) :
    bv_unsigned (alu64 .AND x y) = AxSymExec3.zland (bv_unsigned x) (bv_unsigned y) := by
  show bv_unsigned (x &&& y) = _
  have hx : bv_unsigned x % two64 = bv_unsigned x :=
    u_small_id _ ⟨(u64_range x).1, (u64_range x).2⟩
  have hy : bv_unsigned y % two64 = bv_unsigned y :=
    u_small_id _ ⟨(u64_range y).1, (u64_range y).2⟩
  unfold bv_unsigned AxSymExec3.zland
  rw [hx, hy, BitVec.toNat_and]
  simp
theorem u_or64 (x y : word) :
    bv_unsigned (alu64 .OR x y) = AxSymExec3.zlor (bv_unsigned x) (bv_unsigned y) := by
  show bv_unsigned (x ||| y) = _
  have hx : bv_unsigned x % two64 = bv_unsigned x :=
    u_small_id _ ⟨(u64_range x).1, (u64_range x).2⟩
  have hy : bv_unsigned y % two64 = bv_unsigned y :=
    u_small_id _ ⟨(u64_range y).1, (u64_range y).2⟩
  unfold bv_unsigned AxSymExec3.zlor
  rw [hx, hy, BitVec.toNat_or]
  simp
theorem u_xor64 (x y : word) :
    bv_unsigned (alu64 .XOR x y) = AxSymExec3.zlxor (bv_unsigned x) (bv_unsigned y) := by
  show bv_unsigned (x ^^^ y) = _
  have hx : bv_unsigned x % two64 = bv_unsigned x :=
    u_small_id _ ⟨(u64_range x).1, (u64_range x).2⟩
  have hy : bv_unsigned y % two64 = bv_unsigned y :=
    u_small_id _ ⟨(u64_range y).1, (u64_range y).2⟩
  unfold bv_unsigned AxSymExec3.zlxor
  rw [hx, hy, BitVec.toNat_xor]
  simp
theorem u_sltu64 (x y : word) :
    bv_unsigned (alu64 .SLTU x y) = if bv_ltu x y then 1 else 0 := by
  show bv_unsigned (if bv_ltu x y then BitVec.ofInt 64 1 else BitVec.ofInt 64 0) = _
  by_cases h : bv_ltu x y = true
  · rw [ite_eq_left h, ite_eq_left h]
    decide
  · rw [ite_eq_right h, ite_eq_right h]
    decide
theorem u_slt64 (x y : word) :
    bv_unsigned (alu64 .SLT x y) = if bv_lts x y then 1 else 0 := by
  show bv_unsigned (if bv_lts x y then BitVec.ofInt 64 1 else BitVec.ofInt 64 0) = _
  by_cases h : bv_lts x y = true
  · rw [ite_eq_left h, ite_eq_left h]
    decide
  · rw [ite_eq_right h, ite_eq_right h]
    decide
theorem u_srl64 (x y : word) :
    bv_unsigned (alu64 .SRL x y) = bv_unsigned x / 2 ^ (bv_unsigned y % 64).toNat := by
  rw [emod64_toNat_eq]
  show bv_unsigned (x >>> (y &&& BitVec.ofInt 64 63).toNat) = _
  unfold bv_unsigned
  rw [shiftmask64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_ediv,
    Int.natCast_pow]
  simp
theorem u_sra64_nonneg (x y : word) (Hx : bv_unsigned x < 2 ^ 63) :
    bv_unsigned (alu64 .SRA x y) = bv_unsigned x / 2 ^ (bv_unsigned y % 64).toNat := by
  rw [emod64_toNat_eq]
  have hx63 : x.toNat < 2 ^ 63 := by
    have h := Hx
    unfold bv_unsigned at h
    omega
  have hxi : x.toInt = (x.toNat : Int) := bv_signed_small x hx63
  show bv_unsigned (x.sshiftRight (y &&& BitVec.ofInt 64 63).toNat) = _
  unfold bv_unsigned
  rw [shiftmask64]
  show ((BitVec.ofInt 64 (x.toInt >>> (y.toNat % 64))).toNat : Int) = _
  rw [BitVec.toNat_ofInt, hxi, Int.shiftRight_eq_div_pow, natCast_pow_two, ← Int.natCast_ediv]
  have hnlt : x.toNat / 2 ^ (y.toNat % 64) < 2 ^ 64 := by
    have h1 : x.toNat / 2 ^ (y.toNat % 64) ≤ x.toNat := Nat.div_le_self _ _
    omega
  have hlt : ((x.toNat / 2 ^ (y.toNat % 64) : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [Int.ofNat_lt]
    exact hnlt
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt, Int.toNat_natCast]

/-! ### The 32-bit (`.w`) family -/
theorem u_addw_small (x y : word) (t : Int) (Ht : 0 ≤ t ∧ t < 2 ^ 31)
    (Hk : ∃ k : Int, bv_unsigned x + bv_unsigned y = t + k * (2 : Int) ^ 32) :
    bv_unsigned (sext 64 (alu32 .ADD (low32 x) (low32 y))) = t := by
  rw [w_addw]
  unfold v_addw
  obtain ⟨k, hk⟩ := Hk
  rw [hk, swrap32_shift, swrap32_small t Ht, u_lit64,
    u_small_id t ⟨Ht.1, two_pow31_lt_two64 t Ht.2⟩]
theorem u_subw_small (x y : word) (t : Int) (Ht : 0 ≤ t ∧ t < 2 ^ 31)
    (Hk : bv_unsigned x - bv_unsigned y = t) :
    bv_unsigned (sext 64 (alu32 .SUB (low32 x) (low32 y))) = t := by
  rw [w_subw]
  unfold v_subw
  rw [Hk, swrap32_small t Ht, u_lit64,
    u_small_id t ⟨Ht.1, two_pow31_lt_two64 t Ht.2⟩]
theorem u_sllw_small (x y : word) (s : Int) (Hs : bv_unsigned y % 64 = s)
    (Hb : bv_unsigned x * 2 ^ (s % 32).toNat < 2 ^ 31) :
    bv_unsigned (sext 64 (alu32 .SLL (low32 x) (low32 y)))
      = bv_unsigned x * 2 ^ (s % 32).toNat := by
  rw [w_sllw]
  unfold v_sllw PropExec.zshiftl
  rw [shamt32_eq y s Hs]
  simp only [← natCast_pow_two]
  have h0 : 0 ≤ bv_unsigned x * (2 : Int) ^ (s % 32).toNat :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.le_of_lt (two_pow_pos_int _))
  have hlt := two_pow31_lt_two64 _ Hb
  rw [swrap32_small _ ⟨h0, Hb⟩, u_lit64, u_small_id _ ⟨h0, hlt⟩]
theorem u_srlw_small (x y : word) (s : Int) (Hs : bv_unsigned y % 64 = s)
    (Hx : bv_unsigned x < 2 ^ 32) (Hb : bv_unsigned x / 2 ^ (s % 32).toNat < 2 ^ 31) :
    bv_unsigned (sext 64 (alu32 .SRL (low32 x) (low32 y)))
      = bv_unsigned x / 2 ^ (s % 32).toNat := by
  rw [w_srlw]
  unfold v_srlw PropExec.zshiftr bv_wrap
  rw [shamt32_eq y s Hs]
  simp only [← natCast_pow_two]
  have hxw : (x.toNat : Int) % (2 : Int) ^ 32 = (x.toNat : Int) := by
    apply Int.emod_eq_of_lt (by omega)
    simpa using Hx
  rw [hxw]
  have h0 : 0 ≤ bv_unsigned x / (2 : Int) ^ (s % 32).toNat :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (Int.le_of_lt (two_pow_pos_int _))
  have hlt := two_pow31_lt_two64 _ Hb
  rw [swrap32_small _ ⟨h0, Hb⟩, u_lit64, u_small_id _ ⟨h0, hlt⟩]
theorem u_sraw_small (x y : word) (s : Int) (Hs : bv_unsigned y % 64 = s)
    (Hx : bv_unsigned x < 2 ^ 31) :
    bv_unsigned (sext 64 (alu32 .SRA (low32 x) (low32 y)))
      = bv_unsigned x / 2 ^ (s % 32).toNat := by
  rw [w_sraw]
  unfold v_sraw PropExec.zshiftr
  rw [shamt32_eq y s Hs]
  simp only [← natCast_pow_two]
  have hx : bv_swrap 32 (x.toNat : Int) = (x.toNat : Int) := swrap32_small _ ⟨by omega, Hx⟩
  rw [hx]
  have h0 : 0 ≤ bv_unsigned x / (2 : Int) ^ (s % 32).toNat :=
    Int.ediv_nonneg (Int.natCast_nonneg _) (Int.le_of_lt (two_pow_pos_int _))
  have hle : bv_unsigned x / (2 : Int) ^ (s % 32).toNat ≤ bv_unsigned x :=
    Int.ediv_le_self _ (Int.natCast_nonneg _)
  have hlt := two_pow31_lt_two64 _ (Int.lt_of_le_of_lt hle Hx)
  rw [swrap32_small _ ⟨h0, Int.lt_of_le_of_lt hle Hx⟩, u_lit64, u_small_id _ ⟨h0, hlt⟩]

/-! ### Multiply-high and division -/
theorem u_mulhu64 (x y : word) :
    bv_unsigned (mul_div .MULHU x y) = bv_unsigned x * bv_unsigned y / 2 ^ 64 := by
  show bv_unsigned (bv_mulhuu x y) = _
  show bv_unsigned (BitVec.ofInt 64 (((x.toNat : Int) * (y.toNat : Int)) >>> 64)) = _
  unfold bv_unsigned
  rw [BitVec.toNat_ofInt, ← Int.natCast_mul, Int.shiftRight_eq_div_pow, natCast_pow_two,
    ← Int.natCast_ediv]
  have h2 : x.toNat < 2 ^ 64 := x.isLt
  have h3 : y.toNat < 2 ^ 64 := y.isLt
  have hprod : x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' h2 h3
  have h128 : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by
    rw [← Nat.pow_add]
  rw [h128] at hprod
  have hnlt : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
    have h1 : x.toNat * y.toNat / 2 ^ 64 ≤ x.toNat * y.toNat := Nat.div_le_self _ _
    omega
  have hlt : ((x.toNat * y.toNat / 2 ^ 64 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [Int.ofNat_lt]
    exact hnlt
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt, Int.toNat_natCast]
theorem u_divu64 (x y : word) (Hy : 0 < bv_unsigned y) :
    bv_unsigned (mul_div .DIVU x y) = bv_unsigned x / bv_unsigned y := by
  have hy0 : y.toNat ≠ 0 := by
    have h := Hy
    unfold bv_unsigned at h
    omega
  show bv_unsigned (if (y.toNat == 0) then BitVec.ofInt 64 (-1) else x.udiv y) = _
  rw [ite_eq_right (by simp [hy0])]
  have h : (x.udiv y).toNat = x.toNat / y.toNat := BitVec.toNat_udiv
  unfold bv_unsigned
  rw [h, Int.natCast_ediv]
theorem u_remu64 (x y : word) (Hy : 0 < bv_unsigned y) :
    bv_unsigned (mul_div .REMU x y) = bv_unsigned x % bv_unsigned y := by
  have hy0 : y.toNat ≠ 0 := by
    have h := Hy
    unfold bv_unsigned at h
    omega
  show bv_unsigned (if (y.toNat == 0) then x else x.umod y) = _
  rw [ite_eq_right (by simp [hy0])]
  have h : (x.umod y).toNat = x.toNat % y.toNat := BitVec.toNat_umod
  unfold bv_unsigned
  rw [h, Int.natCast_emod]

/-! ### Extension and byte-blob value bounds -/
theorem u_ext_zx (lo n : Nat) (v : word) :
    bv_unsigned (ext_val false lo n v) = bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n)
    ∧ bv_unsigned (ext_val false lo n v) ≤ 2 ^ (8 * n) - 1
    ∧ bv_unsigned (ext_val false lo n v) ≤ two64 - 1 := by
  have hv := u64_range v
  have hw : 0 < (2 : Int) ^ (8 * n) := two_pow_pos_int _
  have hq0 : 0 ≤ bv_unsigned v / 2 ^ (8 * lo) :=
    Int.ediv_nonneg hv.1 (Int.le_of_lt (two_pow_pos_int _))
  have hu0 : 0 ≤ bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n) :=
    Int.emod_nonneg _ (two_pow_ne (8 * n))
  have huq : bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n)
      ≤ bv_unsigned v / 2 ^ (8 * lo) := emod_le_self _ _ hq0 hw
  have hqle : bv_unsigned v / 2 ^ (8 * lo) ≤ bv_unsigned v := Int.ediv_le_self _ hv.1
  have hult : bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n) < two64 := by
    rw [two64_eq]
    exact Int.lt_of_le_of_lt huq (Int.lt_of_le_of_lt hqle hv.2)
  have hlit : bv_unsigned (ext_val false lo n v)
      = bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n) := by
    unfold ext_val ext_Z
    rw [ite_eq_right (by decide)]
    show bv_unsigned (Z_to_bv 64 (bv_unsigned v / 2 ^ (8 * lo) % 2 ^ (8 * n))) = _
    rw [u_lit64, Int.emod_eq_of_lt hu0 hult]
  refine ⟨hlit, ?_, ?_⟩
  · rw [hlit]
    exact Int.le_sub_one_of_lt
      (Int.emod_lt_of_pos (bv_unsigned v / 2 ^ (8 * lo)) hw)
  · rw [hlit]
    exact Int.le_sub_one_of_lt hult
theorem u_ext_zx0_small (n : Nat) (v : word) (Hv : bv_unsigned v < 2 ^ (8 * n)) :
    bv_unsigned (ext_val false 0 n v) = bv_unsigned v := by
  have hv := u64_range v
  have h := (u_ext_zx 0 n v).1
  simp only [Nat.mul_zero, Int.pow_zero, Int.ediv_one] at h
  rw [h]
  exact Int.emod_eq_of_lt hv.1 Hv
theorem u_ext_sx0_small (n : Nat) (v : word)
    (Hv : bv_unsigned v < 2 ^ (8 * n) / 2) :
    bv_unsigned (ext_val true 0 n v) = bv_unsigned v := by
  have hv := u64_range v
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at Hv
      have h0 : (2 : Int) ^ (8 * 0) / 2 = 0 := by decide
      rw [h0] at Hv
      have h1 := hv.1
      unfold bv_unsigned at Hv h1
      omega
    · exact h
  have h8 : 1 ≤ 8 * n := by omega
  have hhalf : (2 : Int) ^ (8 * n) / 2 = ((2 ^ (8 * n - 1) : Nat) : Int) := by
    rw [natCast_pow_two (8 * n), two_pow_half (8 * n) h8]
    rw [Int.mul_comm 2]
    exact Int.mul_ediv_cancel _ (b := 2) (by decide)
  have hmono : ((2 ^ (8 * n - 1) : Nat) : Int) ≤ (2 : Int) ^ (8 * n) := by
    rw [natCast_pow_two (8 * n)]
    exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  have hlt2 : bv_unsigned v < 2 ^ (8 * n) := by
    refine Int.lt_of_lt_of_le ?_ hmono
    rw [← hhalf]
    exact Hv
  have hmod : bv_unsigned v % 2 ^ (8 * n) = bv_unsigned v :=
    Int.emod_eq_of_lt hv.1 hlt2
  have hsw : bv_swrap (8 * n) (bv_unsigned v) = bv_unsigned v := by
    refine bv_swrap_small (8 * n) h8 _ ⟨hv.1, ?_⟩
    rw [← hhalf]
    exact Hv
  have hz : ext_Z true 0 n (bv_unsigned v) = bv_swrap (8 * n) (bv_unsigned v) := by
    unfold ext_Z
    rw [ite_eq_left rfl]
    simp only [Nat.mul_zero, Int.pow_zero, Int.ediv_one, hmod]
  unfold ext_val
  rw [hz, hsw, u_lit64, u_small_id _ ⟨hv.1, hv.2⟩]
theorem u_ext_sx0_high (n : Nat) (v : word)
    (Hv : 2 ^ (8 * n) / 2 ≤ bv_unsigned v ∧ bv_unsigned v < 2 ^ (8 * n))
    (Hn : 1 ≤ n ∧ n ≤ 8) :
    bv_unsigned (ext_val true 0 n v) = 2 ^ 64 - 2 ^ (8 * n) + bv_unsigned v := by
  have hv := u64_range v
  have h8 : 1 ≤ 8 * n := by omega
  have h64 : 8 * n ≤ 64 := by omega
  have hhalf : (2 : Int) ^ (8 * n) / 2 = ((2 ^ (8 * n - 1) : Nat) : Int) := by
    rw [natCast_pow_two (8 * n), two_pow_half (8 * n) h8]
    rw [Int.mul_comm 2]
    exact Int.mul_ediv_cancel _ (b := 2) (by decide)
  have hmod : bv_unsigned v % 2 ^ (8 * n) = bv_unsigned v :=
    Int.emod_eq_of_lt hv.1 Hv.2
  have hsw : bv_swrap (8 * n) (bv_unsigned v) = bv_unsigned v - 2 ^ (8 * n) := by
    refine bv_swrap_hi (8 * n) _ (by omega) ?_ ?_
    · rw [← hhalf]
      exact Hv.1
    · rw [← natCast_pow_two (8 * n)]
      exact Hv.2
  have hz : ext_Z true 0 n (bv_unsigned v) = bv_swrap (8 * n) (bv_unsigned v) := by
    unfold ext_Z
    rw [ite_eq_left rfl]
    simp only [Nat.mul_zero, Int.pow_zero, Int.ediv_one, hmod]
  unfold ext_val
  rw [hz, hsw, u_lit64]
  have hlt : bv_unsigned v - 2 ^ (8 * n) < 0 := by omega
  have hge : -((2 : Int) ^ 64) ≤ bv_unsigned v - 2 ^ (8 * n) := by
    have hle : (2 : Int) ^ (8 * n) ≤ (2 : Int) ^ 64 := int_pow_le_pow _ _ h64
    omega
  rw [show two64 = (2 : Int) ^ 64 from rfl, mod_wrap_neg _ hge hlt]
  omega
theorem u_blob_zx (bs : List byte) (i : Int) (n : Nat) :
    bv_unsigned (blob_val false bs i n) ≤ 2 ^ (8 * n) - 1
    ∧ bv_unsigned (blob_val false bs i n) ≤ two64 - 1 := by
  have hb := bytes_le_to_Z_bound (blob_bytes bs i n)
  have hlen : (blob_bytes bs i n).length ≤ n := by
    unfold blob_bytes
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have hpow : (2 : Int) ^ (8 * (blob_bytes bs i n).length) ≤ (2 : Int) ^ (8 * n) :=
    int_pow_le_pow _ _ (by omega)
  have hzlt : bytes_le_to_Z (blob_bytes bs i n) < (2 : Int) ^ (8 * n) :=
    Int.lt_of_lt_of_le hb.2 hpow
  have hlit : bv_unsigned (blob_val false bs i n)
      = bytes_le_to_Z (blob_bytes bs i n) % two64 := by
    unfold blob_val
    rw [ite_eq_right (by decide)]
    show bv_unsigned (Z_to_bv 64 (bytes_le_to_Z (blob_bytes bs i n))) = _
    rw [u_lit64]
  rw [hlit]
  constructor
  · refine Int.le_trans ?_ (Int.le_sub_one_of_lt hzlt)
    exact emod_le_self _ _ hb.1 two64_pos
  · exact Int.le_sub_one_of_lt
      (Int.emod_lt_of_pos (bytes_le_to_Z (blob_bytes bs i n)) two64_pos)

/-! ### Signed extension at a literal, and the value of a load
 -/

/-- `Int.bmod` at `2 ^ m` is the signed wrap .
    `1 ≤ m` — `bv_swrap 0` differs from `bmod` at width `0`
    (the same deviation `extz_0` records). -/
theorem bmod_eq_swrap (m : Nat) (hm : 1 ≤ m) (u : Int)
    (hu : 0 ≤ u ∧ u < ((2 ^ m : Nat) : Int)) : u.bmod (2 ^ m) = bv_swrap m u := by
  have hh : ((2 ^ m : Nat) : Int) = 2 * ((2 ^ (m - 1) : Nat) : Int) := two_pow_half m hm
  have hhalf : (((2 ^ m : Nat) : Int) + 1) / 2 = ((2 ^ (m - 1) : Nat) : Int) := by
    rw [hh]
    omega
  have hmod : u % ((2 ^ m : Nat) : Int) = u := Int.emod_eq_of_lt hu.1 hu.2
  rw [Int.bmod_def, hmod, hhalf]
  unfold bv_swrap
  rw [hh]
  by_cases h : u < ((2 ^ (m - 1) : Nat) : Int)
  · rw [ite_eq_left h]
    rw [Int.emod_eq_of_lt (by have := natCast_two_pow_pos (m - 1); omega)
      (by have := natCast_two_pow_pos (m - 1); omega)]
    omega
  · rw [ite_eq_right h]
    rw [show u + ((2 ^ (m - 1) : Nat) : Int)
        = (u - ((2 ^ (m - 1) : Nat) : Int)) + 2 * ((2 ^ (m - 1) : Nat) : Int) from by omega]
    rw [Int.add_emod_right,
      Int.emod_eq_of_lt (by omega) (by have := natCast_two_pow_pos (m - 1); omega)]
    omega

/-- `sext64_small`.  `1 ≤ m`, the documented
    `bv_swrap`-at-`0` deviation. -/
theorem sext64_small (m : Nat) (u : Int) (Hm : m ≤ 64) (Hm1 : 1 ≤ m)
    (Hu : 0 ≤ u ∧ u < 2 ^ m) :
    sext 64 (Z_to_bv m u) = Z_to_bv 64 (bv_swrap m u) := by
  rw [SymExec.sext64_lit _ Hm]
  have hu' : 0 ≤ u ∧ u < ((2 ^ m : Nat) : Int) := by
    refine ⟨Hu.1, ?_⟩
    rw [Int.natCast_pow]
    exact Hu.2
  rw [BitVec.toInt_ofInt, bmod_eq_swrap m Hm1 u hu']

/-- `load_result_val`: the value a load writes back is the
    signed/zero extension of the little-endian reading of its bytes. -/
theorem load_result_val (sz : MSize) (sx : Bool) (bs : List byte)
    (Hlen : bs.length = SymStepR.msize_bytes sz) :
    load_result sz sx bs
      = Z_to_bv 64 (extz (eff_sx sz sx) (SymStepR.msize_bytes sz) (bytes_le_to_Z bs)) := by
  have hb := bytes_le_to_Z_bound bs
  cases sz with
  | SZ1 =>
    have hl : bs.length = 1 := Hlen
    have hlt : bytes_le_to_Z bs < (2 : Int) ^ 8 := by
      rw [hl] at hb
      exact hb.2
    cases sx with
    | true =>
      show sext 64 (bits 0 8 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 8 _ (by decide),
        sext64_small 8 _ (by decide) (by decide) ⟨hb.1, hlt⟩]
      simp
    | false =>
      show zext 64 (bits 0 8 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 8 _ (by decide),
        zext64_small 8 _ (by decide) ⟨hb.1, hlt⟩]
      simp
  | SZ2 =>
    have hl : bs.length = 2 := Hlen
    have hlt : bytes_le_to_Z bs < (2 : Int) ^ 16 := by
      rw [hl] at hb
      exact hb.2
    cases sx with
    | true =>
      show sext 64 (bits 0 16 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 16 _ (by decide),
        sext64_small 16 _ (by decide) (by decide) ⟨hb.1, hlt⟩]
      simp
    | false =>
      show zext 64 (bits 0 16 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 16 _ (by decide),
        zext64_small 16 _ (by decide) ⟨hb.1, hlt⟩]
      simp
  | SZ4 =>
    have hl : bs.length = 4 := Hlen
    have hlt : bytes_le_to_Z bs < (2 : Int) ^ 32 := by
      rw [hl] at hb
      exact hb.2
    cases sx with
    | true =>
      show sext 64 (bits 0 32 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 32 _ (by decide),
        sext64_small 32 _ (by decide) (by decide) ⟨hb.1, hlt⟩]
      simp
    | false =>
      show zext 64 (bits 0 32 (le_bytes_to_word bs)) = _
      simp only [SymStepR.msize_bytes, eff_sx, extz]
      rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
        extract0_Z_to_bv64 32 _ (by decide),
        zext64_small 32 _ (by decide) ⟨hb.1, hlt⟩]
      simp
  | SZ8 =>
    have hl : bs.length = 8 := Hlen
    have hlt : bytes_le_to_Z bs < (2 : Int) ^ 64 := by
      rw [hl] at hb
      exact hb.2
    show bits 0 64 (le_bytes_to_word bs) = _
    simp only [SymStepR.msize_bytes, eff_sx, extz]
    rw [show le_bytes_to_word bs = Z_to_bv 64 (bytes_le_to_Z bs) from rfl,
      extract0_Z_to_bv64 64 _ (by decide)]
    simp

/-!  This tree's `zlor`
    truncates at 64 bits, so the identity holds modulo `two64` — which is
    all any call site needs (`extz`/`Z_to_bv 64` truncate anyway). -/

/-- `2 ^ 64 = 2 ^ 56 * 256`, for the Nat-level shift/mod bridge. -/
theorem two_pow_split64 : (2 : Nat) ^ 64 = 2 ^ 56 * 256 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]

/-- `two64` as the natural cast of `2 ^ 64`. -/
theorem two64_eq_natCast : two64 = ((2 ^ 64 : Nat) : Int) := by
  rw [two64_eq]
  exact (Int.natCast_pow 2 64).symm

/-- The Nat-level bit bridge: OR-ing a byte with the low 64 bits of a
    shifted byte string is the same as adding it (the low byte of the
    shifted part is zero, so the OR does not carry). -/
theorem or_shift256_mod (b n : Nat) (hb : b < 2 ^ 8) :
    b ||| (n * 256 % 2 ^ 64) = (b + n * 256) % 2 ^ 64 := by
  have hX : n * 256 % 2 ^ 64 = ((n % 2 ^ 56) * 256) := by
    rw [two_pow_split64, Nat.mul_mod_mul_right]
  rw [hX]
  have hshift : (n % 2 ^ 56) * 256 = (n % 2 ^ 56) <<< 8 := by
    rw [Nat.shiftLeft_eq]
  rw [hshift, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb, Nat.shiftLeft_eq]
  have hbnd : (n % 2 ^ 56) * 256 + b < 2 ^ 64 := by
    have h1 : n % 2 ^ 56 < 2 ^ 56 := Nat.mod_lt _ (by decide)
    have h2 : (2 : Nat) ^ 56 * 256 = 2 ^ 64 := two_pow_split64.symm
    omega
  have hb64 : b < 2 ^ 64 := by
    have h1 : (2 : Nat) ^ 8 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  rw [Nat.add_mod b (n * 256) (2 ^ 64), hX, Nat.mod_eq_of_lt hb64,
    Nat.add_comm b ((n % 2 ^ 56) * 256), Nat.mod_eq_of_lt hbnd]

/-- The shifted accumulator, truncated at 64 bits, read back as a `Nat`. -/
theorem toNat_emod_mul256 (n : Nat) :
    (((((n : Int) % two64) * 256) % two64)).toNat = (n * 256) % 2 ^ 64 := by
  have h1 : ((n : Int) % two64) = ((n % 2 ^ 64 : Nat) : Int) := by
    rw [two64_eq_natCast]
    exact (Int.natCast_emod n (2 ^ 64)).symm
  rw [h1, show (256 : Int) = ((256 : Nat) : Int) from rfl, ← Int.natCast_mul,
    two64_eq_natCast,
    Int.toNat_emod (Int.natCast_nonneg _) (Int.natCast_nonneg _), Int.toNat_natCast,
    Int.toNat_natCast]
  rw [two_pow_split64, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right,
    Nat.mod_mod_of_dvd n (by decide : (2 : Nat) ^ 56 ∣ 2 ^ 56 * 256)]

/-- `zbytes_map`, modulo this tree's 64-bit truncation. -/
theorem zbytes_map (bs : List byte) :
    zbytes_le_to_Z (bs.map (fun b => bv_unsigned b)) = bytes_le_to_Z bs % two64 := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb8 : b.toNat < 2 ^ 8 := b.isLt
    have hb64 : b.toNat < 2 ^ 64 := by
      have hle : (2 ^ 8 : Nat) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
      omega
    have hbmod : (((b.toNat : Int)) % two64).toNat = b.toNat := by
      rw [two64_eq_natCast, Int.toNat_emod (by omega) (Int.natCast_nonneg _)]
      simp only [Int.toNat_natCast]
      exact Nat.mod_eq_of_lt hb64
    have hz : AxSymExec3.zshiftl ((bytes_le_to_Nat rest : Int) % two64) 8
        = ((bytes_le_to_Nat rest : Int) % two64) * 256 := by
      unfold AxSymExec3.zshiftl
      rw [show (2 : Int) ^ 8 = 256 from by decide]
    have hor : (b.toNat ||| (bytes_le_to_Nat rest <<< 8) : Nat)
        = b.toNat + bytes_le_to_Nat rest * 256 := by
      have h := Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb8 (bytes_le_to_Nat rest)
      rw [Nat.shiftLeft_eq] at h
      rw [Nat.shiftLeft_eq, Nat.or_comm, ← h, Nat.add_comm]
    show AxSymExec3.zlor (bv_unsigned b)
      (AxSymExec3.zshiftl (zbytes_le_to_Z (rest.map (fun b => bv_unsigned b))) 8)
      = bytes_le_to_Z (b :: rest) % two64
    rw [ih, show bytes_le_to_Z rest = ((bytes_le_to_Nat rest : Int)) from rfl, hz]
    show ((bv_unsigned b % two64).toNat
        ||| (((bytes_le_to_Nat rest : Int) % two64 * 256) % two64).toNat : Int)
      = ((b.toNat ||| (bytes_le_to_Nat rest <<< 8) : Nat) : Int) % two64
    rw [show (bv_unsigned b % two64).toNat = b.toNat from hbmod,
      toNat_emod_mul256, hor]
    rw [show (((b.toNat + bytes_le_to_Nat rest * 256 : Nat)) : Int) % two64
        = ((((b.toNat + bytes_le_to_Nat rest * 256) % 2 ^ 64 : Nat)) : Int) from by
      rw [two64_eq_natCast]
      exact (Int.natCast_emod _ _).symm]
    rw [← or_shift256_mod b.toNat (bytes_le_to_Nat rest) hb8]

/-! ### The mask block

    `mask_cover h` is the smallest `2^k - 1` covering `h`; these are the
    bounds `erange_f_sound` needs for `AND`/`OR`/`XOR`.
    `zlog2_up` is therefore characterised directly (`zlog2_up_spec`, via
    `Nat.lt_log2_self`), and the bit operations are this tree's 64-bit
    WINDOWED `zland`/`zlor`/`zlxor`, so the two monotonicity lemmas carry
    the `x < 2^64` the window makes necessary (`lor x y` can be smaller
    than `x` when `x` lies above the window).  Every call site feeds
    `bv_unsigned`, so the side condition is free there. -/

/-- `zlog2_up` is non-negative. -/
theorem zlog2_up_nonneg (n : Int) : 0 ≤ zlog2_up n := by
  unfold zlog2_up
  split
  · omega
  · exact Int.natCast_nonneg _

/-- `Z.log2_up_spec`: `n <= 2 ^ log2_up n` for `n > 0`. -/
theorem zlog2_up_spec (n : Int) (Hn : 0 < n) : n ≤ zpow 2 (zlog2_up n) := by
  unfold zlog2_up
  split
  · rename_i h1
    unfold zpow
    rw [Int.toNat_zero, Int.pow_zero]
    omega
  · rename_i h1
    have hn0 : (0 : Int) ≤ n := by omega
    have hnt : 1 ≤ n.toNat := by
      have : 0 < n.toNat := Int.pos_iff_toNat_pos.mp Hn
      omega
    have hlt : n.toNat - 1 < 2 ^ (Nat.log2 (n.toNat - 1) + 1) :=
      Nat.lt_log2_self (n := n.toNat - 1)
    have hle : n.toNat ≤ 2 ^ (Nat.log2 (n.toNat - 1) + 1) := by omega
    unfold zpow
    rw [Int.toNat_natCast, natCast_pow_two, ← Int.toNat_of_nonneg hn0]
    exact Int.ofNat_le.mpr hle
theorem pow_cover (h : Int) (Hh : 0 ≤ h) :
    h + 1 ≤ zpow 2 (zlog2_up (h + 1)) ∧ 0 ≤ zlog2_up (h + 1) :=
  ⟨zlog2_up_spec (h + 1) (by omega), zlog2_up_nonneg _⟩

/-- `mask_cover` is non-negative. -/
theorem mask_cover_nonneg (h : Int) : 0 ≤ mask_cover h := by
  unfold mask_cover
  split
  · omega
  · rename_i hnn
    unfold zpow
    have h1 : (1 : Int) ≤ 2 ^ (zlog2_up (h + 1)).toNat := by
      rw [natCast_pow_two]
      exact Int.ofNat_le.mpr Nat.one_le_two_pow
    omega

/-- `mask_cover_sound`: everything below `h` is below the mask. -/
theorem mask_cover_sound (h x : Int) (Hx : 0 ≤ x ∧ x ≤ h) : x ≤ mask_cover h := by
  have hge : ¬ h < 0 := by omega
  have hp := zlog2_up_spec (h + 1) (by omega)
  unfold mask_cover
  rw [ite_eq_right hge]
  unfold zpow at hp ⊢
  omega

/-- The borrow-free `zlor` is always inside the 64-bit window. -/
theorem zlor_lt_two64 (x y : Int) : AxSymExec3.zlor x y < 2 ^ 64 := by
  have hx0 : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ two64_ne
  have hxlt : x % 2 ^ 64 < ((2 ^ 64 : Nat) : Int) := by
    have := Int.emod_lt_of_pos x (b := 2 ^ 64) two64_pos
    simpa using this
  have hy0 : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ two64_ne
  have hylt : y % 2 ^ 64 < ((2 ^ 64 : Nat) : Int) := by
    have := Int.emod_lt_of_pos y (b := 2 ^ 64) two64_pos
    simpa using this
  have h1 : (x % 2 ^ 64).toNat < 2 ^ 64 := (Int.toNat_lt hx0).mpr hxlt
  have h2 : (y % 2 ^ 64).toNat < 2 ^ 64 := (Int.toNat_lt hy0).mpr hylt
  have h3 : ((x % 2 ^ 64).toNat ||| (y % 2 ^ 64).toNat) < 2 ^ 64 :=
    Nat.or_lt_two_pow h1 h2
  unfold AxSymExec3.zlor two64
  rw [natCast_pow_two]
  exact Int.ofNat_lt.mpr h3

/-- The same window bound for `zlxor`. -/
theorem zlxor_lt_two64 (x y : Int) : AxSymExec3.zlxor x y < 2 ^ 64 := by
  have hx0 : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ two64_ne
  have hxlt : x % 2 ^ 64 < ((2 ^ 64 : Nat) : Int) := by
    have := Int.emod_lt_of_pos x (b := 2 ^ 64) two64_pos
    simpa using this
  have hy0 : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ two64_ne
  have hylt : y % 2 ^ 64 < ((2 ^ 64 : Nat) : Int) := by
    have := Int.emod_lt_of_pos y (b := 2 ^ 64) two64_pos
    simpa using this
  have h1 : (x % 2 ^ 64).toNat < 2 ^ 64 := (Int.toNat_lt hx0).mpr hxlt
  have h2 : (y % 2 ^ 64).toNat < 2 ^ 64 := (Int.toNat_lt hy0).mpr hylt
  have h3 : ((x % 2 ^ 64).toNat ^^^ (y % 2 ^ 64).toNat) < 2 ^ 64 :=
    Nat.xor_lt_two_pow h1 h2
  unfold AxSymExec3.zlxor two64
  rw [natCast_pow_two]
  exact Int.ofNat_lt.mpr h3

/-- `lor_cover`, in this tree's 64-bit window. -/
theorem lor_cover (h x y : Int) (Hx : 0 ≤ x ∧ x ≤ h) (Hy : 0 ≤ y ∧ y ≤ h) :
    AxSymExec3.zlor x y ≤ mask_cover h := by
  have h0 : 0 ≤ h := by omega
  obtain ⟨hP, hk0⟩ := pow_cover h h0
  have hmask : h ≤ mask_cover h := mask_cover_sound h h ⟨h0, by omega⟩
  by_cases hbig : 2 ^ 64 - 1 ≤ h
  · have hz := zlor_lt_two64 x y
    omega
  · have hlt : h + 1 ≤ 2 ^ 64 := by omega
    have hx64 : x < 2 ^ 64 := by omega
    have hy64 : y < 2 ^ 64 := by omega
    have hbig' : x < ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      have hp := hP
      unfold zpow at hp
      rw [natCast_pow_two] at hp
      omega
    have hbigy' : y < ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      have hp := hP
      unfold zpow at hp
      rw [natCast_pow_two] at hp
      omega
    have hxN : x.toNat < 2 ^ (zlog2_up (h + 1)).toNat := by
      rw [Int.toNat_lt Hx.1]
      exact hbig'
    have hyN : y.toNat < 2 ^ (zlog2_up (h + 1)).toNat := by
      rw [Int.toNat_lt Hy.1]
      exact hbigy'
    have hor : (x.toNat ||| y.toNat) < 2 ^ (zlog2_up (h + 1)).toNat :=
      Nat.or_lt_two_pow hxN hyN
    have hxeq : (x % 2 ^ 64).toNat = x.toNat := by rw [Int.emod_eq_of_lt Hx.1 hx64]
    have hyeq : (y % 2 ^ 64).toNat = y.toNat := by rw [Int.emod_eq_of_lt Hy.1 hy64]
    have hpow : zpow 2 (zlog2_up (h + 1))
        = ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      unfold zpow
      exact natCast_pow_two _
    have hmask' : mask_cover h = zpow 2 (zlog2_up (h + 1)) - 1 := by
      unfold mask_cover
      rw [ite_eq_right (by omega)]
    rw [hmask', hpow]
    unfold AxSymExec3.zlor two64
    rw [hxeq, hyeq]
    have := Int.ofNat_lt.mpr hor
    omega
theorem lxor_cover (h x y : Int) (Hx : 0 ≤ x ∧ x ≤ h) (Hy : 0 ≤ y ∧ y ≤ h) :
    0 ≤ AxSymExec3.zlxor x y ∧ AxSymExec3.zlxor x y ≤ mask_cover h := by
  have h0 : 0 ≤ h := by omega
  obtain ⟨hP, hk0⟩ := pow_cover h h0
  have hmask : h ≤ mask_cover h := mask_cover_sound h h ⟨h0, by omega⟩
  have hnn : 0 ≤ AxSymExec3.zlxor x y := by
    unfold AxSymExec3.zlxor
    exact Int.natCast_nonneg _
  refine ⟨hnn, ?_⟩
  by_cases hbig : 2 ^ 64 - 1 ≤ h
  · have hz := zlxor_lt_two64 x y
    omega
  · have hlt : h + 1 ≤ 2 ^ 64 := by omega
    have hx64 : x < 2 ^ 64 := by omega
    have hy64 : y < 2 ^ 64 := by omega
    have hbig' : x < ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      have hp := hP
      unfold zpow at hp
      rw [natCast_pow_two] at hp
      omega
    have hbigy' : y < ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      have hp := hP
      unfold zpow at hp
      rw [natCast_pow_two] at hp
      omega
    have hxN : x.toNat < 2 ^ (zlog2_up (h + 1)).toNat := by
      rw [Int.toNat_lt Hx.1]
      exact hbig'
    have hyN : y.toNat < 2 ^ (zlog2_up (h + 1)).toNat := by
      rw [Int.toNat_lt Hy.1]
      exact hbigy'
    have hor : (x.toNat ^^^ y.toNat) < 2 ^ (zlog2_up (h + 1)).toNat :=
      Nat.xor_lt_two_pow hxN hyN
    have hxeq : (x % 2 ^ 64).toNat = x.toNat := by rw [Int.emod_eq_of_lt Hx.1 hx64]
    have hyeq : (y % 2 ^ 64).toNat = y.toNat := by rw [Int.emod_eq_of_lt Hy.1 hy64]
    have hpow : zpow 2 (zlog2_up (h + 1))
        = ((2 ^ (zlog2_up (h + 1)).toNat : Nat) : Int) := by
      unfold zpow
      exact natCast_pow_two _
    have hmask' : mask_cover h = zpow 2 (zlog2_up (h + 1)) - 1 := by
      unfold mask_cover
      rw [ite_eq_right (by omega)]
    rw [hmask', hpow]
    unfold AxSymExec3.zlxor two64
    rw [hxeq, hyeq]
    have := Int.ofNat_lt.mpr hor
    omega

/-- `land_le_l`: `Z.land` never exceeds its left argument.
     -/
theorem land_le_l (a b : Int) (Ha : 0 ≤ a) (Hb : 0 ≤ b) : AxSymExec3.zland a b ≤ a := by
  have h1 : (a % 2 ^ 64).toNat ≤ a.toNat :=
    Int.toNat_le_toNat (emod_le_self a (2 ^ 64) Ha (by decide))
  have h2 : ((a % 2 ^ 64).toNat &&& (b % 2 ^ 64).toNat) ≤ a.toNat :=
    Nat.le_trans Nat.and_le_left h1
  have h2' : ((((a % 2 ^ 64).toNat &&& (b % 2 ^ 64).toNat : Nat)) : Int)
      ≤ ((a.toNat : Nat) : Int) := Int.ofNat_le.mpr h2
  rw [Int.toNat_of_nonneg Ha] at h2'
  simpa [AxSymExec3.zland, two64] using h2'
theorem land_le_r (a b : Int) (Ha : 0 ≤ a) (Hb : 0 ≤ b) : AxSymExec3.zland a b ≤ b := by
  rw [show AxSymExec3.zland a b = AxSymExec3.zland b a from by
    unfold AxSymExec3.zland; rw [Nat.and_comm]]
  exact land_le_l b a Hb Ha

/-- `lor_ge_l`.  This tree's `zlor` truncates at 64 bits, so the
    statement needs `x` inside the window. -/
theorem lor_ge_l (x y : Int) (Hx : 0 ≤ x) (Hx64 : x < 2 ^ 64) :
    x ≤ AxSymExec3.zlor x y := by
  have hxeq : (x % 2 ^ 64).toNat = x.toNat := by rw [Int.emod_eq_of_lt Hx Hx64]
  unfold AxSymExec3.zlor two64
  rw [hxeq, ← Int.toNat_of_nonneg Hx]
  exact Int.ofNat_le.mpr Nat.left_le_or
theorem lor_ge_r (x y : Int) (Hy : 0 ≤ y) (Hy64 : y < 2 ^ 64) :
    y ≤ AxSymExec3.zlor x y := by
  have hyeq : (y % 2 ^ 64).toNat = y.toNat := by rw [Int.emod_eq_of_lt Hy Hy64]
  unfold AxSymExec3.zlor two64
  rw [hyeq, ← Int.toNat_of_nonneg Hy]
  exact Int.ofNat_le.mpr Nat.right_le_or

/-!  Bit INDICES are `Nat` ; `2^j` at `Int` level is `zpow 2 j` in this tree. -/

/-- `testbit_mask`: the bits of the high mask `2^64 - 2^j` are
    exactly the positions `j <= i < 64`. -/
theorem testbit_mask_nat (j i : Nat) (hj : j ≤ 64) :
    Nat.testBit (2 ^ 64 - 2 ^ j) i = (decide (j ≤ i) && decide (i < 64)) := by
  have h2 : 2 ^ j * 2 ^ (64 - j) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hm : 2 ^ 64 - 2 ^ j = 2 ^ j * (2 ^ (64 - j) - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, h2]
  rw [hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases hji : j ≤ i
  · have hd : decide (i - j < 64 - j) = decide (i < 64) := by
      rcases Nat.lt_or_ge i 64 with h | h
      · simp [h, show i - j < 64 - j from by omega]
      · simp [h, show ¬ (i - j < 64 - j) from by omega]
    simp [hji, hd]
  · simp [hji]

/-- `testbit_drop_low`: bits at or above `j` do not see the low
    part `r < 2^j`. -/
theorem testbit_drop_low (q r j i : Nat) (hr : r < 2 ^ j) (hji : j ≤ i) :
    Nat.testBit (q * 2 ^ j + r) i = Nat.testBit (q * 2 ^ j) i := by
  have hsum : q * 2 ^ j + r = 2 ^ j * q + r := by rw [Nat.mul_comm q (2 ^ j)]
  have hmul : q * 2 ^ j = 2 ^ j * q := by rw [Nat.mul_comm q (2 ^ j)]
  rw [hsum, hmul, Nat.testBit_two_pow_mul_add (a := q) (b := r) (i := j) hr i,
    ite_eq_right (by omega), Nat.testBit_two_pow_mul]
  simp [hji]

/-- `land_highmask`, `Nat` half: masking with `2^64 - 2^j` clears
    the low `j` bits, i.e. rounds `x` down to a multiple of `2^j`. -/
theorem and_highmask_nat (x j : Nat) (hj : j < 64) (hx : x < 2 ^ 64) :
    x &&& (2 ^ 64 - 2 ^ j) = x - x % 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testbit_mask_nat j i (by omega)]
  have hxr : x - x % 2 ^ j = 2 ^ j * (x / 2 ^ j) := by
    have h1 : 2 ^ j * (x / 2 ^ j) + x % 2 ^ j = x := Nat.div_add_mod x (2 ^ j)
    omega
  rw [hxr, Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases hji : j ≤ i
  · rw [Nat.sub_add_cancel hji]
    by_cases hi : i < 64
    · cases hb : Nat.testBit x i <;> simp [hji, hi, hb]
    · have hxi : x < 2 ^ i :=
        Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
      have hfalse : Nat.testBit x i = false := Nat.testBit_lt_two_pow hxi
      simp [hji, hi, hfalse]
  · cases hb : Nat.testBit x i <;> simp [hji, hb]

/-- `land_highmask`: `Z.land x (2^64 - 2^j) = x - x mod 2^j` for
    `x` in the window.  This tree's `zland` truncates, but both operands
    here are below `2^64`, so the window is inert. -/
theorem land_highmask (x j : Int) (Hj : 0 ≤ j ∧ j < 64) (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    AxSymExec3.zland x (2 ^ 64 - zpow 2 j) = x - x % zpow 2 j := by
  have hjN : j.toNat < 64 := by
    rw [Int.toNat_lt Hj.1]
    exact Hj.2
  have hpow : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := by
    unfold zpow
    exact natCast_pow_two _
  have h64 : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := natCast_pow_two 64
  have hN : (2 ^ j.toNat : Nat) ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hz0 : (0 : Int) < zpow 2 j := by
    rw [hpow]
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm0 : (0 : Int) ≤ 2 ^ 64 - zpow 2 j := by
    rw [hpow, h64]
    omega
  have hmlt : 2 ^ 64 - zpow 2 j < 2 ^ 64 := by
    rw [h64]
    omega
  have hxt : x % 2 ^ 64 = x := Int.emod_eq_of_lt Hx.1 Hx.2
  have hmt : (2 ^ 64 - zpow 2 j) % 2 ^ 64 = 2 ^ 64 - zpow 2 j :=
    Int.emod_eq_of_lt hm0 hmlt
  have hmtoNat : (2 ^ 64 - zpow 2 j).toNat = 2 ^ 64 - 2 ^ j.toNat := by
    have h1 : (((2 ^ 64 : Nat) : Int) - ((2 ^ j.toNat : Nat) : Int))
        = 2 ^ 64 - zpow 2 j := by
      rw [h64, hpow]
    have h2 : (((2 ^ 64 : Nat) : Int) - ((2 ^ j.toNat : Nat) : Int)).toNat
        = 2 ^ 64 - 2 ^ j.toNat := by
      rw [Int.toNat_sub'' (Int.natCast_nonneg _) (Int.natCast_nonneg _)]
      rw [Int.toNat_natCast, Int.toNat_natCast]
    rw [← h1]
    exact h2
  have hr : x % zpow 2 j = ((x.toNat % 2 ^ j.toNat : Nat) : Int) := by
    rw [hpow, ← Int.toNat_of_nonneg Hx.1, ← Int.natCast_emod]
    simp
  have hsub : x - x % zpow 2 j = ((x.toNat - x.toNat % 2 ^ j.toNat : Nat) : Int) := by
    rw [hr]
    rw [Int.natCast_sub (n := x.toNat % 2 ^ j.toNat) (m := x.toNat) (Nat.mod_le _ _)]
    rw [Int.toNat_of_nonneg Hx.1]
  have hxN : x.toNat < 2 ^ 64 := (Int.toNat_lt Hx.1).mpr Hx.2
  rw [hsub]
  unfold AxSymExec3.zland two64
  rw [hxt, hmt, hmtoNat, and_highmask_nat x.toNat j.toNat hjN hxN]

/-- `land_align_mask`: an aligned `x` survives the high mask. -/
theorem land_align_mask (x j : Int) (Hj : 0 ≤ j ∧ j < 64) (Hx : 0 ≤ x ∧ x < 2 ^ 64)
    (Hmod : x % zpow 2 j = 0) :
    AxSymExec3.zland x (2 ^ 64 - zpow 2 j) = x := by
  rw [land_highmask x j Hj Hx, Hmod]
  omega

/-! ### `lin_range_sound`

    The interval of a linear form, given pointwise-sound atom intervals. -/
theorem lin_range_sound (E : env) (rng : expr → Option (Int × Int))
    (Hrng : ∀ a lo hi, rng a = some (lo, hi) →
      lo ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ hi) :
    ∀ (c : Int) (ts : List (Int × expr)) (lo hi : Int),
      lin_range rng c ts = some (lo, hi) →
      lo ≤ c + tden E ts ∧ c + tden E ts ≤ hi := by
  intro c ts
  induction ts with
  | nil =>
    intro lo hi H
    simp only [lin_range, Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨h1, h2⟩ := H
    rw [← h1, ← h2]
    simp only [tden_nil]
    omega
  | cons t rest ih =>
    intro lo hi H
    obtain ⟨k, a⟩ := t
    simp only [lin_range] at H
    cases hr : rng a with
    | none =>
      rw [hr] at H
      exact absurd H (by simp)
    | some r =>
      obtain ⟨al, ah⟩ := r
      cases hl : lin_range rng c rest with
      | none =>
        rw [hr, hl] at H
        exact absurd H (by simp)
      | some l =>
        obtain ⟨lo', hi'⟩ := l
        simp only [hr, hl] at H
        have ih' := ih lo' hi' hl
        have hb := Hrng a al ah hr
        have hu : uE E a = bv_unsigned (edenot E a) := rfl
        by_cases hk : 0 ≤ k
        · rw [ite_eq_left hk] at H
          simp only [Option.some.injEq, Prod.ext_iff] at H
          rw [← H.1, ← H.2, tden_cons, hu]
          have hm1 : k * al ≤ k * bv_unsigned (edenot E a) :=
            Int.mul_le_mul_of_nonneg_left hb.1 hk
          have hm2 : k * bv_unsigned (edenot E a) ≤ k * ah :=
            Int.mul_le_mul_of_nonneg_left hb.2 hk
          omega
        · rw [ite_eq_right hk] at H
          have hkn : k ≤ 0 := by omega
          simp only [Option.some.injEq, Prod.ext_iff] at H
          rw [← H.1, ← H.2, tden_cons, hu]
          have hm1 : k * ah ≤ k * bv_unsigned (edenot E a) :=
            Int.mul_le_mul_of_nonpos_left hkn hb.2
          have hm2 : k * bv_unsigned (edenot E a) ≤ k * al :=
            Int.mul_le_mul_of_nonpos_left hkn hb.1
          omega

/-! ### Helpers for `erange_f_sound`'s remaining cases

    The mask block above gives the two `land` identities; these are the
    arithmetic facts the `AND`/`EExt` cases of `erange_f_sound` need on
    top of them: the low mask (`2^j - 1`), the quotient of an interval
    that stays inside one `2^j` block, and the `zpow`/`8 * n` bridge. -/

/-- `zlog2` is non-negative. -/
theorem zlog2_nonneg (z : Int) : 0 ≤ AxSymExec3.zlog2 z := by
  unfold AxSymExec3.zlog2
  split
  · omega
  · exact Int.natCast_nonneg _

/-- The low mask `2^j - 1` truncates to `x mod 2^j` . -/
theorem land_lowmask (x m j : Int) (Hj : 0 ≤ j ∧ j ≤ 64) (Hm : m = zpow 2 j - 1)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    AxSymExec3.zland x m = x % zpow 2 j := by
  have hpow : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := by
    unfold zpow
    exact natCast_pow_two _
  have hjN : j.toNat ≤ 64 := by
    rw [Int.toNat_le]
    omega
  have hge1 : (1 : Int) ≤ ((2 ^ j.toNat : Nat) : Int) :=
    Int.ofNat_le.mpr Nat.one_le_two_pow
  have hle64 : ((2 ^ j.toNat : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) :=
    Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hjN)
  have hm0 : 0 ≤ m := by
    rw [Hm, hpow]
    omega
  have hmlt : m < 2 ^ 64 := by
    rw [Hm, hpow, natCast_pow_two]
    omega
  have hxt : x % 2 ^ 64 = x := Int.emod_eq_of_lt Hx.1 Hx.2
  have hmt : m % 2 ^ 64 = m := Int.emod_eq_of_lt hm0 hmlt
  have hmtoNat : m.toNat = 2 ^ j.toNat - 1 := by
    rw [Hm, hpow, Int.toNat_sub'' (Int.natCast_nonneg _) (by decide), Int.toNat_natCast]
    rfl
  have hr : x % zpow 2 j = ((x.toNat % 2 ^ j.toNat : Nat) : Int) := by
    rw [hpow, ← Int.toNat_of_nonneg Hx.1, ← Int.natCast_emod]
    simp
  rw [hr]
  unfold AxSymExec3.zland two64
  rw [hxt, hmt, hmtoNat]
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- Inside one `2^j` block, `x`'s quotient is `al`'s quotient. -/
theorem ediv_block (x al ah P : Int) (hP : 0 < P) (h1 : al ≤ x) (h2 : x ≤ ah)
    (hq : al / P = ah / P) : x / P = al / P := by
  have hle : al / P ≤ x / P := Int.ediv_le_ediv hP h1
  have hle' : x / P ≤ ah / P := Int.ediv_le_ediv hP h2
  omega

/-- Inside one `2^j` block, the residues are ordered . -/
theorem emod_block (x al ah P : Int) (hP : 0 < P) (h1 : al ≤ x) (h2 : x ≤ ah)
    (hq : al / P = ah / P) : al % P ≤ x % P ∧ x % P ≤ ah % P := by
  have hxq := ediv_block x al ah P hP h1 h2 hq
  have e1 := Int.ediv_mul_add_emod al P
  have e2 := Int.ediv_mul_add_emod x P
  have e3 := Int.ediv_mul_add_emod ah P
  rw [hq] at e1
  rw [hxq, hq] at e2
  constructor <;> omega

/-- Inside one `2^j` block, rounding both ends down is monotone. -/
theorem esub_emod_block (x al ah P : Int) (hP : 0 < P) (h1 : al ≤ x) (h2 : x ≤ ah)
    (hq : al / P = ah / P) :
    al - al % P ≤ x - x % P ∧ x - x % P ≤ ah - ah % P := by
  have hxq := ediv_block x al ah P hP h1 h2 hq
  have e1 := Int.ediv_mul_add_emod al P
  have e2 := Int.ediv_mul_add_emod x P
  have e3 := Int.ediv_mul_add_emod ah P
  rw [hq] at e1
  rw [hxq, hq] at e2
  constructor <;> omega

/-- `zpow 2 (8 * n)` at the `Int` exponent this tree's `EExt` uses. -/
theorem zpow_two_8n (n : Nat) : zpow 2 (8 * (n : Int)) = (2 : Int) ^ (8 * n) := by
  unfold zpow
  have h : 8 * (n : Int) = ((8 * n : Nat) : Int) := (Int.natCast_mul 8 n).symm
  rw [h, Int.toNat_natCast]

/-- `zsigned64` below the sign bit is the value itself. -/
theorem zsigned64_of_lt (v : Int) (Hv : v < two63z) : zsigned64 v = v := by
  unfold zsigned64
  rw [ite_eq_right (by omega)]

/-- `zsigned64` above the sign bit subtracts `2^64`. -/
theorem zsigned64_of_ge (v : Int) (Hv : two63z ≤ v) : zsigned64 v = v - two64 := by
  unfold zsigned64
  rw [ite_eq_left Hv]

/-- The linear-form case of `erange_f_sound`: when the
    form's plain interval `[lo1, hi1]` lies inside ONE `2^64` block, the
    block index is forced, so the residue interval pins the VALUE (not just
    the residue mod `2^64`).  `erange_f` then returns the interval shifted
    down by that block (`lo - q * two64`). -/
theorem erange_f_lin_sound (E : env) (kn : List kentry) (fuel : Nat) (e : expr)
    (IH : ∀ (a : expr) (lo hi : Int), erange_f fuel kn a = some (lo, hi) →
      lo ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ hi)
    (lo1 hi1 : Int)
    (hlr : lin_range (erange_f fuel kn) (lin_of e).1 (lin_of e).2 = some (lo1, hi1))
    (hq : (zdiv64 lo1 == zdiv64 hi1) = true) :
    lo1 - zdiv64 lo1 * two64 ≤ bv_unsigned (edenot E e) ∧
      bv_unsigned (edenot E e) ≤ hi1 - zdiv64 lo1 * two64 := by
  have hb := lin_range_sound E (erange_f fuel kn) (fun a lo hi Ha => IH a lo hi Ha)
    (lin_of e).1 (lin_of e).2 lo1 hi1 hlr
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨q, hq'⟩ := lin_of_sound E e
  have hld : lden E (lin_of e) = (lin_of e).1 + tden E (lin_of e).2 := rfl
  rw [hld] at hq'
  have hu : uE E e = bv_unsigned (edenot E e) := rfl
  rw [hu] at hq'
  have hbv : bv_unsigned (edenot E e) = ((edenot E e).toNat : Int) := rfl
  rw [hbv] at hq' ⊢
  have hp : zdiv64 lo1 = zdiv64 hi1 := beq_iff_eq.mp hq
  have hv := u64_range (edenot E e)
  have e1 : lo1 / two64 * two64 + lo1 % two64 = lo1 := Int.ediv_mul_add_emod lo1 two64
  have e2 : hi1 / two64 * two64 + hi1 % two64 = hi1 := Int.ediv_mul_add_emod hi1 two64
  have m1 : 0 ≤ lo1 % two64 := Int.emod_nonneg lo1 two64_ne
  have m1' : lo1 % two64 < two64 := Int.emod_lt_of_pos lo1 two64_pos
  have m2 : 0 ≤ hi1 % two64 := Int.emod_nonneg hi1 two64_ne
  have m2' : hi1 % two64 < two64 := Int.emod_lt_of_pos hi1 two64_pos
  have hd1 : zdiv64 lo1 = lo1 / two64 := zdiv64_eq2 lo1
  have hd2 : zdiv64 hi1 = hi1 / two64 := zdiv64_eq2 hi1
  rw [hd1] at hp ⊢
  have htwo : two64 = 18446744073709551616 := by decide
  rw [htwo] at e1 e2 m1 m1' m2 m2' hd1 hd2 hp ⊢
  omega









/-! ### `erange_f_sound` — the per-case arithmetic

    Each helper takes the two sub-interval bounds (the induction
    hypothesis, already applied) and the branch condition that
    `erange_f` checked, and concludes the interval it returned.  Keeping
    them out of the big case bash keeps every piece independently
    checkable. -/

/-- `ELit`: `erange_f` returns `(zmod64 z, zmod64 z)`. -/
theorem erange_lit_sound (E : env) (z rlo rhi : Int)
    (H : some (zmod64 z, zmod64 z) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.ELit z)) ∧ bv_unsigned (edenot E (.ELit z)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show zmod64 z ≤ bv_unsigned (Z_to_bv 64 z) ∧ bv_unsigned (Z_to_bv 64 z) ≤ zmod64 z
  rw [zmod64_eq2, u_lit64]
  exact ⟨Int.le_refl _, Int.le_refl _⟩

/-- `ADD`, no wrap: `ah + bh < 2^64`. -/
theorem erange_add_sound (E : env) (a b : expr) (al ah bl bh : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : ah + bh < 2 ^ 64) :
    al + bl ≤ bv_unsigned (edenot E (.EAlu .ADD a b)) ∧
      bv_unsigned (edenot E (.EAlu .ADD a b)) ≤ ah + bh := by
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al + bl ≤ bv_unsigned (edenot E a + edenot E b) ∧
      bv_unsigned (edenot E a + edenot E b) ≤ ah + bh
  rw [u_add64]
  have h0 : 0 ≤ bv_unsigned (edenot E a) + bv_unsigned (edenot E b) := by omega
  have hlt : bv_unsigned (edenot E a) + bv_unsigned (edenot E b) < 2 ^ 64 := by omega
  rw [Int.emod_eq_of_lt h0 hlt]
  omega

/-- `ADD`, wrap: `2^64 ≤ al + bl` (and `¬ ah + bh < 2^64`). -/
theorem erange_add_sound_hi (E : env) (a b : expr) (al ah bl bh : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : ¬ (ah + bh < 2 ^ 64)) (hc2 : 2 ^ 64 ≤ al + bl) :
    al + bl - 2 ^ 64 ≤ bv_unsigned (edenot E (.EAlu .ADD a b)) ∧
      bv_unsigned (edenot E (.EAlu .ADD a b)) ≤ ah + bh - 2 ^ 64 := by
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al + bl - 2 ^ 64 ≤ bv_unsigned (edenot E a + edenot E b) ∧
      bv_unsigned (edenot E a + edenot E b) ≤ ah + bh - 2 ^ 64
  rw [u_add64]
  have hge : (2 : Int) ^ 64 ≤ bv_unsigned (edenot E a) + bv_unsigned (edenot E b) := by omega
  have hlt : bv_unsigned (edenot E a) + bv_unsigned (edenot E b) < 2 ^ 64 + 2 ^ 64 := by omega
  rw [mod_wrap_hi _ ⟨hge, hlt⟩]
  omega

/-- `SUB`, no wrap: `bh ≤ al`. -/
theorem erange_sub_sound (E : env) (a b : expr) (al ah bl bh : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : bh ≤ al) :
    al - bh ≤ bv_unsigned (edenot E (.EAlu .SUB a b)) ∧
      bv_unsigned (edenot E (.EAlu .SUB a b)) ≤ ah - bl := by
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al - bh ≤ bv_unsigned (edenot E a - edenot E b) ∧
      bv_unsigned (edenot E a - edenot E b) ≤ ah - bl
  rw [u_sub64]
  have h0 : 0 ≤ bv_unsigned (edenot E a) - bv_unsigned (edenot E b) := by omega
  have hlt : bv_unsigned (edenot E a) - bv_unsigned (edenot E b) < 2 ^ 64 := by omega
  rw [Int.emod_eq_of_lt h0 hlt]
  omega

/-- `SUB`, wrap: `ah < bl`. -/
theorem erange_sub_sound_hi (E : env) (a b : expr) (al ah bl bh : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : ¬ bh ≤ al) (hc2 : ah < bl) :
    al - bh + 2 ^ 64 ≤ bv_unsigned (edenot E (.EAlu .SUB a b)) ∧
      bv_unsigned (edenot E (.EAlu .SUB a b)) ≤ ah - bl + 2 ^ 64 := by
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al - bh + 2 ^ 64 ≤ bv_unsigned (edenot E a - edenot E b) ∧
      bv_unsigned (edenot E a - edenot E b) ≤ ah - bl + 2 ^ 64
  rw [u_sub64]
  have hlt : bv_unsigned (edenot E a) - bv_unsigned (edenot E b) < 0 := by omega
  have hge : -((2 : Int) ^ 64) ≤ bv_unsigned (edenot E a) - bv_unsigned (edenot E b) := by
    omega
  rw [mod_wrap_neg _ hge hlt]
  omega

/-- `AND`, low mask `2^j - 1` on a range inside one `2^j` block. -/
theorem erange_and_low_sound (E : env) (a : expr) (m : Int) (al ah j rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hj : 0 ≤ j ∧ j ≤ 64)
    (hpow : (m % two64 + 1 == zpow 2 j) = true)
    (heq : (al / zpow 2 j == ah / zpow 2 j) = true)
    (H : some (al % zpow 2 j, ah % zpow 2 j) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .AND a (.ELit m))) ∧
      bv_unsigned (edenot E (.EAlu .AND a (.ELit m))) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hPpos : 0 < zpow 2 j := by
    unfold zpow
    exact two_pow_pos_int _
  have hm' : m % two64 = zpow 2 j - 1 := by
    have hp := beq_iff_eq.mp hpow
    omega
  have hqa : al / zpow 2 j = ah / zpow 2 j := beq_iff_eq.mp heq
  have hmono := emod_block (bv_unsigned (edenot E a)) al ah (zpow 2 j) hPpos ha.1 ha.2 hqa
  have hlit : bv_unsigned (edenot E (.ELit m)) = m % two64 := by
    show bv_unsigned (Z_to_bv 64 m) = m % two64
    exact u_lit64 m
  show al % zpow 2 j ≤ bv_unsigned (alu64 .AND (edenot E a) (edenot E (.ELit m))) ∧
      bv_unsigned (alu64 .AND (edenot E a) (edenot E (.ELit m))) ≤ ah % zpow 2 j
  rw [u_and64, hlit, hm',
    land_lowmask (bv_unsigned (edenot E a)) (zpow 2 j - 1) j hj rfl hu]
  exact hmono

/-- `AND`, high mask `2^64 - 2^jh`: both bounds rounded down to a multiple
    of `2^jh` (`x ↦ x - x mod 2^jh` is monotone). -/
theorem erange_and_high_sound (E : env) (a : expr) (m : Int) (al ah jh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hj : 0 ≤ jh ∧ jh < 64)
    (hpow : (two64 - m % two64 == zpow 2 jh) = true)
    (H : some (al - al % zpow 2 jh, ah - ah % zpow 2 jh) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .AND a (.ELit m))) ∧
      bv_unsigned (edenot E (.EAlu .AND a (.ELit m))) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hPpos : 0 < zpow 2 jh := by
    unfold zpow
    exact two_pow_pos_int _
  have hm' : m % two64 = 2 ^ 64 - zpow 2 jh := by
    have hp := beq_iff_eq.mp hpow
    have h2 : two64 = 2 ^ 64 := two64_eq
    omega
  have hlit : bv_unsigned (edenot E (.ELit m)) = m % two64 := by
    show bv_unsigned (Z_to_bv 64 m) = m % two64
    exact u_lit64 m
  show al - al % zpow 2 jh ≤ bv_unsigned (alu64 .AND (edenot E a) (edenot E (.ELit m))) ∧
      bv_unsigned (alu64 .AND (edenot E a) (edenot E (.ELit m))) ≤ ah - ah % zpow 2 jh
  rw [u_and64, hlit, hm', land_highmask (bv_unsigned (edenot E a)) jh hj hu]
  have e1 : al - al % zpow 2 jh = al / zpow 2 jh * zpow 2 jh := by
    have := Int.ediv_mul_add_emod al (zpow 2 jh)
    omega
  have e2 : ah - ah % zpow 2 jh = ah / zpow 2 jh * zpow 2 jh := by
    have := Int.ediv_mul_add_emod ah (zpow 2 jh)
    omega
  have e3 : bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 jh
      = bv_unsigned (edenot E a) / zpow 2 jh * zpow 2 jh := by
    have := Int.ediv_mul_add_emod (bv_unsigned (edenot E a)) (zpow 2 jh)
    omega
  rw [e1, e2, e3]
  have h1' : al / zpow 2 jh ≤ bv_unsigned (edenot E a) / zpow 2 jh :=
    Int.ediv_le_ediv hPpos ha.1
  have h2' : bv_unsigned (edenot E a) / zpow 2 jh ≤ ah / zpow 2 jh :=
    Int.ediv_le_ediv hPpos ha.2
  have h0 : 0 ≤ zpow 2 jh := by omega
  exact ⟨Int.mul_le_mul_of_nonneg_right h1' h0, Int.mul_le_mul_of_nonneg_right h2' h0⟩

/-- `AND` with no usable mask info: `(0, min ah bh)`. -/
theorem erange_and_min_sound (E : env) (a b : expr) (ah bh rlo rhi : Int)
    (ha : bv_unsigned (edenot E a) ≤ ah)
    (hb : bv_unsigned (edenot E b) ≤ bh)
    (H : some (0, min ah bh) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .AND a b)) ∧
      bv_unsigned (edenot E (.EAlu .AND a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 0 ≤ bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ≤ min ah bh
  rw [u_and64]
  have hl := land_le_l (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hu.1 hv.1
  have hr := land_le_r (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hu.1 hv.1
  have hnn : 0 ≤ AxSymExec3.zland (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) := by
    unfold AxSymExec3.zland
    exact Int.natCast_nonneg _
  refine ⟨hnn, ?_⟩
  exact Int.le_min.mpr ⟨by omega, by omega⟩

/-- `OR`: `(max al bl, mask_cover (max ah bh))`. -/
theorem erange_or_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (H : some (max al bl, mask_cover (max ah bh)) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .OR a b)) ∧
      bv_unsigned (edenot E (.EAlu .OR a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show max al bl ≤ bv_unsigned (alu64 .OR (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .OR (edenot E a) (edenot E b)) ≤ mask_cover (max ah bh)
  rw [u_or64]
  constructor
  · have hgl := lor_ge_l (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hu.1 hu.2
    have hgr := lor_ge_r (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hv.1 hv.2
    have hmax : max al bl ≤ AxSymExec3.zlor (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) :=
      Int.max_le.mpr ⟨by omega, by omega⟩
    exact hmax
  · exact lor_cover (max ah bh) _ _
      ⟨hu.1, Int.le_trans ha.2 (Int.le_max_left _ _)⟩
      ⟨hv.1, Int.le_trans hb.2 (Int.le_max_right _ _)⟩

/-- `XOR`: `(0, mask_cover (max ah bh))`. -/
theorem erange_xor_sound (E : env) (a b : expr) (ah bh rlo rhi : Int)
    (ha : bv_unsigned (edenot E a) ≤ ah)
    (hb : bv_unsigned (edenot E b) ≤ bh)
    (H : some (0, mask_cover (max ah bh)) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .XOR a b)) ∧
      bv_unsigned (edenot E (.EAlu .XOR a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 0 ≤ bv_unsigned (alu64 .XOR (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .XOR (edenot E a) (edenot E b)) ≤ mask_cover (max ah bh)
  rw [u_xor64]
  exact lxor_cover (max ah bh) _ _
    ⟨hu.1, Int.le_trans ha (Int.le_max_left _ _)⟩
    ⟨hv.1, Int.le_trans hb (Int.le_max_right _ _)⟩


/-! Bridge lemmas between the `bv_*` spellings the interval lemmas use
    and the `Nat` comparisons the ISA predicates decide. -/

theorem bv_lt_two_pow_iff (x : word) (k : Nat) :
    bv_unsigned x < (2 : Int) ^ k ↔ x.toNat < 2 ^ k := by
  rw [natCast_pow_two]
  exact Int.ofNat_lt

theorem bv_ltu_eq_true (x y : word) :
    bv_ltu x y = true ↔ bv_unsigned x < bv_unsigned y := by
  unfold bv_ltu
  rw [decide_eq_true_eq]
  exact Int.ofNat_lt.symm

theorem bv_lts_eq_true (x y : word) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    bv_lts x y = true ↔ bv_unsigned x < bv_unsigned y := by
  unfold bv_lts
  rw [decide_eq_true_eq, bv_signed_small x hx, bv_signed_small y hy]

/-- `SLTU`, decided `(1,1)`: `ah < bl`. -/
theorem erange_sltu_lt_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : ah < bl)
    (H : some (1, 1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLTU a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLTU a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show 1 ≤ bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ≤ 1
  rw [u_sltu64]
  have hlt : bv_ltu (edenot E a) (edenot E b) = true := by
    rw [bv_ltu_eq_true]
    omega
  rw [ite_eq_left hlt]
  omega

/-- `SLTU`, decided `(0,0)`: `bh ≤ al`. -/
theorem erange_sltu_gt_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hc : bh ≤ al)
    (H : some (0, 0) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLTU a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLTU a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show 0 ≤ bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ≤ 0
  rw [u_sltu64]
  have hlt : ¬ (bv_ltu (edenot E a) (edenot E b) = true) := by
    rw [bv_ltu_eq_true]
    omega
  rw [ite_eq_right hlt]
  omega

/-- `SLTU`, undecided `(0,1)`. -/
theorem erange_sltu_mid_sound (E : env) (a b : expr) (rlo rhi : Int)
    (H : some (0, 1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLTU a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLTU a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show 0 ≤ bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLTU (edenot E a) (edenot E b)) ≤ 1
  rw [u_sltu64]
  split <;> omega

/-- `SLT`, decided `(1,1)`: both operands below `2^63` and `ah < bl`. -/
theorem erange_slt_lt_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hah : ah < 2 ^ 63) (hbh : bh < 2 ^ 63) (hc : ah < bl)
    (H : some (1, 1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLT a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLT a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 1 ≤ bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ≤ 1
  rw [u_slt64]
  have ha63 : (edenot E a).toNat < 2 ^ 63 := (bv_lt_two_pow_iff _ 63).mp (by omega)
  have hb63 : (edenot E b).toNat < 2 ^ 63 := (bv_lt_two_pow_iff _ 63).mp (by omega)
  have hlt : bv_lts (edenot E a) (edenot E b) = true := by
    rw [bv_lts_eq_true _ _ ha63 hb63]
    omega
  rw [ite_eq_left hlt]
  omega

/-- `SLT`, decided `(0,0)`: both operands below `2^63` and `bh ≤ al`. -/
theorem erange_slt_gt_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (hah : ah < 2 ^ 63) (hbh : bh < 2 ^ 63) (hc : bh ≤ al)
    (H : some (0, 0) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLT a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLT a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 0 ≤ bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ≤ 0
  rw [u_slt64]
  have ha63 : (edenot E a).toNat < 2 ^ 63 := (bv_lt_two_pow_iff _ 63).mp (by omega)
  have hb63 : (edenot E b).toNat < 2 ^ 63 := (bv_lt_two_pow_iff _ 63).mp (by omega)
  have hlt : ¬ (bv_lts (edenot E a) (edenot E b) = true) := by
    rw [bv_lts_eq_true _ _ ha63 hb63]
    omega
  rw [ite_eq_right hlt]
  omega

/-- `SLT`, undecided `(0,1)`. -/
theorem erange_slt_mid_sound (E : env) (a b : expr) (rlo rhi : Int)
    (H : some (0, 1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLT a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLT a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show 0 ≤ bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLT (edenot E a) (edenot E b)) ≤ 1
  rw [u_slt64]
  split <;> omega

/-- `2^32 * 2^32 = 2^64`, the `k` of the wrapping 32-bit cases. -/
theorem two32_mul_two32 : (2 : Int) ^ 32 * (2 : Int) ^ 32 = 2 ^ 64 := by
  rw [← Int.pow_add]

/-- `ADDW`: the value is `t`, a `32`-bit signed wrap of `ua + ub`. -/
theorem erange_addw_sound (E : env) (a b : expr) (lo hi t rlo rhi : Int)
    (Ht : 0 ≤ t ∧ t < 2 ^ 31)
    (Hk : ∃ k : Int, bv_unsigned (edenot E a) + bv_unsigned (edenot E b)
      = t + k * (2 : Int) ^ 32)
    (hlo : lo ≤ t) (hhi : t ≤ hi)
    (H : some (lo, hi) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAluw .ADD a b)) ∧
      bv_unsigned (edenot E (.EAluw .ADD a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show lo ≤ bv_unsigned (sext 64 (alu32 .ADD (low32 (edenot E a)) (low32 (edenot E b)))) ∧
      bv_unsigned (sext 64 (alu32 .ADD (low32 (edenot E a)) (low32 (edenot E b)))) ≤ hi
  rw [u_addw_small _ _ t Ht Hk]
  omega

/-- `SUBW`. -/
theorem erange_subw_sound (E : env) (a b : expr) (lo hi t rlo rhi : Int)
    (Ht : 0 ≤ t ∧ t < 2 ^ 31)
    (Hk : bv_unsigned (edenot E a) - bv_unsigned (edenot E b) = t)
    (hlo : lo ≤ t) (hhi : t ≤ hi)
    (H : some (lo, hi) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAluw .SUB a b)) ∧
      bv_unsigned (edenot E (.EAluw .SUB a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show lo ≤ bv_unsigned (sext 64 (alu32 .SUB (low32 (edenot E a)) (low32 (edenot E b)))) ∧
      bv_unsigned (sext 64 (alu32 .SUB (low32 (edenot E a)) (low32 (edenot E b)))) ≤ hi
  rw [u_subw_small _ _ t Ht Hk]
  omega

/-- `SLLW`. -/
theorem erange_sllw_sound (E : env) (a b : expr) (lo hi s rlo rhi : Int)
    (hb : bv_unsigned (edenot E b) % 64 = s)
    (Hb : bv_unsigned (edenot E a) * 2 ^ (s % 32).toNat < 2 ^ 31)
    (hlo : lo ≤ bv_unsigned (edenot E a) * 2 ^ (s % 32).toNat)
    (hhi : bv_unsigned (edenot E a) * 2 ^ (s % 32).toNat ≤ hi)
    (H : some (lo, hi) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAluw .SLL a b)) ∧
      bv_unsigned (edenot E (.EAluw .SLL a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show lo ≤ bv_unsigned (sext 64 (alu32 .SLL (low32 (edenot E a)) (low32 (edenot E b)))) ∧
      bv_unsigned (sext 64 (alu32 .SLL (low32 (edenot E a)) (low32 (edenot E b)))) ≤ hi
  rw [u_sllw_small _ _ s hb Hb]
  omega

/-- `SRLW`. -/
theorem erange_srlw_sound (E : env) (a b : expr) (lo hi s rlo rhi : Int)
    (hb : bv_unsigned (edenot E b) % 64 = s)
    (Hx : bv_unsigned (edenot E a) < 2 ^ 32)
    (Hb : bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat < 2 ^ 31)
    (hlo : lo ≤ bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat)
    (hhi : bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat ≤ hi)
    (H : some (lo, hi) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAluw .SRL a b)) ∧
      bv_unsigned (edenot E (.EAluw .SRL a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show lo ≤ bv_unsigned (sext 64 (alu32 .SRL (low32 (edenot E a)) (low32 (edenot E b)))) ∧
      bv_unsigned (sext 64 (alu32 .SRL (low32 (edenot E a)) (low32 (edenot E b)))) ≤ hi
  rw [u_srlw_small _ _ s hb Hx Hb]
  omega

/-- `SRAW`. -/
theorem erange_sraw_sound (E : env) (a b : expr) (lo hi s rlo rhi : Int)
    (hb : bv_unsigned (edenot E b) % 64 = s)
    (Hx : bv_unsigned (edenot E a) < 2 ^ 31)
    (hlo : lo ≤ bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat)
    (hhi : bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat ≤ hi)
    (H : some (lo, hi) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAluw .SRA a b)) ∧
      bv_unsigned (edenot E (.EAluw .SRA a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show lo ≤ bv_unsigned (sext 64 (alu32 .SRA (low32 (edenot E a)) (low32 (edenot E b)))) ∧
      bv_unsigned (sext 64 (alu32 .SRA (low32 (edenot E a)) (low32 (edenot E b)))) ≤ hi
  rw [u_sraw_small _ _ s hb Hx]
  omega

/-- `SRL`: `(al / 2^s, ah / 2^s)` with `s` the literal shift amount. -/
theorem erange_srl_sound (E : env) (a b : expr) (al ah s rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hs : bv_unsigned (edenot E b) % 64 = s)
    (H : some (al / zpow 2 s, ah / zpow 2 s) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SRL a b)) ∧
      bv_unsigned (edenot E (.EAlu .SRL a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show al / zpow 2 s ≤ bv_unsigned (alu64 .SRL (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SRL (edenot E a) (edenot E b)) ≤ ah / zpow 2 s
  rw [u_srl64, hs]
  have hpos : 0 < (2 : Int) ^ s.toNat := two_pow_pos_int _
  exact ⟨Int.ediv_le_ediv hpos ha.1, Int.ediv_le_ediv hpos ha.2⟩

/-- `SRA`: as `SRL`, when `ah < 2^63` (so the operand is non-negative). -/
theorem erange_sra_sound (E : env) (a b : expr) (al ah s rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hs : bv_unsigned (edenot E b) % 64 = s)
    (hc : ah < 2 ^ 63)
    (H : some (al / zpow 2 s, ah / zpow 2 s) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SRA a b)) ∧
      bv_unsigned (edenot E (.EAlu .SRA a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  show al / zpow 2 s ≤ bv_unsigned (alu64 .SRA (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SRA (edenot E a) (edenot E b)) ≤ ah / zpow 2 s
  rw [u_sra64_nonneg _ _ (by omega), hs]
  have hpos : 0 < (2 : Int) ^ s.toNat := two_pow_pos_int _
  exact ⟨Int.ediv_le_ediv hpos ha.1, Int.ediv_le_ediv hpos ha.2⟩

/-- `SLL`: `(al * 2^s, ah * 2^s)` when `ah * 2^s < 2^64`. -/
theorem erange_sll_sound (E : env) (a b : expr) (al ah s rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hs : bv_unsigned (edenot E b) % 64 = s)
    (hc : ah * zpow 2 s < 2 ^ 64)
    (H : some (al * zpow 2 s, ah * zpow 2 s) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .SLL a b)) ∧
      bv_unsigned (edenot E (.EAlu .SLL a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1, h2⟩ := H
  rw [← h1, ← h2]
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  show al * zpow 2 s ≤ bv_unsigned (alu64 .SLL (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .SLL (edenot E a) (edenot E b)) ≤ ah * zpow 2 s
  rw [u_sll64, hs]
  have hge0 : (0 : Int) ≤ 2 ^ s.toNat := Int.le_of_lt (two_pow_pos_int _)
  have hm1 : al * 2 ^ s.toNat ≤ bv_unsigned (edenot E a) * 2 ^ s.toNat :=
    Int.mul_le_mul_of_nonneg_right ha.1 hge0
  have hm2 : bv_unsigned (edenot E a) * 2 ^ s.toNat ≤ ah * 2 ^ s.toNat :=
    Int.mul_le_mul_of_nonneg_right ha.2 hge0
  have h0 : 0 ≤ bv_unsigned (edenot E a) * 2 ^ s.toNat :=
    Int.mul_nonneg hu.1 hge0
  have hc' : ah * 2 ^ s.toNat < 2 ^ 64 := hc
  have hlt : bv_unsigned (edenot E a) * 2 ^ s.toNat < 2 ^ 64 :=
    Int.lt_of_le_of_lt hm2 hc' 
  rw [Int.emod_eq_of_lt h0 hlt]
  exact ⟨hm1, hm2⟩

/-- `MUL`, no wrap: `0 ≤ al`, `0 ≤ bl`, `ah * bh < 2^64`. -/
theorem erange_mul_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (h1 : 0 ≤ al) (h2 : 0 ≤ bl) (hc : ah * bh < 2 ^ 64)
    (H : some (al * bl, ah * bh) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EMd .MUL a b)) ∧
      bv_unsigned (edenot E (.EMd .MUL a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al * bl ≤ bv_unsigned (edenot E a * edenot E b) ∧
      bv_unsigned (edenot E a * edenot E b) ≤ ah * bh
  rw [u_mul64]
  have hm1 : al * bl ≤ bv_unsigned (edenot E a) * bv_unsigned (edenot E b) := by
    exact Int.mul_le_mul ha.1 hb.1 h2 hu.1
  have hm2 : bv_unsigned (edenot E a) * bv_unsigned (edenot E b) ≤ ah * bh :=
    Int.mul_le_mul ha.2 hb.2 hv.1 (by omega)
  have h0 : 0 ≤ bv_unsigned (edenot E a) * bv_unsigned (edenot E b) :=
    Int.mul_nonneg hu.1 hv.1
  have hlt : bv_unsigned (edenot E a) * bv_unsigned (edenot E b) < 2 ^ 64 := by omega
  rw [Int.emod_eq_of_lt h0 hlt]
  exact ⟨hm1, hm2⟩

/-- `MULHU`: the high half of the product. -/
theorem erange_mulhu_sound (E : env) (a b : expr) (al ah bl bh rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hb : bl ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) ≤ bh)
    (h1 : 0 ≤ al) (h2 : 0 ≤ bl)
    (H : some (al * bl / two64, ah * bh / two64) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EMd .MULHU a b)) ∧
      bv_unsigned (edenot E (.EMd .MULHU a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show al * bl / two64 ≤ bv_unsigned (mul_div .MULHU (edenot E a) (edenot E b)) ∧
      bv_unsigned (mul_div .MULHU (edenot E a) (edenot E b)) ≤ ah * bh / two64
  rw [u_mulhu64]
  have hpos : (0 : Int) < 2 ^ 64 := by have := two_pow_pos_int 64; omega
  have hm1 : al * bl ≤ bv_unsigned (edenot E a) * bv_unsigned (edenot E b) := by
    exact Int.mul_le_mul ha.1 hb.1 h2 hu.1
  have hm2 : bv_unsigned (edenot E a) * bv_unsigned (edenot E b) ≤ ah * bh :=
    Int.mul_le_mul ha.2 hb.2 hv.1 (by omega)
  exact ⟨Int.ediv_le_ediv hpos hm1, Int.ediv_le_ediv hpos hm2⟩

/-- `DIVU`: division by the literal `d' = d mod 2^64 > 0`. -/
theorem erange_divu_sound (E : env) (a : expr) (d al ah rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (hc : 0 < d % two64)
    (H : some (al / (d % two64), ah / (d % two64)) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EMd .DIVU a (.ELit d))) ∧
      bv_unsigned (edenot E (.EMd .DIVU a (.ELit d))) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hlit : bv_unsigned (edenot E (.ELit d)) = d % two64 := by
    show bv_unsigned (Z_to_bv 64 d) = d % two64
    exact u_lit64 d
  show al / (d % two64) ≤ bv_unsigned (mul_div .DIVU (edenot E a) (edenot E (.ELit d))) ∧
      bv_unsigned (mul_div .DIVU (edenot E a) (edenot E (.ELit d))) ≤ ah / (d % two64)
  rw [u_divu64 _ _ (by rw [hlit]; exact hc), hlit]
  exact ⟨Int.ediv_le_ediv hc ha.1, Int.ediv_le_ediv hc ha.2⟩

/-- `REMU`: the remainder against `d' - 1`. -/
theorem erange_remu_sound (E : env) (a : expr) (d ah rlo rhi : Int)
    (ha : bv_unsigned (edenot E a) ≤ ah)
    (hc : 0 < d % two64)
    (H : some (0, min ah (d % two64 - 1)) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EMd .REMU a (.ELit d))) ∧
      bv_unsigned (edenot E (.EMd .REMU a (.ELit d))) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hlit : bv_unsigned (edenot E (.ELit d)) = d % two64 := by
    show bv_unsigned (Z_to_bv 64 d) = d % two64
    exact u_lit64 d
  show 0 ≤ bv_unsigned (mul_div .REMU (edenot E a) (edenot E (.ELit d))) ∧
      bv_unsigned (mul_div .REMU (edenot E a) (edenot E (.ELit d)))
        ≤ min ah (d % two64 - 1)
  rw [u_remu64 _ _ (by rw [hlit]; exact hc), hlit]
  have hnn : 0 ≤ bv_unsigned (edenot E a) % (d % two64) :=
    Int.emod_nonneg _ (by omega)
  have h1 : bv_unsigned (edenot E a) % (d % two64) ≤ ah :=
    Int.le_trans (emod_le_self _ _ hu.1 hc) ha
  have h2 : bv_unsigned (edenot E a) % (d % two64) ≤ d % two64 - 1 :=
    Int.le_sub_one_of_lt (Int.emod_lt_of_pos _ hc)
  exact ⟨hnn, Int.le_min.mpr ⟨h1, h2⟩⟩

/-! ### `EExt` and `EBlob` -/

/-- Sign-extending extension, operand already inside the low half. -/
theorem erange_ext_sx_small (E : env) (a : expr) (n : Nat) (al ah rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (h0 : 0 ≤ al) (h1 : ah < zpow 2 (8 * (n : Int)) / 2)
    (H : some (al, ah) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EExt true 0 n a)) ∧
      bv_unsigned (edenot E (.EExt true 0 n a)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  rw [zpow_two_8n] at h1
  have hlt : bv_unsigned (edenot E a) < 2 ^ (8 * n) / 2 := by omega
  show al ≤ bv_unsigned (ext_val true 0 n (edenot E a)) ∧
      bv_unsigned (ext_val true 0 n (edenot E a)) ≤ ah
  rw [u_ext_sx0_small n _ hlt]
  omega

/-- Sign-extending extension of an operand in the high half. -/
theorem erange_ext_sx_high (E : env) (a : expr) (n : Nat) (al ah rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (h1 : 1 ≤ n ∧ n ≤ 8)
    (h2 : zpow 2 (8 * (n : Int)) / 2 ≤ al)
    (h3 : ah < zpow 2 (8 * (n : Int)))
    (H : some (two64 - zpow 2 (8 * (n : Int)) + al,
        two64 - zpow 2 (8 * (n : Int)) + ah) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EExt true 0 n a)) ∧
      bv_unsigned (edenot E (.EExt true 0 n a)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hv : 2 ^ (8 * n) / 2 ≤ bv_unsigned (edenot E a) ∧
      bv_unsigned (edenot E a) < 2 ^ (8 * n) := by
    rw [zpow_two_8n] at h2 h3
    omega
  have hw : zpow 2 (8 * (n : Int)) = 2 ^ (8 * n) := zpow_two_8n n
  show two64 - zpow 2 (8 * (n : Int)) + al
      ≤ bv_unsigned (ext_val true 0 n (edenot E a)) ∧
    bv_unsigned (ext_val true 0 n (edenot E a))
      ≤ two64 - zpow 2 (8 * (n : Int)) + ah
  rw [u_ext_sx0_high n _ hv h1, hw]
  have htwo : two64 = 2 ^ 64 := two64_eq
  omega

/-- Zero-extending extension of a small operand. -/
theorem erange_ext_zx_small (E : env) (a : expr) (n : Nat) (al ah rlo rhi : Int)
    (ha : al ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) ≤ ah)
    (h0 : 0 ≤ al) (h1 : ah < zpow 2 (8 * (n : Int)))
    (H : some (al, ah) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EExt false 0 n a)) ∧
      bv_unsigned (edenot E (.EExt false 0 n a)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hlt : bv_unsigned (edenot E a) < 2 ^ (8 * n) := by
    rw [zpow_two_8n] at h1
    omega
  show al ≤ bv_unsigned (ext_val false 0 n (edenot E a)) ∧
      bv_unsigned (ext_val false 0 n (edenot E a)) ≤ ah
  rw [u_ext_zx0_small n _ hlt]
  omega

/-- Zero-extending extension, unconstrained operand: `(0, min (2^(8n)-1) (2^64-1))`. -/
theorem erange_ext_zx_other (E : env) (a : expr) (lo n : Nat) (rlo rhi : Int)
    (H : some (0, min (zpow 2 (8 * (n : Int)) - 1) two64m1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EExt false lo n a)) ∧
      bv_unsigned (edenot E (.EExt false lo n a)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2', zpow_two_8n]
  obtain ⟨hb1, hb2, hb3⟩ := u_ext_zx lo n (edenot E a)
  show 0 ≤ bv_unsigned (ext_val false lo n (edenot E a)) ∧
      bv_unsigned (ext_val false lo n (edenot E a))
        ≤ min (2 ^ (8 * n) - 1) two64m1
  refine ⟨?_, Int.le_min.mpr ⟨hb2, hb3⟩⟩
  rw [hb1]
  exact Int.emod_nonneg _ (two_pow_ne _)

/-- Sign-extended blob slice: still a word. -/
theorem erange_blob_sx_sound (E : env) (k : Nat) (i : Int) (n : Nat)
    (rlo rhi : Int) (H : some (0, two64m1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EBlob true k i n)) ∧
      bv_unsigned (edenot E (.EBlob true k i n)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (blob_val true (E.eb k) i n) ∧
      bv_unsigned (blob_val true (E.eb k) i n) < 2 ^ 64 := u64_range _
  have htwo : two64m1 = 2 ^ 64 - 1 := by
    unfold two64m1
    rw [two64_eq]
  show 0 ≤ bv_unsigned (blob_val true (E.eb k) i n) ∧
      bv_unsigned (blob_val true (E.eb k) i n) ≤ two64m1
  rw [htwo]
  omega

/-- Zero-extended blob slice: `(0, min (2^(8n)-1) (2^64-1))`. -/
theorem erange_blob_zx_sound (E : env) (k : Nat) (i : Int) (n : Nat)
    (rlo rhi : Int)
    (H : some (0, min (zpow 2 (8 * (n : Int)) - 1) two64m1) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EBlob false k i n)) ∧
      bv_unsigned (edenot E (.EBlob false k i n)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2', zpow_two_8n]
  obtain ⟨hb1, hb2⟩ := u_blob_zx (E.eb k) i n
  have hu : 0 ≤ bv_unsigned (blob_val false (E.eb k) i n) := (u64_range _).1
  show 0 ≤ bv_unsigned (blob_val false (E.eb k) i n) ∧
      bv_unsigned (blob_val false (E.eb k) i n) ≤ min (2 ^ (8 * n) - 1) two64m1
  exact ⟨hu, Int.le_min.mpr ⟨hb1, hb2⟩⟩

/-- `AND`, fallback with only `a` bounded. -/
theorem erange_and_min_l_sound (E : env) (a b : expr) (ah rlo rhi : Int)
    (ha : bv_unsigned (edenot E a) ≤ ah)
    (H : some (0, ah) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .AND a b)) ∧
      bv_unsigned (edenot E (.EAlu .AND a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 0 ≤ bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ≤ ah
  rw [u_and64]
  have hl := land_le_l (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hu.1 hv.1
  have hnn : 0 ≤ AxSymExec3.zland (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) := by
    unfold AxSymExec3.zland
    exact Int.natCast_nonneg _
  exact ⟨hnn, by omega⟩

/-- `AND`, fallback with only `b` bounded. -/
theorem erange_and_min_r_sound (E : env) (a b : expr) (bh rlo rhi : Int)
    (hb : bv_unsigned (edenot E b) ≤ bh)
    (H : some (0, bh) = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E (.EAlu .AND a b)) ∧
      bv_unsigned (edenot E (.EAlu .AND a b)) ≤ rhi := by
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨h1', h2'⟩ := H
  rw [← h1', ← h2']
  have hu : 0 ≤ bv_unsigned (edenot E a) ∧ bv_unsigned (edenot E a) < 2 ^ 64 :=
    u64_range (edenot E a)
  have hv : 0 ≤ bv_unsigned (edenot E b) ∧ bv_unsigned (edenot E b) < 2 ^ 64 :=
    u64_range (edenot E b)
  show 0 ≤ bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ∧
      bv_unsigned (alu64 .AND (edenot E a) (edenot E b)) ≤ bh
  rw [u_and64]
  have hr := land_le_r (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) hu.1 hv.1
  have hnn : 0 ≤ AxSymExec3.zland (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) := by
    unfold AxSymExec3.zland
    exact Int.natCast_nonneg _
  exact ⟨hnn, by omega⟩

/-- A power of two equal to `m mod 2^64 + 1` has exponent at most `64`
    (the `j ≤ 64` side condition of `land_lowmask`). -/
theorem pow_two_le_of_mod_succ (m j : Int) (h : m % two64 + 1 = zpow 2 j) : j ≤ 64 := by
  have hlt : m % two64 + 1 ≤ (2 : Int) ^ 64 := by
    have h1 := Int.emod_lt_of_pos m two64_pos
    rw [two64_eq] at h1 ⊢
    omega
  have hle : zpow 2 j ≤ (2 : Int) ^ 64 := by rw [← h]; exact hlt
  have hz : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := by
    unfold zpow
    exact natCast_pow_two _
  rw [hz, natCast_pow_two 64] at hle
  have h2 : (2 : Nat) ^ j.toNat ≤ 2 ^ 64 := Int.ofNat_le.mp hle
  have h3 : j.toNat ≤ 64 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h2
  have := (Int.toNat_le (m := j) (n := 64)).mp h3
  simpa using this

/-! ### `erange_f_sound`

    The main lemma.  `find_range` gives the `KRange` interval; the linear
    form gives the shifted interval when it lies inside one `2^64` block;
    otherwise the syntax-directed arms. -/
theorem erange_f_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (Hkn : know_ok segs E M kn) :
    ∀ (fuel : Nat) (e : expr) (rlo rhi : Int),
      erange_f fuel kn e = some (rlo, rhi) →
      rlo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ rhi := by
  intro fuel
  induction fuel with
  | zero =>
    intro e rlo rhi H
    simp [erange_f] at H
  | succ fuel ih =>
    intro e rlo rhi H
    cases hfr : find_range kn e with
    | some r =>
      simp only [erange_f, hfr] at H
      have hb := find_range_sound segs E M kn e r.1 r.2 Hkn hfr
      exact clampi_sound (edenot E e) r.1 r.2 rlo rhi hb (Option.some.inj H)
    | none =>
      simp only [erange_f, hfr] at H
      split at H
      · -- the linear form decides
        rename_i xL rL heqL
        obtain ⟨lo1, hi1⟩ := rL
        obtain ⟨hA1, hA2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj H)
        by_cases htriv : lin_trivial (lin_of e) = true
        · rw [ite_eq_left htriv] at heqL
          simp at heqL
        · rw [ite_eq_right htriv] at heqL
          cases hlr : lin_range (erange_f fuel kn) (lin_of e).fst (lin_of e).snd with
          | none => rw [hlr] at heqL; simp at heqL
          | some p =>
            obtain ⟨lo2, hi2⟩ := p
            rw [hlr] at heqL
            dsimp only at heqL
            by_cases hq : (zdiv64 lo2 == zdiv64 hi2) = true
            · rw [ite_eq_left hq] at heqL
              obtain ⟨he1, he2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj heqL)
              rw [← hA1, ← hA2, ← he1, ← he2]
              exact erange_f_lin_sound E kn fuel e ih lo2 hi2 hlr hq
            · rw [ite_eq_right hq] at heqL
              simp at heqL
      · -- the syntax-directed arms
        cases e with
        | ELit z =>
          dsimp only at H
          exact erange_lit_sound E z rlo rhi H
        | EVar n =>
          dsimp only at H
          simp at H
        | EAlu op a b =>
          dsimp only at H
          cases op with
          | ADD =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : ah + bh < two64
                · rw [ite_eq_left hc] at H
                  obtain ⟨e1, e2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj H)
                  rw [← e1, ← e2]
                  exact erange_add_sound E a b al ah bl bh (ih a al ah h1) (ih b bl bh h2) hc
                · rw [ite_eq_right hc] at H
                  by_cases hc2 : two64 ≤ al + bl
                  · rw [ite_eq_left hc2] at H
                    obtain ⟨e1, e2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj H)
                    rw [← e1, ← e2]
                    exact erange_add_sound_hi E a b al ah bl bh
                      (ih a al ah h1) (ih b bl bh h2) hc hc2
                  · rw [ite_eq_right hc2] at H
                    simp at H
          | SUB =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : bh ≤ al
                · rw [ite_eq_left hc] at H
                  obtain ⟨e1, e2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj H)
                  rw [← e1, ← e2]
                  exact erange_sub_sound E a b al ah bl bh (ih a al ah h1) (ih b bl bh h2) hc
                · rw [ite_eq_right hc] at H
                  by_cases hc2 : ah < bl
                  · rw [ite_eq_left hc2] at H
                    obtain ⟨e1, e2⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj H)
                    rw [← e1, ← e2]
                    exact erange_sub_sound_hi E a b al ah bl bh
                      (ih a al ah h1) (ih b bl bh h2) hc hc2
                  · rw [ite_eq_right hc2] at H
                    simp at H
          | AND =>
            dsimp only at H
            cases b with
            | ELit m =>
              cases h1 : erange_f fuel kn a with
              | none =>
                cases h2 : erange_f fuel kn (expr.ELit m) with
                | none => rw [h1, h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h1, h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.ELit m) bh rlo rhi
                    (ih (expr.ELit m) bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                dsimp only at H
                by_cases hc1 : (m % two64 + 1 == zpow 2 (AxSymExec3.zlog2 (m % two64 + 1)) && al / zpow 2 (AxSymExec3.zlog2 (m % two64 + 1)) ≤ ah / zpow 2 (AxSymExec3.zlog2 (m % two64 + 1)) && al / zpow 2 (AxSymExec3.zlog2 (m % two64 + 1)) == ah / zpow 2 (AxSymExec3.zlog2 (m % two64 + 1))) = true
                · rw [ite_eq_left hc1] at H
                  dsimp only at H
                  obtain ⟨hAB, hC⟩ := (Bool.and_eq_true ..).mp hc1
                  obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp hAB
                  exact erange_and_low_sound E a m al ah (AxSymExec3.zlog2 (m % two64 + 1)) rlo rhi
                    (ih a al ah h1)
                    ⟨zlog2_nonneg _, pow_two_le_of_mod_succ m _ (beq_iff_eq.mp hA)⟩ hA hC H
                · rw [ite_eq_right hc1] at H
                  by_cases hc2 : (two64 - m % two64 == zpow 2 (AxSymExec3.zlog2 (two64 - m % two64)) && AxSymExec3.zlog2 (two64 - m % two64) < 64) = true
                  · rw [ite_eq_left hc2] at H
                    dsimp only at H
                    obtain ⟨hP, hJ⟩ := (Bool.and_eq_true ..).mp hc2
                    exact erange_and_high_sound E a m al ah
                      (AxSymExec3.zlog2 (two64 - m % two64)) rlo rhi (ih a al ah h1)
                      ⟨zlog2_nonneg _, by simpa using hJ⟩ hP H
                  · rw [ite_eq_right hc2] at H
                    cases h2 : erange_f fuel kn (expr.ELit m) with
                    | none => rw [h2] at H; dsimp only at H
                              exact erange_and_min_l_sound E a (expr.ELit m) ah rlo rhi
                                (ih a al ah h1).2 H
                    | some p2 =>
                      obtain ⟨bl, bh⟩ := p2
                      rw [h2] at H; dsimp only at H
                      exact erange_and_min_sound E a (expr.ELit m) ah bh rlo rhi
                        (ih a al ah h1).2 (ih (expr.ELit m) bl bh h2).2 H
            | EVar n =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EVar n) with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EVar n) bh rlo rhi (ih (expr.EVar n) bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EVar n) with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EVar n) ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EVar n) ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EVar n) bl bh h2).2 H
            | EAlu op' a' b' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EAlu op' a' b') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EAlu op' a' b') bh rlo rhi (ih (expr.EAlu op' a' b') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EAlu op' a' b') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EAlu op' a' b') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EAlu op' a' b') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EAlu op' a' b') bl bh h2).2 H
            | EAluw op' a' b' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EAluw op' a' b') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EAluw op' a' b') bh rlo rhi (ih (expr.EAluw op' a' b') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EAluw op' a' b') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EAluw op' a' b') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EAluw op' a' b') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EAluw op' a' b') bl bh h2).2 H
            | EMd op' a' b' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EMd op' a' b') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EMd op' a' b') bh rlo rhi (ih (expr.EMd op' a' b') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EMd op' a' b') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EMd op' a' b') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EMd op' a' b') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EMd op' a' b') bl bh h2).2 H
            | EMdw op' a' b' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EMdw op' a' b') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EMdw op' a' b') bh rlo rhi (ih (expr.EMdw op' a' b') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EMdw op' a' b') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EMdw op' a' b') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EMdw op' a' b') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EMdw op' a' b') bl bh h2).2 H
            | EExt sx' lo' n' a' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EExt sx' lo' n' a') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EExt sx' lo' n' a') bh rlo rhi (ih (expr.EExt sx' lo' n' a') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EExt sx' lo' n' a') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EExt sx' lo' n' a') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EExt sx' lo' n' a') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EExt sx' lo' n' a') bl bh h2).2 H
            | EBlob sx' k' i' n' =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EBlob sx' k' i' n') with
                | none => rw [h2] at H; dsimp only at H; simp at H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H; dsimp only at H
                  exact erange_and_min_r_sound E a (expr.EBlob sx' k' i' n') bh rlo rhi (ih (expr.EBlob sx' k' i' n') bl bh h2).2 H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                cases h2 : erange_f fuel kn (expr.EBlob sx' k' i' n') with
                | none => rw [h2] at H; dsimp only at H
                          exact erange_and_min_l_sound E a (expr.EBlob sx' k' i' n') ah rlo rhi (ih a al ah h1).2 H
                | some p2 =>
                  obtain ⟨bl, bh⟩ := p2
                  rw [h2] at H
                  dsimp only at H
                  exact erange_and_min_sound E a (expr.EBlob sx' k' i' n') ah bh rlo rhi
                    (ih a al ah h1).2 (ih (expr.EBlob sx' k' i' n') bl bh h2).2 H
          | OR =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                exact erange_or_sound E a b al ah bl bh rlo rhi
                  (ih a al ah h1) (ih b bl bh h2) H
          | XOR =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                exact erange_xor_sound E a b ah bh rlo rhi
                  (ih a al ah h1).2 (ih b bl bh h2).2 H
          | SRL =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                exact erange_srl_sound E a b al ah s rlo rhi (ih a al ah h1) hbs H
          | SRA =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                by_cases hc : ah < zpow 2 63
                · rw [ite_eq_left hc] at H
                  exact erange_sra_sound E a b al ah s rlo rhi (ih a al ah h1) hbs hc H
                · rw [ite_eq_right hc] at H
                  simp at H
          | SLL =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                by_cases hc : ah * zpow 2 s < two64
                · rw [ite_eq_left hc] at H
                  exact erange_sll_sound E a b al ah s rlo rhi (ih a al ah h1) hbs hc H
                · rw [ite_eq_right hc] at H
                  simp at H
          | SLTU =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H
                      exact erange_sltu_mid_sound E a b rlo rhi H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H
                        exact erange_sltu_mid_sound E a b rlo rhi H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : ah < bl
                · rw [ite_eq_left hc] at H
                  exact erange_sltu_lt_sound E a b al ah bl bh rlo rhi
                    (ih a al ah h1) (ih b bl bh h2) hc H
                · rw [ite_eq_right hc] at H
                  by_cases hc2 : bh ≤ al
                  · rw [ite_eq_left hc2] at H
                    exact erange_sltu_gt_sound E a b al ah bl bh rlo rhi
                      (ih a al ah h1) (ih b bl bh h2) hc2 H
                  · rw [ite_eq_right hc2] at H
                    exact erange_sltu_mid_sound E a b rlo rhi H
          | SLT =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H
                      exact erange_slt_mid_sound E a b rlo rhi H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H
                        exact erange_slt_mid_sound E a b rlo rhi H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hcc : (ah < zpow 2 63 && bh < zpow 2 63) = true
                · rw [ite_eq_left hcc] at H
                  obtain ⟨hx, hy⟩ := (Bool.and_eq_true ..).mp hcc
                  have ha63 : ah < 2 ^ 63 := of_decide_eq_true hx
                  have hb63 : bh < 2 ^ 63 := of_decide_eq_true hy
                  by_cases hc : ah < bl
                  · rw [ite_eq_left hc] at H
                    exact erange_slt_lt_sound E a b al ah bl bh rlo rhi
                      (ih a al ah h1) (ih b bl bh h2) ha63 hb63 hc H
                  · rw [ite_eq_right hc] at H
                    by_cases hc2 : bh ≤ al
                    · rw [ite_eq_left hc2] at H
                      exact erange_slt_gt_sound E a b al ah bl bh rlo rhi
                        (ih a al ah h1) (ih b bl bh h2) ha63 hb63 hc2 H
                    · rw [ite_eq_right hc2] at H
                      exact erange_slt_mid_sound E a b rlo rhi H
                · rw [ite_eq_right hcc] at H
                  exact erange_slt_mid_sound E a b rlo rhi H
        | EAluw op a b =>
          dsimp only at H
          cases op with
          | ADD =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hbe : (bl == bh) = true
                · repeat rw [ite_eq_left hbe] at H
                  by_cases hs : two63z ≤ bl
                  · rw [zsigned64_of_ge bl hs] at H
                    have hbh : two63z ≤ bh := by rw [← beq_iff_eq.mp hbe]; exact hs
                    rw [zsigned64_of_ge bh hbh] at H
                    by_cases hc : (0 ≤ al + (bl - two64) && ah + (bh - two64) < zpow 2 31) = true
                    · rw [ite_eq_left hc] at H
                      obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                      have hc0' : 0 ≤ al + (bl - two64) := by simpa using hc0
                      have hc1' : ah + (bh - two64) < zpow 2 31 := of_decide_eq_true hc1
                      have hc1'' : ah + (bh - two64) < 2 ^ 31 := hc1'
                      refine erange_addw_sound E a b (al + (bl - two64)) (ah + (bh - two64))
                        (bv_unsigned (edenot E a) + bv_unsigned (edenot E b) - two64) rlo rhi
                        ⟨by omega, by omega⟩ ⟨2 ^ 32, by rw [two32_mul_two32, ← two64_eq]; omega⟩
                        (by omega) (by omega) H
                    · rw [ite_eq_right hc] at H
                      simp at H
                  · rw [zsigned64_of_lt bl (by omega)] at H
                    have hbh : ¬ two63z ≤ bh := by rw [← beq_iff_eq.mp hbe]; exact hs
                    rw [zsigned64_of_lt bh (by omega)] at H
                    by_cases hc : (0 ≤ al + bl && ah + bh < zpow 2 31) = true
                    · rw [ite_eq_left hc] at H
                      obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                      have hc0' : 0 ≤ al + bl := by simpa using hc0
                      have hc1' : ah + bh < 2 ^ 31 := of_decide_eq_true hc1
                      refine erange_addw_sound E a b (al + bl) (ah + bh)
                        (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) rlo rhi
                        ⟨by omega, by omega⟩ ⟨0, by omega⟩ (by omega) (by omega) H
                    · rw [ite_eq_right hc] at H
                      simp at H
                · repeat rw [ite_eq_right hbe] at H
                  by_cases hc : (0 ≤ al + bl && ah + bh < zpow 2 31) = true
                  · rw [ite_eq_left hc] at H
                    obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                    have hc0' : 0 ≤ al + bl := by simpa using hc0
                    have hc1' : ah + bh < 2 ^ 31 := of_decide_eq_true hc1
                    refine erange_addw_sound E a b (al + bl) (ah + bh)
                      (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) rlo rhi
                      ⟨by omega, by omega⟩ ⟨0, by omega⟩ (by omega) (by omega) H
                  · rw [ite_eq_right hc] at H
                    simp at H
          | SUB =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : (bh ≤ al && ah - bl < zpow 2 31) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                  have hc0' : bh ≤ al := by simpa using hc0
                  have hc1' : ah - bl < 2 ^ 31 := of_decide_eq_true hc1
                  refine erange_subw_sound E a b (al - bh) (ah - bl)
                    _ rlo rhi ⟨by omega, by omega⟩ rfl (by omega) (by omega) H
                · rw [ite_eq_right hc] at H
                  simp at H
          | SLL =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                have hzp : zpow 2 (s % 32) = 2 ^ (s % 32).toNat := rfl
                have hzp31 : zpow 2 31 = (2 : Int) ^ 31 := rfl
                rw [hzp, hzp31] at H
                by_cases hc : ah * 2 ^ (s % 32).toNat < (2 : Int) ^ 31
                · rw [ite_eq_left hc] at H
                  have hb' : bv_unsigned (edenot E a) * 2 ^ (s % 32).toNat < 2 ^ 31 := by
                    have hle : bv_unsigned (edenot E a) * 2 ^ (s % 32).toNat
                        ≤ ah * 2 ^ (s % 32).toNat :=
                      Int.mul_le_mul_of_nonneg_right (ih a al ah h1).2
                        (Int.le_of_lt (two_pow_pos_int _))
                    omega
                  refine erange_sllw_sound E a b (al * 2 ^ (s % 32).toNat)
                    (ah * 2 ^ (s % 32).toNat) s rlo rhi hbs hb' ?_ ?_ H
                  · exact Int.mul_le_mul_of_nonneg_right (ih a al ah h1).1
                      (Int.le_of_lt (two_pow_pos_int _))
                  · exact Int.mul_le_mul_of_nonneg_right (ih a al ah h1).2
                      (Int.le_of_lt (two_pow_pos_int _))
                · rw [ite_eq_right hc] at H
                  simp at H
          | SRL =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                have hzp : zpow 2 (s % 32) = 2 ^ (s % 32).toNat := rfl
                have hzp32 : zpow 2 32 = (2 : Int) ^ 32 := rfl
                have hzp31 : zpow 2 31 = (2 : Int) ^ 31 := rfl
                rw [hzp, hzp32, hzp31] at H
                by_cases hc : (ah < (2 : Int) ^ 32
                    && (0 < s % 32 || ah < (2 : Int) ^ 31)) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                  have hx32' : ah < (2 : Int) ^ 32 := of_decide_eq_true hc0
                  have hx32 : bv_unsigned (edenot E a) < (2 : Int) ^ 32 := by omega
                  have hb' : bv_unsigned (edenot E a) / 2 ^ (s % 32).toNat < 2 ^ 31 := by
                    rcases (Bool.or_eq_true ..).mp hc1 with h0 | h0
                    · have hs1 : 0 < s % 32 := of_decide_eq_true h0
                      have hd : (2 : Int) ≤ 2 ^ (s % 32).toNat := by
                        have h1' : ((s % 32).toNat : Int) = s % 32 :=
                          Int.toNat_of_nonneg (by omega)
                        have h2 : (1 : Nat) ≤ (s % 32).toNat := by
                          rw [← Int.ofNat_le, h1']
                          omega
                        have h3 := int_pow_le_pow 1 (s % 32).toNat h2
                        simpa using h3
                      have hmul : (2 : Int) ^ 31 * 2 ≤ (2 : Int) ^ 31 * 2 ^ (s % 32).toNat :=
                        Int.mul_le_mul_of_nonneg_left hd (Int.le_of_lt (two_pow_pos_int 31))
                      have h32 : (2 : Int) ^ 31 * 2 = 2 ^ 32 := by
                        rw [← Int.pow_succ]
                      rw [Int.ediv_lt_iff_lt_mul (two_pow_pos_int _)]
                      omega
                    · have h0' : bv_unsigned (edenot E a) < (2 : Int) ^ 31 := by
                        have hh : ah < (2 : Int) ^ 31 := by simpa using h0
                        omega
                      exact Int.lt_of_le_of_lt
                        (Int.ediv_le_self _ (Int.natCast_nonneg _)) h0'
                  refine erange_srlw_sound E a b (al / 2 ^ (s % 32).toNat)
                    (ah / 2 ^ (s % 32).toNat) s rlo rhi hbs ?_ hb' ?_ ?_ H
                  · exact hx32
                  · exact Int.ediv_le_ediv (two_pow_pos_int _) (ih a al ah h1).1
                  · exact Int.ediv_le_ediv (two_pow_pos_int _) (ih a al ah h1).2
                · rw [ite_eq_right hc] at H
                  simp at H
          | SRA =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              have hA := ih a al ah h1
              cases hl : lit_shamt b with
              | none => rw [hl] at H; dsimp only at H; simp at H
              | some s =>
                rw [hl] at H
                dsimp only at H
                obtain ⟨hbs, hs0, hs64⟩ := lit_shamt_sound E b s hl
                have hzp : zpow 2 (s % 32) = 2 ^ (s % 32).toNat := rfl
                have hzp31 : zpow 2 31 = (2 : Int) ^ 31 := rfl
                rw [hzp, hzp31] at H
                by_cases hc : ah < (2 : Int) ^ 31
                · rw [ite_eq_left hc] at H
                  refine erange_sraw_sound E a b (al / 2 ^ (s % 32).toNat)
                    (ah / 2 ^ (s % 32).toNat) s rlo rhi hbs (by omega) ?_ ?_ H
                  · exact Int.ediv_le_ediv (two_pow_pos_int _) (ih a al ah h1).1
                  · exact Int.ediv_le_ediv (two_pow_pos_int _) (ih a al ah h1).2
                · rw [ite_eq_right hc] at H
                  simp at H
          | _ =>
            simp at H
        | EMd op a b =>
          dsimp only at H
          cases op with
          | MUL =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : (0 ≤ al && 0 ≤ bl && ah * bh < two64) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc01, hc2⟩ := (Bool.and_eq_true ..).mp hc
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc01
                  have h0 : 0 ≤ al := by simpa using hc0
                  have h0' : 0 ≤ bl := by simpa using hc1
                  have hc2' : ah * bh < two64 := by simpa using hc2
                  exact erange_mul_sound E a b al ah bl bh rlo rhi
                    (ih a al ah h1) (ih b bl bh h2) h0 h0' hc2' H
                · rw [ite_eq_right hc] at H
                  simp at H
          | MULHU =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              cases h2 : erange_f fuel kn b with
              | none => rw [h1, h2] at H; dsimp only at H; simp at H
              | some p2 =>
                obtain ⟨bl, bh⟩ := p2
                rw [h1, h2] at H
                dsimp only at H
                have hA := ih a al ah h1
                have hB := ih b bl bh h2
                by_cases hc : (0 ≤ al && 0 ≤ bl) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                  have h0 : 0 ≤ al := by simpa using hc0
                  have h0' : 0 ≤ bl := by simpa using hc1
                  exact erange_mulhu_sound E a b al ah bl bh rlo rhi
                    (ih a al ah h1) (ih b bl bh h2) h0 h0' H
                · rw [ite_eq_right hc] at H
                  simp at H
          | DIVU =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              cases b with
              | ELit d =>
                dsimp only at H
                by_cases hc : 0 < d % two64
                · rw [ite_eq_left hc] at H
                  exact erange_divu_sound E a d al ah rlo rhi (ih a al ah h1) hc H
                · rw [ite_eq_right hc] at H
                  simp at H
              | EVar n => dsimp only at H; simp at H
              | EAlu op' a' b' => dsimp only at H; simp at H
              | EAluw op' a' b' => dsimp only at H; simp at H
              | EMd op' a' b' => dsimp only at H; simp at H
              | EMdw op' a' b' => dsimp only at H; simp at H
              | EExt sx' lo' n' a' => dsimp only at H; simp at H
              | EBlob sx' k' i' n' => dsimp only at H; simp at H
          | REMU =>
            dsimp only at H
            cases h1 : erange_f fuel kn a with
            | none => rw [h1] at H; dsimp only at H; simp at H
            | some p1 =>
              obtain ⟨al, ah⟩ := p1
              rw [h1] at H
              cases b with
              | ELit d =>
                dsimp only at H
                by_cases hc : 0 < d % two64
                · rw [ite_eq_left hc] at H
                  exact erange_remu_sound E a d ah rlo rhi (ih a al ah h1).2 hc H
                · rw [ite_eq_right hc] at H
                  simp at H
              | EVar n => dsimp only at H; simp at H
              | EAlu op' a' b' => dsimp only at H; simp at H
              | EAluw op' a' b' => dsimp only at H; simp at H
              | EMd op' a' b' => dsimp only at H; simp at H
              | EMdw op' a' b' => dsimp only at H; simp at H
              | EExt sx' lo' n' a' => dsimp only at H; simp at H
              | EBlob sx' k' i' n' => dsimp only at H; simp at H
          | _ =>
            simp at H
        | EMdw op a b =>
          simp at H
        | EExt sx lo n a =>
          dsimp only at H
          cases sx with
          | true =>
            rw [ite_eq_left rfl] at H
            cases lo with
            | zero =>
              cases h1 : erange_f fuel kn a with
              | none => rw [h1] at H; simp at H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                simp only [Option.some.injEq, Prod.mk.injEq] at H
                by_cases hc : (0 ≤ al && ah < zpow 2 (8 * (n : Int)) / 2) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                  have h0 : 0 ≤ al := by simpa using hc0
                  have h1' : ah < zpow 2 (8 * (n : Int)) / 2 := by simpa using hc1
                  exact erange_ext_sx_small E a n al ah rlo rhi (ih a al ah h1) h0 h1' H
                · rw [ite_eq_right hc] at H
                  by_cases hc2 : (1 ≤ n && n ≤ 8 && zpow 2 (8 * (n : Int)) / 2 ≤ al
                      && ah < zpow 2 (8 * (n : Int))) = true
                  · rw [ite_eq_left hc2] at H
                    obtain ⟨hc2', hAh⟩ := (Bool.and_eq_true ..).mp hc2
                    obtain ⟨hc2'', hAl⟩ := (Bool.and_eq_true ..).mp hc2'
                    obtain ⟨h1n, h8n⟩ := (Bool.and_eq_true ..).mp hc2''
                    have hn1 : 1 ≤ n := of_decide_eq_true h1n
                    have hn8 : n ≤ 8 := of_decide_eq_true h8n
                    have hal' : zpow 2 (8 * (n : Int)) / 2 ≤ al := of_decide_eq_true hAl
                    have hah' : ah < zpow 2 (8 * (n : Int)) := of_decide_eq_true hAh
                    exact erange_ext_sx_high E a n al ah rlo rhi
                      (ih a al ah h1) ⟨hn1, hn8⟩ hal' hah' H
                  · rw [ite_eq_right hc2] at H
                    simp at H
            | succ lo =>
              simp at H
          | false =>
            rw [ite_eq_right (by decide)] at H
            cases lo with
            | zero =>
              cases h1 : erange_f fuel kn a with
              | none =>
                rw [h1] at H
                exact erange_ext_zx_other E a 0 n rlo rhi H
              | some p1 =>
                obtain ⟨al, ah⟩ := p1
                rw [h1] at H
                simp only [Option.some.injEq, Prod.mk.injEq] at H
                by_cases hc : (0 ≤ al && ah < zpow 2 (8 * (n : Int))) = true
                · rw [ite_eq_left hc] at H
                  obtain ⟨hc0, hc1⟩ := (Bool.and_eq_true ..).mp hc
                  have h0 : 0 ≤ al := by simpa using hc0
                  have h1' : ah < zpow 2 (8 * (n : Int)) := by simpa using hc1
                  exact erange_ext_zx_small E a n al ah rlo rhi (ih a al ah h1) h0 h1' H
                · rw [ite_eq_right hc] at H
                  exact erange_ext_zx_other E a 0 n rlo rhi H
            | succ lo =>
              exact erange_ext_zx_other E a (lo + 1) n rlo rhi H
        | EBlob sx k i n =>
          dsimp only at H
          cases sx with
          | true =>
            rw [ite_eq_left rfl] at H
            exact erange_blob_sx_sound E k i n rlo rhi H
          | false =>
            rw [ite_eq_right (by decide)] at H
            exact erange_blob_zx_sound E k i n rlo rhi H

/-! ### `facts_of`, `erange0`, `deand`, `erange` -/

/-- Filtering a knowledge list preserves its denotation. -/
theorem facts_of_ok (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (H : know_ok segs E M kn) :
    know_ok segs E M (facts_of kn) := by
  intro K HK
  rw [facts_of_filter] at HK
  exact H K (List.mem_filter.mp HK).1

/-- `erange0_sound`: the basic interval domain is sound. -/
theorem erange0_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (rlo rhi : Int) (Hkn : know_ok segs E M kn)
    (H : erange0 kn e = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ rhi :=
  erange_f_sound segs E M (facts_of kn) (facts_of_ok segs E M kn Hkn) erange_fuel e rlo rhi H

/-- The `deand`-does-nothing case: `s = 0`, `rho = 0`. -/
theorem deand_zero (E : env) (e : expr) :
    0 ≤ (0 : Int) ∧ ∃ rho : Int, (0 ≤ rho ∧ rho ≤ 0) ∧
      eqm (bv_unsigned (edenot E e)) (bv_unsigned (edenot E e) - rho) :=
  ⟨Int.le_refl 0, 0, ⟨Int.le_refl 0, Int.le_refl 0⟩,
    by simpa using eqm_refl (bv_unsigned (edenot E e))⟩

/-- **[deand]**: the value of [e] is that of the de-ANDed form minus a
    residue of at most [s] (modulo 2^64). -/
theorem deand_sound (E : env) (e : expr) :
    ∀ (e' : expr) (s : Int), deand e = (e', s) →
      0 ≤ s ∧ ∃ rho : Int, (0 ≤ rho ∧ rho ≤ s) ∧
        eqm (bv_unsigned (edenot E e)) (bv_unsigned (edenot E e') - rho) := by
  induction e with
  | ELit z =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.ELit z)
  | EVar n =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EVar n)
  | EAlu op a b iha ihb =>
    intro e' s H
    cases op with
    | ADD =>
      obtain ⟨pa, h1⟩ : ∃ p : expr × Int, deand a = p := ⟨deand a, rfl⟩
      obtain ⟨a', s1⟩ := pa
      obtain ⟨pb, h2⟩ : ∃ p : expr × Int, deand b = p := ⟨deand b, rfl⟩
      obtain ⟨b', s2⟩ := pb
      simp only [deand, h1, h2, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      obtain ⟨hs1, r1, ⟨hr1a, hr1b⟩, he1⟩ := iha a' s1 h1
      obtain ⟨hs2, r2, ⟨hr2a, hr2b⟩, he2⟩ := ihb b' s2 h2
      have h1' : eqm (bv_unsigned (edenot E (.EAlu .ADD a b)))
          (bv_unsigned (edenot E a) + bv_unsigned (edenot E b)) := u_add_eqm _ _
      have h2' : eqm (bv_unsigned (edenot E (.EAlu .ADD a' b')))
          (bv_unsigned (edenot E a') + bv_unsigned (edenot E b')) := u_add_eqm _ _
      refine ⟨by omega, r1 + r2, ⟨by omega, by omega⟩, ?_⟩
      refine eqm_trans (eqm_trans h1' (eqm_add he1 he2)) ?_
      have e1 : (bv_unsigned (edenot E a') - r1) + (bv_unsigned (edenot E b') - r2)
          = (bv_unsigned (edenot E a') + bv_unsigned (edenot E b')) + (-(r1 + r2)) := by
        omega
      have e2 : bv_unsigned (edenot E (.EAlu .ADD a' b')) - (r1 + r2)
          = bv_unsigned (edenot E (.EAlu .ADD a' b')) + (-(r1 + r2)) := by omega
      rw [e1, e2]
      exact eqm_add (eqm_sym h2') (eqm_refl _)
    | AND =>
      cases b with
      | ELit m =>
        simp only [deand] at H
        generalize hmm : m % two64 = mm at H
        generalize hj : AxSymExec3.zlog2 (two64 - mm) = j at H
        by_cases hc : (two64 - mm == zpow 2 j && decide (j ≤ 48)) = true
        · rw [ite_eq_left hc] at H
          obtain ⟨hp, hj48⟩ := (Bool.and_eq_true ..).mp hc
          have hpow : two64 - mm = zpow 2 j := by simpa using hp
          have hjle : j ≤ 48 := of_decide_eq_true hj48
          have hj0 : 0 ≤ j := by rw [← hj]; exact zlog2_nonneg _
          have hjlt : j < 64 := by omega
          have hmm2 : mm = 2 ^ 64 - zpow 2 j := by
            rw [← two64_eq]
            omega
          have hpow_pos : (0 : Int) < zpow 2 j := by
            have h : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := natCast_pow_two _
            rw [h]
            exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
          obtain ⟨pa, h1⟩ : ∃ p : expr × Int, deand a = p := ⟨deand a, rfl⟩
          obtain ⟨a', s1⟩ := pa
          simp only [h1] at H
          simp only [Prod.mk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          obtain ⟨hs1, r1, ⟨hr1a, hr1b⟩, he1⟩ := iha a' s1 h1
          have hx := u64_range (edenot E a)
          have hmod0 : 0 ≤ bv_unsigned (edenot E a) % zpow 2 j :=
            Int.emod_nonneg _ (Int.ne_of_gt hpow_pos)
          have hmodlt : bv_unsigned (edenot E a) % zpow 2 j < zpow 2 j :=
            Int.emod_lt_of_pos _ hpow_pos
          have huE : bv_unsigned (edenot E (.EAlu .AND a (.ELit m)))
              = bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j := by
            show bv_unsigned (alu64 .AND (edenot E a) (edenot E (.ELit m))) = _
            rw [u_and64]
            have hlit : bv_unsigned (edenot E (.ELit m)) = mm := by
              show bv_unsigned (Z_to_bv 64 m) = mm
              rw [u_lit64]
              exact hmm
            rw [hlit, hmm2]
            exact land_highmask _ j ⟨hj0, hjlt⟩ ⟨hx.1, hx.2⟩
          refine ⟨by omega, r1 + bv_unsigned (edenot E a) % zpow 2 j,
            ⟨by omega, by omega⟩, ?_⟩
          rw [huE]
          have e1 : bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j
              = bv_unsigned (edenot E a) + -(bv_unsigned (edenot E a) % zpow 2 j) := by omega
          have e2 : bv_unsigned (edenot E a')
                - (r1 + bv_unsigned (edenot E a) % zpow 2 j)
              = (bv_unsigned (edenot E a') - r1)
                + -(bv_unsigned (edenot E a) % zpow 2 j) := by omega
          rw [e1, e2]
          exact eqm_add he1 (eqm_refl _)
        · rw [ite_eq_right hc] at H
          simp only [Prod.mk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          exact deand_zero E (.EAlu .AND a (.ELit m))
      | EVar n =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EVar n))
      | EAlu op2 a2 b2 =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EAlu op2 a2 b2))
      | EAluw op2 a2 b2 =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EAluw op2 a2 b2))
      | EMd op2 a2 b2 =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EMd op2 a2 b2))
      | EMdw op2 a2 b2 =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EMdw op2 a2 b2))
      | EExt sx lo n a2 =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EExt sx lo n a2))
      | EBlob sx k i n =>
        simp only [deand, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact deand_zero E (.EAlu .AND a (.EBlob sx k i n))
    | SUB =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SUB a b)
    | SLL =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SLL a b)
    | SLT =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SLT a b)
    | SLTU =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SLTU a b)
    | XOR =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .XOR a b)
    | SRL =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SRL a b)
    | SRA =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .SRA a b)
    | OR =>
      simp only [deand, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      exact deand_zero E (.EAlu .OR a b)
  | EAluw op a b =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EAluw op a b)
  | EMd op a b =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EMd op a b)
  | EMdw op a b =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EMdw op a b)
  | EExt sx lo n a =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EExt sx lo n a)
  | EBlob sx k i n =>
    intro e' s H
    simp only [deand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    exact deand_zero E (.EBlob sx k i n)

/-- `erange_sound`: the interval domain with the align-down
    tightening is sound. -/
theorem erange_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (rlo rhi : Int) (Hkn : know_ok segs E M kn)
    (H : erange kn e = some (rlo, rhi)) :
    rlo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ rhi := by
  have H0 : ∀ (lo hi : Int), erange0 kn e = some (lo, hi) →
      lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi :=
    fun lo hi He => erange0_sound segs E M kn e lo hi Hkn He
  obtain ⟨p, Hd⟩ : ∃ p : expr × Int, deand e = p := ⟨deand e, rfl⟩
  obtain ⟨e', s⟩ := p
  simp only [erange, Hd] at H
  by_cases hs0 : (s == 0) = true
  · rw [ite_eq_left hs0] at H
    exact H0 rlo rhi H
  · rw [ite_eq_right hs0] at H
    cases he : erange0 kn (unlin (lin_of e')) with
    | none =>
      simp only [he] at H
      exact H0 rlo rhi H
    | some p2 =>
      obtain ⟨lo', hi'⟩ := p2
      simp only [he] at H
      have hb' := erange0_sound segs E M kn (unlin (lin_of e')) lo' hi' Hkn he
      have Hn : edenot E (unlin (lin_of e')) = edenot E e' := by
        rw [← Z_to_bv_unsigned (edenot E (unlin (lin_of e'))), ← Z_to_bv_unsigned (edenot E e')]
        apply eqm_Z_to_bv
        exact eqm_trans (unlin_sound E (lin_of e')) (lin_of_sound E e')
      have hb'1 : lo' ≤ bv_unsigned (edenot E e') := by simpa only [Hn] using hb'.1
      have hb'2 : bv_unsigned (edenot E e') ≤ hi' := by simpa only [Hn] using hb'.2
      obtain ⟨hs0', rho, ⟨hrho0, hrhos⟩, hq⟩ := deand_sound E e e' s Hd
      obtain ⟨q, hqeq⟩ := hq
      have hue0 : 0 ≤ bv_unsigned (edenot E e) := (u64_range (edenot E e)).1
      have hue1 : bv_unsigned (edenot E e) < 2 ^ 64 := (u64_range (edenot E e)).2
      have hue'0 : 0 ≤ bv_unsigned (edenot E e') := (u64_range (edenot E e')).1
      have hue'1 : bv_unsigned (edenot E e') < 2 ^ 64 := (u64_range (edenot E e')).2
      by_cases hs : s ≤ lo'
      · rw [ite_eq_left hs] at H
        have hq0 : q = 0 := by omega
        rw [hq0] at hqeq
        cases hr : erange0 kn e with
        | none =>
          simp only [hr] at H
          simp only [Option.some.injEq, Prod.mk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          exact ⟨by omega, by omega⟩
        | some p3 =>
          obtain ⟨lo, hi⟩ := p3
          simp only [hr] at H
          simp only [Option.some.injEq, Prod.mk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          have hb := erange0_sound segs E M kn e lo hi Hkn hr
          exact ⟨by omega, by omega⟩
      · rw [ite_eq_right hs] at H
        exact H0 rlo rhi H
theorem base_range_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo hi : Int) (Hkn : know_ok segs E M kn)
    (H : base_range kn e = some (lo, hi)) :
    lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
  cases e with
  | ELit z =>
    simp only [base_range] at H
    simp only [Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    have h : bv_unsigned (edenot E (.ELit z)) = z % two64 := by
      show bv_unsigned (Z_to_bv 64 z) = z % two64
      exact u_lit64a z
    rw [h]
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  | EVar n => exact erange_sound segs E M kn _ lo hi Hkn H
  | EAlu op a b => exact erange_sound segs E M kn _ lo hi Hkn H
  | EAluw op a b => exact erange_sound segs E M kn _ lo hi Hkn H
  | EMd op a b => exact erange_sound segs E M kn _ lo hi Hkn H
  | EMdw op a b => exact erange_sound segs E M kn _ lo hi Hkn H
  | EExt sx lo2 n a => exact erange_sound segs E M kn _ lo hi Hkn H
  | EBlob sx k i n => exact erange_sound segs E M kn _ lo hi Hkn H
theorem zlit64_eq (z : Int) : zlit64 z = z % two64 := by
  unfold zlit64
  by_cases h : (0 ≤ z && z < two64) = true
  · rw [ite_eq_left h]
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true ..).mp h
    exact (u_small_id z ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩).symm
  · rw [ite_eq_right h]

/-! ### Linear forms without wrap, exact term arithmetic, `find_align`
 -/

/-- `lin_nowrap_sound`: a linear form whose interval lies in
    `[0, 2^64)` denotes exactly its (unwrapped) linear value. -/
theorem lin_nowrap_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E M kn)
    (H : lin_nowrap kn e = true) :
    bv_unsigned (edenot E e) = lden E (lin_of e) := by
  cases hl : lin_range (erange kn) (lin_of e).1 (lin_of e).2 with
  | none =>
    simp only [lin_nowrap, hl] at H
    exact absurd H (by simp)
  | some p =>
    obtain ⟨lo, hi⟩ := p
    simp only [lin_nowrap, hl] at H
    obtain ⟨H1, H2⟩ := (Bool.and_eq_true ..).mp H
    have h1 : 0 ≤ lo := of_decide_eq_true H1
    have h2 : hi < 2 ^ 64 := by
      have hh := of_decide_eq_true H2
      simpa [two64] using hh
    have Hb : lo ≤ lden E (lin_of e) ∧ lden E (lin_of e) ≤ hi :=
      lin_range_sound E (erange kn)
        (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) _ _ _ _ hl
    obtain ⟨q, hq⟩ := lin_of_sound E e
    have hq' : lden E (lin_of e) = bv_unsigned (edenot E e) + q * 2 ^ 64 := hq
    have hue0 : 0 ≤ bv_unsigned (edenot E e) := (u64_range (edenot E e)).1
    have hue1 : bv_unsigned (edenot E e) < 2 ^ 64 := (u64_range (edenot E e)).2
    omega
theorem lins_e_sound (E : env) (k : Int) (a : expr) :
    ∀ ts : List (Int × expr), tden E (lins_e k a ts) = k * uE E a + tden E ts := by
  intro ts
  induction ts with
  | nil =>
    simp only [lins_e]
    by_cases hk : (k == 0) = true
    · rw [ite_eq_left hk]
      have hk0 : k = 0 := beq_iff_eq.mp hk
      rw [hk0]
      simp
    · rw [ite_eq_right hk]
      simp [tden]
  | cons t rest ih =>
    obtain ⟨k', a'⟩ := t
    simp only [lins_e]
    by_cases he : expr_eqb a a' = true
    · rw [ite_eq_left he]
      have hae : a = a' := expr_eqb_eq a a' he
      rw [hae]
      by_cases hs : (k + k' == 0) = true
      · rw [ite_eq_left hs]
        have hs0 : k + k' = 0 := beq_iff_eq.mp hs
        have hkk : k = -k' := by omega
        rw [hkk, Int.neg_mul]
        simp only [tden]
        omega
      · rw [ite_eq_right hs]
        simp only [tden]
        rw [Int.add_mul]
        omega
    · rw [ite_eq_right he]
      simp only [tden]
      rw [ih]
      omega

/-- `lsub_e_sound`: exact difference of two term lists. -/
theorem lsub_e_sound (E : env) (ts2 : List (Int × expr)) :
    ∀ ts1 : List (Int × expr), tden E (lsub_e ts2 ts1) = tden E ts2 - tden E ts1 := by
  intro ts1
  induction ts1 with
  | nil => simp [lsub_e, tden]
  | cons t rest ih =>
    obtain ⟨k, a⟩ := t
    have h : lsub_e ts2 ((k, a) :: rest) = lins_e (-k) a (lsub_e ts2 rest) := rfl
    rw [h, lins_e_sound, ih, Int.neg_mul]
    simp only [tden]
    omega
theorem find_align_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (a : expr) (m : Int) :
    ∀ (kn : List kentry), know_ok segs E base kn → find_align kn a = some m →
      0 < m ∧ bv_unsigned (edenot E a) % m = 0 := by
  intro kn
  induction kn with
  | nil =>
    intro _ H
    simp [find_align] at H
  | cons K rest ih =>
    intro Hkn H
    have HK : kentry_ok segs E base K := Hkn K (by simp)
    have Hrest : know_ok segs E base rest := fun K' h => Hkn K' (by simp [h])
    cases K with
    | KAlign e' m' =>
      simp only [find_align] at H
      by_cases he : expr_eqb a e' = true
      · rw [ite_eq_left he] at H
        have hm : m' = m := by simpa using H
        subst hm
        have hae : a = e' := expr_eqb_eq a e' he
        subst hae
        exact HK
      · rw [ite_eq_right he] at H
        exact ih Hrest H
    | KWord a' w v =>
      simp only [find_align] at H
      exact ih Hrest H
    | KZero a' n =>
      simp only [find_align] at H
      exact ih Hrest H
    | KBlob a' n kk =>
      simp only [find_align] at H
      exact ih Hrest H
    | KImg lo hi =>
      simp only [find_align] at H
      exact ih Hrest H
    | KRange e' lo hi =>
      simp only [find_align] at H
      exact ih Hrest H
    | KWr a' n =>
      simp only [find_align] at H
      exact ih Hrest H
    | KDisj a1 n1 a2 n2 =>
      simp only [find_align] at H
      exact ih Hrest H
    | KFill a' n c =>
      simp only [find_align] at H
      exact ih Hrest H
    | KUnk a' n =>
      simp only [find_align] at H
      exact ih Hrest H

/-! ### Divisibility arithmetic for the alignment domain -/

/-- `zpow a` is additive in the (non-negative) exponent. -/
theorem zpow_int_add (a : Int) {m n : Int} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    zpow a (m + n) = zpow a m * zpow a n := by
  show a ^ (m + n).toNat = a ^ m.toNat * a ^ n.toNat
  rw [Int.toNat_add hm hn, Int.pow_add]
theorem ctz_fuel_sound (f : Nat) :
    ∀ z : Int, 0 ≤ ctz_fuel f z ∧ zpow 2 (ctz_fuel f z) ∣ z ∧ ctz_fuel f z ≤ (f : Int) := by
  induction f with
  | zero =>
    intro z
    have h0 : ctz_fuel 0 z = 0 := rfl
    refine ⟨by rw [h0]; exact Int.le_refl 0, ?_, by rw [h0]; exact Int.le_refl 0⟩
    show (1 : Int) ∣ z
    exact Int.one_dvd z
  | succ f ih =>
    intro z
    obtain ⟨A, B, C⟩ := ih (z / 2)
    have hred : ctz_fuel (f + 1) z
        = (if z % 2 == 0 then 1 + ctz_fuel f (z / 2) else 0) := rfl
    rw [hred]
    by_cases hz : (z % 2 == 0) = true
    · repeat rw [ite_eq_left hz]
      have hz0 : z % 2 = 0 := by simpa using hz
      have hzdiv : z = 2 * (z / 2) := by
        have h := Int.ediv_mul_add_emod z 2
        rw [hz0] at h
        omega
      have hzp : zpow 2 (1 + ctz_fuel f (z / 2))
          = 2 * zpow 2 (ctz_fuel f (z / 2)) := by
        show (2 : Int) ^ (1 + ctz_fuel f (z / 2)).toNat
            = 2 * (2 : Int) ^ (ctz_fuel f (z / 2)).toNat
        rw [Int.toNat_add (by omega) A, Int.pow_add]
        simp
      obtain ⟨kk, hk⟩ := B
      refine ⟨by omega, ?_, by omega⟩
      rw [hzp]
      exact ⟨kk, by
        calc z = 2 * (z / 2) := hzdiv
          _ = 2 * (zpow 2 (ctz_fuel f (z / 2)) * kk) :=
            congrArg (fun t : Int => 2 * t) hk
          _ = 2 * zpow 2 (ctz_fuel f (z / 2)) * kk := (Int.mul_assoc _ _ _).symm⟩
    · repeat rw [ite_eq_right hz]
      refine ⟨by omega, ?_, by omega⟩
      show (1 : Int) ∣ z
      exact Int.one_dvd z
theorem ctz64_sound (z : Int) : (0 ≤ ctz64 z ∧ ctz64 z ≤ 64) ∧ zpow 2 (ctz64 z) ∣ z := by
  obtain ⟨A, B, C⟩ := ctz_fuel_sound 64 z
  exact ⟨⟨A, by simpa [ctz64] using C⟩, B⟩

/-- `pow2_divide_le`: a smaller power of two divides a larger. -/
theorem pow2_divide_le (a b : Int) (H : 0 ≤ a ∧ a ≤ b) : zpow 2 a ∣ zpow 2 b := by
  refine ⟨zpow 2 (b - a), ?_⟩
  show (2 : Int) ^ b.toNat = (2 : Int) ^ a.toNat * (2 : Int) ^ (b - a).toNat
  have h2 : 0 ≤ b - a := by omega
  have h3 : b.toNat = a.toNat + (b - a).toNat := by
    rw [← Int.toNat_add H.1 h2]
    congr 1
    omega
  rw [h3, Int.pow_add]

/-- `divide_mod64`: a power of two dividing `t` divides `t mod 2^64`. -/
theorem divide_mod64 (k t : Int) (Hk : 0 ≤ k ∧ k ≤ 64) (Hd : zpow 2 k ∣ t) :
    zpow 2 k ∣ t % 2 ^ 64 := by
  have h : t % 2 ^ 64 = t - t / 2 ^ 64 * 2 ^ 64 := by
    have hh := Int.ediv_mul_add_emod t (2 ^ 64)
    omega
  rw [h]
  exact Int.dvd_sub Hd (Int.dvd_mul_of_dvd_right (pow2_divide_le k 64 Hk))

/-! ### `ealign0_sound` -/

/-- `2^k` divides a `Nat` iff all its bits below `k` vanish. -/
theorem two_pow_dvd_iff_testbit (n k : Nat) :
    2 ^ k ∣ n ↔ ∀ i, i < k → n.testBit i = false := by
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h i hi
    have h2 : (n % 2 ^ k).testBit i = false := by rw [h]; exact Nat.zero_testBit i
    rw [Nat.testBit_mod_two_pow] at h2
    have hd : decide (i < k) = true := by simp [hi]
    rw [hd] at h2
    simpa using h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < k
    · rw [show decide (i < k) = true from by simp [hi], h i hi]
      rfl
    · rw [show decide (i < k) = false from by simp [hi]]
      rfl

/-- The `Int`/`Nat` bridge for the alignment domain: `zpow 2 k` divides a
    `Nat`-valued `Int` iff the low `k` bits vanish. -/
theorem zpow_two_dvd_nat_iff {k : Int} (hk : 0 ≤ k) {n : Nat} :
    zpow 2 k ∣ (n : Int) ↔ ∀ i, i < k.toNat → n.testBit i = false := by
  have hz : zpow 2 k = ((2 ^ k.toNat : Nat) : Int) := natCast_pow_two k.toNat
  rw [hz, Int.ofNat_dvd, two_pow_dvd_iff_testbit]

/-- `bv_unsigned` of an `AND` at the `Nat` level. -/
theorem u_and64_nat (x y : word) :
    bv_unsigned (alu64 .AND x y) = ((x.toNat &&& y.toNat : Nat) : Int) := by
  show bv_unsigned (x &&& y) = _
  unfold bv_unsigned
  rw [BitVec.toNat_and]

/-- `bv_unsigned` of an `OR` at the `Nat` level. -/
theorem u_or64_nat (x y : word) :
    bv_unsigned (alu64 .OR x y) = ((x.toNat ||| y.toNat : Nat) : Int) := by
  show bv_unsigned (x ||| y) = _
  unfold bv_unsigned
  rw [BitVec.toNat_or]

/-- An `AND` preserves a power-of-two divisor of the left operand. -/
theorem dvd_and_of_dvd_left {k : Int} (hk : 0 ≤ k) (x y : word)
    (h : zpow 2 k ∣ bv_unsigned x) : zpow 2 k ∣ bv_unsigned (alu64 .AND x y) := by
  rw [u_and64_nat, zpow_two_dvd_nat_iff hk]
  intro i hi
  have hx : x.toNat.testBit i = false := (zpow_two_dvd_nat_iff hk).mp h i hi
  simp [Nat.testBit_and, hx]

/-- An `AND` preserves a power-of-two divisor of the right operand. -/
theorem dvd_and_of_dvd_right {k : Int} (hk : 0 ≤ k) (x y : word)
    (h : zpow 2 k ∣ bv_unsigned y) : zpow 2 k ∣ bv_unsigned (alu64 .AND x y) := by
  rw [u_and64_nat, zpow_two_dvd_nat_iff hk]
  intro i hi
  have hy : y.toNat.testBit i = false := (zpow_two_dvd_nat_iff hk).mp h i hi
  simp [Nat.testBit_and, hy]

/-- An `OR` preserves a common power-of-two divisor. -/
theorem dvd_or_of_dvd {k : Int} (hk : 0 ≤ k) (x y : word)
    (hx : zpow 2 k ∣ bv_unsigned x) (hy : zpow 2 k ∣ bv_unsigned y) :
    zpow 2 k ∣ bv_unsigned (alu64 .OR x y) := by
  rw [u_or64_nat, zpow_two_dvd_nat_iff hk]
  intro i hi
  have h1 : x.toNat.testBit i = false := (zpow_two_dvd_nat_iff hk).mp hx i hi
  have h2 : y.toNat.testBit i = false := (zpow_two_dvd_nat_iff hk).mp hy i hi
  simp [Nat.testBit_or, h1, h2]

/-- A product of divisors divides the product. -/
theorem dvd_mul_mul {a b x y : Int} (h1 : a ∣ x) (h2 : b ∣ y) : a * b ∣ x * y := by
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, rfl⟩ := h2
  exact ⟨p * q, by ac_rfl⟩

/-- The `0` case of the fact-free alignment (`1` divides everything). -/
theorem ealign_zero_sound (E : env) (kn : List kentry) (e : expr)
    (h : ealign0_nofact kn e = 0) :
    (0 ≤ ealign0_nofact kn e ∧ ealign0_nofact kn e ≤ 64) ∧
      zpow 2 (ealign0_nofact kn e) ∣ bv_unsigned (edenot E e) := by
  rw [h]
  refine ⟨⟨Int.le_refl 0, by decide⟩, ?_⟩
  show (1 : Int) ∣ _
  exact Int.one_dvd _

/-- The fact-free half of the alignment domain: sound on its own. -/
theorem ealign_nofact_sound (E : env) (kn : List kentry) :
    ∀ e : expr, (0 ≤ ealign0_nofact kn e ∧ ealign0_nofact kn e ≤ 64) ∧
      zpow 2 (ealign0_nofact kn e) ∣ bv_unsigned (edenot E e) := by
  intro e
  induction e with
  | ELit z =>
    have hred : ealign0_nofact kn (.ELit z) = ctz64 (z % two64) := rfl
    rw [hred]
    obtain ⟨A, B⟩ := ctz64_sound (z % two64)
    refine ⟨A, ?_⟩
    show zpow 2 (ctz64 (z % two64)) ∣ bv_unsigned (Z_to_bv 64 z)
    rw [u_lit64]
    exact B
  | EVar n => exact ealign_zero_sound E kn _ rfl
  | EAlu op a b iha ihb =>
    cases op with
    | ADD =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      obtain ⟨⟨A2, B2⟩, C2⟩ := ihb
      have hred : ealign0_nofact kn (.EAlu .ADD a b)
          = min (ealign0_nofact kn a) (ealign0_nofact kn b) := rfl
      rw [hred]
      have hL : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn a :=
        Int.min_le_left ..
      have hR : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn b :=
        Int.min_le_right ..
      have h0 : 0 ≤ min (ealign0_nofact kn a) (ealign0_nofact kn b) := by omega
      have h64 : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ 64 := by omega
      refine ⟨⟨h0, h64⟩, ?_⟩
      have hka : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E a) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hL⟩) C1
      have hkb : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E b) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hR⟩) C2
      show zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E a + edenot E b)
      rw [u_add64]
      exact divide_mod64 _ _ ⟨h0, h64⟩ (Int.dvd_add hka hkb)
    | SUB =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      obtain ⟨⟨A2, B2⟩, C2⟩ := ihb
      have hred : ealign0_nofact kn (.EAlu .SUB a b)
          = min (ealign0_nofact kn a) (ealign0_nofact kn b) := rfl
      rw [hred]
      have hL : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn a :=
        Int.min_le_left ..
      have hR : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn b :=
        Int.min_le_right ..
      have h0 : 0 ≤ min (ealign0_nofact kn a) (ealign0_nofact kn b) := by omega
      have h64 : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ 64 := by omega
      refine ⟨⟨h0, h64⟩, ?_⟩
      have hka : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E a) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hL⟩) C1
      have hkb : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E b) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hR⟩) C2
      show zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E a - edenot E b)
      rw [u_sub64]
      exact divide_mod64 _ _ ⟨h0, h64⟩ (Int.dvd_sub hka hkb)
    | AND =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      obtain ⟨⟨A2, B2⟩, C2⟩ := ihb
      have hred : ealign0_nofact kn (.EAlu .AND a b)
          = max (ealign0_nofact kn a) (ealign0_nofact kn b) := rfl
      rw [hred]
      have hL : ealign0_nofact kn a ≤ max (ealign0_nofact kn a) (ealign0_nofact kn b) :=
        Int.le_max_left ..
      have hR : ealign0_nofact kn b ≤ max (ealign0_nofact kn a) (ealign0_nofact kn b) :=
        Int.le_max_right ..
      have h0 : 0 ≤ max (ealign0_nofact kn a) (ealign0_nofact kn b) := by omega
      have h64 : max (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ 64 := by omega
      refine ⟨⟨h0, h64⟩, ?_⟩
      by_cases hc : ealign0_nofact kn b ≤ ealign0_nofact kn a
      · have he : max (ealign0_nofact kn a) (ealign0_nofact kn b) = ealign0_nofact kn a := by
          omega
        rw [he]
        exact dvd_and_of_dvd_left A1 _ _ C1
      · have he : max (ealign0_nofact kn a) (ealign0_nofact kn b) = ealign0_nofact kn b := by
          omega
        rw [he]
        exact dvd_and_of_dvd_right A2 _ _ C2
    | OR =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      obtain ⟨⟨A2, B2⟩, C2⟩ := ihb
      have hred : ealign0_nofact kn (.EAlu .OR a b)
          = min (ealign0_nofact kn a) (ealign0_nofact kn b) := rfl
      rw [hred]
      have hL : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn a :=
        Int.min_le_left ..
      have hR : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ ealign0_nofact kn b :=
        Int.min_le_right ..
      have h0 : 0 ≤ min (ealign0_nofact kn a) (ealign0_nofact kn b) := by omega
      have h64 : min (ealign0_nofact kn a) (ealign0_nofact kn b) ≤ 64 := by omega
      refine ⟨⟨h0, h64⟩, ?_⟩
      have hka : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E a) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hL⟩) C1
      have hkb : zpow 2 (min (ealign0_nofact kn a) (ealign0_nofact kn b))
          ∣ bv_unsigned (edenot E b) :=
        Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hR⟩) C2
      exact dvd_or_of_dvd h0 _ _ hka hkb
    | SLL =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      have hred : ealign0_nofact kn (.EAlu .SLL a b)
          = (match lit_shamt b with
             | some s => min (ealign0_nofact kn a + s) 64
             | none => 0) := rfl
      rw [hred]
      cases hs : lit_shamt b with
      | none =>
        simp only [hs]
        refine ⟨⟨Int.le_refl 0, by decide⟩, ?_⟩
        show (1 : Int) ∣ _
        exact Int.one_dvd _
      | some s =>
        obtain ⟨Hsv, Hs0, Hs64⟩ := lit_shamt_sound E b s hs
        have h0 : 0 ≤ min (ealign0_nofact kn a + s) 64 := by omega
        have h64 : min (ealign0_nofact kn a + s) 64 ≤ 64 := Int.min_le_right ..
        refine ⟨⟨h0, h64⟩, ?_⟩
        have hL : min (ealign0_nofact kn a + s) 64 ≤ ealign0_nofact kn a + s :=
          Int.min_le_left ..
        show zpow 2 (min (ealign0_nofact kn a + s) 64)
            ∣ bv_unsigned (alu64 .SLL (edenot E a) (edenot E b))
        rw [u_sll64, Hsv]
        apply divide_mod64 _ _ ⟨h0, h64⟩
        refine Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hL⟩) ?_
        have hsplit : zpow 2 (ealign0_nofact kn a + s)
            = zpow 2 (ealign0_nofact kn a) * zpow 2 s := zpow_int_add 2 A1 Hs0
        rw [hsplit]
        show zpow 2 (ealign0_nofact kn a) * (2 : Int) ^ s.toNat
            ∣ bv_unsigned (edenot E a) * (2 : Int) ^ s.toNat
        obtain ⟨q, hq⟩ := C1
        exact ⟨q, by rw [hq]; ac_rfl⟩
    | SLT => exact ealign_zero_sound E kn _ rfl
    | SLTU => exact ealign_zero_sound E kn _ rfl
    | XOR => exact ealign_zero_sound E kn _ rfl
    | SRL => exact ealign_zero_sound E kn _ rfl
    | SRA => exact ealign_zero_sound E kn _ rfl
  | EAluw op a b => exact ealign_zero_sound E kn _ rfl
  | EMd op a b iha ihb =>
    cases op with
    | MUL =>
      obtain ⟨⟨A1, B1⟩, C1⟩ := iha
      obtain ⟨⟨A2, B2⟩, C2⟩ := ihb
      have hred : ealign0_nofact kn (.EMd .MUL a b)
          = min (ealign0_nofact kn a + ealign0_nofact kn b) 64 := rfl
      rw [hred]
      have h0 : 0 ≤ min (ealign0_nofact kn a + ealign0_nofact kn b) 64 := by omega
      have h64 : min (ealign0_nofact kn a + ealign0_nofact kn b) 64 ≤ 64 :=
        Int.min_le_right ..
      refine ⟨⟨h0, h64⟩, ?_⟩
      have hL : min (ealign0_nofact kn a + ealign0_nofact kn b) 64
          ≤ ealign0_nofact kn a + ealign0_nofact kn b := Int.min_le_left ..
      show zpow 2 (min (ealign0_nofact kn a + ealign0_nofact kn b) 64)
          ∣ bv_unsigned (edenot E a * edenot E b)
      rw [u_mul64]
      apply divide_mod64 _ _ ⟨h0, h64⟩
      refine Int.dvd_trans (pow2_divide_le _ _ ⟨h0, hL⟩) ?_
      have hsplit : zpow 2 (ealign0_nofact kn a + ealign0_nofact kn b)
          = zpow 2 (ealign0_nofact kn a) * zpow 2 (ealign0_nofact kn b) :=
        zpow_int_add 2 A1 A2
      rw [hsplit]
      exact dvd_mul_mul C1 C2
    | MULH => exact ealign_zero_sound E kn _ rfl
    | MULHSU => exact ealign_zero_sound E kn _ rfl
    | MULHU => exact ealign_zero_sound E kn _ rfl
    | DIV => exact ealign_zero_sound E kn _ rfl
    | DIVU => exact ealign_zero_sound E kn _ rfl
    | REM => exact ealign_zero_sound E kn _ rfl
    | REMU => exact ealign_zero_sound E kn _ rfl
  | EMdw op a b => exact ealign_zero_sound E kn _ rfl
  | EExt sx lo n a => exact ealign_zero_sound E kn _ rfl
  | EBlob sx k i n => exact ealign_zero_sound E kn _ rfl
theorem ealign0_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E M kn) :
    (0 ≤ ealign0 kn e ∧ ealign0 kn e ≤ 64) ∧
      zpow 2 (ealign0 kn e) ∣ bv_unsigned (edenot E e) := by
  have hred : ealign0 kn e = (match find_align kn e with
      | some m => if 0 < m then ctz64 m else 0
      | none => ealign0_nofact kn e) := rfl
  rw [hred]
  cases hfa : find_align kn e with
  | none =>
    simpa only [hfa] using ealign_nofact_sound E kn e
  | some m =>
    obtain ⟨Hm, Hmod⟩ := find_align_sound segs E M e m kn Hkn hfa
    by_cases hm : 0 < m
    · simp only [hfa, ite_eq_left hm]
      obtain ⟨A, B⟩ := ctz64_sound m
      exact ⟨A, Int.dvd_trans B (Int.dvd_of_emod_eq_zero Hmod)⟩
    · simp only [hfa, ite_eq_right hm]
      refine ⟨⟨Int.le_refl 0, by decide⟩, ?_⟩
      show (1 : Int) ∣ _
      exact Int.one_dvd _

/-! ### The page-rounding atom finder -/

theorem find_and_atom_k_some (sg : Int) :
    ∀ (ts : List (Int × expr)) (y : expr) (mm : Int),
      find_and_atom_k sg ts = some (y, mm) → 0 < mm ∧ AxSymExec3.zland (mm + 1) mm = 0 := by
  intro ts
  induction ts with
  | nil =>
    intro y mm H
    simp [find_and_atom_k] at H
  | cons t rest ih =>
    intro y mm H
    obtain ⟨k, a⟩ := t
    cases a with
    | ELit z =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EVar n =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EAluw op b1 b2 =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EMd op b1 b2 =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EMdw op b1 b2 =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EExt sx lo n b =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EBlob sx kk i n =>
      simp only [find_and_atom_k] at H
      exact ih y mm H
    | EAlu op b1 b2 =>
      cases op with
      | AND =>
        cases b2 with
        | ELit m =>
          simp only [find_and_atom_k] at H
          by_cases hc : (k == sg && 0 < m && AxSymExec3.zland (m + 1) m == 0) = true
          · rw [ite_eq_left hc] at H
            obtain ⟨hc1, hland⟩ := (Bool.and_eq_true ..).mp hc
            obtain ⟨-, hm0⟩ := (Bool.and_eq_true ..).mp hc1
            simp only [Option.some.injEq, Prod.mk.injEq] at H
            obtain ⟨rfl, rfl⟩ := H
            exact ⟨of_decide_eq_true hm0, beq_iff_eq.mp hland⟩
          · rw [ite_eq_right hc] at H
            exact ih y mm H
        | EVar n =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EAlu op2 c1 c2 =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EAluw op2 c1 c2 =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EMd op2 c1 c2 =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EMdw op2 c1 c2 =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EExt sx lo n c =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
        | EBlob sx kk i n =>
          simp only [find_and_atom_k] at H
          exact ih y mm H
      | ADD =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SUB =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SLL =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SLT =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SLTU =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | XOR =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SRL =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | SRA =>
        simp only [find_and_atom_k] at H
        exact ih y mm H
      | OR =>
        simp only [find_and_atom_k] at H
        exact ih y mm H

theorem find_and_atom_some (ts : List (Int × expr)) (y : expr) (mm : Int)
    (H : find_and_atom ts = some (y, mm)) : 0 < mm ∧ AxSymExec3.zland (mm + 1) mm = 0 :=
  find_and_atom_k_some 1 ts y mm H

/-- `u_and_mask`: masking with `mm = 2^k - 1` is `mod 2^k`. -/
theorem u_and_mask (E : env) (y : expr) (mm k : Int) (Hk : 0 ≤ k ∧ k ≤ 64)
    (Hm : mm + 1 = zpow 2 k) :
    bv_unsigned (edenot E (.EAlu .AND y (.ELit mm)))
      = bv_unsigned (edenot E y) % zpow 2 k := by
  have hx : 0 ≤ bv_unsigned (edenot E y) ∧ bv_unsigned (edenot E y) < 2 ^ 64 :=
    u64_range (edenot E y)
  have hmm : mm = zpow 2 k - 1 := by omega
  have hpow1 : (1 : Int) ≤ zpow 2 k := by
    have h1 : zpow 2 k = ((2 ^ k.toNat : Nat) : Int) := natCast_pow_two k.toNat
    rw [h1]
    exact Int.ofNat_le.mpr Nat.one_le_two_pow
  have hpow64 : zpow 2 k ≤ 2 ^ 64 := by
    have h1 : zpow 2 k = ((2 ^ k.toNat : Nat) : Int) := natCast_pow_two k.toNat
    rw [h1]
    exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  show bv_unsigned (alu64 .AND (edenot E y) (edenot E (.ELit mm)))
      = bv_unsigned (edenot E y) % zpow 2 k
  rw [u_and64]
  have hlit : bv_unsigned (edenot E (.ELit mm)) = zpow 2 k - 1 := by
    show bv_unsigned (Z_to_bv 64 mm) = zpow 2 k - 1
    rw [u_lit64, hmm]
    exact u_small_id _ ⟨by omega, by omega⟩
  rw [hlit]
  exact land_lowmask _ _ k Hk rfl ⟨hx.1, hx.2⟩
theorem fold_lins_e_sg_sound (E : env) (sg : Int) (ts acc : List (Int × expr)) :
    tden E (ts.foldr (fun t a => lins_e (sg * t.1) t.2 a) acc)
      = sg * tden E ts + tden E acc := by
  induction ts with
  | nil => simp [tden]
  | cons t rest ih =>
    obtain ⟨k, a⟩ := t
    simp only [List.foldr_cons, tden]
    rw [lins_e_sound, ih, Int.mul_add, Int.mul_assoc]
    omega
theorem fold_lins_e1_sound (E : env) (ts acc : List (Int × expr)) :
    tden E (ts.foldr (fun t a => lins_e (1 * t.1) t.2 a) acc)
      = tden E ts + tden E acc := by
  rw [fold_lins_e_sg_sound E 1 ts acc]
  omega

/-- A `Nat` whose successor-AND-self vanishes is a power of two. -/
theorem nat_pow2_of_land_sub_one (n : Nat) (h0 : 0 < n) (h : n &&& (n - 1) = 0) :
    ∃ k : Nat, n = 2 ^ k := by
  by_cases hc : ∃ k : Nat, n = 2 ^ k
  · exact hc
  · have hc' : ∀ k : Nat, n ≠ 2 ^ k := fun k he => hc ⟨k, he⟩
    have hne : n ≠ 0 := by omega
    have hk : n.testBit n.log2 = true := Nat.testBit_log2 hne
    have h1 : 2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) :=
      (Nat.log2_eq_iff hne).mp rfl
    have hlt : 2 ^ n.log2 < n := by
      have h2 : 2 ^ n.log2 ≠ n := fun he => hc' n.log2 he.symm
      omega
    have hsub : 0 < n - 1 := by omega
    have hlog2 : (n - 1).log2 = n.log2 := by
      rw [Nat.log2_eq_iff (by omega : (n - 1) ≠ 0)]
      omega
    have ht2 : (n - 1).testBit n.log2 = true := by
      rw [← hlog2]
      exact Nat.testBit_log2 (by omega : (n - 1) ≠ 0)
    have htand : (n &&& (n - 1)).testBit n.log2 = true := by
      rw [Nat.testBit_and, hk, ht2]
      rfl
    rw [h] at htand
    exact absurd htand (by simp)

/-- The `mm + 1` reconstruction used by `pageup_low_k_sound`: a positive
    `Int` whose successor has no common set bit with it is `2^K`. -/
theorem pow2_of_zland_succ (mm : Int) (h0 : 0 < mm) (h64 : mm + 1 ≤ 2 ^ 64)
    (h : AxSymExec3.zland (mm + 1) mm = 0) :
    ∃ K : Int, 0 ≤ K ∧ K ≤ 64 ∧ mm + 1 = zpow 2 K := by
  by_cases hcase : mm + 1 = 2 ^ 64
  · refine ⟨64, by decide, by decide, ?_⟩
    rw [hcase]
    show (2 : Int) ^ 64 = zpow 2 (64 : Int)
    rfl
  · have hlt : mm + 1 < 2 ^ 64 := by omega
    have hn0 : (0 : Int) ≤ mm + 1 := by omega
    generalize hn : (mm + 1).toNat = n
    have hnc : (n : Int) = mm + 1 := by
      rw [← hn]
      exact Int.toNat_of_nonneg hn0
    have hnpos : 0 < n := by omega
    have hz : (n &&& (n - 1) : Nat) = 0 := by
      have h1 : AxSymExec3.zland (mm + 1) mm
          = (((mm + 1) % two64).toNat &&& (mm % two64).toNat : Nat) := rfl
      rw [h1] at h
      have e1 : ((mm + 1) % two64).toNat = n := by
        have h2 : (mm + 1) % two64 = mm + 1 := Int.emod_eq_of_lt hn0 hlt
        rw [h2, hn]
      have e2 : (mm % two64).toNat = n - 1 := by
        have hmm0 : 0 ≤ mm := by omega
        have hmmlt : mm < 2 ^ 64 := by omega
        have h2 : mm % two64 = mm := Int.emod_eq_of_lt hmm0 hmmlt
        rw [h2]
        have h3 : (mm + 1).toNat = mm.toNat + 1 := by
          rw [Int.toNat_add hmm0 (by decide : (0 : Int) ≤ 1)]
          rfl
        rw [hn] at h3
        omega
      rw [e1, e2] at h
      exact_mod_cast h
    obtain ⟨k, hk⟩ := nat_pow2_of_land_sub_one n hnpos hz
    have hk64 : k ≤ 64 := by
      have h2 : (n : Int) < (2 : Int) ^ 64 := by rw [hnc]; exact hlt
      have h3 : (n : Int) < ((2 ^ 64 : Nat) : Int) := by
        rw [← natCast_pow_two]
        exact h2
      have h4 : n < 2 ^ 64 := Int.ofNat_lt.mp h3
      rw [hk] at h4
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_of_lt h4)
    refine ⟨(k : Int), Int.natCast_nonneg k, by exact_mod_cast hk64, ?_⟩
    rw [← hnc, hk]
    show (((2 ^ k : Nat)) : Int) = zpow 2 (k : Int)
    rw [← natCast_pow_two]
    rfl

/-! ### `u_srl_lit`, `fold_lins_e_sound`, `u_srl_rem` -/

/-- `u_srl_lit`: `SRL` by a literal shift amount is a division.
    the exponent is a `Nat` here, `.toNat` of the
    `Z` exponent . -/
theorem u_srl_lit (E : env) (e : expr) (s : Int) :
    bv_unsigned (edenot E (.EAlu .SRL e (.ELit s)))
      = bv_unsigned (edenot E e) / 2 ^ (((s % two64) % 64).toNat) := by
  show bv_unsigned (alu64 .SRL (edenot E e) (edenot E (.ELit s))) = _
  rw [u_srl64]
  have h : bv_unsigned (edenot E (.ELit s)) % 64 = (s % two64) % 64 := by
    show bv_unsigned (Z_to_bv 64 s) % 64 = _
    rw [u_lit64]
  rw [h]

/-- `fold_lins_e_sound` (the `sg`-free spelling of
    `fold_lins_e_sg_sound`). -/
theorem fold_lins_e_sound (E : env) (q : Int) (ts acc : List (Int × expr)) :
    tden E (ts.foldr (fun t a => lins_e (q * t.1) t.2 a) acc)
      = q * tden E ts + tden E acc :=
  fold_lins_e_sg_sound E q ts acc

/-- `u_srl_rem`: the residual atom `e AND (2^s - 1)`. -/
theorem u_srl_rem (E : env) (e : expr) (s : Int) (Hs : 0 ≤ s ∧ s < 64) :
    bv_unsigned (edenot E (srl_rem e (zpow 2 s))) = bv_unsigned (edenot E e) % zpow 2 s :=
  u_and_mask E e (zpow 2 s - 1) s ⟨Hs.1, by omega⟩ (by omega)

/-! ### `pageup_low_k_sound` -/

/-- `pageup_low_k_sound`: the residue reported by `pageup_low_k`
    is the true residue of the form modulo `m`, provided `sg = ±1` and
    `m` is a power of two (`m = 2^j`, `0 ≤ j ≤ 64`).

    The page-up form is `c + sg*(y AND mm) - ...`, where `mm + 1 = 2^K`
    for some `K` (the reconstruction `pow2_of_zland_succ`).  Since
    `m | mm+1 = 2^K`, both `2^K = w1*m` and `2^64 = 2^K*w2` are multiples
    of `m`, so the whole form is `(c + sg*cy)` up to a multiple of `m`. -/
theorem pageup_low_k_sound (sg : Int) (E : env) (e : expr) (m j r : Int)
    (Hsg : sg = 1 ∨ sg = -1) (Hj : 0 ≤ j ∧ j ≤ 64) (Hm : m = zpow 2 j)
    (H : pageup_low_k sg e m = some r) :
    bv_unsigned (edenot E e) % m = r ∧ 0 ≤ r ∧ r < m := by
  unfold pageup_low_k at H
  try simp only [] at H
  generalize hlin : lin_of e = l at H
  obtain ⟨c, ts⟩ := l
  try simp only [] at H
  cases hfa : find_and_atom_k sg ts with
  | none =>
    rw [hfa] at H
    exact absurd H (by simp)
  | some p =>
    obtain ⟨y, mm⟩ := p
    rw [hfa] at H
    try simp only [] at H
    obtain ⟨hmm0, hland⟩ := find_and_atom_k_some sg ts y mm hfa
    by_cases hcond : (0 < m && (mm + 1) % m == 0 && mm + 1 ≤ two64) = true
    · rw [ite_eq_left hcond] at H
      try simp only [] at H
      obtain ⟨hc12, hle64⟩ := (Bool.and_eq_true ..).mp hcond
      obtain ⟨hm0b, hdm0⟩ := (Bool.and_eq_true ..).mp hc12
      have hm0 : 0 < m := of_decide_eq_true hm0b
      have hdm : (mm + 1) % m = 0 := beq_iff_eq.mp hdm0
      have hle : mm + 1 ≤ (2 : Int) ^ 64 := of_decide_eq_true hle64
      generalize hly : lin_of y = ly at H
      obtain ⟨cy, tsy⟩ := ly
      try simp only [] at H
      generalize hrest : lins_e (-sg) (.EAlu .AND y (.ELit mm)) ts = rest at H
      cases hfold : rest.foldr (fun t a => lins_e (sg * t.1) t.2 a) tsy with
      | nil =>
        rw [hfold] at H
        try simp only [] at H
        have hr : (c + sg * cy) % m = r := Option.some.inj H
        obtain ⟨K, hK0, hK64, hKe⟩ := pow2_of_zland_succ mm hmm0 hle hland
        obtain ⟨w1, hw1⟩ := Int.dvd_of_emod_eq_zero (a := m) (b := mm + 1) hdm
        have hw1' : zpow 2 K = w1 * m := by rw [← hKe, hw1, Int.mul_comm]
        obtain ⟨w2, hw2⟩ := pow2_div_64 K ⟨hK0, hK64⟩
        obtain ⟨q1, hq1⟩ := lin_of_sound E e
        obtain ⟨q2, hq2⟩ := lin_of_sound E y
        have hq1' : c + tden E ts = bv_unsigned (edenot E e) + q1 * 2 ^ 64 := by
          have h := hq1
          simp only [lden, uE] at h
          rw [hlin] at h
          simpa using h
        have hq2' : cy + tden E tsy = bv_unsigned (edenot E y) + q2 * 2 ^ 64 := by
          have h := hq2
          simp only [lden, uE] at h
          rw [hly] at h
          simpa using h
        have hrest' : tden E rest
            = -sg * bv_unsigned (edenot E (.EAlu .AND y (.ELit mm))) + tden E ts := by
          have h := lins_e_sound E (-sg) (.EAlu .AND y (.ELit mm)) ts
          simp only [uE] at h
          rw [hrest] at h
          exact h
        have huand : bv_unsigned (edenot E (.EAlu .AND y (.ELit mm)))
            = bv_unsigned (edenot E y) % zpow 2 K :=
          u_and_mask E y mm K ⟨hK0, hK64⟩ hKe
        have hf0 : sg * tden E rest + tden E tsy = 0 := by
          have h := fold_lins_e_sg_sound E sg rest tsy
          rw [hfold] at h
          simpa [tden] using h.symm
        have hxdec : bv_unsigned (edenot E y) / zpow 2 K * zpow 2 K
            + bv_unsigned (edenot E y) % zpow 2 K = bv_unsigned (edenot E y) :=
          Int.ediv_mul_add_emod _ _
        have hmono1 : bv_unsigned (edenot E y) / zpow 2 K * zpow 2 K
            = (w1 * (bv_unsigned (edenot E y) / zpow 2 K)) * m := by
          rw [hw1']
          ac_rfl
        obtain rfl | hneg := Hsg
        · -- `sg = 1`
          simp only [Int.one_mul] at hrest' hf0 hr
          have hdist : q1 * 2 ^ 64 + q2 * 2 ^ 64 = (q1 + q2) * 2 ^ 64 :=
            (Int.add_mul q1 q2 (2 ^ 64)).symm
          have hmono2 : (q1 + q2) * 2 ^ 64 = ((q1 + q2) * w2 * w1) * m := by
            rw [hw2, hw1']
            ac_rfl
          have hv : bv_unsigned (edenot E e)
              = (c + cy) - (w1 * (bv_unsigned (edenot E y) / zpow 2 K)) * m
                - ((q1 + q2) * w2 * w1) * m := by
            omega
          refine ⟨?_, ?_, ?_⟩
          · rw [hv, ← hr]
            rw [Int.sub_mul_emod_self_right, Int.sub_mul_emod_self_right]
          · rw [← hr]
            exact Int.emod_nonneg _ (by omega)
          · rw [← hr]
            exact Int.emod_lt_of_pos _ hm0
        · -- `sg = -1`  (nb. the residue is `c - cy + 2^K*xq - ...`: the sign
          -- of the `2^K*xq` term flips with `sg`; both are `0` modulo `m`.)
          subst hneg
          simp only [Int.neg_one_mul, Int.neg_neg, Int.one_mul] at hrest' hf0 hr
          have hdist : (q1 + -1 * q2) * 2 ^ 64 = q1 * 2 ^ 64 - q2 * 2 ^ 64 := by
            rw [Int.add_mul, Int.neg_one_mul, Int.neg_mul, Int.sub_eq_add_neg]
          have hmono2 : (q1 + -1 * q2) * 2 ^ 64 = ((q1 + -1 * q2) * w2 * w1) * m := by
            rw [hw2, hw1']
            ac_rfl
          have hv : bv_unsigned (edenot E e)
              = (c + -cy) + (w1 * (bv_unsigned (edenot E y) / zpow 2 K)) * m
                - ((q1 + -1 * q2) * w2 * w1) * m := by
            omega
          refine ⟨?_, ?_, ?_⟩
          · rw [hv, ← hr]
            rw [Int.sub_mul_emod_self_right, Int.add_mul_emod_self_right]
          · rw [← hr]
            exact Int.emod_nonneg _ (by omega)
          · rw [← hr]
            exact Int.emod_lt_of_pos _ hm0
      | cons t0 r0 =>
        rw [hfold] at H
        exact absurd H (by simp)
    · rw [ite_eq_right hcond] at H
      exact absurd H (by simp)

/-- `pageup_low_sound`: the `+1` idiom first, then the dual. -/
theorem pageup_low_sound (E : env) (e : expr) (m j r : Int)
    (Hj : 0 ≤ j ∧ j ≤ 64) (Hm : m = zpow 2 j) (H : pageup_low e m = some r) :
    bv_unsigned (edenot E e) % m = r ∧ 0 ≤ r ∧ r < m := by
  unfold pageup_low at H
  generalize h1 : pageup_low_k 1 e m = o at H
  cases o with
  | none =>
    simp only [h1] at H
    exact pageup_low_k_sound (-1) E e m j r (Or.inr rfl) Hj Hm H
  | some r1 =>
    simp only [h1] at H
    obtain rfl := Option.some.inj H
    exact pageup_low_k_sound 1 E e m j r1 (Or.inl rfl) Hj Hm h1

/-- `pageup_align_sound`: `pageup_align e = k` is a real alignment:
    `2^k` divides the value. -/
theorem pageup_align_sound (E : env) (e : expr) :
    (0 ≤ pageup_align e ∧ pageup_align e ≤ 64) ∧
      zpow 2 (pageup_align e) ∣ bv_unsigned (edenot E e) := by
  unfold pageup_align
  dsimp only
  split
  · rename_i y mm
    split
    · rename_i hc
      obtain ⟨hme, hk64b⟩ := (Bool.and_eq_true ..).mp hc
      have hme' : y + 1 = zpow 2 (ctz64 (y + 1)) := beq_iff_eq.mp hme
      have hk64 : ctz64 (y + 1) ≤ 64 := of_decide_eq_true hk64b
      have hk0 : 0 ≤ ctz64 (y + 1) := (ctz64_sound (y + 1)).1.1
      split
      · rename_i hpl
        have hmod := (pageup_low_sound E e (y + 1) (ctz64 (y + 1)) 0
          ⟨hk0, hk64⟩ hme' hpl).1
        refine ⟨⟨hk0, hk64⟩, ?_⟩
        rw [← hme']
        exact Int.dvd_of_emod_eq_zero hmod
      · refine ⟨⟨by omega, by omega⟩, ?_⟩
        show (1 : Int) ∣ _
        exact Int.one_dvd _
    · refine ⟨⟨by omega, by omega⟩, ?_⟩
      show (1 : Int) ∣ _
      exact Int.one_dvd _
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    show (1 : Int) ∣ _
    exact Int.one_dvd _

/-- `ealign_sound`: the alignment domain is a real alignment. -/
theorem ealign_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E M kn) :
    (0 ≤ ealign kn e ∧ ealign kn e ≤ 64) ∧
      zpow 2 (ealign kn e) ∣ bv_unsigned (edenot E e) := by
  obtain ⟨A1, B1⟩ := ealign0_sound segs E M (facts_of kn) e (facts_of_ok segs E M kn Hkn)
  obtain ⟨A2, B2⟩ := pageup_align_sound E e
  unfold ealign
  by_cases hle : ealign0 (facts_of kn) e ≤ pageup_align e
  · rw [Int.max_eq_right hle]
    exact ⟨⟨by omega, by omega⟩, B2⟩
  · rw [Int.max_eq_left (by omega)]
    exact ⟨⟨by omega, by omega⟩, B1⟩

/-! ### `srl_expand_sound` -/

/-- `highmask_s` recognises a high mask: `highmask_s mk = some s` says
    `mk = 2^64 - 2^s` modulo `2^64` with `0 < s < 64`. -/
theorem highmask_s_some (mk s : Int) (H : highmask_s mk = some s) :
    mk % two64 = two64 - zpow 2 s ∧ 0 < s ∧ s < 64 := by
  unfold highmask_s at H
  generalize hm' : mk % two64 = m' at H
  by_cases hc : (two64 - m' == zpow 2 (AxSymExec3.zlog2 (two64 - m')) && 0 < AxSymExec3.zlog2 (two64 - m')
      && AxSymExec3.zlog2 (two64 - m') < 64) = true
  · rw [ite_eq_left hc] at H
    have hs : AxSymExec3.zlog2 (two64 - m') = s := Option.some.inj H
    obtain ⟨hc1, hs64b⟩ := (Bool.and_eq_true ..).mp hc
    obtain ⟨hmeb, hs0b⟩ := (Bool.and_eq_true ..).mp hc1
    have hme : two64 - m' = zpow 2 (AxSymExec3.zlog2 (two64 - m')) := beq_iff_eq.mp hmeb
    refine ⟨?_, ?_, ?_⟩
    · rw [hm', hs] at *
      omega
    · rw [← hs]; exact of_decide_eq_true hs0b
    · rw [← hs]; exact of_decide_eq_true hs64b
  · rw [ite_eq_right hc] at H
    exact absurd H (by simp)

/-- `srl_expand_sound`: every SRL / high-AND atom the page-rounding
    expansion removes is replaced by a form with the SAME `tden`, so the
    expansion preserves the denotation exactly. -/
theorem srl_expand_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) :
    ∀ (ts : List (Int × expr)) (c : Int) (ts' : List (Int × expr)),
      know_ok segs E M kn → srl_expand kn ts = (c, ts') → tden E ts = c + tden E ts' := by
  intro ts
  induction ts with
  | nil =>
    intro c ts' _ H
    simp only [srl_expand, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    simp [tden]
  | cons t rest ih =>
    obtain ⟨k, a⟩ := t
    intro c ts' Hkn H
    simp only [srl_expand] at H
    generalize hr : srl_expand kn rest = p at H
    obtain ⟨c0, t0⟩ := p
    simp only [] at H
    have ih' : tden E rest = c0 + tden E t0 := ih c0 t0 Hkn hr
    have KEEP : (c0, lins_e k a t0) = (c, ts') →
        tden E ((k, a) :: rest) = c + tden E ts' := by
      intro h
      rw [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      simp only [tden]
      rw [ih', lins_e_sound]
      omega
    cases a with
    | ELit z => exact KEEP H
    | EVar n => exact KEEP H
    | EAluw op b1 b2 => exact KEEP H
    | EMdw op b1 b2 => exact KEEP H
    | EExt sx lo n b1 => exact KEEP H
    | EBlob sx kk i n => exact KEEP H
    | EMd op b1 b2 => exact KEEP H
    | EAlu op b1 b2 =>
      cases op with
      | SRL =>
        cases b2 with
        | ELit s =>
          simp only [] at H
          generalize hm : zpow 2 ((s % two64) % 64) = mv at H
          by_cases hc : (k % mv == 0 && lin_nowrap kn b1) = true
          · rw [ite_eq_left hc] at H
            obtain ⟨hdivb, hnw⟩ := (Bool.and_eq_true ..).mp hc
            have hdiv : k % mv = 0 := beq_iff_eq.mp hdivb
            have hj0 : 0 ≤ (s % two64) % 64 := Int.emod_nonneg _ (by decide)
            have hjlt : (s % two64) % 64 < 64 := Int.emod_lt_of_pos _ (by decide)
            have hmv0 : 0 < mv := by
              rw [← hm]
              exact two_pow_pos_int _
            have hk : k = k / mv * mv := by
              have h := Int.ediv_mul_add_emod k mv
              omega
            have hsv : uE E (.EAlu .SRL b1 (.ELit s)) = uE E b1 / mv := by
              have h := u_srl_lit E b1 s
              have hz : (2 : Int) ^ (((s % two64) % 64).toNat) = mv := by
                rw [← hm]; rfl
              rw [hz] at h
              exact h
            have hxm : uE E b1 / mv * mv = uE E b1 - uE E b1 % mv := by
              have h := Int.ediv_mul_add_emod (uE E b1) mv
              omega
            have he : uE E b1 = (lin_of b1).1 + tden E (lin_of b1).2 :=
              lin_nowrap_sound segs E M kn b1 Hkn hnw
            generalize hle : lin_of b1 = le at H ⊢
            obtain ⟨ce, te⟩ := le
            simp only [] at H ⊢
            have hel : uE E b1 = ce + tden E te := by rw [hle] at he; simpa using he
            have h1 : k * (uE E b1 / mv) = (k / mv) * ((uE E b1 / mv) * mv) := by
              conv => lhs; rw [hk]
              ac_rfl
            have h3 : (k / mv) * uE E b1 = (k / mv) * ce + (k / mv) * tden E te := by
              rw [hel, Int.mul_add]
            have hfold : tden E (te.foldr (fun t acc => lins_e ((k / mv) * t.1) t.2 acc) t0)
                = (k / mv) * tden E te + tden E t0 :=
              fold_lins_e_sound E (k / mv) te t0
            by_cases hje : (s % two64) % 64 ≤ ealign kn b1
            · -- exact: `e` is a multiple of `m`, so the remainder vanishes
              rw [ite_eq_left hje] at H
              rw [Prod.mk.injEq] at H
              obtain ⟨hc, hts⟩ := H
              have hx0 : uE E b1 % mv = 0 := by
                obtain ⟨-, hdv⟩ := ealign_sound segs E M kn b1 Hkn
                have hd : mv ∣ uE E b1 := by
                  rw [← hm]
                  exact Int.dvd_trans (pow2_divide_le _ _ ⟨hj0, hje⟩) hdv
                exact Int.emod_eq_zero_of_dvd hd
              have h2 : (k / mv) * ((uE E b1 / mv) * mv) = (k / mv) * uE E b1 := by
                rw [hxm, hx0]
                simp
              rw [← hc, ← hts]
              simp only [tden]
              rw [ih', hsv, hfold]
              omega
            · -- residual: keep `-q * (e AND (m-1))`
              rw [ite_eq_right hje] at H
              rw [Prod.mk.injEq] at H
              obtain ⟨hc, hts⟩ := H
              have hrem : uE E (srl_rem b1 mv) = uE E b1 % mv := by
                rw [← hm]
                exact u_srl_rem E b1 ((s % two64) % 64) ⟨hj0, by omega⟩
              have h2 : (k / mv) * ((uE E b1 / mv) * mv)
                  = (k / mv) * uE E b1 - (k / mv) * (uE E b1 % mv) := by
                rw [hxm, Int.mul_sub]
              have hneg : (-(k / mv)) * (uE E b1 % mv) = -((k / mv) * (uE E b1 % mv)) :=
                Int.neg_mul _ _
              rw [← hc, ← hts]
              simp only [tden]
              rw [ih', hsv, lins_e_sound, hrem, hfold]
              omega
          · rw [ite_eq_right hc] at H
            exact KEEP H
        | _ => exact KEEP H
      | AND =>
        cases b2 with
        | ELit mk =>
          simp only [] at H
          cases hhm : highmask_s mk with
          | none => rw [hhm] at H; simp only [] at H; exact KEEP H
          | some s =>
            rw [hhm] at H
            simp only [] at H
            by_cases hnw : lin_nowrap kn b1 = true
            · rw [ite_eq_left hnw] at H
              obtain ⟨hmm', hs0, hs64⟩ := highmask_s_some mk s hhm
              have huand : uE E (.EAlu .AND b1 (.ELit mk))
                  = uE E b1 - uE E b1 % zpow 2 s := by
                show bv_unsigned (alu64 .AND (edenot E b1) (edenot E (.ELit mk)))
                  = bv_unsigned (edenot E b1) - bv_unsigned (edenot E b1) % zpow 2 s
                rw [u_and64]
                have hlit : bv_unsigned (edenot E (.ELit mk)) = (2 : Int) ^ 64 - zpow 2 s := by
                  show bv_unsigned (Z_to_bv 64 mk) = _
                  rw [u_lit64, hmm', two64_eq]
                rw [hlit]
                have hx := u64_range (edenot E b1)
                exact land_highmask _ s ⟨by omega, hs64⟩ ⟨hx.1, hx.2⟩
              have he : uE E b1 = (lin_of b1).1 + tden E (lin_of b1).2 :=
                lin_nowrap_sound segs E M kn b1 Hkn hnw
              generalize hle : lin_of b1 = le at H ⊢
              obtain ⟨ce, te⟩ := le
              simp only [] at H ⊢
              have hel : uE E b1 = ce + tden E te := by rw [hle] at he; simpa using he
              rw [Prod.mk.injEq] at H
              obtain ⟨hc, hts⟩ := H
              have hfold : tden E (te.foldr (fun t acc => lins_e (k * t.1) t.2 acc) t0)
                  = k * tden E te + tden E t0 := fold_lins_e_sound E k te t0
              have hrem : uE E (srl_rem b1 (zpow 2 s)) = uE E b1 % zpow 2 s :=
                u_srl_rem E b1 s ⟨by omega, hs64⟩
              have hqx : k * uE E b1 = k * ce + k * tden E te := by
                rw [hel, Int.mul_add]
              have hdist : k * (uE E b1 - uE E b1 % zpow 2 s)
                  = k * uE E b1 - k * (uE E b1 % zpow 2 s) :=
                Int.mul_sub k _ _
              have hneg : (-k) * (uE E b1 % zpow 2 s) = -(k * (uE E b1 % zpow 2 s)) :=
                Int.neg_mul _ _
              rw [← hc, ← hts]
              simp only [tden]
              rw [ih', huand, lins_e_sound, hrem, hfold]
              omega
            · rw [ite_eq_right hnw] at H
              exact KEEP H
        | _ => exact KEEP H
      | ADD => exact KEEP H
      | SUB => exact KEEP H
      | SLL => exact KEEP H
      | SLT => exact KEEP H
      | SLTU => exact KEEP H
      | XOR => exact KEEP H
      | OR => exact KEEP H
      | SRA => exact KEEP H

/-- An `Int` multiple of `2^64` lying strictly between `-2^64` and `2^64` is
    zero.  (Splitting this out of `fact_nowrap_sound` keeps the linear
    arithmetic coefficient-free: `omega` is unreliable with the coefficient
    `2^64` on a variable.) -/
theorem mul_two64_eq_zero {q : Int} (h1 : -(2 ^ 64) < q * 2 ^ 64)
    (h2 : q * 2 ^ 64 < 2 ^ 64) : q = 0 := by
  have hpos : (0 : Int) < 2 ^ 64 := two_pow_pos_int 64
  have hlt1 : q < 1 := by
    have h : 0 < (2 : Int) ^ 64 - (2 : Int) ^ 64 * q := by omega
    have h' : (2 : Int) ^ 64 * (1 - q) = (2 : Int) ^ 64 - (2 : Int) ^ 64 * q := by
      rw [Int.mul_sub, Int.mul_one]
    rw [← h'] at h
    have h2' := Int.pos_of_mul_pos_right h hpos
    omega
  have hgt : -1 < q := by
    have h : 0 < (2 : Int) ^ 64 * q + 2 ^ 64 := by omega
    have h' : (2 : Int) ^ 64 * (q + 1) = (2 : Int) ^ 64 * q + 2 ^ 64 := by
      rw [Int.mul_add, Int.mul_one]
    rw [← h'] at h
    have h2' := Int.pos_of_mul_pos_right h hpos
    omega
  omega

/-! ### Relational sum-fact bounds, J2-b -/

/-- `sum_fact_x_sound`: the srl-expanded copy of a fact is sound. -/
theorem sum_fact_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) (ts : List (Int × expr)) (lo hi : Int)
    (Hall : know_ok segs E M allkn) (Hb : lo ≤ tden E ts ∧ tden E ts ≤ hi) :
    ∀ f ∈ sum_fact_x allkn ts lo hi, sfact_ok E f := by
  unfold sum_fact_x
  generalize hx : srl_expand allkn ts = p
  obtain ⟨c2, ts2⟩ := p
  simp only []
  have S1 : tden E ts = c2 + tden E ts2 :=
    srl_expand_sound segs E M allkn ts c2 ts2 Hall hx
  cases ts2 with
  | nil => intro f hf; simp at hf
  | cons t r =>
    by_cases hc : (c2 == 0) = true
    · rw [ite_eq_left hc]
      intro f hf
      simp at hf
    · rw [ite_eq_right hc]
      intro f hf
      rw [List.mem_singleton] at hf
      subst hf
      show lo - c2 ≤ tden E (t :: r) ∧ tden E (t :: r) ≤ hi - c2
      omega

/-- `fact_nowrap_sound`: a fact whose plain interval admits no
    other representative pins the linear form exactly. -/
theorem fact_nowrap_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) (e : expr) (lo hi : Int)
    (Hall : know_ok segs E M allkn) (H : fact_nowrap allkn e hi = true)
    (Hb : lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi) :
    bv_unsigned (edenot E e) = (lin_of e).1 + tden E (lin_of e).2 := by
  unfold fact_nowrap at H
  cases hlr : lin_range (erange allkn) (lin_of e).1 (lin_of e).2 with
  | none =>
    simp only [hlr] at H
    exact absurd H (by simp)
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only [hlr] at H
    obtain ⟨H1, H2⟩ := (Bool.and_eq_true ..).mp H
    have h1 : b < 2 ^ 64 := by have hh := of_decide_eq_true H1; simpa [two64] using hh
    have h2 : a + 2 ^ 64 > hi := by have hh := of_decide_eq_true H2; simpa [two64] using hh
    have hr := lin_range_sound E (erange allkn)
      (fun a lo hi Ha => erange_sound segs E M allkn a lo hi Hall Ha) _ _ _ _ hlr
    have hv : 0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) < 2 ^ 64 :=
      u64_range (edenot E e)
    -- the form `c + ts` and its value `v` differ by a multiple of 2^64; that
    -- multiple is squeezed into `(-2^64, 2^64)` and must be zero.  The two
    -- additive steps are done BEFORE `q` enters the context: `omega` is
    -- unreliable once the huge coefficient of `q * 2^64` is around.
    have hT1a : -(2 ^ 64) < (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) := by
      omega
    have hT2a : (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) < 2 ^ 64 := by
      omega
    obtain ⟨q, hq⟩ := lin_of_sound E e
    have hq' : (lin_of e).1 + tden E (lin_of e).2 = bv_unsigned (edenot E e) + q * 2 ^ 64 := hq
    have htq : q * 2 ^ 64 = (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) := by
      rw [hq', Int.add_comm (bv_unsigned (edenot E e)), Int.add_sub_cancel]
    have hT1 : -(2 ^ 64) < q * 2 ^ 64 := by rw [htq]; exact hT1a
    have hT2 : q * 2 ^ 64 < 2 ^ 64 := by rw [htq]; exact hT2a
    have hq0 : q = 0 := mul_two64_eq_zero hT1 hT2
    rw [hq0, Int.zero_mul, Int.add_zero] at hq'
    show bv_unsigned (edenot E e) = (lin_of e).1 + tden E (lin_of e).2
    exact hq'.symm

/-- `sub_fact_sound`: subtracting `q * fts` scales the total. -/
theorem sub_fact_sound (E : env) (q : Int) (fts ts : List (Int × expr)) :
    tden E (sub_fact q fts ts) = tden E ts - q * tden E fts := by
  unfold sub_fact
  induction fts with
  | nil => simp [tden]
  | cons t r ih =>
    obtain ⟨k, a⟩ := t
    simp only [List.foldr_cons, tden]
    rw [lins_e_sound, ih, Int.mul_add]
    have hneg : (-(q * k)) * uE E a = -(q * (k * uE E a)) := by
      rw [Int.neg_mul, Int.mul_assoc]
    rw [hneg]
    omega

/-!  This is the "explicit `ts = t1 :: t2 ::
    tl`" route this tree needs because `cases h : lin_of e` cannot reach a
    scrutinee that only lives inside a `match` in the definition body. -/

/-- The one-step unfolding of `sum_facts` at a `.KRange` entry. -/
theorem sum_facts_KRange_unfold (allkn : List kentry) (e : expr) (lo hi : Int)
    (rest : List kentry) :
    sum_facts allkn (.KRange e lo hi :: rest) =
      (match e with
       | .EVar _ => sum_facts allkn rest
       | _ =>
         match lin_of e with
         | (c, ts@(_ :: _ :: _)) =>
             if fact_nowrap allkn e hi then
               (ts, (lo - c, hi - c)) ::
                 (sum_fact_x allkn ts (lo - c) (hi - c) ++ sum_facts allkn rest)
             else sum_facts allkn rest
         | _ => sum_facts allkn rest) := rfl

/-- `sum_facts` at a `.KRange` entry whose form has >= 2 atoms: the digested
    fact plus its srl-expanded copy, then the rest of the list. -/
theorem sum_facts_KRange_cc (allkn : List kentry) (e : expr) (lo hi : Int)
    (rest : List kentry) (c : Int) (t1 t2 : Int × expr) (tl : List (Int × expr))
    (hle : lin_of e = (c, t1 :: t2 :: tl)) :
    sum_facts allkn (.KRange e lo hi :: rest) =
      (if fact_nowrap allkn e hi then
        ((t1 :: t2 :: tl), (lo - c, hi - c)) ::
          (sum_fact_x allkn (t1 :: t2 :: tl) (lo - c) (hi - c) ++ sum_facts allkn rest)
       else sum_facts allkn rest) := by
  rw [sum_facts_KRange_unfold, hle]
  cases e <;> simp_all [lin_of]

/-- `sum_facts` at a `.KRange` entry with a CONSTANT linear form. -/
theorem sum_facts_KRange_nil (allkn : List kentry) (e : expr) (lo hi : Int)
    (rest : List kentry) (c : Int) (hle : lin_of e = (c, [])) :
    sum_facts allkn (.KRange e lo hi :: rest) = sum_facts allkn rest := by
  rw [sum_facts_KRange_unfold, hle]
  cases e <;> simp_all [lin_of]

/-- `sum_facts` at a `.KRange` entry with a SINGLE-atom linear form. -/
theorem sum_facts_KRange_one (allkn : List kentry) (e : expr) (lo hi : Int)
    (rest : List kentry) (c : Int) (t : Int × expr) (hle : lin_of e = (c, [t])) :
    sum_facts allkn (.KRange e lo hi :: rest) = sum_facts allkn rest := by
  rw [sum_facts_KRange_unfold, hle]
  cases e <;> simp_all [lin_of]

/-- `sum_facts_sound`: the digested facts of `kn` are sound, given
    that the knowledge list `allkn` the ranges are computed from is itself
    sound and that `kn` holds in the same memory. -/
theorem sum_facts_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn kn : List kentry) (Hall : know_ok segs E M allkn) (Hkn : know_ok segs E M kn) :
    ∀ f ∈ sum_facts allkn kn, sfact_ok E f := by
  revert Hkn
  induction kn with
  | nil =>
    intro _ f hf
    simp [sum_facts] at hf
  | cons K rest IH =>
    intro Hkn f hf
    cases K with
    | KRange e lo hi =>
      obtain ⟨HK1, HK2⟩ := Hkn (.KRange e lo hi) List.mem_cons_self
      have Hrest : know_ok segs E M rest :=
        fun K hK => Hkn K (List.mem_cons_of_mem _ hK)
      -- `GEN` from , with the shape of `lin_of e` supplied by
      -- `cases ts` instead of by an as-pattern in the definition.
      have key : ∀ (c : Int) (ts : List (Int × expr)), lin_of e = (c, ts) →
          ∀ f ∈ sum_facts allkn (.KRange e lo hi :: rest), sfact_ok E f := by
        intro c ts hle
        cases ts with
        | nil => rw [sum_facts_KRange_nil allkn e lo hi rest c hle]; exact IH Hrest
        | cons t r =>
          cases r with
          | nil => rw [sum_facts_KRange_one allkn e lo hi rest c t hle]; exact IH Hrest
          | cons t2 tl =>
            rw [sum_facts_KRange_cc allkn e lo hi rest c t t2 tl hle]
            by_cases hnw : fact_nowrap allkn e hi = true
            · rw [ite_eq_left hnw]
              have He0 := fact_nowrap_sound segs E M allkn e lo hi Hall hnw ⟨HK1, HK2⟩
              rw [hle] at He0
              have He : bv_unsigned (edenot E e) = c + tden E (t :: t2 :: tl) := He0
              have Hb : lo - c ≤ tden E (t :: t2 :: tl) ∧
                  tden E (t :: t2 :: tl) ≤ hi - c := by
                constructor <;> omega
              intro f hf
              rcases List.mem_cons.mp hf with rfl | hf
              · exact Hb
              · rcases List.mem_append.mp hf with hf | hf
                · exact sum_fact_x_sound segs E M allkn (t :: t2 :: tl) (lo - c) (hi - c)
                    Hall Hb f hf
                · exact IH Hrest f hf
            · rw [ite_eq_right hnw]
              exact IH Hrest
      exact key _ _ rfl f hf
    | KWord a w v => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KZero a n => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KBlob a n k => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KImg lo hi => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KAlign e m => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KWr a n => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KDisj a1 n1 a2 n2 => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KFill a n c => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf
    | KUnk a n => exact IH (fun K hK => Hkn K (List.mem_cons_of_mem _ hK)) f hf

/-- `sum_subst_sound`: the greedy substitution of sum facts never
    loses the value's bracket — the residual terms plus the accumulated
    interval still contain `tden E ts + lo` … `tden E ts + hi`. -/
theorem sum_subst_sound (E : env) :
    ∀ (fs : List sfact) (ts : List (Int × expr)) (lo hi : Int) (hit : Bool)
      (ts' : List (Int × expr)) (lo' hi' : Int) (hit' : Bool),
      (∀ f ∈ fs, sfact_ok E f) →
      sum_subst fs ts lo hi hit = (ts', (lo', hi'), hit') →
      tden E ts' + lo' ≤ tden E ts + lo ∧ tden E ts + hi ≤ tden E ts' + hi' := by
  intro fs
  induction fs with
  | nil =>
    intro ts lo hi hit ts' lo' hi' hit' _ H
    simp only [sum_subst] at H
    cases H
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  | cons f r ih =>
    intro ts lo hi hit ts' lo' hi' hit' Hfs H
    obtain ⟨fts, flo, fhi⟩ := f
    have Hf : flo ≤ tden E fts ∧ tden E fts ≤ fhi := Hfs _ List.mem_cons_self
    have Hr : ∀ g ∈ r, sfact_ok E g := fun g hg => Hfs g (List.mem_cons_of_mem _ hg)
    simp only [sum_subst] at H
    generalize hq : fact_quot fts ts none = p at H
    cases p with
    | none =>
      simp only [] at H
      exact ih ts lo hi hit ts' lo' hi' hit' Hr H
    | some q =>
      simp only [] at H
      by_cases hq0 : 0 ≤ q
      · rw [ite_eq_left hq0] at H
        obtain ⟨A, B⟩ := ih (sub_fact q fts ts) (lo + q * flo) (hi + q * fhi) true
          ts' lo' hi' hit' Hr H
        rw [sub_fact_sound] at A B
        -- `q * tden E fts` stays an atom: `omega` is linear, so the two
        -- monotonicity steps are supplied by hand.
        have h1 : q * flo ≤ q * tden E fts := Int.mul_le_mul_of_nonneg_left Hf.1 hq0
        have h2 : q * tden E fts ≤ q * fhi := Int.mul_le_mul_of_nonneg_left Hf.2 hq0
        constructor <;> omega
      · rw [ite_eq_right hq0] at H
        obtain ⟨A, B⟩ := ih (sub_fact q fts ts) (lo + q * fhi) (hi + q * flo) true
          ts' lo' hi' hit' Hr H
        rw [sub_fact_sound] at A B
        have hqle : q ≤ 0 := by omega
        have h1 : q * tden E fts ≤ q * flo := Int.mul_le_mul_of_nonpos_left hqle Hf.1
        have h2 : q * fhi ≤ q * tden E fts := Int.mul_le_mul_of_nonpos_left hqle Hf.2
        constructor <;> omega

/-- `lin_test_rel_sound`: the RELATIONAL interval of `c + Σ ts` is
    sound — the sum facts replace whole sub-sums, then the residual form is
    bounded per atom (`lin_range`). -/
theorem lin_test_rel_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : Int) (ts : List (Int × expr)) (test : Int → Int → Bool)
    (Hkn : know_ok segs E M kn) (H : lin_test_rel kn c ts test = true) :
    ∃ lo hi, test lo hi = true ∧ lo ≤ c + tden E ts ∧ c + tden E ts ≤ hi := by
  unfold lin_test_rel at H
  generalize hsf : sum_facts kn kn = sf at H
  cases sf with
  | nil => simp at H
  | cons f fs =>
    simp only [] at H
    generalize hs : sum_subst (f :: fs) ts 0 0 false = q at H
    obtain ⟨ts', ⟨lo0, hi0⟩, hit⟩ := q
    cases hit with
    | false => simp at H
    | true =>
      simp only [] at H
      generalize hl : lin_range (erange kn) c ts' = r at H
      cases r with
      | none => simp at H
      | some p =>
        obtain ⟨lo, hi⟩ := p
        simp only [] at H
        refine ⟨lo + lo0, hi + hi0, H, ?_⟩
        have Hb := lin_range_sound E (erange kn)
          (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) c ts' lo hi hl
        have Hfs := sum_facts_sound segs E M kn kn Hkn Hkn
        rw [hsf] at Hfs
        obtain ⟨A, B⟩ := sum_subst_sound E (f :: fs) ts 0 0 false ts' lo0 hi0 true Hfs hs
        omega

/-- `lin_test_sound`: the per-atom interval when `test` accepts it,
    else the relational interval. -/
theorem lin_test_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : Int) (ts : List (Int × expr)) (test : Int → Int → Bool)
    (Hkn : know_ok segs E M kn) (H : lin_test kn c ts test = true) :
    ∃ lo hi, test lo hi = true ∧ lo ≤ c + tden E ts ∧ c + tden E ts ≤ hi := by
  unfold lin_test at H
  generalize hl : lin_range (erange kn) c ts = r at H
  cases r with
  | none =>
    simp only [] at H
    exact lin_test_rel_sound segs E M kn c ts test Hkn H
  | some p =>
    obtain ⟨lo, hi⟩ := p
    simp only [] at H
    by_cases ht : test lo hi = true
    · rw [ite_eq_left ht] at H
      exact ⟨lo, hi, ht, lin_range_sound E (erange kn)
        (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) c ts lo hi hl⟩
    · rw [ite_eq_right ht] at H
      exact lin_test_rel_sound segs E M kn c ts test Hkn H

/-- `lin_brange_sound`: the relational interval of a linear form is
    the VALUE's interval when it is non-negative and below `2^64` (so the
    modular representative is the value itself). -/
theorem lin_brange_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo hi : Int) (Hkn : know_ok segs E M kn)
    (H : lin_brange kn e = some (lo, hi)) :
    lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
  unfold lin_brange at H
  generalize hsf : sum_facts kn kn = sf at H
  cases sf with
  | nil => simp at H
  | cons f fs =>
    simp only [] at H
    generalize hs : sum_subst (f :: fs) (lin_of e).2 0 0 false = q at H
    obtain ⟨ts', ⟨lo0, hi0⟩, hit⟩ := q
    cases hit with
    | false => simp at H
    | true =>
      simp only [] at H
      generalize hl : lin_range (erange kn) (lin_of e).1 ts' = r at H
      cases r with
      | none => simp at H
      | some p =>
        obtain ⟨l, h⟩ := p
        simp only [] at H
        by_cases hc : (0 ≤ (l + lo0) && (h + hi0) < two64) = true
        · rw [ite_eq_left hc] at H
          obtain ⟨rfl, rfl⟩ := H
          obtain ⟨hc1, hc2⟩ := (Bool.and_eq_true ..).mp hc
          have h1 : 0 ≤ l + lo0 := of_decide_eq_true hc1
          have h2 : h + hi0 < 2 ^ 64 := by
            have hh := of_decide_eq_true hc2; simpa [two64] using hh
          have Hb := lin_range_sound E (erange kn)
            (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha) (lin_of e).1 ts' l h hl
          have Hfs := sum_facts_sound segs E M kn kn Hkn Hkn
          rw [hsf] at Hfs
          obtain ⟨A, B⟩ := sum_subst_sound E (f :: fs) (lin_of e).2 0 0 false
            ts' lo0 hi0 true Hfs hs
          -- the form and the value differ by `q * 2^64`, squeezed to zero
          have Hu : 0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) < 2 ^ 64 :=
            u64_range (edenot E e)
          have hT1a : -(2 ^ 64) < (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) := by
            omega
          have hT2a : (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) < 2 ^ 64 := by
            omega
          obtain ⟨q, hq⟩ := lin_of_sound E e
          have hq' : (lin_of e).1 + tden E (lin_of e).2 =
              bv_unsigned (edenot E e) + q * 2 ^ 64 := hq
          have htq : q * 2 ^ 64 =
              (lin_of e).1 + tden E (lin_of e).2 - bv_unsigned (edenot E e) := by
            rw [hq', Int.add_comm (bv_unsigned (edenot E e)), Int.add_sub_cancel]
          have hq0 : q = 0 := mul_two64_eq_zero (by rw [htq]; exact hT1a)
            (by rw [htq]; exact hT2a)
          rw [hq0, Int.zero_mul, Int.add_zero] at hq'
          rw [← hq']
          omega
        · rw [ite_eq_right hc] at H
          simp at H

/-- `tden_map_scale`: scaling every coefficient scales the total
    (the scaled-expansion interval). -/
theorem tden_map_scale (E : env) (sc : Int) (ts : List (Int × expr)) :
    tden E (ts.map (fun t => (sc * t.1, t.2))) = sc * tden E ts := by
  induction ts with
  | nil => simp [tden]
  | cons t rest ih =>
    obtain ⟨k, a⟩ := t
    simp only [List.map_cons, tden, ih]
    rw [Int.mul_add, Int.mul_assoc]

/-- `lin_srange_sound`: the scaled-expansion interval, divided back
    by the scaling factor, is the value's interval.  `srl_scale_need` picks
    the factor `2^j` (`0 <= j <= 24`) at which the SRL atoms of the form
    become expandable; `srl_expand` is applied twice over the scaled list,
    and the resulting Z-interval `lo', hi'` is divided back with a ceiling
    (`zcdiv`) resp. a floor (`/`).  The value differs from the form by a
    multiple of `2^64`, which the interval `[lo, hi] ⊆ [0, 2^64)` squeezes
    to zero. -/
theorem lin_srange_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo hi : Int) (Hkn : know_ok segs E M kn)
    (H : lin_srange kn e = some (lo, hi)) :
    lo ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) ≤ hi := by
  unfold lin_srange at H
  generalize hlin : lin_of e = l at H
  obtain ⟨c, ts⟩ := l
  try simp only [] at H
  generalize hj : srl_scale_need ts = j at H
  try simp only [] at H
  generalize hx2 : srl_expand kn (ts.map (fun t => (zpow 2 j * t.1, t.2))) = p2 at H
  obtain ⟨c2, t2⟩ := p2
  try simp only [] at H
  generalize hx3 : (if has_srl t2 then srl_expand kn t2 else ((0 : Int), t2)) = p3 at H
  obtain ⟨c3, t3⟩ := p3
  try simp only [] at H
  by_cases hJ : (decide (0 ≤ j) && decide (j ≤ 24)) = true
  · rw [ite_eq_left hJ] at H
    try simp only [] at H
    obtain ⟨hJ1, hJ2⟩ := (Bool.and_eq_true ..).mp hJ
    have hj0 : 0 ≤ j := of_decide_eq_true hJ1
    have hsc : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
    generalize hlr : lin_range (erange kn) (zpow 2 j * c + c2 + c3) t3 = r at H
    cases r with
    | none => try simp only [] at H; simp at H
    | some q =>
      obtain ⟨lo', hi'⟩ := q
      try simp only [] at H
      by_cases hfin : (decide (0 ≤ zcdiv lo' (zpow 2 j)) &&
          (decide (zcdiv lo' (zpow 2 j) ≤ hi' / zpow 2 j) &&
           decide (hi' / zpow 2 j < two64))) = true
      · rw [ite_eq_left hfin] at H
        simp only [Option.some.injEq, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨hf1, hf23⟩ := (Bool.and_eq_true ..).mp hfin
        obtain ⟨hf2, hf3⟩ := (Bool.and_eq_true ..).mp hf23
        have h1 : 0 ≤ zcdiv lo' (zpow 2 j) := of_decide_eq_true hf1
        have h2 : zcdiv lo' (zpow 2 j) ≤ hi' / zpow 2 j := of_decide_eq_true hf2
        have h3 : hi' / zpow 2 j < 2 ^ 64 := by
          have hh := of_decide_eq_true hf3; simpa [two64] using hh
        -- the two expansions
        have S1 : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) = c2 + tden E t2 :=
          srl_expand_sound segs E M kn _ c2 t2 Hkn hx2
        have Smap : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) =
            zpow 2 j * tden E ts := tden_map_scale E (zpow 2 j) ts
        have S2 : tden E t2 = c3 + tden E t3 := by
          by_cases hsr : has_srl t2 = true
          · rw [ite_eq_left hsr] at hx3
            exact srl_expand_sound segs E M kn t2 c3 t3 Hkn hx3
          · rw [ite_eq_right hsr] at hx3
            simp only [Prod.mk.injEq] at hx3
            obtain ⟨h1', h2'⟩ := hx3
            subst h1' h2'
            rw [Int.zero_add]
        have Hb := lin_range_sound E (erange kn)
          (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha)
          (zpow 2 j * c + c2 + c3) t3 lo' hi' hlr
        -- the scaled form is `2^j * (c + tden E ts)`
        have hT : zpow 2 j * tden E ts = c2 + c3 + tden E t3 := by
          rw [← Smap, S1, S2]
          omega
        have hd : zpow 2 j * (c + tden E ts) = zpow 2 j * c + c2 + c3 + tden E t3 := by
          rw [Int.mul_add, hT]
          omega
        have HL : lo' ≤ zpow 2 j * (c + tden E ts) ∧
            zpow 2 j * (c + tden E ts) ≤ hi' := by
          rw [hd]
          exact Hb
        -- divide the scaled interval back
        have Hfl : c + tden E ts ≤ hi' / zpow 2 j := by
          refine Int.le_ediv_of_mul_le hsc ?_
          rw [Int.mul_comm]
          exact HL.2
        have Hce : zcdiv lo' (zpow 2 j) ≤ c + tden E ts := by
          have hle : (-(c + tden E ts)) ≤ (-lo') / zpow 2 j := by
            refine Int.le_ediv_of_mul_le hsc ?_
            have hneg : -(zpow 2 j * (c + tden E ts)) = (-(c + tden E ts)) * zpow 2 j := by
              rw [Int.neg_mul, Int.mul_comm]
            rw [← hneg]
            omega
          unfold zcdiv
          omega
        -- the value's interval
        have Hu : 0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) < 2 ^ 64 :=
          u64_range (edenot E e)
        have HL0 : 0 ≤ c + tden E ts := by omega
        have HL64 : c + tden E ts < 2 ^ 64 := by omega
        have hT1a : -(2 ^ 64) < c + tden E ts - bv_unsigned (edenot E e) := by omega
        have hT2a : c + tden E ts - bv_unsigned (edenot E e) < 2 ^ 64 := by omega
        obtain ⟨qq, hq⟩ := lin_of_sound E e
        have hq2 : c + tden E ts = bv_unsigned (edenot E e) + qq * 2 ^ 64 := by
          have h := hq
          rw [hlin] at h
          simpa [lden, uE] using h
        have htq : qq * 2 ^ 64 = c + tden E ts - bv_unsigned (edenot E e) := by
          rw [hq2, Int.add_comm (bv_unsigned (edenot E e)), Int.add_sub_cancel]
        have hq0 : qq = 0 := mul_two64_eq_zero (by rw [htq]; exact hT1a)
          (by rw [htq]; exact hT2a)
        rw [hq0, Int.zero_mul, Int.add_zero] at hq2
        rw [← hq2]
        exact ⟨by omega, by omega⟩
      · rw [ite_eq_right hfin] at H
        simp at H
  · rw [ite_eq_right hJ] at H
    simp at H

/-- `lin_srange_exact`: the scaled-expansion interval, divided back
    by the scaling factor, is the value's interval.  `srl_scale_need` picks
    the factor `2^j` (`0 <= j <= 24`) at which the SRL atoms of the form
    become expandable; `srl_expand` is applied twice over the scaled list,
    and the resulting Z-interval `lo', hi'` is divided back with a ceiling
    (`zcdiv`) resp. a floor (`/`).  The same squeeze as `lin_srange_sound`
    (the form differs from the value by a multiple of `2^64`, and both lie
    in `[0, 2^64)`) here yields the linear form EXACTLY, not just a
    bracket: that is what the no-wrap decision of `lin_nowrapR` needs. -/
theorem lin_srange_exact (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo hi : Int) (Hkn : know_ok segs E M kn)
    (H : lin_srange kn e = some (lo, hi)) :
    bv_unsigned (edenot E e) = (lin_of e).1 + tden E (lin_of e).2 := by
  unfold lin_srange at H
  generalize hlin : lin_of e = l at H
  obtain ⟨c, ts⟩ := l
  try simp only [] at H
  generalize hj : srl_scale_need ts = j at H
  try simp only [] at H
  generalize hx2 : srl_expand kn (ts.map (fun t => (zpow 2 j * t.1, t.2))) = p2 at H
  obtain ⟨c2, t2⟩ := p2
  try simp only [] at H
  generalize hx3 : (if has_srl t2 then srl_expand kn t2 else ((0 : Int), t2)) = p3 at H
  obtain ⟨c3, t3⟩ := p3
  try simp only [] at H
  by_cases hJ : (decide (0 ≤ j) && decide (j ≤ 24)) = true
  · rw [ite_eq_left hJ] at H
    try simp only [] at H
    obtain ⟨hJ1, hJ2⟩ := (Bool.and_eq_true ..).mp hJ
    have hj0 : 0 ≤ j := of_decide_eq_true hJ1
    have hsc : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
    generalize hlr : lin_range (erange kn) (zpow 2 j * c + c2 + c3) t3 = r at H
    cases r with
    | none => try simp only [] at H; simp at H
    | some q =>
      obtain ⟨lo', hi'⟩ := q
      try simp only [] at H
      by_cases hfin : (decide (0 ≤ zcdiv lo' (zpow 2 j)) &&
          (decide (zcdiv lo' (zpow 2 j) ≤ hi' / zpow 2 j) &&
           decide (hi' / zpow 2 j < two64))) = true
      · rw [ite_eq_left hfin] at H
        simp only [Option.some.injEq, Prod.mk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨hf1, hf23⟩ := (Bool.and_eq_true ..).mp hfin
        obtain ⟨hf2, hf3⟩ := (Bool.and_eq_true ..).mp hf23
        have h1 : 0 ≤ zcdiv lo' (zpow 2 j) := of_decide_eq_true hf1
        have h2 : zcdiv lo' (zpow 2 j) ≤ hi' / zpow 2 j := of_decide_eq_true hf2
        have h3 : hi' / zpow 2 j < 2 ^ 64 := by
          have hh := of_decide_eq_true hf3; simpa [two64] using hh
        -- the two expansions
        have S1 : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) = c2 + tden E t2 :=
          srl_expand_sound segs E M kn _ c2 t2 Hkn hx2
        have Smap : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) =
            zpow 2 j * tden E ts := tden_map_scale E (zpow 2 j) ts
        have S2 : tden E t2 = c3 + tden E t3 := by
          by_cases hsr : has_srl t2 = true
          · rw [ite_eq_left hsr] at hx3
            exact srl_expand_sound segs E M kn t2 c3 t3 Hkn hx3
          · rw [ite_eq_right hsr] at hx3
            simp only [Prod.mk.injEq] at hx3
            obtain ⟨h1', h2'⟩ := hx3
            subst h1' h2'
            rw [Int.zero_add]
        have Hb := lin_range_sound E (erange kn)
          (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha)
          (zpow 2 j * c + c2 + c3) t3 lo' hi' hlr
        -- the scaled form is `2^j * (c + tden E ts)`
        have hT : zpow 2 j * tden E ts = c2 + c3 + tden E t3 := by
          rw [← Smap, S1, S2]
          omega
        have hd : zpow 2 j * (c + tden E ts) = zpow 2 j * c + c2 + c3 + tden E t3 := by
          rw [Int.mul_add, hT]
          omega
        have HL : lo' ≤ zpow 2 j * (c + tden E ts) ∧
            zpow 2 j * (c + tden E ts) ≤ hi' := by
          rw [hd]
          exact Hb
        -- divide the scaled interval back
        have Hfl : c + tden E ts ≤ hi' / zpow 2 j := by
          refine Int.le_ediv_of_mul_le hsc ?_
          rw [Int.mul_comm]
          exact HL.2
        have Hce : zcdiv lo' (zpow 2 j) ≤ c + tden E ts := by
          have hle : (-(c + tden E ts)) ≤ (-lo') / zpow 2 j := by
            refine Int.le_ediv_of_mul_le hsc ?_
            have hneg : -(zpow 2 j * (c + tden E ts)) = (-(c + tden E ts)) * zpow 2 j := by
              rw [Int.neg_mul, Int.mul_comm]
            rw [← hneg]
            omega
          unfold zcdiv
          omega
        -- the value's interval
        have Hu : 0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) < 2 ^ 64 :=
          u64_range (edenot E e)
        have HL0 : 0 ≤ c + tden E ts := by omega
        have HL64 : c + tden E ts < 2 ^ 64 := by omega
        have hT1a : -(2 ^ 64) < c + tden E ts - bv_unsigned (edenot E e) := by omega
        have hT2a : c + tden E ts - bv_unsigned (edenot E e) < 2 ^ 64 := by omega
        obtain ⟨qq, hq⟩ := lin_of_sound E e
        have hq2 : c + tden E ts = bv_unsigned (edenot E e) + qq * 2 ^ 64 := by
          have h := hq
          rw [hlin] at h
          simpa [lden, uE] using h
        have htq : qq * 2 ^ 64 = c + tden E ts - bv_unsigned (edenot E e) := by
          rw [hq2, Int.add_comm (bv_unsigned (edenot E e)), Int.add_sub_cancel]
        have hq0 : qq = 0 := mul_two64_eq_zero (by rw [htq]; exact hT1a)
          (by rw [htq]; exact hT2a)
        rw [hq0, Int.zero_mul, Int.add_zero] at hq2
        exact hq2.symm
      · rw [ite_eq_right hfin] at H
        simp at H
  · rw [ite_eq_right hJ] at H
    simp at H
/-- Local: the `erange` → `lin_brange` → `lin_srange` fallback chain of
    `xlo` . -/
theorem xlo_fallback (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo : Int) (Hkn : know_ok segs E M kn)
    (H : (match erange kn e with
          | some (l, _) => some l
          | none =>
            match lin_brange kn e with
            | some (l, _) => some l
            | none =>
              match lin_srange kn e with
              | some (l, _) => some l
              | none => none) = some lo) :
    lo ≤ bv_unsigned (edenot E e) := by
  generalize her : erange kn e = r1 at H
  cases r1 with
  | none =>
    try simp only [] at H
    generalize hbr : lin_brange kn e = r2 at H
    cases r2 with
    | none =>
      try simp only [] at H
      generalize hsr : lin_srange kn e = r3 at H
      cases r3 with
      | none => simp at H
      | some p =>
        obtain ⟨l, h⟩ := p
        try simp only [] at H
        have h1 : l = lo := Option.some.inj H
        rw [← h1]
        exact (lin_srange_sound segs E M kn e l h Hkn hsr).1
    | some p =>
      obtain ⟨l, h⟩ := p
      try simp only [] at H
      have h1 : l = lo := Option.some.inj H
      rw [← h1]
      exact (lin_brange_sound segs E M kn e l h Hkn hbr).1
  | some p =>
    obtain ⟨l, h⟩ := p
    try simp only [] at H
    have h1 : l = lo := Option.some.inj H
    rw [← h1]
    exact (erange_sound segs E M kn e l h Hkn her).1

theorem xlo_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (lo : Int) (Hkn : know_ok segs E M kn)
    (H : xlo kn e = some lo) : lo ≤ bv_unsigned (edenot E e) := by
  cases e with
  | ELit z =>
    unfold xlo at H
    simp only [] at H
    have h1 : zlit64 z = lo := Option.some.inj H
    rw [← h1]
    have h2 : bv_unsigned (edenot E (.ELit z)) = zlit64 z := by
      show bv_unsigned (Z_to_bv 64 z) = zlit64 z
      rw [u_lit64a, zlit64_eq, two64_eq]
    rw [h2]
    exact Int.le_refl _
  | EVar n => exact xlo_fallback segs E M kn _ lo Hkn H
  | EAlu op a b => exact xlo_fallback segs E M kn _ lo Hkn H
  | EAluw op a b => exact xlo_fallback segs E M kn _ lo Hkn H
  | EMd op a b => exact xlo_fallback segs E M kn _ lo Hkn H
  | EMdw op a b => exact xlo_fallback segs E M kn _ lo Hkn H
  | EExt sx lo2 n a => exact xlo_fallback segs E M kn _ lo Hkn H
  | EBlob sx k i n => exact xlo_fallback segs E M kn _ lo Hkn H


/-- Local: the `xhi` fallback chain (dual of `xlo_fallback`). -/
theorem xhi_fallback (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (hi : Int) (Hkn : know_ok segs E M kn)
    (H : (match erange kn e with
          | some (_, h) => some h
          | none =>
            match lin_brange kn e with
            | some (_, h) => some h
            | none =>
              match lin_srange kn e with
              | some (_, h) => some h
              | none => none) = some hi) :
    bv_unsigned (edenot E e) ≤ hi := by
  generalize her : erange kn e = r1 at H
  cases r1 with
  | none =>
    try simp only [] at H
    generalize hbr : lin_brange kn e = r2 at H
    cases r2 with
    | none =>
      try simp only [] at H
      generalize hsr : lin_srange kn e = r3 at H
      cases r3 with
      | none => simp at H
      | some p =>
        obtain ⟨l, h⟩ := p
        try simp only [] at H
        have h1 : h = hi := Option.some.inj H
        rw [← h1]
        exact (lin_srange_sound segs E M kn e l h Hkn hsr).2
    | some p =>
      obtain ⟨l, h⟩ := p
      try simp only [] at H
      have h1 : h = hi := Option.some.inj H
      rw [← h1]
      exact (lin_brange_sound segs E M kn e l h Hkn hbr).2
  | some p =>
    obtain ⟨l, h⟩ := p
    try simp only [] at H
    have h1 : h = hi := Option.some.inj H
    rw [← h1]
    exact (erange_sound segs E M kn e l h Hkn her).2

theorem xhi_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (hi : Int) (Hkn : know_ok segs E M kn)
    (H : xhi kn e = some hi) : bv_unsigned (edenot E e) ≤ hi := by
  cases e with
  | ELit z =>
    unfold xhi at H
    simp only [] at H
    have h1 : zlit64 z = hi := Option.some.inj H
    rw [← h1]
    have h2 : bv_unsigned (edenot E (.ELit z)) = zlit64 z := by
      show bv_unsigned (Z_to_bv 64 z) = zlit64 z
      rw [u_lit64a, zlit64_eq, two64_eq]
    rw [h2]
    exact Int.le_refl _
  | EVar n => exact xhi_fallback segs E M kn _ hi Hkn H
  | EAlu op a b => exact xhi_fallback segs E M kn _ hi Hkn H
  | EAluw op a b => exact xhi_fallback segs E M kn _ hi Hkn H
  | EMd op a b => exact xhi_fallback segs E M kn _ hi Hkn H
  | EMdw op a b => exact xhi_fallback segs E M kn _ hi Hkn H
  | EExt sx lo2 n a => exact xhi_fallback segs E M kn _ hi Hkn H
  | EBlob sx k i n => exact xhi_fallback segs E M kn _ hi Hkn H

theorem lin_nowrapR_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E M kn)
    (H : lin_nowrapR kn e = true) :
    bv_unsigned (edenot E e) = (lin_of e).1 + tden E (lin_of e).2 := by
  unfold lin_nowrapR at H
  try simp only [] at H
  generalize hx : srl_expand kn (lin_of e).2 = p at H
  obtain ⟨c2, t2⟩ := p
  try simp only [] at H
  by_cases ht : lin_test kn ((lin_of e).1 + c2) t2 (fun lo hi => (0 ≤ lo && hi < two64)) = true
  · rw [ite_eq_left ht] at H
    obtain ⟨lo, hi, Ht, Hb1, Hb2⟩ := lin_test_sound segs E M kn ((lin_of e).1 + c2) t2
      (fun lo hi => (0 ≤ lo && hi < two64)) Hkn ht
    obtain ⟨H1, H2⟩ := (Bool.and_eq_true ..).mp Ht
    have h1 : 0 ≤ lo := of_decide_eq_true H1
    have h2 : hi < 2 ^ 64 := by have hh := of_decide_eq_true H2; simpa [two64] using hh
    have S1 : tden E (lin_of e).2 = c2 + tden E t2 := srl_expand_sound segs E M kn _ c2 t2 Hkn hx
    have hL : (lin_of e).1 + tden E (lin_of e).2 = (lin_of e).1 + c2 + tden E t2 := by
      rw [S1]; omega
    have Hu : 0 ≤ bv_unsigned (edenot E e) ∧ bv_unsigned (edenot E e) < 2 ^ 64 :=
      u64_range (edenot E e)
    have HL1 : -(2 ^ 64) < (lin_of e).1 + c2 + tden E t2 - bv_unsigned (edenot E e) := by omega
    have HL2 : (lin_of e).1 + c2 + tden E t2 - bv_unsigned (edenot E e) < 2 ^ 64 := by omega
    obtain ⟨qq, hq⟩ := lin_of_sound E e
    have hq' : (lin_of e).1 + tden E (lin_of e).2 =
        bv_unsigned (edenot E e) + qq * 2 ^ 64 := hq
    have htq : qq * 2 ^ 64 =
        (lin_of e).1 + c2 + tden E t2 - bv_unsigned (edenot E e) := by
      rw [← hL, hq', Int.add_comm (bv_unsigned (edenot E e)), Int.add_sub_cancel]
    have hq0 : qq = 0 := mul_two64_eq_zero (by rw [htq]; exact HL1) (by rw [htq]; exact HL2)
    rw [hq0, Int.zero_mul, Int.add_zero] at hq'
    exact hq'.symm
  · rw [ite_eq_right ht] at H
    generalize hs : lin_srange kn e = q at H
    cases q with
    | none => simp at H
    | some p2 =>
      obtain ⟨slo, shi⟩ := p2
      try simp only [] at H
      exact lin_srange_exact segs E M kn e slo shi Hkn hs

theorem lin_apart_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int)
    (Hkn : know_ok segs E M kn) (H : lin_apart kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b1 k1) + n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + n2 ≤ estart E (SA b1 k1) := by
  unfold lin_apart at H
  by_cases hsv : shares_var b1 b2 = true
  · rw [ite_eq_left hsv] at H
    unfold lin_apart0 at H
    try simp only [] at H
    obtain ⟨Hw, Hm⟩ := (Bool.and_eq_true ..).mp H
    obtain ⟨Hw1, Hw2⟩ := (Bool.and_eq_true ..).mp Hw
    have E1 := lin_nowrapR_sound segs E M kn b1 Hkn Hw1
    have E2 := lin_nowrapR_sound segs E M kn b2 Hkn Hw2
    obtain ⟨lo, hi, Ht, Hb1, Hb2⟩ := lin_test_sound segs E M kn
      ((lin_of b2).1 + k2 - (lin_of b1).1 - k1) (lsub_e (lin_of b2).2 (lin_of b1).2)
      (fun lo hi => (n1 ≤ lo || hi ≤ -n2)) Hkn Hm
    rw [lsub_e_sound] at Hb1 Hb2
    have ht := Ht
    rw [Bool.or_eq_true] at ht
    show bv_unsigned (edenot E b1) + k1 + n1 ≤ bv_unsigned (edenot E b2) + k2 ∨
      bv_unsigned (edenot E b2) + k2 + n2 ≤ bv_unsigned (edenot E b1) + k1
    rcases ht with h | h
    · have hj : n1 ≤ lo := of_decide_eq_true h
      left; omega
    · have hj : n2 ≤ -hi := by
        have hh := of_decide_eq_true h
        omega
      right; omega
  · rw [ite_eq_right hsv] at H
    simp at H


/-! ### Symbolic-length comparisons -/

/-- `xt_lin_sound`: the flattened linear form of a sum of
    offset terms denotes exactly the sum (`+ k` offsets included). -/
theorem xt_lin_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (ts : xterms) (Hkn : know_ok segs E M kn)
    (H : xt_nowrap kn ts = true) : xt_const ts + tden E (xt_lin ts) = xt_den E ts := by
  induction ts with
  | nil => simp [xt_nowrap, xt_const, xt_lin, xt_den, tden]
  | cons p r ih =>
    obtain ⟨e, k⟩ := p
    simp only [xt_nowrap, xt_const, xt_lin, xt_den] at H ⊢
    obtain ⟨H1, H2⟩ := (Bool.and_eq_true ..).mp H
    have He := lin_nowrapR_sound segs E M kn e Hkn H1
    have IH := ih H2
    have FR : ∀ (l : List (Int × expr)) (acc : List (Int × expr)),
        tden E (List.foldr (fun t acc => lins_e t.1 t.2 acc) acc l) =
          tden E l + tden E acc := by
      intro l
      induction l with
      | nil => intro acc; simp [tden]
      | cons t rest ih2 =>
        intro acc
        obtain ⟨k', a'⟩ := t
        simp only [List.foldr_cons, tden]
        rw [lins_e_sound, ih2]
        omega
    rw [FR]
    omega

/-- `lin_ge0_scaled_sound`: the SCALED expansion interval proves
    `c + Σ ts >= 0` — divide the scaled witness `2^j * (c + tden E ts) >= 0`
    back by the positive factor `2^j`. -/
theorem lin_ge0_scaled_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : Int) (ts : List (Int × expr)) (Hkn : know_ok segs E M kn)
    (H : lin_ge0_scaled kn c ts = true) : 0 ≤ c + tden E ts := by
  unfold lin_ge0_scaled at H
  generalize hj : srl_scale_need ts = j at H
  try simp only [] at H
  by_cases hJ : (decide (0 < j) && decide (j ≤ 24)) = true
  · rw [ite_eq_left hJ] at H
    try simp only [] at H
    obtain ⟨hJ1, hJ2⟩ := (Bool.and_eq_true ..).mp hJ
    have hj0 : 0 < j := of_decide_eq_true hJ1
    have hsc : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
    generalize hx2 : srl_expand kn (ts.map (fun t => (zpow 2 j * t.1, t.2))) = p2 at H
    obtain ⟨c2, t2⟩ := p2
    try simp only [] at H
    generalize hx3 : (if has_srl t2 then srl_expand kn t2 else ((0 : Int), t2)) = p3 at H
    obtain ⟨c3, t3⟩ := p3
    try simp only [] at H
    obtain ⟨lo, hi, Hr, Hb1, Hb2⟩ := lin_test_sound segs E M kn
      (zpow 2 j * c + c2 + c3) t3 (fun lo _ => 0 ≤ lo) Hkn H
    have h0 : 0 ≤ lo := of_decide_eq_true Hr
    have S1 : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) = c2 + tden E t2 :=
      srl_expand_sound segs E M kn _ c2 t2 Hkn hx2
    have Smap : tden E (ts.map (fun t => (zpow 2 j * t.1, t.2))) = zpow 2 j * tden E ts :=
      tden_map_scale E (zpow 2 j) ts
    have S2 : tden E t2 = c3 + tden E t3 := by
      by_cases hsr : has_srl t2 = true
      · rw [ite_eq_left hsr] at hx3
        exact srl_expand_sound segs E M kn t2 c3 t3 Hkn hx3
      · rw [ite_eq_right hsr] at hx3
        simp only [Prod.mk.injEq] at hx3
        obtain ⟨h1', h2'⟩ := hx3
        subst h1' h2'
        rw [Int.zero_add]
    have hT : zpow 2 j * tden E ts = c2 + c3 + tden E t3 := by
      rw [← Smap, S1, S2]
      omega
    have hd : zpow 2 j * (c + tden E ts) = zpow 2 j * c + c2 + c3 + tden E t3 := by
      rw [Int.mul_add, hT]
      omega
    have hge : 0 ≤ (c + tden E ts) * zpow 2 j := by
      rw [Int.mul_comm, hd]
      omega
    exact Int.nonneg_of_mul_nonneg_left hge hsc
  · rw [ite_eq_right hJ] at H
    simp at H


/-- `lin_ge0_sound`: `Σ pos >= Σ neg` when the plain, the
    srl-expanded, the twice-expanded or the scaled-interval test accepts the
    difference of the two flattened forms. -/
theorem lin_ge0_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (pos neg : xterms) (Hkn : know_ok segs E M kn)
    (H : lin_ge0 kn pos neg = true) : xt_den E neg ≤ xt_den E pos := by
  unfold lin_ge0 at H
  try simp only [] at H
  obtain ⟨Hpn, HB⟩ := (Bool.and_eq_true ..).mp H
  obtain ⟨Hp, Hn⟩ := (Bool.and_eq_true ..).mp Hpn
  have XP := xt_lin_sound segs E M kn pos Hkn Hp
  have XN := xt_lin_sound segs E M kn neg Hkn Hn
  have goal_of : ∀ (c0 : Int) (t : List (Int × expr)),
      0 ≤ c0 + tden E t →
      c0 = xt_const pos - xt_const neg →
      tden E t = tden E (xt_lin pos) - tden E (xt_lin neg) →
      xt_den E neg ≤ xt_den E pos := by
    intro c0 t hge hc ht
    omega
  have ls : tden E (lsub_e (xt_lin pos) (xt_lin neg)) =
      tden E (xt_lin pos) - tden E (xt_lin neg) := lsub_e_sound E _ _
  have scaled_case : lin_ge0_scaled kn (xt_const pos - xt_const neg)
      (lsub_e (xt_lin pos) (xt_lin neg)) = true → xt_den E neg ≤ xt_den E pos := by
    intro HS
    have SC := lin_ge0_scaled_sound segs E M kn (xt_const pos - xt_const neg)
      (lsub_e (xt_lin pos) (xt_lin neg)) Hkn HS
    exact goal_of (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) SC rfl ls
  by_cases h1 : lin_test kn (xt_const pos - xt_const neg)
      (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => 0 ≤ lo) = true
  · rw [ite_eq_left h1] at HB
    obtain ⟨lo, hi, Hr, Hb1, Hb2⟩ := lin_test_sound segs E M kn
      (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))
      (fun lo _ => 0 ≤ lo) Hkn h1
    have h0 : 0 ≤ lo := of_decide_eq_true Hr
    exact goal_of (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) (by omega) rfl ls
  · rw [ite_eq_right h1] at HB
    try simp only [] at HB
    generalize hx : srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) = p at HB
    obtain ⟨c2, t2⟩ := p
    try simp only [] at HB
    have S1 : tden E (lsub_e (xt_lin pos) (xt_lin neg)) = c2 + tden E t2 :=
      srl_expand_sound segs E M kn _ c2 t2 Hkn hx
    by_cases h2 : lin_test kn (xt_const pos - xt_const neg + c2) t2
        (fun lo _ => 0 ≤ lo) = true
    · rw [ite_eq_left h2] at HB
      obtain ⟨lo, hi, Hr, Hb1, Hb2⟩ := lin_test_sound segs E M kn
        (xt_const pos - xt_const neg + c2) t2 (fun lo _ => 0 ≤ lo) Hkn h2
      have h0 : 0 ≤ lo := of_decide_eq_true Hr
      refine goal_of (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) ?_ rfl ?_
      · rw [S1]; omega
      · rw [S1]; omega
    · rw [ite_eq_right h2] at HB
      by_cases h3 : has_srl t2 = true
      · rw [ite_eq_left h3] at HB
        try simp only [] at HB
        generalize hx3 : srl_expand kn t2 = p3 at HB
        obtain ⟨c3, t3⟩ := p3
        try simp only [] at HB
        have S2 : tden E t2 = c3 + tden E t3 :=
          srl_expand_sound segs E M kn _ c3 t3 Hkn hx3
        by_cases hX : lin_test kn (xt_const pos - xt_const neg + c2 + c3) t3
            (fun lo _ => 0 ≤ lo) = true
        · rw [ite_eq_left hX] at HB
          obtain ⟨lo, hi, Hr, Hb1, Hb2⟩ := lin_test_sound segs E M kn
            (xt_const pos - xt_const neg + c2 + c3) t3 (fun lo _ => 0 ≤ lo) Hkn hX
          have h0 : 0 ≤ lo := of_decide_eq_true Hr
          refine goal_of (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)) ?_ rfl ?_
          · rw [S1, S2]; omega
          · rw [S1, S2]; omega
        · rw [ite_eq_right hX] at HB
          exact scaled_case HB
      · rw [ite_eq_right h3] at HB
        try simp only [] at HB
        exact scaled_case HB

/-- `xinside_sound`: symbolic containment — the algebraic test
    (`lin_ge0` on both ends) or, for a literal-based container, the numeric
    bounds. -/
theorem xinside_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr) (k2 : Int)
    (n2 : expr) (Hkn : know_ok segs E M kn) (H : xinside kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b2 k2) ≤ estart E (SA b1 k1) ∧
      estart E (SA b1 k1) + elenZ E n1 ≤ estart E (SA b2 k2) + elenZ E n2 := by
  unfold xinside at H
  by_cases hsv : shares_var b1 b2 = true
  · rw [ite_eq_left hsv] at H
    unfold xinside0 at H
    try simp only [] at H
    by_cases hA : lin_ge0 kn [(b1, k1)] [(b2, k2)] = true
    · rw [ite_eq_left hA] at H
      have A := lin_ge0_sound segs E M kn [(b1, k1)] [(b2, k2)] Hkn hA
      have B := lin_ge0_sound segs E M kn [(b2, k2), (n2, 0)] [(b1, k1), (n1, 0)] Hkn H
      simp only [xt_den] at A B
      show bv_unsigned (edenot E b2) + k2 ≤ bv_unsigned (edenot E b1) + k1 ∧
        bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1) ≤
          bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2)
      omega
    · rw [ite_eq_right hA] at H
      simp at H
  · rw [ite_eq_right hsv] at H
    by_cases hnv : novars b2 = true
    · rw [ite_eq_left hnv] at H
      unfold xinside_num at H
      try simp only [] at H
      generalize hl2 : xlo kn b2 = r1 at H
      cases r1 with
      | none => simp at H
      | some lo2 =>
        try simp only [] at H
        generalize hh2 : xhi kn b2 = r2 at H
        cases r2 with
        | none => simp at H
        | some hi2 =>
          try simp only [] at H
          by_cases heq : (lo2 == hi2) = true
          · rw [ite_eq_left heq] at H
            try simp only [] at H
            generalize hbr : base_range kn b1 = r3 at H
            cases r3 with
            | none => simp at H
            | some p =>
              obtain ⟨lo1, hi1⟩ := p
              try simp only [] at H
              generalize hh1 : xhi kn n1 = r4 at H
              cases r4 with
              | none => simp at H
              | some h1 =>
                try simp only [] at H
                generalize hl2n : xlo kn n2 = r5 at H
                cases r5 with
                | none => simp at H
                | some l2 =>
                  try simp only [] at H
                  obtain ⟨HA, HBc⟩ := (Bool.and_eq_true ..).mp H
                  have hA : lo2 + k2 ≤ lo1 + k1 := of_decide_eq_true HA
                  have hB : hi1 + k1 + h1 ≤ lo2 + k2 + l2 := of_decide_eq_true HBc
                  have he : lo2 = hi2 := beq_iff_eq.mp heq
                  have X1 := xlo_sound segs E M kn b2 lo2 Hkn hl2
                  have X2 := xhi_sound segs E M kn b2 hi2 Hkn hh2
                  obtain ⟨BR1, BR2⟩ := base_range_sound segs E M kn b1 lo1 hi1 Hkn hbr
                  have X3 := xhi_sound segs E M kn n1 h1 Hkn hh1
                  have X4 := xlo_sound segs E M kn n2 l2 Hkn hl2n
                  show bv_unsigned (edenot E b2) + k2 ≤ bv_unsigned (edenot E b1) + k1 ∧
                    bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1) ≤
                      bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2)
                  omega
          · rw [ite_eq_right heq] at H
            simp at H
    · rw [ite_eq_right hnv] at H
      simp at H

theorem sub_itv_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) (b : expr) (k n : Int) (c : saddr) (m : expr)
    (Hkn : know_ok segs E M allkn) (H : sub_itv allkn b k n c m = true) :
    estart E c ≤ estart E (SA b k) ∧ estart E (SA b k) + n ≤ estart E c + elenZ E m := by
  obtain ⟨cb, ck⟩ := c
  have fallback : ∀ (_ : (decide (0 ≤ n) && decide (n < two64)) = true),
      xinside allkn b k (.ELit n) cb ck m = true →
      estart E (SA cb ck) ≤ estart E (SA b k) ∧
        estart E (SA b k) + n ≤ estart E (SA cb ck) + elenZ E m := by
    intro h3 HX
    obtain ⟨sn1, sn2⟩ := (Bool.and_eq_true ..).mp h3
    have hn0 : 0 ≤ n := of_decide_eq_true sn1
    have hn64 : n < 2 ^ 64 := by have hh := of_decide_eq_true sn2; simpa [two64] using hh
    obtain ⟨X1, X2⟩ := xinside_sound segs E M allkn b k (.ELit n) cb ck m Hkn HX
    have hlen : elenZ E (.ELit n) = n := by
      show bv_unsigned (Z_to_bv 64 n) = n
      rw [u_lit64]
      exact u_small_id n ⟨hn0, hn64⟩
    rw [hlen] at X2
    exact ⟨X1, X2⟩
  unfold sub_itv at H
  try simp only [] at H
  split at H
  · split at H
    · rename_i hc x0 s0 heq
      obtain ⟨hbe, hck⟩ := (Bool.and_eq_true ..).mp hc
      have hcb : cb = b := (expr_eqb_eq b cb hbe).symm
      have hckle : ck ≤ k := of_decide_eq_true hck
      split at H
      · rename_i hkn0
        have hkn : k + n ≤ ck + s0 := of_decide_eq_true hkn0
        have X := xlo_sound segs E M allkn m s0 Hkn heq
        show bv_unsigned (edenot E cb) + ck ≤ bv_unsigned (edenot E b) + k ∧
          bv_unsigned (edenot E b) + k + n ≤
            bv_unsigned (edenot E cb) + ck + bv_unsigned (edenot E m)
        subst hcb
        omega
      · try simp only [] at H
        by_cases h3 : (decide (0 ≤ n) && decide (n < two64)) = true
        · rw [ite_eq_left h3] at H
          exact fallback h3 H
        · rw [ite_eq_right h3] at H
          simp at H
    · rename_i hc x0 heq
      try simp only [] at H
      by_cases h3 : (decide (0 ≤ n) && decide (n < two64)) = true
      · rw [ite_eq_left h3] at H
        exact fallback h3 H
      · rw [ite_eq_right h3] at H
        simp at H
  · rename_i hc
    try simp only [] at H
    by_cases h3 : (decide (0 ≤ n) && decide (n < two64)) = true
    · rw [ite_eq_left h3] at H
      exact fallback h3 H
    · rw [ite_eq_right h3] at H
      simp at H

theorem if3_cases (a b c d e : Bool)
    (H : (if (if a then b else false) then true
          else if (if c then d else false) then true else e) = true) :
    (a = true ∧ b = true) ∨ (c = true ∧ d = true) ∨ e = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

/-- `kdisj_apart_sound_gen`: a recorded `KDisj` fact separates
    the two ranges (`allkn` is the list the `sub_itv` tests are evaluated
    against, `kn` the one being scanned). -/
theorem kdisj_apart_sound_gen (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int)
    (Hall : know_ok segs E M allkn) :
    know_ok segs E M kn → kdisj_apart allkn kn b1 k1 n1 b2 k2 n2 = true →
    estart E (SA b1 k1) + n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + n2 ≤ estart E (SA b1 k1) := by
  induction kn with
  | nil => intro _ H; unfold kdisj_apart at H; simp at H
  | cons K rest IH =>
    intro Hkn H
    have HK : kentry_ok segs E M K := Hkn K List.mem_cons_self
    have Hrest : know_ok segs E M rest := fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    cases K with
    | KDisj c1 m1 c2 m2 =>
      simp only [kdisj_apart] at H
      rcases if3_cases (sub_itv allkn b1 k1 n1 c1 m1) (sub_itv allkn b2 k2 n2 c2 m2)
          (sub_itv allkn b1 k1 n1 c2 m2) (sub_itv allkn b2 k2 n2 c1 m1)
          (kdisj_apart allkn rest b1 k1 n1 b2 k2 n2) H with ⟨Ha, Hb⟩ | ⟨Ha, Hb⟩ | H2
      · obtain ⟨A1, A2⟩ := sub_itv_sound segs E M allkn b1 k1 n1 c1 m1 Hall Ha
        obtain ⟨B1, B2⟩ := sub_itv_sound segs E M allkn b2 k2 n2 c2 m2 Hall Hb
        rcases HK with h | h
        · omega
        · omega
      · obtain ⟨A1, A2⟩ := sub_itv_sound segs E M allkn b1 k1 n1 c2 m2 Hall Ha
        obtain ⟨B1, B2⟩ := sub_itv_sound segs E M allkn b2 k2 n2 c1 m1 Hall Hb
        rcases HK with h | h
        · omega
        · omega
      · exact IH Hrest H2
    | KWord a w v => simp only [kdisj_apart] at H; exact IH Hrest H
    | KZero a n => simp only [kdisj_apart] at H; exact IH Hrest H
    | KBlob a n k => simp only [kdisj_apart] at H; exact IH Hrest H
    | KImg lo hi => simp only [kdisj_apart] at H; exact IH Hrest H
    | KAlign e m => simp only [kdisj_apart] at H; exact IH Hrest H
    | KRange e lo hi => simp only [kdisj_apart] at H; exact IH Hrest H
    | KWr a n => simp only [kdisj_apart] at H; exact IH Hrest H
    | KFill a n c => simp only [kdisj_apart] at H; exact IH Hrest H
    | KUnk a n => simp only [kdisj_apart] at H; exact IH Hrest H


/-- `kdisj_apart_sound`: the same list for the facts and for the
    scan. -/
theorem kdisj_apart_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int)
    (Hkn : know_ok segs E M kn) (H : kdisj_apart kn kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b1 k1) + n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + n2 ≤ estart E (SA b1 k1) :=
  kdisj_apart_sound_gen segs E M kn kn b1 k1 n1 b2 k2 n2 Hkn Hkn H


/-- Local: `if A then true else if B then true else C` is the `Bool`
    sum of the three attempts . -/
theorem if3b (A B C : Bool) (H : (if A then true else if B then true else C) = true) :
    A = true ∨ B = true ∨ C = true := by
  cases A <;> cases B <;> cases C <;> simp_all


/-- `ranges_apart_sound`: numeric apartness first (both bases
    bracketed), then a `KDisj` fact, then the linear comparison. -/
theorem ranges_apart_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int)
    (Hkn : know_ok segs E M kn) (H : ranges_apart kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b1 k1) + n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + n2 ≤ estart E (SA b1 k1) := by
  unfold ranges_apart at H
  rcases if3b _ _ _ H with hA | hB | hC
  · generalize h1 : base_range kn b1 = r1 at hA
    cases r1 with
    | none => simp at hA
    | some p1 =>
      obtain ⟨lo1, hi1⟩ := p1
      generalize h2 : base_range kn b2 = r2 at hA
      cases r2 with
      | none => simp at hA
      | some p2 =>
        obtain ⟨lo2, hi2⟩ := p2
        try simp only [] at hA
        obtain ⟨A1, A2⟩ := base_range_sound segs E M kn b1 lo1 hi1 Hkn h1
        obtain ⟨B1, B2⟩ := base_range_sound segs E M kn b2 lo2 hi2 Hkn h2
        show bv_unsigned (edenot E b1) + k1 + n1 ≤ bv_unsigned (edenot E b2) + k2 ∨
          bv_unsigned (edenot E b2) + k2 + n2 ≤ bv_unsigned (edenot E b1) + k1
        rcases (Bool.or_eq_true ..).mp hA with h | h
        · have hh : hi1 + k1 + n1 ≤ lo2 + k2 := of_decide_eq_true h
          omega
        · have hh : hi2 + k2 + n2 ≤ lo1 + k1 := of_decide_eq_true h
          omega
  · exact kdisj_apart_sound segs E M kn b1 k1 n1 b2 k2 n2 Hkn hB
  · exact lin_apart_sound segs E M kn b1 k1 n1 b2 k2 n2 Hkn hC


/-- `sub_itv_x_sound`: symbolic-length containment in a `KDisj`
    side. -/
theorem sub_itv_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b : expr) (k : Int) (n : expr) (c : saddr) (m : expr)
    (Hkn : know_ok segs E M kn) (H : sub_itv_x kn b k n c m = true) :
    estart E c ≤ estart E (SA b k) ∧ estart E (SA b k) + elenZ E n ≤ estart E c + elenZ E m := by
  obtain ⟨cb, ck⟩ := c
  unfold sub_itv_x at H
  exact xinside_sound segs E M kn b k n cb ck m Hkn H


/-- `kdisj_apart_x_sound`: `kdisj_apart` with symbolic
    lengths. -/
theorem kdisj_apart_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr) (k2 : Int)
    (n2 : expr) (Hall : know_ok segs E M allkn) :
    know_ok segs E M kn → kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2 = true →
    estart E (SA b1 k1) + elenZ E n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + elenZ E n2 ≤ estart E (SA b1 k1) := by
  induction kn with
  | nil => intro _ H; unfold kdisj_apart_x at H; simp at H
  | cons K rest IH =>
    intro Hkn H
    have HK : kentry_ok segs E M K := Hkn K List.mem_cons_self
    have Hrest : know_ok segs E M rest := fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    cases K with
    | KDisj c1 m1 c2 m2 =>
      simp only [kdisj_apart_x] at H
      rcases if3_cases (sub_itv_x allkn b1 k1 n1 c1 m1) (sub_itv_x allkn b2 k2 n2 c2 m2)
          (sub_itv_x allkn b1 k1 n1 c2 m2) (sub_itv_x allkn b2 k2 n2 c1 m1)
          (kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2) H with ⟨Ha, Hb⟩ | ⟨Ha, Hb⟩ | H2
      · obtain ⟨A1, A2⟩ := sub_itv_x_sound segs E M allkn b1 k1 n1 c1 m1 Hall Ha
        obtain ⟨B1, B2⟩ := sub_itv_x_sound segs E M allkn b2 k2 n2 c2 m2 Hall Hb
        rcases HK with h | h
        · omega
        · omega
      · obtain ⟨A1, A2⟩ := sub_itv_x_sound segs E M allkn b1 k1 n1 c2 m2 Hall Ha
        obtain ⟨B1, B2⟩ := sub_itv_x_sound segs E M allkn b2 k2 n2 c1 m1 Hall Hb
        rcases HK with h | h
        · omega
        · omega
      · exact IH Hrest H2
    | KWord a w v => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KZero a n => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KBlob a n k => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KImg lo hi => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KAlign e m => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KRange e lo hi => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KWr a n => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KFill a n c => simp only [kdisj_apart_x] at H; exact IH Hrest H
    | KUnk a n => simp only [kdisj_apart_x] at H; exact IH Hrest H


/-! ## Part P4c: the knowledge walk, accumulator discipline

     2689–2736.  The three `_acc` lemmas say the side conditions a
    lookup hands back are the caller's `acc` with something PREPENDED — the
    walk only ever conses (`SCInside`), never replaces or drops.  The
    drivers use this to recover the obligations they handed in.

    ABBREVIATION. with LHit _ scs _ | LMiss scs _ => exists pre, scs = pre ++
    acc | LStuck => True`. -/

/-- The accumulator discipline of a lookup result: the returned side
    conditions are `acc` with a prefix prepended. -/
def acc_ok (acc : List sidecond) : lres → Prop
  | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
  | .LMiss scs _ => ∃ pre, scs = pre ++ acc
  | .LStuck => True

theorem know_lookupA0_acc (allkn : List kentry) (segs : List Segment) (kn : List kentry)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) :
    (match know_lookupA0 allkn segs kn rb rk n sx hints acc with
     | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
     | .LMiss scs _ => ∃ pre, scs = pre ++ acc
     | .LStuck => True) := by
  show acc_ok acc (know_lookupA0 allkn segs kn rb rk n sx hints acc)
  induction kn generalizing rb rk n sx hints acc with
  | nil => simp only [know_lookupA0]; exact ⟨[], rfl⟩
  | cons K rest IH =>
    cases K with
    | KWord a w v =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      generalize h : rel_lit rb rk (n : Int) kb kk (w : Int) = r
      cases r with
      | RInside d => exact ⟨[], rfl⟩
      | RDisjoint => exact IH rb rk n sx hints acc
      | RPartial => exact IH rb rk n sx hints acc
      | RUnknown => exact IH rb rk n sx hints acc
    | KZero a len =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      have hsym : ∀ m : expr, acc_ok acc
          (if xinside allkn rb rk (elen n) kb kk m then .LHit (.ELit 0) acc hints
           else match hints with
             | true :: hs => .LHit (.ELit 0) (.SCInside (SA rb rk) (elen n) (SA kb kk) m :: acc) hs
             | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
             | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
        intro m
        generalize h2 : xinside allkn rb rk (elen n) kb kk m = b
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          cases hints with
          | nil => exact IH rb rk n sx [] acc
          | cons hd hs =>
            cases hd
            · exact IH rb rk n sx hs acc
            · exact ⟨[.SCInside (SA rb rk) (elen n) (SA kb kk) m], rfl⟩
        · simp only [ite_true]
          exact ⟨[], rfl⟩
      cases len with
      | ELit l0 =>
        simp only []
        generalize h : rel_lit rb rk (n : Int) kb kk (l0 % two64) = r
        cases r with
        | RInside d => exact ⟨[], rfl⟩
        | RDisjoint => exact IH rb rk n sx hints acc
        | RPartial => exact IH rb rk n sx hints acc
        | RUnknown => exact hsym (.ELit l0)
      | EVar nn => exact hsym _
      | EAlu op x y => exact hsym _
      | EAluw op x y => exact hsym _
      | EMd op x y => exact hsym _
      | EMdw op x y => exact hsym _
      | EExt s l w e => exact hsym _
      | EBlob s k i w => exact hsym _
    | KFill a len c =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      have hsym : ∀ m : expr, acc_ok acc
          (if xinside allkn rb rk (elen n) kb kk m then .LHit (fill_lit sx n c) acc hints
           else match hints with
             | true :: hs => .LHit (fill_lit sx n c) (.SCInside (SA rb rk) (elen n) (SA kb kk) m :: acc) hs
             | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
             | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
        intro m
        generalize h2 : xinside allkn rb rk (elen n) kb kk m = b
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          cases hints with
          | nil => exact IH rb rk n sx [] acc
          | cons hd hs =>
            cases hd
            · exact IH rb rk n sx hs acc
            · exact ⟨[.SCInside (SA rb rk) (elen n) (SA kb kk) m], rfl⟩
        · simp only [ite_true]
          exact ⟨[], rfl⟩
      cases len with
      | ELit l0 =>
        simp only []
        generalize h : rel_lit rb rk (n : Int) kb kk (l0 % two64) = r
        cases r with
        | RInside d => exact ⟨[], rfl⟩
        | RDisjoint => exact IH rb rk n sx hints acc
        | RPartial => exact IH rb rk n sx hints acc
        | RUnknown => exact hsym (.ELit l0)
      | EVar nn => exact hsym _
      | EAlu op x y => exact hsym _
      | EAluw op x y => exact hsym _
      | EMd op x y => exact hsym _
      | EMdw op x y => exact hsym _
      | EExt s l w e => exact hsym _
      | EBlob s k i w => exact hsym _
    | KBlob a len k =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      generalize h1 : expr_eqb rb kb = e1
      cases e1
      · simp only [Bool.false_eq_true, ite_false]
        exact IH rb rk n sx hints acc
      · simp only [ite_true]
        by_cases h2 : kk ≤ rk
        · rw [ite_eq_left h2]
          have hsym : ∀ m : expr, acc_ok acc
              (if (match erange allkn m with
                   | some (lo, snd) => decide (rk + (n : Int) ≤ kk + lo)
                   | none => false) = true then .LHit (.EBlob sx k (rk - kk) n) acc hints
               else match hints with
                 | true :: hs => .LHit (.EBlob sx k (rk - kk) n)
                                   (.SCInside (SA rb rk) (elen n) (SA kb kk) m :: acc) hs
                 | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                 | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
            intro m
            generalize h3 : erange allkn m = r
            cases r with
            | none =>
              simp only []
              simp only [Bool.false_eq_true, ite_false]
              cases hints with
              | nil => exact IH rb rk n sx [] acc
              | cons hd hs =>
                cases hd
                · exact IH rb rk n sx hs acc
                · exact ⟨[.SCInside (SA rb rk) (elen n) (SA kb kk) m], rfl⟩
            | some p =>
              obtain ⟨l1, h1'⟩ := p
              simp only []
              simp only [decide_eq_true_eq]
              by_cases h4 : rk + (n : Int) ≤ kk + l1
              · rw [ite_eq_left h4]; exact ⟨[], rfl⟩
              · rw [ite_eq_right h4]
                cases hints with
                | nil => exact IH rb rk n sx [] acc
                | cons hd hs =>
                  cases hd
                  · exact IH rb rk n sx hs acc
                  · exact ⟨[.SCInside (SA rb rk) (elen n) (SA kb kk) m], rfl⟩
          cases len with
          | ELit l0 =>
            simp only []
            by_cases h3 : rk + (n : Int) ≤ kk + (l0 % two64)
            · rw [ite_eq_left h3]; exact ⟨[], rfl⟩
            · rw [ite_eq_right h3]
              by_cases h4 : kk + (l0 % two64) ≤ rk
              · rw [ite_eq_left h4]; exact IH rb rk n sx hints acc
              · rw [ite_eq_right h4]; exact trivial
          | EVar nn => simp only []; exact hsym _
          | EAlu op x y => simp only []; exact hsym _
          | EAluw op x y => simp only []; exact hsym _
          | EMd op x y => simp only []; exact hsym _
          | EMdw op x y => simp only []; exact hsym _
          | EExt s l w e => simp only []; exact hsym _
          | EBlob s k2 i w => simp only []; exact hsym _
        · rw [ite_eq_right h2]
          exact IH rb rk n sx hints acc
    | KImg lo hi =>
      simp only [know_lookupA0]
      have hsym : ∀ m : expr, acc_ok acc
          (if (decide (lo ≤ rk) && decide (rk + (n : Int) ≤ hi)) = true then
            (match img_bytes segs rk n with
             | some bs => .LHit (lit_of_bytes sx n bs) acc hints
             | none => .LStuck)
           else know_lookupA0 allkn segs rest m rk n sx hints acc) := by
        intro m
        generalize hb : (decide (lo ≤ rk) && decide (rk + (n : Int) ≤ hi)) = b
        cases b
        · simp only [Bool.false_eq_true, ite_false]
          exact IH m rk n sx hints acc
        · simp only [ite_true]
          generalize hib : img_bytes segs rk n = ib
          cases ib with
          | none => exact trivial
          | some bs => exact ⟨[], rfl⟩
      split
      · exact hsym _
      · exact IH _ rk n sx hints acc
    | KAlign e m => simp only [know_lookupA0]; exact IH rb rk n sx hints acc
    | KRange e lo hi => simp only [know_lookupA0]; exact IH rb rk n sx hints acc
    | KWr a nn => simp only [know_lookupA0]; exact IH rb rk n sx hints acc
    | KDisj a1 n1 a2 n2 => simp only [know_lookupA0]; exact IH rb rk n sx hints acc
    | KUnk a nn => simp only [know_lookupA0]; exact IH rb rk n sx hints acc

/-- `know_lookupA_acc`: `know_lookupA` only prepends too (the
    bytewise composition hits with the accumulator the walk returned). -/
theorem know_lookupA_acc (allkn : List kentry) (segs : List Segment) (kn : List kentry)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) :
    (match know_lookupA allkn segs kn rb rk n sx hints acc with
     | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
     | .LMiss scs _ => ∃ pre, scs = pre ++ acc
     | .LStuck => True) := by
  show acc_ok acc (know_lookupA allkn segs kn rb rk n sx hints acc)
  unfold know_lookupA
  generalize h0 : know_lookupA0 allkn segs kn rb rk n sx hints acc = r0
  have H : acc_ok acc r0 := h0 ▸ know_lookupA0_acc allkn segs kn rb rk n sx hints acc
  cases r0 with
  | LHit v scs h => exact H
  | LMiss scs h =>
    cases know_bytes_lit segs kn rb rk n with
    | none => exact H
    | some bs => exact H
  | LStuck => exact H
theorem know_lookup_acc (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) :
    (match know_lookup segs kn rb rk n sx hints acc with
     | .LHit _ scs _ => ∃ pre, scs = pre ++ acc
     | .LMiss scs _ => ∃ pre, scs = pre ++ acc
     | .LStuck => True) := by
  show acc_ok acc (know_lookup segs kn rb rk n sx hints acc)
  unfold know_lookup
  exact know_lookupA_acc kn segs kn rb rk n sx hints acc


/-! ### Relation decided by `rel_lit` holds semantically -/
theorem rel_lit_inside (E : env) (rb : expr) (rk rn : Int) (kb : expr) (kk kn d : Int)
    (H : rel_lit rb rk rn kb kk kn = .RInside d) :
    rb = kb ∧ d = rk - kk ∧ kk ≤ rk ∧ rk + rn ≤ kk + kn ∧
      estart E (SA rb rk) = estart E (SA kb kk) + d := by
  unfold rel_lit at H
  by_cases he : (expr_eqb rb kb) = true
  · rw [ite_eq_left he] at H
    have hbk : rb = kb := expr_eqb_eq rb kb he
    subst hbk
    by_cases hin : (kk ≤ rk && rk + rn ≤ kk + kn) = true
    · rw [ite_eq_left hin] at H
      injection H with hd
      rcases (Bool.and_eq_true ..).mp hin with ⟨h1, h2⟩
      have h1' : kk ≤ rk := of_decide_eq_true h1
      have h2' : rk + rn ≤ kk + kn := of_decide_eq_true h2
      refine ⟨rfl, hd.symm, h1', h2', ?_⟩
      show bv_unsigned (edenot E rb) + rk = bv_unsigned (edenot E rb) + kk + d
      omega
    · rw [ite_eq_right hin] at H
      by_cases hdis : (rk + rn ≤ kk || kk + kn ≤ rk) = true
      · rw [ite_eq_left hdis] at H; simp at H
      · rw [ite_eq_right hdis] at H; simp at H
  · rw [ite_eq_right he] at H; simp at H
theorem rel_lit_disjoint (E : env) (rb : expr) (rk rn : Int) (kb : expr) (kk kn : Int)
    (H : rel_lit rb rk rn kb kk kn = .RDisjoint) :
    rb = kb ∧ (estart E (SA rb rk) + rn ≤ estart E (SA kb kk) ∨
      estart E (SA kb kk) + kn ≤ estart E (SA rb rk)) := by
  unfold rel_lit at H
  by_cases he : (expr_eqb rb kb) = true
  · rw [ite_eq_left he] at H
    have hbk : rb = kb := expr_eqb_eq rb kb he
    subst hbk
    by_cases hin : (kk ≤ rk && rk + rn ≤ kk + kn) = true
    · rw [ite_eq_left hin] at H; simp at H
    · rw [ite_eq_right hin] at H
      by_cases hdis : (rk + rn ≤ kk || kk + kn ≤ rk) = true
      · rw [ite_eq_left hdis] at H
        refine ⟨rfl, ?_⟩
        show bv_unsigned (edenot E rb) + rk + rn ≤ bv_unsigned (edenot E rb) + kk ∨
          bv_unsigned (edenot E rb) + kk + kn ≤ bv_unsigned (edenot E rb) + rk
        rcases (Bool.or_eq_true ..).mp hdis with h | h
        · exact Or.inl (by have := of_decide_eq_true h; omega)
        · exact Or.inr (by have := of_decide_eq_true h; omega)
      · rw [ite_eq_right hdis] at H; simp at H
  · rw [ite_eq_right he] at H; simp at H


/-! ### Part P4d: knowledge lookup soundness — the arithmetic prefix
 -/
theorem u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0 := by decide

/-- `Z_to_bv` only sees its argument modulo `2^64`. -/
theorem Z_to_bv_emod64 (z : Int) : Z_to_bv 64 (z % 2 ^ 64) = Z_to_bv 64 z := by
  apply BitVec.eq_of_toNat_eq
  have h1 : bv_unsigned (Z_to_bv 64 (z % 2 ^ 64)) = bv_unsigned (Z_to_bv 64 z) := by
    rw [u_lit64a, u_lit64a, Int.emod_emod]
  exact Int.ofNat.inj h1

/-- `bv_swrap` at a width `≤ 64` does not see the reduction mod `2^64`. -/
theorem bv_swrap_emod64 (n : Nat) (hn : n ≤ 64) (z : Int) :
    bv_swrap n (z % 2 ^ 64) = bv_swrap n z := by
  unfold bv_swrap
  have hdvd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hn)
  have hcast : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := (natCast_pow_two 64).symm
  rw [hcast] at hdvd
  rw [Int.add_emod, Int.emod_emod_of_dvd z hdvd, ← Int.add_emod]
theorem estart_lit0 (E : env) (rk : Int) : estart E (SA (.ELit 0) rk) = rk := by
  show bv_unsigned (edenot E (.ELit 0)) + rk = rk
  rw [show edenot E (.ELit 0) = Z_to_bv 64 0 from rfl, u_lit0]
  omega

/-- `adenot_shift`: a flat address at offset `d` into a flat base
    is the base value plus `d` (as a word). -/
theorem adenot_shift (E : env) (ka ra : saddr) (nk nr d : Int)
    (Hfk : flat E ka nk) (Hfr : flat E ra nr) (Hst : estart E ra = estart E ka + d)
    (Hd : 0 ≤ d) :
    adenot E ra = adenot E ka + nat_to_word d.toNat := by
  have h1 := flat_u E ra nr Hfr
  have h2 := flat_u E ka nk Hfk
  have hra : adenot E ra = Z_to_bv 64 (estart E ra) := by
    rw [← h1]; exact (Z_to_bv_unsigned _).symm
  have hka : adenot E ka = Z_to_bv 64 (estart E ka) := by
    rw [← h2]; exact (Z_to_bv_unsigned _).symm
  rw [hra, hka, Hst]
  have hkey : Z_to_bv 64 (estart E ka) + nat_to_word d.toNat
      = Z_to_bv 64 (estart E ka + (d.toNat : Int)) := by
    rw [w_add_nat]
    congr 1
    rw [u_small ⟨Hfk.1, Hfk.2.1⟩]
  rw [hkey, Int.toNat_of_nonneg Hd]
theorem elenZ_lit (E : env) (l0 : Int) : elenZ E (.ELit l0) = l0 % 2 ^ 64 := by
  show bv_unsigned (edenot E (.ELit l0)) = l0 % 2 ^ 64
  exact u_lit64a l0
theorem u8_lit (c : Int) : bv_unsigned (Z_to_bv 8 c) = c % 256 := by
  show ((BitVec.ofInt 8 c).toNat : Int) = c % 256
  rw [BitVec.toNat_ofInt]
  have h2 : ((2 : Nat) ^ 8) = 256 := by decide
  rw [h2]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
theorem map_unsigned_repeat8 (c : Int) (n : Nat) :
    (List.replicate n (Z_to_bv 8 c)).map bv_unsigned = List.replicate n (c % 256) := by
  rw [List.map_replicate, u8_lit]

/-- The literal an `n`-byte constant fill denotes.   `fill_lit_denot`
    carries no side condition; this tree needs `n ≤ 8` because this tree's
    `zbytes_le_to_Z` truncates at 64 bits (`zbytes_map`) and the byte
    arithmetic of `bv_swrap` at `8n > 64` would see that.  Every call site
    (`fill_read`, and the `KFill` case of the lookup) has `n ≤ 8`. -/
theorem fill_lit_denot (E : env) (sx : Bool) (n : Nat) (c : Int) (hn : n ≤ 8) :
    edenot E (fill_lit sx n c) =
      Z_to_bv 64 (extz sx n (bytes_le_to_Z (List.replicate n (Z_to_bv 8 c)))) := by
  have hrep : List.replicate n (c % 256)
      = (List.replicate n (Z_to_bv 8 c)).map (fun b => bv_unsigned b) := by
    rw [List.map_replicate, u8_lit]
  show Z_to_bv 64 (let u := zbytes_le_to_Z (List.replicate n (c % 256))
                   if sx then bv_swrap (8 * n) u else u) = _
  rw [hrep, zbytes_map]
  simp only [two64]
  unfold extz
  cases sx with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [Z_to_bv_emod64]
  | true =>
    simp only [ite_true]
    rw [bv_swrap_emod64 (8 * n) (by omega)]

/-- A read inside a constant-byte region reads the fill literal.
     -/
theorem fill_read (segs : List Segment) (E : env) (base : word → Option byte)
    (ka ra : saddr) (n : Nat) (sx : Bool) (c : Int) (L : Int)
    (hit : expr)
    (Hc : ∀ i, 0 ≤ i → i < L →
      base (Z_to_bv 64 (estart E ka + i)) = some (Z_to_bv 8 c))
    (Hfr : flat E ra (n : Int))
    (Hlo : estart E ka ≤ estart E ra)
    (Hhi : estart E ra + (n : Int) ≤ estart E ka + L)
    (hn : n ≤ 8)
    (Hhit : edenot E hit =
      Z_to_bv 64 (extz sx n (bytes_le_to_Z (List.replicate n (Z_to_bv 8 c))))) :
    ∃ bs, rdn segs base (adenot E ra) n = some bs ∧ bs.length = n ∧
      Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E hit := by
  obtain ⟨h1, h2, h3, h4⟩ := Hfr
  refine ⟨List.replicate n (Z_to_bv 8 c), ?_, List.length_replicate, ?_⟩
  · apply rdn_pointwise
    · exact List.length_replicate
    · rw [flat_u E ra _ ⟨h1, h2, h3, h4⟩]; omega
    · intro j hj
      rw [flat_u E ra _ ⟨h1, h2, h3, h4⟩]
      have hgd : (List.replicate n (Z_to_bv 8 c)).getD j (Z_to_bv 8 0) = Z_to_bv 8 c := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hj]
        rfl
      rw [hgd]
      have hidx : estart E ka + (estart E ra - estart E ka + (j : Int))
          = estart E ra + (j : Int) := by omega
      rw [← hidx]
      exact Hc _ (by omega) (by omega)
  · exact Hhit.symm


/-- `ext_hit_value`: reading `n` bytes at offset `d` of a stored
    word is the `(d, n)` extension of it. -/
theorem ext_hit_value (sx : Bool) (d : Int) (n w : Nat) (V : word)
    (Hdn : d.toNat + n ≤ w) :
    Z_to_bv 64 (extz sx n (bytes_le_to_Z ((word_to_le_bytes w V).drop d.toNat |>.take n)))
      = ext_val sx d.toNat n V := by
  rw [slice_word_bytes w d.toNat n V Hdn]
  unfold ext_val ext_Z extz
  rfl

/-- `getD` of a `drop`/`take` window (local: this tree uses `nth`). -/
theorem getD_drop_take {A : Type} (l : List A) (d n j : Nat) (dflt : A) (hj : j < n) :
    ((l.drop d).take n).getD j dflt = l.getD (d + j) dflt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj, List.getElem?_drop,
    List.getD_eq_getElem?_getD]

/-- The value a `KBlob` entry read at an offset denotes. -/
theorem blob_denot_eq (E : env) (sx : Bool) (k : Nat) (i : Int) (n : Nat) :
    edenot E (.EBlob sx k i n)
      = Z_to_bv 64 (extz sx n (bytes_le_to_Z ((E.eb k).drop i.toNat |>.take n))) := rfl

/-- A `match b with | .ELit 0 => a | _ => c` at the literal `0` reduces to
    `a` (local: Lean compiles the literal pattern into a matcher that
    does NOT iota-reduce, so the two cases are stated as rewrite rules). -/
theorem match_elit0_pos {A : Type} (a c : A) :
    (match expr.ELit (0 : Int) with | .ELit 0 => a | _ => c) = a := by
  split
  · rfl
  · rename_i h; exact absurd rfl h

/-- The same matcher at a NON-zero literal selects the default branch. -/
theorem match_elit0_neg {A : Type} (z : Int) (a c : A) (hz : z ≠ 0) :
    (match expr.ELit z with | .ELit 0 => a | _ => c) = c := by
  split
  · rename_i h
    exact absurd (by injection h : z = 0) hz
  · rfl

/-- The conclusion of a lookup at one read, as a PREDICATE on the lookup
    result. -/
def hit_ok (segs : List Segment) (base : word → Option byte) (E : env)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) : lres → Prop
  | .LHit v scs _ =>
      scs_denot segs base E scs → flat E (SA rb rk) (n : Int) →
      ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.length = n ∧
        Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | _ => True


/-!  Each
    memory-covering constructor (`KWord`, `KZero`, `KFill`, `KBlob`,
    `KImg`) produces the same shape: an `Hin` fact (the read is the hit
    value, from `rdn_pointwise`/`rdn_slice`/`fill_read`/`rdn_img`), and,
    for the symbolic-extent forms, the `xinside`/hint machinery.  The
    literal-length `KZero`/`KFill` branches additionally peel the
    `rel_lit` match; because Lean's fall-through (`| x =>`) matchers do
    not reduce definitionally, those branches need an explicit
    `simp only []` after the `cases` (this tree's usual idiom).
    (a) The conclusion is `hit_ok ...` (see
    above), so the result is an ordinary argument.  In Lean the same trick is unavailable once the fact
    is quantified over a variable, so `Hin` and the hint script are
    stated for an ARBITRARY length expression `m` together with the byte
    predicate for `m`'s extent; both call sites (`len` itself, and the
    `ELit l0` the literal branch peels off) pass the entry's own
    predicate. -/

theorem know_lookupA0_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn : List kentry) (base : word → Option byte) :
    ∀ (kn : List kentry) (rb : expr) (rk : Int) (n : Nat) (sx : Bool)
      (hints : List Bool) (acc : List sidecond),
      know_ok segs E M0 allkn → know_ok segs E base kn → 1 ≤ n → n ≤ 8 →
      hit_ok segs base E rb rk n sx (know_lookupA0 allkn segs kn rb rk n sx hints acc) := by
  intro kn
  induction kn with
  | nil =>
    intro rb rk n sx hints acc Hall Hkn Hn1 Hn8
    simp only [know_lookupA0, hit_ok]
  | cons K rest IH =>
    intro rb rk n sx hints acc Hall Hkn Hn1 Hn8
    have HK : kentry_ok segs E base K := Hkn K List.mem_cons_self
    have Hrest : know_ok segs E base rest := fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    have HIH : ∀ hints : List Bool,
        hit_ok segs base E rb rk n sx (know_lookupA0 allkn segs rest rb rk n sx hints acc) :=
      fun hs => IH rb rk n sx hs acc Hall Hrest Hn1 Hn8
    cases K with
    | KWord a w v =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      obtain ⟨Hkw8, Hfk, Hrd⟩ := HK
      generalize hrel : rel_lit rb rk (n : Int) kb kk (w : Int) = r
      cases r with
      | RInside d =>
        intro Hscs Hfr
        obtain ⟨heq, hd, hkk, hrn, hst⟩ :=
          rel_lit_inside E rb rk (n : Int) kb kk (w : Int) d hrel
        subst heq
        refine ⟨(word_to_le_bytes w (edenot E v)).drop d.toNat |>.take n, ?_, ?_, ?_⟩
        · have hshift := adenot_shift E (SA rb kk) (SA rb rk) (w : Int) (n : Int) d
              Hfk Hfr hst (by omega)
          rw [hshift]
          exact rdn_slice segs base w (adenot E (SA rb kk))
            (word_to_le_bytes w (edenot E v)) d.toNat n Hrd (by omega)
        · rw [List.length_take, List.length_drop, length_N_to_le_bytes]
          omega
        · rw [mkExt_denot E sx d.toNat n v Hn8 (Or.inr Hn1)]
          exact ext_hit_value sx d n w (edenot E v) (by omega)
      | RDisjoint => simp only []; exact HIH hints
      | RPartial => simp only []; exact HIH hints
      | RUnknown => simp only []; exact HIH hints
    | KZero a len =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      obtain ⟨Hfk, Hc⟩ := HK
      have Hin : ∀ (m : expr),
          (∀ i, 0 ≤ i → i < elenZ E m →
            base (Z_to_bv 64 (estart E (SA kb kk) + i)) = some (Z_to_bv 8 0)) →
          flat E (SA rb rk) (n : Int) →
          estart E (SA kb kk) ≤ estart E (SA rb rk) →
          estart E (SA rb rk) + (n : Int) ≤ estart E (SA kb kk) + elenZ E m →
          ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.length = n ∧
            Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (.ELit 0) := by
        intro m Hcm Hfr Hlo Hhi
        exact fill_read segs E base (SA kb kk) (SA rb rk) n sx 0 (elenZ E m) (.ELit 0)
          Hcm Hfr Hlo Hhi Hn8 (by rw [bytes_le_to_Z_repeat0, extz_0 sx n (Or.inr Hn1)]; rfl)
      have hsym : ∀ (m : expr),
          (∀ i, 0 ≤ i → i < elenZ E m →
            base (Z_to_bv 64 (estart E (SA kb kk) + i)) = some (Z_to_bv 8 0)) →
          hit_ok segs base E rb rk n sx
            (if xinside allkn rb rk (elen n) kb kk m then lres.LHit (.ELit 0) acc hints
             else match hints with
               | true :: hs =>
                   lres.LHit (.ELit 0)
                     (sidecond.SCInside (SA rb rk) (elen n) (SA kb kk) m :: acc) hs
               | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
               | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
        intro m Hcm
        by_cases hxi : xinside allkn rb rk (elen n) kb kk m = true
        · rw [ite_eq_left hxi]
          intro _ Hfr
          obtain ⟨hlo, hhi⟩ := xinside_sound segs E M0 allkn rb rk (elen n) kb kk m Hall hxi
          rw [elenZ_elen E n Hn8] at hhi
          exact Hin m Hcm Hfr hlo hhi
        · rw [ite_eq_right hxi]
          cases hints with
          | nil => exact HIH []
          | cons hd hs =>
            cases hd with
            | false => exact HIH hs
            | true =>
              intro Hscs Hfr
              obtain ⟨Hsc, _⟩ := (scs_denot_cons segs base E _ acc).mp Hscs
              obtain ⟨-, -, Hlo, Hhi⟩ := Hsc
              rw [elenZ_elen E n Hn8] at Hhi
              exact Hin m Hcm Hfr Hlo Hhi
      cases len with
      | ELit l0 =>
        simp only []
        generalize hrel : rel_lit rb rk (n : Int) kb kk (l0 % two64) = r
        cases r with
        | RInside d =>
          intro Hscs Hfr
          obtain ⟨heq, hd, hkk, hrn, hst⟩ :=
            rel_lit_inside E rb rk (n : Int) kb kk (l0 % two64) d hrel
          subst heq
          refine Hin (.ELit l0) Hc Hfr (by omega) ?_
          rw [two64_eq] at hrn
          simp only [elenZ_lit, two64]
          show bv_unsigned (edenot E rb) + rk + (n : Int)
              ≤ bv_unsigned (edenot E rb) + kk + l0 % 2 ^ 64
          omega
        | RDisjoint => simp only []; exact HIH hints
        | RPartial => simp only []; exact HIH hints
        | RUnknown => exact hsym _ Hc
      | EVar nn => exact hsym _ Hc
      | EAlu op x y => exact hsym _ Hc
      | EAluw op x y => exact hsym _ Hc
      | EMd op x y => exact hsym _ Hc
      | EMdw op x y => exact hsym _ Hc
      | EExt s l w e => exact hsym _ Hc
      | EBlob s k2 i w => exact hsym _ Hc
    | KFill a len c =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      obtain ⟨Hfk, Hc⟩ := HK
      have Hin : ∀ (m : expr),
          (∀ i, 0 ≤ i → i < elenZ E m →
            base (Z_to_bv 64 (estart E (SA kb kk) + i)) = some (Z_to_bv 8 c)) →
          flat E (SA rb rk) (n : Int) →
          estart E (SA kb kk) ≤ estart E (SA rb rk) →
          estart E (SA rb rk) + (n : Int) ≤ estart E (SA kb kk) + elenZ E m →
          ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.length = n ∧
            Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (fill_lit sx n c) := by
        intro m Hcm Hfr Hlo Hhi
        exact fill_read segs E base (SA kb kk) (SA rb rk) n sx c (elenZ E m) (fill_lit sx n c)
          Hcm Hfr Hlo Hhi Hn8 (by exact fill_lit_denot E sx n c Hn8)
      have hsym : ∀ (m : expr),
          (∀ i, 0 ≤ i → i < elenZ E m →
            base (Z_to_bv 64 (estart E (SA kb kk) + i)) = some (Z_to_bv 8 c)) →
          hit_ok segs base E rb rk n sx
            (if xinside allkn rb rk (elen n) kb kk m then lres.LHit (fill_lit sx n c) acc hints
             else match hints with
               | true :: hs =>
                   lres.LHit (fill_lit sx n c)
                     (sidecond.SCInside (SA rb rk) (elen n) (SA kb kk) m :: acc) hs
               | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
               | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
        intro m Hcm
        by_cases hxi : xinside allkn rb rk (elen n) kb kk m = true
        · rw [ite_eq_left hxi]
          intro _ Hfr
          obtain ⟨hlo, hhi⟩ := xinside_sound segs E M0 allkn rb rk (elen n) kb kk m Hall hxi
          rw [elenZ_elen E n Hn8] at hhi
          exact Hin m Hcm Hfr hlo hhi
        · rw [ite_eq_right hxi]
          cases hints with
          | nil => exact HIH []
          | cons hd hs =>
            cases hd with
            | false => exact HIH hs
            | true =>
              intro Hscs Hfr
              obtain ⟨Hsc, _⟩ := (scs_denot_cons segs base E _ acc).mp Hscs
              obtain ⟨-, -, Hlo, Hhi⟩ := Hsc
              rw [elenZ_elen E n Hn8] at Hhi
              exact Hin m Hcm Hfr Hlo Hhi
      cases len with
      | ELit l0 =>
        simp only []
        generalize hrel : rel_lit rb rk (n : Int) kb kk (l0 % two64) = r
        cases r with
        | RInside d =>
          intro Hscs Hfr
          obtain ⟨heq, hd, hkk, hrn, hst⟩ :=
            rel_lit_inside E rb rk (n : Int) kb kk (l0 % two64) d hrel
          subst heq
          refine Hin (.ELit l0) Hc Hfr (by omega) ?_
          rw [two64_eq] at hrn
          simp only [elenZ_lit, two64]
          show bv_unsigned (edenot E rb) + rk + (n : Int)
              ≤ bv_unsigned (edenot E rb) + kk + l0 % 2 ^ 64
          omega
        | RDisjoint => simp only []; exact HIH hints
        | RPartial => simp only []; exact HIH hints
        | RUnknown => exact hsym _ Hc
      | EVar nn => exact hsym _ Hc
      | EAlu op x y => exact hsym _ Hc
      | EAluw op x y => exact hsym _ Hc
      | EMd op x y => exact hsym _ Hc
      | EMdw op x y => exact hsym _ Hc
      | EExt s l w e => exact hsym _ Hc
      | EBlob s k2 i w => exact hsym _ Hc
    | KBlob a len k =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_lookupA0]
      obtain ⟨Hfk, Hlen, Hb⟩ := HK
      by_cases heqb : (expr_eqb rb kb) = true
      · rw [ite_eq_left heqb]
        have hbk : rb = kb := expr_eqb_eq rb kb heqb
        subst hbk
        by_cases hkk : kk ≤ rk
        · rw [ite_eq_left hkk]
          have Hst : estart E (SA rb rk) = estart E (SA rb kk) + (rk - kk) := by
            show bv_unsigned (edenot E rb) + rk
              = bv_unsigned (edenot E rb) + kk + (rk - kk)
            omega
          have Hin : ∀ (m : expr),
              (∀ i, 0 ≤ i → i < elenZ E m →
                base (Z_to_bv 64 (estart E (SA rb kk) + i)) = some ((E.eb k).getD i.toNat (Z_to_bv 8 0))) →
              ((E.eb k).length : Int) = elenZ E m →
              flat E (SA rb rk) (n : Int) →
              rk - kk + (n : Int) ≤ elenZ E m →
              ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.length = n ∧
                Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
                  = edenot E (.EBlob sx k (rk - kk) n) := by
            intro m Hbm Hlm Hfr Hhi
            obtain ⟨g1, g2, g3, g4⟩ := Hfr
            have hlen : ((rk - kk).toNat + n ≤ (E.eb k).length) := by
              have h2 : ((rk - kk).toNat + n : Int) ≤ ((E.eb k).length : Int) := by
                rw [Hlm]
                have hd : ((rk - kk).toNat : Int) = rk - kk := Int.toNat_of_nonneg (by omega)
                omega
              omega
            refine ⟨(E.eb k).drop (rk - kk).toNat |>.take n, ?_, ?_, ?_⟩
            · apply rdn_pointwise
              · rw [List.length_take, List.length_drop]; omega
              · rw [flat_u E _ _ ⟨g1, g2, g3, g4⟩]; omega
              · intro j hj
                rw [flat_u E _ _ ⟨g1, g2, g3, g4⟩]
                rw [getD_drop_take (E.eb k) (rk - kk).toNat n j (Z_to_bv 8 0) hj]
                rw [Hst]
                have hidx : estart E (SA rb kk) + (rk - kk) + (j : Int)
                    = estart E (SA rb kk) + ((rk - kk) + (j : Int)) := by omega
                rw [hidx]
                rw [Hbm _ (by omega) (by omega)]
                have hcast : ((rk - kk) + (j : Int))
                    = (((rk - kk).toNat + j : Nat) : Int) := by
                  rw [← Int.toNat_of_nonneg (show 0 ≤ rk - kk by omega)]
                  push_cast
                  rfl
                rw [hcast]
                simp only [Int.toNat_natCast]
            · rw [List.length_take, List.length_drop]; omega
            · exact (blob_denot_eq E sx k (rk - kk) n).symm
          have hsym : ∀ (m : expr),
              (∀ i, 0 ≤ i → i < elenZ E m →
                base (Z_to_bv 64 (estart E (SA rb kk) + i)) = some ((E.eb k).getD i.toNat (Z_to_bv 8 0))) →
              ((E.eb k).length : Int) = elenZ E m →
              hit_ok segs base E rb rk n sx
                (if (match erange allkn m with
                     | some (lo, snd) => decide (rk + (n : Int) ≤ kk + lo)
                     | none => false) = true then
                   lres.LHit (.EBlob sx k (rk - kk) n) acc hints
                 else match hints with
                   | true :: hs => lres.LHit (.EBlob sx k (rk - kk) n)
                                     (sidecond.SCInside (SA rb rk) (elen n) (SA rb kk) m :: acc) hs
                   | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                   | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc) := by
            intro m Hbm Hlm
            by_cases hrge : (match erange allkn m with
                             | some (lo, snd) => decide (rk + (n : Int) ≤ kk + lo)
                             | none => false) = true
            · rw [ite_eq_left hrge]
              intro _ Hfr
              refine Hin m Hbm Hlm Hfr ?_
              generalize hre : erange allkn m = rr at hrge
              cases rr with
              | none => simp at hrge
              | some p =>
                obtain ⟨rlo, rhi⟩ := p
                simp only [] at hrge
                have hle : rk + (n : Int) ≤ kk + rlo := of_decide_eq_true hrge
                have hsound : rlo ≤ elenZ E m :=
                  (erange_sound segs E M0 allkn m rlo rhi Hall hre).1
                omega
            · rw [ite_eq_right hrge]
              cases hints with
              | nil => exact HIH []
              | cons hd hs =>
                cases hd with
                | false => exact HIH hs
                | true =>
                  intro Hscs Hfr
                  obtain ⟨Hsc, _⟩ := (scs_denot_cons segs base E _ acc).mp Hscs
                  obtain ⟨-, -, Hlo, Hhi⟩ := Hsc
                  rw [elenZ_elen E n Hn8] at Hhi
                  exact Hin m Hbm Hlm Hfr (by omega)
          cases len with
          | ELit l0 =>
            simp only []
            by_cases hle : rk + (n : Int) ≤ kk + (l0 % two64)
            · rw [ite_eq_left hle]
              intro _ Hfr
              refine Hin (.ELit l0) Hb Hlen Hfr ?_
              rw [two64_eq] at hle
              simp only [elenZ_lit, two64]
              omega
            · rw [ite_eq_right hle]
              by_cases hgt : kk + (l0 % two64) ≤ rk
              · rw [ite_eq_left hgt]; exact HIH hints
              · rw [ite_eq_right hgt]; exact trivial
          | EVar nn => exact hsym _ Hb Hlen
          | EAlu op x y => exact hsym _ Hb Hlen
          | EAluw op x y => exact hsym _ Hb Hlen
          | EMd op x y => exact hsym _ Hb Hlen
          | EMdw op x y => exact hsym _ Hb Hlen
          | EExt s l w e => exact hsym _ Hb Hlen
          | EBlob s k2 i w => exact hsym _ Hb Hlen
        · rw [ite_eq_right hkk]; exact HIH hints
      · rw [ite_eq_right heqb]; exact HIH hints
    | KImg lo hi =>
      simp only [know_lookupA0]
      obtain ⟨Hlo0, Hhi64, Hnone⟩ := HK
      cases rb with
      | ELit z =>
        split
        · rename_i heq
          have hz : z = 0 := by injection heq
          subst hz
          by_cases hr : (decide (lo ≤ rk) && decide (rk + (n : Int) ≤ hi)) = true
          · rw [ite_eq_left hr]
            rcases (Bool.and_eq_true ..).mp hr with ⟨h1, h2⟩
            have h1' : lo ≤ rk := of_decide_eq_true h1
            have h2' : rk + (n : Int) ≤ hi := of_decide_eq_true h2
            generalize himg : img_bytes segs rk n = ib
            cases ib with
            | none => exact trivial
            | some zs =>
              intro Hscs Hfr
              obtain ⟨g1, g2, g3, g4⟩ := Hfr
              have Hu : bv_unsigned (adenot E (SA (.ELit 0) rk)) = rk := by
                rw [flat_u E _ _ ⟨g1, g2, g3, g4⟩]
                exact estart_lit0 E rk
              have hw : bv_unsigned (adenot E (SA (.ELit 0) rk)) + (n : Int) ≤ 2 ^ 64 := by
                rw [flat_u E _ _ ⟨g1, g2, g3, g4⟩]; omega
              have hpt : ∀ j : Nat, j < n →
                  base (Z_to_bv 64 (bv_unsigned (adenot E (SA (.ELit 0) rk)) + (j : Int)))
                    = none := by
                intro j hj
                rw [Hu]
                exact Hnone _ (by omega) (by omega)
              have himg' : img_bytes segs (bv_unsigned (adenot E (SA (.ELit 0) rk))) n
                  = some zs := by
                rw [Hu]; exact himg
              obtain ⟨bs, Hbs, Hmap⟩ :=
                rdn_img segs base n (adenot E (SA (.ELit 0) rk)) zs hw hpt himg'
              refine ⟨bs, Hbs, rdn_length segs base n _ bs Hbs, ?_⟩
              show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
                = edenot E (lit_of_bytes sx n zs)
              show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
                = Z_to_bv 64 (let u := zbytes_le_to_Z zs
                              if sx then bv_swrap (8 * n) u else u)
              rw [← Hmap, zbytes_map]
              simp only [two64]
              unfold extz
              cases sx with
              | false =>
                simp only [Bool.false_eq_true, ite_false]
                rw [Z_to_bv_emod64]
              | true =>
                simp only [ite_true]
                rw [bv_swrap_emod64 (8 * n) (by omega)]
          · rw [ite_eq_right hr]; exact HIH hints
        · exact HIH hints
      | EVar nn =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EAlu op x y =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EAluw op x y =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EMd op x y =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EMdw op x y =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EExt s l w e =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
      | EBlob s k2 i w =>
        split
        · rename_i heq; exact absurd heq (by intro h; cases h)
        · exact HIH hints
    | KAlign e m => simp only [know_lookupA0]; exact HIH hints
    | KRange e lo hi => simp only [know_lookupA0]; exact HIH hints
    | KWr a nn => simp only [know_lookupA0]; exact HIH hints
    | KDisj a1 n1 a2 n2 => simp only [know_lookupA0]; exact HIH hints
    | KUnk a nn => simp only [know_lookupA0]; exact HIH hints


/-!  `log_lookup_sound` is a prerequisite of
    `sym_step_sound`: the load path consults the store log BEFORE the
    knowledge.  Only `ext_hit_value` of this region had been stated . -/

/-- Reading inside one stored slot. -/
theorem rdn_inside_wbytes (segs : List Segment) (E : env) (M : word → Option byte)
    (ka : saddr) (w : Nat) (V : word) (ra : saddr) (n d : Nat)
    (Hfk : flat E ka (w : Int)) (Hfr : flat E ra (n : Int))
    (Hst : estart E ra = estart E ka + (d : Int))
    (Hdn : (d : Int) + (n : Int) ≤ (w : Int)) :
    rdn segs (wbytes M (adenot E ka) (word_to_le_bytes w V)) (adenot E ra) n
      = some ((word_to_le_bytes w V).drop d |>.take n) := by
  have hshift := adenot_shift E ka ra (w : Int) (n : Int) (d : Int) Hfk Hfr Hst (by omega)
  rw [Int.toNat_natCast] at hshift
  rw [hshift]
  refine rdn_slice segs (wbytes M (adenot E ka) (word_to_le_bytes w V)) w
    (adenot E ka) (word_to_le_bytes w V) d n ?_ (by omega)
  have hno : ((adenot E ka).toNat : Int) + ((word_to_le_bytes w V).length : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [length_N_to_le_bytes, ← natCast_pow_two]
    show bv_unsigned (adenot E ka) + (w : Int) ≤ (2 : Int) ^ 64
    rw [flat_u E ka (w : Int) Hfk]
    exact Hfk.2.2.2
  have hhit := SeqExec.rdn_wbytes_hit segs (word_to_le_bytes w V) M (adenot E ka) hno
  rw [length_N_to_le_bytes] at hhit
  exact hhit

/-- `zpow` at a nonnegative multiple of 8 is the corresponding `Nat`
    power . -/
theorem zpow_two_eight_mul (d : Int) (hd : 0 ≤ d) :
    zpow 2 (8 * d) = (2 : Int) ^ (8 * d.toNat) := by
  show (2 : Int) ^ (8 * d).toNat = (2 : Int) ^ (8 * d.toNat)
  have h : (8 * d).toNat = 8 * d.toNat := by
    have h1 : ((8 * d).toNat : Int) = 8 * d := Int.toNat_of_nonneg (by omega)
    have h2 : ((8 * d.toNat : Nat) : Int) = 8 * d := by
      push_cast
      rw [Int.toNat_of_nonneg hd]
    exact Int.ofNat.inj (h1.trans h2.symm)
  rw [h]

/-- The byte `d` of a stored word literal, in the shape the executor's
    bytewise log/knowledge lookups compute it. -/
theorem byte_at_lit_eq (E : env) (d : Int) (hd : 0 ≤ d) (z : Int) :
    bv_unsigned (edenot E (.ELit z)) / 2 ^ (8 * d.toNat) % 256
      = ((z % two64) / zpow 2 (8 * d)) % 256 := by
  have h1 : bv_unsigned (edenot E (.ELit z)) = z % two64 := u_lit64a z
  rw [h1, zpow_two_eight_mul d hd]

/-- `Z_to_bv 8` does not see the reduction mod 256.   -/
theorem Z_to_bv8_mod (c : Int) : Z_to_bv 8 (c % 256) = Z_to_bv 8 c := by
  have h1 : bv_unsigned (Z_to_bv 8 (c % 256)) = bv_unsigned (Z_to_bv 8 c) := by
    rw [u8_lit, u8_lit, Int.emod_emod]
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h1)

/-- The value of a one-byte window of a word. -/
theorem word_byte_at (w d : Nat) (V : word) (Hw : d + 1 ≤ w) :
    ((word_to_le_bytes w V).drop d |>.take 1)
      = [Z_to_bv 8 (bv_unsigned V / 2 ^ (8 * d) % 256)] := by
  unfold word_to_le_bytes
  rw [skipn_Z_to_le_bytes w d (V.toNat : Int) (by omega)]
  rw [firstn_Z_to_le_bytes (w - d) 1 _ (by omega)]
  show [Z_to_bv 8 ((V.toNat : Int) / 2 ^ (8 * d))]
      = [Z_to_bv 8 (bv_unsigned V / 2 ^ (8 * d) % 256)]
  rw [Z_to_bv8_mod]

/-- A one-byte read of an overlay byte. -/
theorem rdn_one (segs : List Segment) (mem : word → Option byte) (a : word) (b : byte)
    (H : SeqExec.rdn_byte segs mem a = some b) : rdn segs mem a 1 = some [b] := by
  have h := SeqExec.rdn_succ_byte segs mem a 0 b H
  rw [SeqExec.rdn_zero] at h
  simpa using h

/-- Bytewise composition out of the log. -/
theorem rdn_cons1 (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat)
    (b : byte) (bs : List byte)
    (H1 : rdn segs mem a 1 = some [b]) (Hn : rdn segs mem (a + 1) n = some bs) :
    rdn segs mem a (n + 1) = some (b :: bs) := by
  cases h : SeqExec.rdn_byte segs mem a with
  | none =>
    rw [SeqExec.rdn_succ_none segs mem a 0 h] at H1
    exact absurd H1 (by simp)
  | some c =>
    have h1 : rdn segs mem a (0 + 1) = some [c] := by
      rw [SeqExec.rdn_succ_byte segs mem a 0 c h, SeqExec.rdn_zero]
      rfl
    have H1' : rdn segs mem a (0 + 1) = some [b] := H1
    rw [h1, Option.some.injEq] at H1'
    have hc : c = b := (List.cons.inj H1').1
    subst hc
    rw [SeqExec.rdn_succ_byte segs mem a n c h, Hn]
    rfl
/-- One literal byte out of the store log. -/
theorem log_byte_lit_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (log : List sentry) :
    ∀ (rb : expr) (rk : Int) (b : Int),
      log_flat E log → log_byte_lit log rb rk = some b → flat E (SA rb rk) 1 →
      rdn segs (mem_denot E base log) (adenot E (SA rb rk)) 1 = some [Z_to_bv 8 b] ∧
        0 ≤ b ∧ b < 256 := by
  induction log with
  | nil =>
    intro rb rk b Hlf H Hfr
    simp only [log_byte_lit] at H
    exact absurd H (by simp)
  | cons e rest IH =>
    obtain ⟨⟨kb, kk⟩, w, v⟩ := e
    intro rb rk b Hlf H Hfr
    rw [log_flat_cons] at Hlf
    obtain ⟨Hw8, Hfk, Hlf'⟩ := Hlf
    simp only [log_byte_lit] at H
    generalize hrel : rel_lit rb rk 1 kb kk (w : Int) = rr at H
    cases rr with
    | RInside d =>
      cases v with
      | ELit z =>
        simp only [Option.some.injEq] at H
        obtain ⟨heq, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk 1 kb kk (w : Int) d hrel
        subst heq
        have hd0 : 0 ≤ d := by omega
        rw [mem_denot_cons]
        refine ⟨?_, ?_, ?_⟩
        · rw [rdn_inside_wbytes segs E (mem_denot E base rest) (SA rb kk) w (edenot E (.ELit z))
              (SA rb rk) (1 : Nat) d.toNat Hfk Hfr ?_ ?_]
          · rw [word_byte_at w d.toNat (edenot E (.ELit z)) (by omega),
              byte_at_lit_eq E d hd0 z, H]
          · rw [Int.toNat_of_nonneg hd0]; exact hst
          · rw [Int.toNat_of_nonneg hd0]
            show d + (1 : Int) ≤ (w : Int)
            omega
        · rw [← H]; exact Int.emod_nonneg _ (by decide)
        · rw [← H]; exact Int.emod_lt_of_pos _ (by decide)
      | EVar n1 => simp at H
      | EAlu op x y => simp at H
      | EAluw op x y => simp at H
      | EMd op x y => simp at H
      | EMdw op x y => simp at H
      | EExt s l w1 e1 => simp at H
      | EBlob s k2 i w1 => simp at H
    | RDisjoint =>
      simp only [] at H
      obtain ⟨IH1, IH2⟩ := IH rb rk b Hlf' H Hfr
      obtain ⟨heq, hdis⟩ := rel_lit_disjoint E rb rk 1 kb kk (w : Int) hrel
      subst heq
      have Hout : ((adenot E (SA rb rk)).toNat : Int) + (1 : Int)
            ≤ ((adenot E (SA rb kk)).toNat : Int)
          ∨ ((adenot E (SA rb kk)).toNat : Int)
              + ((word_to_le_bytes w (edenot E v)).length : Int)
              ≤ ((adenot E (SA rb rk)).toNat : Int) := by
        rw [length_N_to_le_bytes]
        rw [show ((adenot E (SA rb rk)).toNat : Int) = estart E (SA rb rk)
              from flat_u E (SA rb rk) 1 Hfr,
            show ((adenot E (SA rb kk)).toNat : Int) = estart E (SA rb kk)
              from flat_u E (SA rb kk) (w : Int) Hfk]
        exact hdis
      have Hnw : ((adenot E (SA rb rk)).toNat : Int) + (1 : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [← natCast_pow_two,
            show ((adenot E (SA rb rk)).toNat : Int) = estart E (SA rb rk)
              from flat_u E (SA rb rk) 1 Hfr]
        exact Hfr.2.2.2
      have Hnw' : ((adenot E (SA rb kk)).toNat : Int)
          + ((word_to_le_bytes w (edenot E v)).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [length_N_to_le_bytes, ← natCast_pow_two,
            show ((adenot E (SA rb kk)).toNat : Int) = estart E (SA rb kk)
              from flat_u E (SA rb kk) (w : Int) Hfk]
        exact Hfk.2.2.2
      refine ⟨?_, IH2.1, IH2.2⟩
      rw [mem_denot_cons,
        rdn_wbytes_out segs (word_to_le_bytes w (edenot E v)) (mem_denot E base rest)
          (adenot E (SA rb kk)) (adenot E (SA rb rk)) 1 Hout Hnw Hnw']
      exact IH1
    | RPartial => simp only [] at H; exact absurd H (by simp)
    | RUnknown => simp only [] at H; exact absurd H (by simp)

/-- `adenot` at offset `rk + 1` is the address one byte further. -/
theorem adenot_add_one (E : env) (rb : expr) (rk : Int)
    (H0 : 0 ≤ bv_unsigned (edenot E rb) + rk) (H1 : bv_unsigned (edenot E rb) + rk < 2 ^ 64) :
    adenot E (SA rb rk) + 1 = adenot E (SA rb (rk + 1)) := by
  show Z_to_bv 64 (bv_unsigned (edenot E rb) + rk) + 1
     = Z_to_bv 64 (bv_unsigned (edenot E rb) + (rk + 1))
  rw [w_add_1]
  congr 1
  rw [u_small ⟨H0, H1⟩]
  omega

/-- Flatness after stepping one byte into the range: a flat `n+1`-byte
    read at `rk` restricts to a flat `n`-byte read at `rk + 1`. -/
theorem flat_step (E : env) (rb : expr) (rk : Int) (n : Nat)
    (H : flat E (SA rb rk) ((n + 2 : Nat) : Int)) : flat E (SA rb (rk + 1)) ((n + 1 : Nat) : Int) := by
  obtain ⟨g1, g2, g3, g4⟩ := H
  have hs1 : estart E (SA rb (rk + 1)) = estart E (SA rb rk) + 1 := by
    show bv_unsigned (edenot E rb) + (rk + 1) = bv_unsigned (edenot E rb) + rk + 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (0 : Int) ≤ estart E (SA rb (rk + 1)); rw [hs1]; omega
  · show estart E (SA rb (rk + 1)) < (2 : Int) ^ 64
    rw [hs1]
    push_cast at g4
    omega
  · show (0 : Int) ≤ ((n + 1 : Nat) : Int); push_cast; omega
  · show estart E (SA rb (rk + 1)) + ((n + 1 : Nat) : Int) ≤ (2 : Int) ^ 64
    rw [hs1]
    push_cast at g4 ⊢
    omega

/-- `n` literal bytes out of the store log.   -/
theorem log_bytes_lit_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (log : List sentry) (n : Nat) :
    ∀ (rb : expr) (rk : Int) (zs : List Int),
      log_flat E log → log_bytes_lit log rb rk n = some zs → flat E (SA rb rk) (n : Int) →
      ∃ bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = some bs ∧
        bs.map bv_unsigned = zs := by
  induction n with
  | zero =>
    intro rb rk zs Hlf H Hfr
    simp only [log_bytes_lit, Option.some.injEq] at H
    rw [← H]
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro rb rk zs Hlf H Hfr
    simp only [log_bytes_lit] at H
    generalize hb : log_byte_lit log rb rk = bb at H
    generalize hr : log_bytes_lit log rb (rk + 1) n = rr at H
    cases bb with
    | none => exact absurd H (by simp)
    | some b =>
      cases rr with
      | none => exact absurd H (by simp)
      | some r =>
        simp only [Option.some.injEq] at H
        rw [← H]
        have Hf1 : flat E (SA rb rk) 1 :=
          flat_mono E (SA rb rk) ((n + 1 : Nat) : Int) 1 Hfr ⟨by omega, by omega⟩
        obtain ⟨H1, Hb8⟩ := log_byte_lit_sound segs E base log rb rk b Hlf hb Hf1
        have hb8' : bv_unsigned (Z_to_bv 8 b) = b := by
          rw [u8_lit, Int.emod_eq_of_lt Hb8.1 Hb8.2]
        cases n with
        | zero =>
          simp only [log_bytes_lit, Option.some.injEq] at hr
          rw [← hr]
          refine ⟨[Z_to_bv 8 b], H1, ?_⟩
          simp only [List.map_cons, List.map_nil, hb8']
        | succ n' =>
          have Hfn : flat E (SA rb (rk + 1)) ((n' + 1 : Nat) : Int) := flat_step E rb rk n' Hfr
          obtain ⟨bs', Hn, Hmap⟩ := ih rb (rk + 1) r Hlf hr Hfn
          have hadd : adenot E (SA rb rk) + 1 = adenot E (SA rb (rk + 1)) :=
            adenot_add_one E rb rk Hfr.1 Hfr.2.1
          have Hn' : rdn segs (mem_denot E base log) (adenot E (SA rb rk) + 1) (n' + 1)
              = some bs' := by
            rw [hadd]; exact Hn
          refine ⟨Z_to_bv 8 b :: bs', ?_, ?_⟩
          · exact rdn_cons1 segs (mem_denot E base log) (adenot E (SA rb rk)) (n' + 1)
              (Z_to_bv 8 b) bs' H1 Hn'
          · simp only [List.map_cons, Hmap, hb8']

/-- Conclusion of a `log_lookup`, as a predicate on its result . -/
def log_hit_ok (segs : List Segment) (base : word → Option byte) (E : env)
    (log : List sentry) (rb : expr) (rk : Int) (n : Nat) (sx : Bool) : lres → Prop
  | .LHit v scs _ =>
      scs_denot segs base E scs → flat E (SA rb rk) (n : Int) →
      ∃ bs, rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n = some bs ∧
        bs.length = n ∧
        Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E v
  | .LMiss scs _ =>
      scs_denot segs base E scs → flat E (SA rb rk) (n : Int) →
      rdn segs (mem_denot E base log) (adenot E (SA rb rk)) n
        = rdn segs base (adenot E (SA rb rk)) n
  | .LStuck => True

/-- One `wbytes` layer in front of a `log_hit_ok`: a read that keeps clear
    of the entry reads the same bytes out of the smaller log. -/
theorem log_hit_ok_wbytes (segs : List Segment) (E : env) (base : word → Option byte)
    (kb : expr) (kk : Int) (w : Nat) (v : expr) (rest : List sentry)
    (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (r : lres)
    (Hfk : flat E (SA kb kk) (w : Int))
    (Hfr : flat E (SA rb rk) (n : Int))
    (Hdis : estart E (SA rb rk) + (n : Int) ≤ estart E (SA kb kk) ∨
            estart E (SA kb kk) + (w : Int) ≤ estart E (SA rb rk))
    (H : log_hit_ok segs base E rest rb rk n sx r) :
    log_hit_ok segs base E (SE (SA kb kk) w v :: rest) rb rk n sx r := by
  have Hout : ((adenot E (SA rb rk)).toNat : Int) + (n : Int)
        ≤ ((adenot E (SA kb kk)).toNat : Int)
      ∨ ((adenot E (SA kb kk)).toNat : Int)
          + ((word_to_le_bytes w (edenot E v)).length : Int)
          ≤ ((adenot E (SA rb rk)).toNat : Int) := by
    rw [length_N_to_le_bytes]
    rw [show ((adenot E (SA rb rk)).toNat : Int) = estart E (SA rb rk)
          from flat_u E (SA rb rk) (n : Int) Hfr,
        show ((adenot E (SA kb kk)).toNat : Int) = estart E (SA kb kk)
          from flat_u E (SA kb kk) (w : Int) Hfk]
    exact Hdis
  have Hnw : ((adenot E (SA rb rk)).toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [← natCast_pow_two,
        show ((adenot E (SA rb rk)).toNat : Int) = estart E (SA rb rk)
          from flat_u E (SA rb rk) (n : Int) Hfr]
    exact Hfr.2.2.2
  have Hnw' : ((adenot E (SA kb kk)).toNat : Int)
      + ((word_to_le_bytes w (edenot E v)).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [length_N_to_le_bytes, ← natCast_pow_two,
        show ((adenot E (SA kb kk)).toNat : Int) = estart E (SA kb kk)
          from flat_u E (SA kb kk) (w : Int) Hfk]
    exact Hfk.2.2.2
  have hrid := rdn_wbytes_out segs (word_to_le_bytes w (edenot E v)) (mem_denot E base rest)
    (adenot E (SA kb kk)) (adenot E (SA rb rk)) n Hout Hnw Hnw'
  cases r with
  | LStuck => exact trivial
  | LHit v' scs hh =>
    simp only [log_hit_ok] at H ⊢
    intro Hscs Hfr'
    obtain ⟨bs, hbs, hlen, hval⟩ := H Hscs Hfr'
    exact ⟨bs, by rw [mem_denot_cons, hrid]; exact hbs, hlen, hval⟩
  | LMiss scs hh =>
    simp only [log_hit_ok] at H ⊢
    intro Hscs Hfr'
    rw [mem_denot_cons, hrid]
    exact H Hscs Hfr'
theorem log_lookup_sound (segs : List Segment) (E : env) (kn : List kentry) :
    ∀ (log : List sentry) (base : word → Option byte)
      (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond),
      know_ok segs E base kn → log_flat E log → 1 ≤ n → n ≤ 8 →
      log_hit_ok segs base E log rb rk n sx (log_lookup kn log rb rk n sx hints acc) := by
  intro log
  induction log with
  | nil =>
    intro base rb rk n sx hints acc Hkn Hlf Hn1 Hn8
    simp only [log_lookup, log_hit_ok]
    intro _ _
    rfl
  | cons e rest IH =>
    obtain ⟨⟨kb, kk⟩, w, v⟩ := e
    intro base rb rk n sx hints acc Hkn Hlf Hn1 Hn8
    have Hlf0 : log_flat E (SE (SA kb kk) w v :: rest) := Hlf
    rw [log_flat_cons] at Hlf
    obtain ⟨Hw8, Hfk, Hlf'⟩ := Hlf
    simp only [log_lookup]
    generalize hrel : rel_lit rb rk (n : Int) kb kk (w : Int) = rr
    cases rr with
    | RInside d =>
      simp only []
      simp only [log_hit_ok]
      intro Hscs Hfr
      obtain ⟨-, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk (n : Int) kb kk (w : Int) d hrel
      have hd0 : 0 ≤ d := by omega
      rw [mem_denot_cons]
      refine ⟨(word_to_le_bytes w (edenot E v)).drop d.toNat |>.take n, ?_, ?_, ?_⟩
      · rw [rdn_inside_wbytes segs E (mem_denot E base rest) (SA kb kk) w (edenot E v)
            (SA rb rk) n d.toNat Hfk Hfr ?_ ?_]
        · rw [Int.toNat_of_nonneg hd0]; exact hst
        · rw [Int.toNat_of_nonneg hd0]; omega
      · rw [length_firstn_skipn (word_to_le_bytes w (edenot E v)) d.toNat n]
        rw [length_N_to_le_bytes]
        omega
      · rw [mkExt_denot E sx d.toNat n v Hn8 (Or.inr Hn1)]
        exact ext_hit_value sx d n w (edenot E v) (by omega)
    | RDisjoint =>
      simp only []
      obtain ⟨-, hdis⟩ := rel_lit_disjoint E rb rk (n : Int) kb kk (w : Int) hrel
      have hIH := IH base rb rk n sx hints acc Hkn Hlf' Hn1 Hn8
      generalize hres : log_lookup kn rest rb rk n sx hints acc = res at hIH ⊢
      cases res with
      | LStuck => exact trivial
      | LHit v' scs hh =>
        simp only [log_hit_ok] at ⊢
        intro Hscs Hfr
        exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LHit v' scs hh)
          Hfk Hfr hdis hIH Hscs Hfr
      | LMiss scs hh =>
        simp only [log_hit_ok] at ⊢
        intro Hscs Hfr
        exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LMiss scs hh)
          Hfk Hfr hdis hIH Hscs Hfr
    | RPartial =>
      simp only []
      generalize hbl : log_bytes_lit (SE (SA kb kk) w v :: rest) rb rk n = bl
      cases bl with
      | none => exact trivial
      | some zs =>
        simp only [log_hit_ok]
        intro Hscs Hfr
        obtain ⟨bs, Hbs, Hmap⟩ :=
          log_bytes_lit_sound segs E base (SE (SA kb kk) w v :: rest) n rb rk zs Hlf0 hbl Hfr
        refine ⟨bs, Hbs, rdn_length segs _ n _ bs Hbs, ?_⟩
        show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (lit_of_bytes sx n zs)
        unfold lit_of_bytes
        show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
          = Z_to_bv 64 (if sx then bv_swrap (8 * n) (zbytes_le_to_Z zs) else zbytes_le_to_Z zs)
        rw [← Hmap, zbytes_map]
        show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
          = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs % 2 ^ 64))
        unfold extz
        cases sx with
        | false => simp only [Bool.false_eq_true, ite_false]; rw [Z_to_bv_emod64]
        | true => simp only [ite_true]; rw [bv_swrap_emod64 (8 * n) (by omega)]
    | RUnknown =>
      simp only []
      have hgen : ∀ (hs : List Bool),
          log_hit_ok segs base E (SE (SA kb kk) w v :: rest) rb rk n sx
            (log_lookup kn rest rb rk n sx hs
              (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)) := by
        intro hs
        have hIH := IH base rb rk n sx hs
          (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) Hkn Hlf' Hn1 Hn8
        have hacc := log_lookup_acc kn rest rb rk n sx hs
          (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
        generalize hres : log_lookup kn rest rb rk n sx hs
          (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) = res at hIH hacc
        cases res with
        | LStuck => exact trivial
        | LHit v' scs hh =>
          simp only [] at hacc
          simp only [log_hit_ok] at ⊢
          intro Hscs Hfr
          obtain ⟨pre, hpre⟩ := hacc
          have Hscs' : scs_denot segs base E (pre ++ sidecond.SCDisj (SA rb rk) (elen n)
              (SA kb kk) (elen w) :: acc) := by rw [← hpre]; exact Hscs
          obtain ⟨-, Hscs2⟩ := (scs_denot_app segs base E pre _).mp Hscs'
          obtain ⟨Hd, -⟩ := (scs_denot_cons segs base E _ acc).mp Hscs2
          obtain ⟨-, -, Hdis⟩ := Hd
          rw [elenZ_elen E n Hn8, elenZ_elen E w (by omega)] at Hdis
          exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LHit v' scs hh)
            Hfk Hfr Hdis hIH Hscs Hfr
        | LMiss scs hh =>
          simp only [] at hacc
          simp only [log_hit_ok] at ⊢
          intro Hscs Hfr
          obtain ⟨pre, hpre⟩ := hacc
          have Hscs' : scs_denot segs base E (pre ++ sidecond.SCDisj (SA rb rk) (elen n)
              (SA kb kk) (elen w) :: acc) := by rw [← hpre]; exact Hscs
          obtain ⟨-, Hscs2⟩ := (scs_denot_app segs base E pre _).mp Hscs'
          obtain ⟨Hd, -⟩ := (scs_denot_cons segs base E _ acc).mp Hscs2
          obtain ⟨-, -, Hdis⟩ := Hd
          rw [elenZ_elen E n Hn8, elenZ_elen E w (by omega)] at Hdis
          exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LMiss scs hh)
            Hfk Hfr Hdis hIH Hscs Hfr
      by_cases hap : ranges_apart kn rb rk (n : Int) kb kk (w : Int) = true
      · rw [ite_eq_left hap]
        have hdis := ranges_apart_sound segs E base kn rb rk (n : Int) kb kk (w : Int) Hkn hap
        have hIH := IH base rb rk n sx hints acc Hkn Hlf' Hn1 Hn8
        generalize hres : log_lookup kn rest rb rk n sx hints acc = res at hIH ⊢
        cases res with
        | LStuck => exact trivial
        | LHit v' scs hh =>
          simp only [log_hit_ok] at ⊢
          intro Hscs Hfr
          exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LHit v' scs hh)
            Hfk Hfr hdis hIH Hscs Hfr
        | LMiss scs hh =>
          simp only [log_hit_ok] at ⊢
          intro Hscs Hfr
          exact log_hit_ok_wbytes segs E base kb kk w v rest rb rk n sx (.LMiss scs hh)
            Hfk Hfr hdis hIH Hscs Hfr
      · rw [ite_eq_right hap]
        cases hints with
        | nil => exact hgen []
        | cons hd hs =>
          cases hd with
          | false => exact trivial
          | true => exact hgen hs

/-! ### The knowledge byte lookups

    `know_byte_lit_sound`, `know_bytes_lit_sound`, `know_lookupA_sound`,
    `know_lookup_sound`.  These are the knowledge-side counterparts of the
    log block above; `know_lookup_sound` is the second half of the load
    path of `sym_step_sound`. -/

/-- Every `byte` value is in `[0, 256)`. -/
theorem u8_range (b : byte) : 0 ≤ bv_unsigned b ∧ bv_unsigned b < 256 := by
  have h : b.toNat < 256 := by
    have h' := b.isLt
    have h2 : ((2 : Nat) ^ 8) = 256 := by decide
    rw [h2] at h'
    exact h'
  have hb : bv_unsigned b = (b.toNat : Int) := rfl
  rw [hb]
  constructor <;> omega

/-- `Z_to_bv` at the unsigned reading of a byte is the byte. -/
theorem Z_to_bv8_unsigned (b : byte) : Z_to_bv 8 (bv_unsigned b) = b := by
  have h : bv_unsigned b = (b.toNat : Int) := rfl
  rw [h]
  show BitVec.ofInt 8 (b.toNat : Int) = b
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- An in-range read starts at a nonnegative offset. -/
theorem rel_inside_nonneg (rk kk : Int) (d : Int) (hkk : kk ≤ rk) (hd : d = rk - kk) :
    0 ≤ d := by omega

/-- An in-range read of `n` bytes ends inside the known extent. -/
theorem rel_inside_le (rk kk n a : Int) (d : Int) (hrn : rk + n ≤ kk + a) (hd : d = rk - kk) :
    d + n ≤ a := by omega

/-- The one-byte instance of `rel_inside_le`. -/
theorem rel_inside_lt (rk kk a : Int) (d : Int) (hrn : rk + 1 ≤ kk + a) (hd : d = rk - kk) :
    d < a := by omega

/-- One literal byte out of the knowledge.   -/
theorem know_byte_lit_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) :
    ∀ (rb : expr) (rk : Int) (b : Int),
      know_ok segs E base kn → know_byte_lit segs kn rb rk = some b → flat E (SA rb rk) 1 →
      rdn segs base (adenot E (SA rb rk)) 1 = some [Z_to_bv 8 b] ∧ 0 ≤ b ∧ b < 256 := by
  induction kn with
  | nil =>
    intro rb rk b Hkn H Hfr
    simp only [know_byte_lit] at H
    exact absurd H (by simp)
  | cons K rest IH =>
    intro rb rk b Hkn H Hfr
    have HK : kentry_ok segs E base K := Hkn K List.mem_cons_self
    have Hrest : know_ok segs E base rest := fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    have HIH : know_byte_lit segs rest rb rk = some b →
        rdn segs base (adenot E (SA rb rk)) 1 = some [Z_to_bv 8 b] ∧ 0 ≤ b ∧ b < 256 :=
      fun h => IH rb rk b Hrest h Hfr
    have ha : adenot E (SA rb rk) = Z_to_bv 64 (estart E (SA rb rk)) := by
      rw [← flat_u E (SA rb rk) 1 Hfr]
      exact (Z_to_bv_unsigned (adenot E (SA rb rk))).symm
    cases K with
    | KWord a w v =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_byte_lit] at H
      cases v with
      | ELit z =>
        cases hrel : rel_lit rb rk 1 kb kk (w : Int) with
        | RInside d =>
          simp only [hrel] at H
          rw [Option.some.injEq] at H
          obtain ⟨heq, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk 1 kb kk (w : Int) d hrel
          subst heq
          obtain ⟨Hkw8, Hfk, Hrd⟩ := HK
          have hd0 : 0 ≤ d := rel_inside_nonneg rk kk d hkk hd
          refine ⟨?_, ?_, ?_⟩
          · rw [← H]
            have hshift := adenot_shift E (SA rb kk) (SA rb rk) (w : Int) 1 d Hfk Hfr hst (by omega)
            rw [hshift]
            rw [rdn_slice segs base w (adenot E (SA rb kk))
              (word_to_le_bytes w (edenot E (.ELit z))) d.toNat 1 Hrd (by
                have h1 : (d.toNat : Int) + 1 ≤ (w : Int) := by
                  rw [Int.toNat_of_nonneg hd0]
                  exact rel_inside_le rk kk (1 : Int) (w : Int) d hrn hd
                omega)]
            rw [word_byte_at w d.toNat (edenot E (.ELit z)) (by omega),
              byte_at_lit_eq E d hd0 z]
          · rw [← H]; omega
          · rw [← H]; omega
        | RDisjoint => simp only [hrel] at H; exact HIH H
        | RPartial => simp only [hrel] at H; exact HIH H
        | RUnknown => simp only [hrel] at H; exact HIH H
      | EVar n1 => simp only [] at H; exact HIH H
      | EAlu op x y => simp only [] at H; exact HIH H
      | EAluw op x y => simp only [] at H; exact HIH H
      | EMd op x y => simp only [] at H; exact HIH H
      | EMdw op x y => simp only [] at H; exact HIH H
      | EExt s l w1 e1 => simp only [] at H; exact HIH H
      | EBlob s k2 i w1 => simp only [] at H; exact HIH H
    | KZero a len =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_byte_lit] at H
      cases len with
      | ELit l0 =>
        cases hrel : rel_lit rb rk 1 kb kk (l0 % two64) with
        | RInside d =>
          simp only [hrel] at H
          rw [Option.some.injEq] at H
          obtain ⟨heq, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk 1 kb kk (l0 % two64) d hrel
          subst heq
          obtain ⟨Hfk, Hz⟩ := HK
          rw [elenZ_lit] at Hz
          have hd0 : 0 ≤ d := rel_inside_nonneg rk kk d hkk hd
          refine ⟨?_, ?_, ?_⟩
          · rw [← H]
            have hmem : base (adenot E (SA rb rk)) = some (Z_to_bv 8 0) := by
              rw [ha, hst]
              exact Hz d hd0 (rel_inside_lt rk kk (l0 % two64) d hrn hd)
            exact rdn_one segs base (adenot E (SA rb rk)) (Z_to_bv 8 0)
              (by simp only [SeqExec.rdn_byte, hmem])
          · rw [← H]; omega
          · rw [← H]; omega
        | RDisjoint => simp only [hrel] at H; exact HIH H
        | RPartial => simp only [hrel] at H; exact HIH H
        | RUnknown => simp only [hrel] at H; exact HIH H
      | EVar nn => simp only [] at H; exact HIH H
      | EAlu op x y => simp only [] at H; exact HIH H
      | EAluw op x y => simp only [] at H; exact HIH H
      | EMd op x y => simp only [] at H; exact HIH H
      | EMdw op x y => simp only [] at H; exact HIH H
      | EExt s l w1 e1 => simp only [] at H; exact HIH H
      | EBlob s k2 i w1 => simp only [] at H; exact HIH H
    | KFill a len c =>
      obtain ⟨kb, kk⟩ := a
      simp only [know_byte_lit] at H
      cases len with
      | ELit l0 =>
        cases hrel : rel_lit rb rk 1 kb kk (l0 % two64) with
        | RInside d =>
          simp only [hrel] at H
          rw [Option.some.injEq] at H
          obtain ⟨heq, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk 1 kb kk (l0 % two64) d hrel
          subst heq
          obtain ⟨Hfk, Hz⟩ := HK
          rw [elenZ_lit] at Hz
          have hd0 : 0 ≤ d := rel_inside_nonneg rk kk d hkk hd
          refine ⟨?_, ?_, ?_⟩
          · rw [← H, Z_to_bv8_mod]
            have hmem : base (adenot E (SA rb rk)) = some (Z_to_bv 8 c) := by
              rw [ha, hst]
              exact Hz d hd0 (rel_inside_lt rk kk (l0 % two64) d hrn hd)
            exact rdn_one segs base (adenot E (SA rb rk)) (Z_to_bv 8 c)
              (by simp only [SeqExec.rdn_byte, hmem])
          · rw [← H]; exact Int.emod_nonneg _ (by decide)
          · rw [← H]; exact Int.emod_lt_of_pos _ (by decide)
        | RDisjoint => simp only [hrel] at H; exact HIH H
        | RPartial => simp only [hrel] at H; exact HIH H
        | RUnknown => simp only [hrel] at H; exact HIH H
      | EVar nn => simp only [] at H; exact HIH H
      | EAlu op x y => simp only [] at H; exact HIH H
      | EAluw op x y => simp only [] at H; exact HIH H
      | EMd op x y => simp only [] at H; exact HIH H
      | EMdw op x y => simp only [] at H; exact HIH H
      | EExt s l w1 e1 => simp only [] at H; exact HIH H
      | EBlob s k2 i w1 => simp only [] at H; exact HIH H
    | KImg lo hi =>
      simp only [know_byte_lit] at H
      cases rb with
      | ELit z =>
        by_cases hz : z = 0
        · subst hz
          simp only [know_byte_lit] at H
          by_cases hr : (decide (lo ≤ rk) && decide (rk < hi)) = true
          · rw [ite_eq_left hr] at H
            rcases (Bool.and_eq_true ..).mp hr with ⟨h1, h2⟩
            have h1' : lo ≤ rk := of_decide_eq_true h1
            have h2' : rk < hi := of_decide_eq_true h2
            cases hrom : seg_rom segs (Z_to_bv 64 rk) with
            | none => rw [hrom] at H; exact absurd H (by simp)
            | some bb =>
              rw [hrom] at H
              rw [Option.some.injEq] at H
              obtain ⟨Hlo0, Hhi64, Hnone⟩ := HK
              rw [← H]
              refine ⟨?_, u8_range bb⟩
              · have Haz : adenot E (SA (.ELit 0) rk) = Z_to_bv 64 rk := by
                  rw [ha, estart_lit0]
                have hbyte : SeqExec.rdn_byte segs base (adenot E (SA (.ELit 0) rk)) = some bb := by
                  simp only [SeqExec.rdn_byte, Haz, Hnone rk h1' h2', hrom]
                rw [Z_to_bv8_unsigned bb]
                exact rdn_one segs base (adenot E (SA (.ELit 0) rk)) bb hbyte
          · rw [ite_eq_right hr] at H; exact HIH H
        · split at H
          · rename_i heq
            exact absurd (by injection heq : z = 0) hz
          · rename_i _
            exact HIH H
      | EVar n1 => simp only [] at H; exact HIH H
      | EAlu op x y => simp only [] at H; exact HIH H
      | EAluw op x y => simp only [] at H; exact HIH H
      | EMd op x y => simp only [] at H; exact HIH H
      | EMdw op x y => simp only [] at H; exact HIH H
      | EExt s l w1 e1 => simp only [] at H; exact HIH H
      | EBlob s k2 i w1 => simp only [] at H; exact HIH H
    | KBlob a nn k => simp only [know_byte_lit] at H; exact HIH H
    | KAlign e m => simp only [know_byte_lit] at H; exact HIH H
    | KRange e lo hi => simp only [know_byte_lit] at H; exact HIH H
    | KWr a nn => simp only [know_byte_lit] at H; exact HIH H
    | KDisj a1 n1 a2 n2 => simp only [know_byte_lit] at H; exact HIH H
    | KUnk a nn => simp only [know_byte_lit] at H; exact HIH H

/-- `n` literal bytes out of the knowledge.   -/
theorem know_bytes_lit_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (n : Nat) :
    ∀ (rb : expr) (rk : Int) (zs : List Int),
      know_ok segs E base kn → know_bytes_lit segs kn rb rk n = some zs →
      flat E (SA rb rk) (n : Int) →
      ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.map bv_unsigned = zs := by
  induction n with
  | zero =>
    intro rb rk zs Hkn H Hfr
    simp only [know_bytes_lit, Option.some.injEq] at H
    rw [← H]
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro rb rk zs Hkn H Hfr
    simp only [know_bytes_lit] at H
    generalize hb : know_byte_lit segs kn rb rk = bb at H
    generalize hr : know_bytes_lit segs kn rb (rk + 1) n = rr at H
    cases bb with
    | none => exact absurd H (by simp)
    | some b =>
      cases rr with
      | none => exact absurd H (by simp)
      | some r =>
        simp only [Option.some.injEq] at H
        rw [← H]
        have Hf1 : flat E (SA rb rk) 1 :=
          flat_mono E (SA rb rk) ((n + 1 : Nat) : Int) 1 Hfr ⟨by omega, by omega⟩
        obtain ⟨H1, Hb8⟩ := know_byte_lit_sound segs E base kn rb rk b Hkn hb Hf1
        have hb8' : bv_unsigned (Z_to_bv 8 b) = b := by
          rw [u8_lit, Int.emod_eq_of_lt Hb8.1 Hb8.2]
        cases n with
        | zero =>
          simp only [know_bytes_lit, Option.some.injEq] at hr
          rw [← hr]
          refine ⟨[Z_to_bv 8 b], H1, ?_⟩
          simp only [List.map_cons, List.map_nil, hb8']
        | succ n' =>
          have Hfn : flat E (SA rb (rk + 1)) ((n' + 1 : Nat) : Int) := flat_step E rb rk n' Hfr
          obtain ⟨bs', Hn, Hmap⟩ := ih rb (rk + 1) r Hkn hr Hfn
          have hadd : adenot E (SA rb rk) + 1 = adenot E (SA rb (rk + 1)) :=
            adenot_add_one E rb rk Hfr.1 Hfr.2.1
          have Hn' : rdn segs base (adenot E (SA rb rk) + 1) (n' + 1) = some bs' := by
            rw [hadd]; exact Hn
          refine ⟨Z_to_bv 8 b :: bs', ?_, ?_⟩
          · exact rdn_cons1 segs base (adenot E (SA rb rk)) (n' + 1) (Z_to_bv 8 b) bs' H1 Hn'
          · simp only [List.map_cons, Hmap, hb8']

/-- `know_lookupA_sound`: the byte-composition layer of the
    knowledge lookup is sound. -/
theorem know_lookupA_sound (allkn : List kentry) (segs : List Segment) (kn : List kentry)
    (E : env) (M0 : word → Option byte) (base : word → Option byte) :
    ∀ (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond),
      know_ok segs E M0 allkn → know_ok segs E base kn → 1 ≤ n → n ≤ 8 →
      hit_ok segs base E rb rk n sx (know_lookupA allkn segs kn rb rk n sx hints acc) := by
  intro rb rk n sx hints acc Hall Hkn Hn1 Hn8
  simp only [know_lookupA]
  have H0 := know_lookupA0_sound segs E M0 allkn base kn rb rk n sx hints acc Hall Hkn Hn1 Hn8
  generalize h0 : know_lookupA0 allkn segs kn rb rk n sx hints acc = r0
  rw [h0] at H0
  cases r0 with
  | LHit v scs h =>
    simp only [hit_ok] at H0 ⊢
    exact H0
  | LMiss scs h =>
    generalize hbl : know_bytes_lit segs kn rb rk n = bl
    cases bl with
    | none => exact H0
    | some zs =>
      simp only [hit_ok]
      intro Hscs Hfr
      obtain ⟨bs, Hbs, Hmap⟩ :=
        know_bytes_lit_sound segs E base kn n rb rk zs Hkn hbl Hfr
      refine ⟨bs, Hbs, rdn_length segs _ n _ bs Hbs, ?_⟩
      show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (lit_of_bytes sx n zs)
      unfold lit_of_bytes
      show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
        = Z_to_bv 64 (if sx then bv_swrap (8 * n) (zbytes_le_to_Z zs) else zbytes_le_to_Z zs)
      rw [← Hmap, zbytes_map]
      show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))
        = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs % 2 ^ 64))
      unfold extz
      cases sx with
      | false => simp only [Bool.false_eq_true, ite_false]; rw [Z_to_bv_emod64]
      | true => simp only [ite_true]; rw [bv_swrap_emod64 (8 * n) (by omega)]
  | LStuck => exact trivial

/-- `know_lookup_sound`: the knowledge lookup is sound.  Together
    with `log_lookup_sound` this is the load path of `sym_step_sound`. -/
theorem know_lookup_sound (segs : List Segment) (E : env) (kn : List kentry)
    (base : word → Option byte) :
    ∀ (rb : expr) (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond),
      know_ok segs E base kn → 1 ≤ n → n ≤ 8 →
      hit_ok segs base E rb rk n sx (know_lookup segs kn rb rk n sx hints acc) := by
  intro rb rk n sx hints acc Hkn Hn1 Hn8
  exact know_lookupA_sound kn segs kn E base base rb rk n sx hints acc Hkn Hkn Hn1 Hn8

/-! ### Part P5a, opening: address denotations -/

/-- `Z_to_bv` of the unsigned reading is the value itself.   -/
theorem Z_to_bv64_u (z : Int) : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 z :=
  Z_to_bv_unsigned (Z_to_bv 64 z)

/-- `Z_to_bv 64` cannot see the reduction mod `2^64`.   -/
theorem Z_to_bv64_mod (z : Int) : Z_to_bv 64 (z % 2 ^ 64) = Z_to_bv 64 z :=
  Z_to_bv_emod64 z

/-- `Z_to_bv` is determined by the argument modulo `2^64`. -/
theorem Z_to_bv64_eq_of_emod (a b : Int) (h : a % 2 ^ 64 = b % 2 ^ 64) :
    Z_to_bv 64 a = Z_to_bv 64 b := by
  rw [← Z_to_bv_emod64 a, ← Z_to_bv_emod64 b, h]

/-- Dropping an inner reduction mod `2^64` under a sum. -/
theorem emod_add_mod (a c : Int) :
    (a % 2 ^ 64 + c) % 2 ^ 64 = (a + c) % 2 ^ 64 := by
  rw [Int.add_emod a c, Int.add_emod (a % 2 ^ 64) c, Int.emod_emod]

/-- Reducing the middle of a three-term sum modulo `2^64` is invisible. -/
theorem emod_add_emod_gen (a b c : Int) :
    ((a + b % 2 ^ 64) + c) % 2 ^ 64 = ((a + b) + c) % 2 ^ 64 := by
  rw [Int.add_emod (a + b % 2 ^ 64) c, Int.add_emod (a + b) c,
      Int.add_emod a (b % 2 ^ 64), Int.add_emod a b, Int.emod_emod]

/-- The address an `saddr` normal form denotes.   -/
theorem to_saddr_denot (E : env) (e : expr) (imm : Int) :
    adenot E (to_saddr e imm) = v_addi (edenot E e) imm := by
  have hgen : ∀ (b : expr) (k : Int), split_lit e = (b, k) →
      adenot E (SA b (k + imm)) = v_addi (edenot E e) imm := by
    intro b k hs
    show Z_to_bv 64 (bv_unsigned (edenot E b) + (k + imm))
       = Z_to_bv 64 (bv_unsigned (edenot E e) + imm)
    apply Z_to_bv64_eq_of_emod
    cases e with
    | ELit z =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk]
      rw [show bv_unsigned (edenot E (.ELit 0)) = 0 from u_lit0,
          show bv_unsigned (edenot E (.ELit z)) = z % 2 ^ 64 from u_lit64a z,
          Int.zero_add, emod_add_mod z imm]
    | EVar n1 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
    | EAlu op a1 a2 =>
      cases op with
      | ADD =>
        cases a2 with
        | ELit z =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk]
          have hu : bv_unsigned (edenot E (.EAlu .ADD a1 (.ELit z)))
              = (bv_unsigned (edenot E a1) + z % 2 ^ 64) % 2 ^ 64 := by
            show bv_unsigned ((edenot E a1) + (Z_to_bv 64 z)) = _
            rw [u_add64, u_lit64a]
          rw [hu, emod_add_mod (bv_unsigned (edenot E a1) + z % 2 ^ 64) imm,
            ← Int.add_assoc, ← emod_add_emod_gen (bv_unsigned (edenot E a1)) z imm]
        | EVar n2 =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EAlu op2 x y =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EAluw op2 x y =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EMd op2 x y =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EMdw op2 x y =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EExt s l w2 e2 =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
        | EBlob s k2 i w2 =>
          obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
          rw [← hb, ← hk, Int.zero_add]
      | SUB =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | SLL =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | SLT =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | SLTU =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | XOR =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | SRL =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | SRA =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | OR =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
      | AND =>
        obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
        rw [← hb, ← hk, Int.zero_add]
    | EAluw op a1 a2 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
    | EMd op a1 a2 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
    | EMdw op a1 a2 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
    | EExt s l w1 e1 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
    | EBlob s k2 i w1 =>
      obtain ⟨hb, hk⟩ := Prod.mk.inj (by simpa only [split_lit] using hs)
      rw [← hb, ← hk, Int.zero_add]
  exact hgen (split_lit e).1 (split_lit e).2 rfl

/-! ## Part P5a: the alignment-mask block

    `and_highmask_val` / `and_mask_id` / `and_lowmask_zero` are the three
    identities `mkAnd`'s aligned split uses, and `coeffs_divk_sound` +
    `lin_lowbits_kn_sound` are the alignment-aware counterparts of
    `coeffs_div_sound` / `lin_lowbits_sound`. -/

/-- `bv_unsigned` determines a `word`.   -/
theorem word_eq_of_bv_unsigned {a b : word} (h : bv_unsigned a = bv_unsigned b) : a = b := by
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj h)

/-- `-2^j` reads as the high mask `2^64 - 2^j` at 64 bits. -/
theorem bv_unsigned_neg_pow2 (j : Int) (Hj : 0 ≤ j) (Hj64 : j < 64) :
    bv_unsigned (Z_to_bv 64 (-(zpow 2 j))) = 2 ^ 64 - zpow 2 j := by
  have hz : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := natCast_pow_two j.toNat
  have hpos : (0 : Int) < zpow 2 j := by
    rw [hz]; exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hlt : zpow 2 j < 2 ^ 64 := by
    rw [hz, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from natCast_pow_two 64]
    exact Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide) (by rw [Int.toNat_lt Hj]; exact Hj64))
  rw [u_lit64a,
    show -(zpow 2 j) = 2 ^ 64 - zpow 2 j - 2 ^ 64 from by omega,
    Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod,
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- `and_highmask_val`: `AND` with a high mask rounds down to a
    multiple of `2^j`. -/
theorem and_highmask_val (v : word) (j : Int) (Hj : 0 ≤ j) (Hj64 : j < 64) :
    alu64 .AND v (Z_to_bv 64 (-(zpow 2 j)))
      = Z_to_bv 64 (bv_unsigned v - bv_unsigned v % zpow 2 j) := by
  have hz : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := natCast_pow_two j.toNat
  have hpos : (0 : Int) < zpow 2 j := by
    rw [hz]; exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hlt : zpow 2 j ≤ 2 ^ 64 := by
    rw [hz, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from natCast_pow_two 64]
    exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))
  have hv1 : 0 ≤ bv_unsigned v := (u64_range v).1
  have hv2 : bv_unsigned v < 2 ^ 64 := (u64_range v).2
  have hmod0 : 0 ≤ bv_unsigned v % zpow 2 j := Int.emod_nonneg _ (by omega)
  have hmodle : bv_unsigned v % zpow 2 j ≤ bv_unsigned v :=
    emod_le_self _ _ hv1 hpos
  apply word_eq_of_bv_unsigned
  rw [u_and64, bv_unsigned_neg_pow2 j Hj Hj64,
    land_highmask (bv_unsigned v) j ⟨Hj, Hj64⟩ ⟨hv1, hv2⟩]
  rw [u_small]
  omega

/-- `and_mask_id`: an already-aligned value survives the high
    mask. -/
theorem and_mask_id (v : word) (j : Int) (Hj : 0 ≤ j) (Hj64 : j < 64)
    (Hmod : bv_unsigned v % zpow 2 j = 0) :
    alu64 .AND v (Z_to_bv 64 (-(zpow 2 j))) = v := by
  apply word_eq_of_bv_unsigned
  rw [u_and64, bv_unsigned_neg_pow2 j Hj Hj64,
    land_align_mask (bv_unsigned v) j ⟨Hj, Hj64⟩ (u64_range v) Hmod]

/-- `and_lowmask_zero`: `AND` with a low mask clears a value whose
    low `j` bits are zero. -/
theorem and_lowmask_zero (v : word) (j : Int) (Hj : 0 ≤ j) (Hj64 : j ≤ 64)
    (Hd : zpow 2 j ∣ bv_unsigned v) :
    alu64 .AND v (Z_to_bv 64 (zpow 2 j - 1)) = Z_to_bv 64 0 := by
  rw [and_lowmask_val v j Hj Hj64, Int.emod_eq_zero_of_dvd Hd]

/-- `coeffs_divk_sound`: every term of a linear form is a multiple
    of `m`, judging by its coefficient alone or by the coefficient times the
    atom's known alignment. -/
theorem coeffs_divk_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (m : Int) (ts : List (Int × expr))
    (Hkn : know_ok segs E M kn) (Hm : 0 < m) (H : coeffs_divk kn m ts = true) :
    tden E ts % m = 0 := by
  induction ts with
  | nil => rw [tden_nil]; exact Int.zero_emod m
  | cons hd rest ih =>
    obtain ⟨k, a⟩ := hd
    rw [coeffs_divk, Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    have hka : k * uE E a % m = 0 := by
      rw [Bool.or_eq_true] at H1
      cases H1 with
      | inl h1 =>
        have hk : k % m = 0 := beq_iff_eq.mp h1
        rw [Int.mul_emod, hk, Int.zero_mul, Int.zero_emod]
      | inr h1 =>
        have hkm : (k * zpow 2 (ealign kn a)) % m = 0 := beq_iff_eq.mp h1
        obtain ⟨q, hq⟩ := (ealign_sound segs E M kn a Hkn).2
        have hmul : k * uE E a = q * (k * zpow 2 (ealign kn a)) := by
          simp only [uE]
          rw [hq]
          ac_rfl
        rw [hmul, Int.mul_emod, hkm, Int.mul_zero, Int.zero_emod]
    have hrest : tden E rest % m = 0 := ih H2
    rw [tden_cons, Int.add_emod, hka, hrest, Int.zero_add, Int.zero_emod]

/-- `lin_lowbits_kn_sound`: the knowledge-aware low-bits read is
    sound (`lin_lowbits_sound` plus the `pageup_low` fallback). -/
theorem lin_lowbits_kn_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (k v : Int) (Hkn : know_ok segs E M kn)
    (Hk : 0 ≤ k ∧ k ≤ 64) (H : lin_lowbits_kn kn e k = some v) :
    bv_unsigned (edenot E e) % zpow 2 k = v ∧ 0 ≤ v ∧ v < zpow 2 k := by
  have hp : 0 < zpow 2 k := by
    unfold zpow
    exact two_pow_pos_int k.toNat
  by_cases hd : coeffs_divk kn (zpow 2 k) (lin_of e).2 = true
  · have hv : v = (lin_of e).1 % zpow 2 k := by
      simp only [lin_lowbits_kn] at H
      rw [ite_eq_left hd] at H
      exact (Option.some.inj H).symm
    have hcd : tden E (lin_of e).2 % zpow 2 k = 0 :=
      coeffs_divk_sound segs E M kn (zpow 2 k) (lin_of e).2 Hkn hp hd
    have hsplit : lden E (lin_of e) % zpow 2 k = (lin_of e).1 % zpow 2 k := by
      simp only [lden]
      rw [Int.add_emod, hcd, Int.add_zero, Int.emod_emod]
    have Hm := eqm_mod_pow2 (lden E (lin_of e)) (uE E e) k Hk (lin_of_sound E e)
    simp only [uE] at Hm
    have h1 : bv_unsigned (edenot E e) % zpow 2 k = (lin_of e).1 % zpow 2 k :=
      Hm.symm.trans hsplit
    refine ⟨?_, ?_, ?_⟩
    · rw [hv]; exact h1
    · rw [hv]; exact Int.emod_nonneg _ (by omega)
    · rw [hv]; exact Int.emod_lt_of_pos _ hp
  · have hpage : pageup_low e (zpow 2 k) = some v := by
      simp only [lin_lowbits_kn] at H
      rw [ite_eq_right hd] at H
      exact H
    exact pageup_low_sound E e (zpow 2 k) k v Hk rfl hpage

/-! ### The folding / denotation of the smart ALU constructors


    `zfast`/`zfastw`/`zfastm` are this tree's bit-sliced re-implementations of
    the closed evaluation `zalu`/`zaluw`/`zmd`; `zfast_eq` and friends say
    they agree on the canonical window, which is what makes the literal
    folding of `mkAlu`/`mkMd` transparent.  `mkAlu_denot` is the denotation
    of the smart ALU constructor. -/
theorem ldiv_terms_sound (E : env) (m : Int) (ts : List (Int × expr))
    (Hm : 0 < m) (H : coeffs_div m ts = true) :
    tden E ts = m * tden E (ldiv_terms m ts) := by
  induction ts with
  | nil => rw [tden_nil, ldiv_terms, tden_nil, Int.mul_zero]
  | cons hd rest ih =>
    obtain ⟨k, a⟩ := hd
    rw [coeffs_div, Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    have hk : k % m = 0 := beq_iff_eq.mp H1
    have hkm : k = k / m * m := by
      have h := Int.ediv_mul_add_emod k m
      rw [hk, Int.add_zero] at h
      exact h.symm
    have hstep : k * uE E a = m * (k / m * uE E a) := by
      conv => lhs; rw [hkm]
      rw [Int.mul_right_comm (k / m) m (uE E a),
        Int.mul_comm (k / m * uE E a) m]
    rw [tden_cons, ldiv_terms, tden_cons, ih H2, Int.mul_add, ← hstep]
theorem wrap64_range (z : Int) : 0 ≤ wrap64 z ∧ wrap64 z < 2 ^ 64 := by
  rw [wrap64_mod]
  exact ⟨Int.emod_nonneg _ (Int.ne_of_gt (two_pow_pos_int 64)),
    Int.emod_lt_of_pos _ (two_pow_pos_int 64)⟩
theorem Z_to_bv_wrap64 (z : Int) : Z_to_bv 64 (wrap64 z) = Z_to_bv 64 z := by
  rw [wrap64_mod]
  exact Z_to_bv_emod64 z

/-- `zfast_eq`: the bit-sliced `zfast` is `zalu` on the window. -/
theorem zfast_eq (op : AluOp) (x y : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hy : 0 ≤ y ∧ y < 2 ^ 64) :
    zfast op x y = zalu op x y := by
  have hx : bv_unsigned (Z_to_bv 64 x) = x := u_small Hx
  have hy : bv_unsigned (Z_to_bv 64 y) = y := u_small Hy
  cases op with
  | ADD =>
    show (if x + y < 2 ^ 64 then x + y else x + y - 2 ^ 64)
      = bv_unsigned (Z_to_bv 64 x + Z_to_bv 64 y)
    rw [u_add64, hx, hy]
    by_cases h : x + y < 2 ^ 64
    · rw [ite_eq_left h, Int.emod_eq_of_lt (by omega) h]
    · rw [ite_eq_right h]
      have h3 : (x + y) % 2 ^ 64 = (x + y - 2 ^ 64) % 2 ^ 64 := by
        rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod]
      rw [h3, Int.emod_eq_of_lt (by omega) (by omega)]
  | SUB =>
    show (if 0 ≤ x - y then x - y else x - y + 2 ^ 64)
      = bv_unsigned (Z_to_bv 64 x - Z_to_bv 64 y)
    rw [u_sub64, hx, hy]
    by_cases h : 0 ≤ x - y
    · rw [ite_eq_left h, Int.emod_eq_of_lt h (by omega)]
    · rw [ite_eq_right h]
      have h3 : (x - y) % 2 ^ 64 = (x - y + 2 ^ 64) % 2 ^ 64 := by
        rw [show x - y + 2 ^ 64 = (x - y) + 1 * 2 ^ 64 from by omega,
          Int.add_mul_emod_self_right]
      rw [h3, Int.emod_eq_of_lt (by omega) (by omega)]
  | AND =>
    show AxSymExec3.zland x y = bv_unsigned (alu64 .AND (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [u_and64, hx, hy]
  | OR =>
    show AxSymExec3.zlor x y = bv_unsigned (alu64 .OR (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [u_or64, hx, hy]
  | XOR =>
    show AxSymExec3.zlxor x y = bv_unsigned (alu64 .XOR (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [u_xor64, hx, hy]
  | SLL =>
    show AxSymExec3.land64 (AxSymExec3.zshiftl x (AxSymExec3.zland y 63).toNat)
      = bv_unsigned (alu64 .SLL (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [land64_eq, land_63, u_sll64, hx, hy]
    simp only [AxSymExec3.zshiftl]
    rw [two64_eq]
  | SRL =>
    show AxSymExec3.zshiftr x (AxSymExec3.zland y 63).toNat
      = bv_unsigned (alu64 .SRL (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [land_63, u_srl64, hx, hy]
    simp only [AxSymExec3.zshiftr]
  | SLTU =>
    show (if x < y then 1 else 0)
      = bv_unsigned (alu64 .SLTU (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [u_sltu64]
    unfold bv_ltu
    have hxN : (Z_to_bv 64 x).toNat = x.toNat := by
      simpa using congrArg Int.toNat hx
    have hyN : (Z_to_bv 64 y).toNat = y.toNat := by
      simpa using congrArg Int.toNat hy
    rw [hxN, hyN]
    have hiff : (x.toNat < y.toNat) ↔ x < y := by
      rw [Int.lt_toNat, Int.toNat_of_nonneg Hx.1]
    simp only [decide_eq_true_iff, hiff]
  | SLT => rfl
  | SRA => rfl

/-- `bv_unsigned` of the M-extension's `v_mul`. -/
theorem u_v_mul (a b : word) :
    bv_unsigned (v_mul a b) = (bv_unsigned a * bv_unsigned b) % 2 ^ 64 := by
  unfold v_mul
  rw [u_lit64a]
theorem zfastm_eq (op : MulOp) (x y : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hy : 0 ≤ y ∧ y < 2 ^ 64) :
    zfastm op x y = zmd op x y := by
  have hx : bv_unsigned (Z_to_bv 64 x) = x := u_small Hx
  have hy : bv_unsigned (Z_to_bv 64 y) = y := u_small Hy
  cases op with
  | MUL =>
    show AxSymExec3.land64 (x * y)
      = bv_unsigned (mul_div .MUL (Z_to_bv 64 x) (Z_to_bv 64 y))
    rw [land64_eq, m_mul, u_v_mul, hx, hy, two64_eq]
  | MULH => rfl
  | MULHSU => rfl
  | MULHU => rfl
  | DIV => rfl
  | DIVU => rfl
  | REM => rfl
  | REMU => rfl
theorem zalu_l_eq (op : AluOp) (x y : Int) : zalu_l op x y = zalu op x y := by
  unfold zalu_l
  rw [zfast_eq op _ _ (wrap64_range x) (wrap64_range y)]
  show bv_unsigned (alu64 op (Z_to_bv 64 (wrap64 x)) (Z_to_bv 64 (wrap64 y)))
    = bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y))
  rw [Z_to_bv_wrap64, Z_to_bv_wrap64]
theorem zmd_l_eq (op : MulOp) (x y : Int) : zmd_l op x y = zmd op x y := by
  unfold zmd_l
  rw [zfastm_eq op _ _ (wrap64_range x) (wrap64_range y)]
  show bv_unsigned (mul_div op (Z_to_bv 64 (wrap64 x)) (Z_to_bv 64 (wrap64 y)))
    = bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y))
  rw [Z_to_bv_wrap64, Z_to_bv_wrap64]

/-! ### `mkAlu` denotation -/

/-- `2^6 = 64`, at `Int`. -/
theorem two_pow_six : (2 : Int) ^ 6 = 64 := by decide

/-- The `SLL` arm of `mkAlu`: the shift-amount normalisation denotes the same
    as the plain `ALU_SLL` . -/
theorem mkAlu_sll_denot (E : env) (a b : expr) :
    edenot E (match shamt_of b 6 with
              | some s => unlin (lscale (zpow 2 s) (lin_of a))
              | none => .EAlu .SLL a b)
      = alu64 .SLL (edenot E a) (edenot E b) := by
  cases hs : shamt_of b 6 with
  | none => rfl
  | some s =>
    have hz6 : zpow 2 6 = (64 : Int) := by
      unfold zpow
      rw [show (6 : Int).toNat = 6 from rfl]
      exact two_pow_six
    obtain ⟨h1, h2, h3⟩ := shamt_of_sound E b 6 s ⟨by omega, by omega⟩ hs
    rw [hz6] at h1
    rw [hz6] at h3
    exact unlin_lsll_amt E a (edenot E b) s h1

/-- The `SRL`/`SRA` arm of `mkAlu`: replacing the shift amount by its literal
    low bits denotes the same . -/
theorem mkAlu_sr_denot (E : env) (op' : AluOp) (hop : op' = .SRL ∨ op' = .SRA)
    (a b : expr) :
    edenot E (match is_lit b with
              | some _ => .EAlu op' a b
              | none => match shamt_of b 6 with
                        | some s => .EAlu op' a (.ELit s)
                        | none => .EAlu op' a b)
      = alu64 op' (edenot E a) (edenot E b) := by
  cases hb : is_lit b with
  | some y => rfl
  | none =>
    cases hs : shamt_of b 6 with
    | none => rfl
    | some s =>
      have hz6 : zpow 2 6 = (64 : Int) := by
        unfold zpow
        rw [show (6 : Int).toNat = 6 from rfl]
        exact two_pow_six
      obtain ⟨h1, h2, h3⟩ := shamt_of_sound E b 6 s ⟨by omega, by omega⟩ hs
      rw [hz6] at h1
      rw [hz6] at h3
      have hu : bv_unsigned (Z_to_bv 64 s) % 64 = s :=
        u_lit_mod s 64 ⟨h2, by rw [two_pow_six]; exact h3⟩ (Or.inl rfl) h3
      cases hop with
      | inl h =>
        rw [h]
        show alu64 .SRL (edenot E a) (Z_to_bv 64 s)
          = alu64 .SRL (edenot E a) (edenot E b)
        exact alu_srl_amt _ _ _ (by rw [hu, h1])
      | inr h =>
        rw [h]
        show alu64 .SRA (edenot E a) (Z_to_bv 64 s)
          = alu64 .SRA (edenot E a) (edenot E b)
        exact alu_sra_amt _ _ _ (by rw [hu, h1])

/-- The `is_lit b = none` instance of the `SRL`/`SRA` arm. -/
theorem mkAlu_sr_none_denot (E : env) (op' : AluOp) (hop : op' = .SRL ∨ op' = .SRA)
    (a b : expr) (hb : is_lit b = none) :
    edenot E (match shamt_of b 6 with
              | some s => .EAlu op' a (.ELit s)
              | none => .EAlu op' a b)
      = alu64 op' (edenot E a) (edenot E b) := by
  have h := mkAlu_sr_denot E op' hop a b
  rw [hb] at h
  simpa only [] using h

/-- `mkAlu_denot`: the smart ALU constructor denotes the ALU
    operation. -/
theorem mkAlu_denot (E : env) (op : AluOp) (a b : expr) :
    edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b) := by
  unfold mkAlu
  cases ha : is_lit a with
  | some x =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      rw [is_lit_some ha, is_lit_some hb]
      show Z_to_bv 64 (zalu_l op x y) = alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)
      rw [zalu_l_eq]
      show Z_to_bv 64 (bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)))
        = alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)
      exact ofInt_toNat _
    | none =>
      simp only []
      cases op with
      | ADD => simp only [] <;> exact unlin_ladd E a b
      | SUB => simp only [] <;> exact unlin_lsub E a b
      | SLL => simp only [] <;> exact mkAlu_sll_denot E a b
      | SRL => simp only [] <;> exact mkAlu_sr_none_denot E .SRL (Or.inl rfl) a b hb
      | SRA => simp only [] <;> exact mkAlu_sr_none_denot E .SRA (Or.inr rfl) a b hb
      | SLT => simp only [] <;> rfl
      | SLTU => simp only [] <;> rfl
      | XOR => simp only [] <;> rfl
      | OR => simp only [] <;> rfl
      | AND => simp only [] <;> rfl
  | none =>
    simp only []
    cases op with
    | ADD => exact unlin_ladd E a b
    | SUB => exact unlin_lsub E a b
    | SLL => exact mkAlu_sll_denot E a b
    | SRL => exact mkAlu_sr_denot E .SRL (Or.inl rfl) a b
    | SRA => exact mkAlu_sr_denot E .SRA (Or.inr rfl) a b
    | SLT => rfl
    | SLTU => rfl
    | XOR => rfl
    | OR => rfl
    | AND => rfl

/-! ### `mkMd` / `mkMdw` denotation -/

/-- `mkMd_denot`: the smart M-extension constructor denotes the
    M-extension operation. -/
theorem mkMd_denot (E : env) (op : MulOp) (a b : expr) :
    edenot E (mkMd op a b) = mul_div op (edenot E a) (edenot E b) := by
  unfold mkMd
  cases ha : is_lit a with
  | some x =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      rw [is_lit_some ha, is_lit_some hb]
      show Z_to_bv 64 (zmd_l op x y) = mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)
      rw [zmd_l_eq]
      show Z_to_bv 64 (bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)))
        = mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)
      exact ofInt_toNat _
    | none =>
      simp only []
      cases op with
      | MUL => simp only [] <;> (rw [is_lit_some ha]; exact unlin_lmul_l E x b)
      | MULH => simp only [] <;> rfl
      | MULHSU => simp only [] <;> rfl
      | MULHU => simp only [] <;> rfl
      | DIV => simp only [] <;> rfl
      | DIVU => simp only [] <;> rfl
      | REM => simp only [] <;> rfl
      | REMU => simp only [] <;> rfl
  | none =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      cases op with
      | MUL => simp only [] <;> (rw [is_lit_some hb]; exact unlin_lmul_r E a y)
      | MULH => simp only [] <;> rfl
      | MULHSU => simp only [] <;> rfl
      | MULHU => simp only [] <;> rfl
      | DIV => simp only [] <;> rfl
      | DIVU => simp only [] <;> rfl
      | REM => simp only [] <;> rfl
      | REMU => simp only [] <;> rfl
    | none => simp only [] <;> rfl

/-- `mkMdw_denot`: the smart 32-bit M-extension constructor. -/
theorem mkMdw_denot (E : env) (op : MulOp) (a b : expr) :
    edenot E (mkMdw op a b)
      = sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b))) := by
  unfold mkMdw
  cases ha : is_lit a with
  | some x =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      rw [is_lit_some ha, is_lit_some hb]
      show Z_to_bv 64 (zmdw op x y)
        = sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y)))
      unfold zmdw
      exact ofInt_toNat _
    | none => rfl
  | none => rfl

/-! ## Part P4e: the split / low-bit block

    `mkSrl_denot` (the `R3.3` `mkSrl` split), `and_highmask_srl` (R6),
    the mod-`2^j` bit lemmas (`land_mod_pow2`, `lor_mod_pow2`,
    `lxor_mod_pow2`, `mod_pow2_mod_pow2`) and `lowbits_sound` (P-c). -/

/-- `alu64` `SRL` at a shift amount whose low six bits are `sh` is floor
    division by `2^sh`.   -/
theorem alu_srl_div (u y : word) (sh : Int) (Hy : bv_unsigned y % 64 = sh) :
    alu64 .SRL u y = Z_to_bv 64 (bv_unsigned u / zpow 2 sh) := by
  have h := u_srl64 u y
  rw [Hy] at h
  show alu64 .SRL u y = Z_to_bv 64 (bv_unsigned u / 2 ^ sh.toNat)
  rw [← h, Z_to_bv_unsigned]

/-- The value of `unlin x` is the `Z_to_bv` of its linear denotation. -/
theorem edenot_unlin (E : env) (x : lin) :
    edenot E (unlin x) = Z_to_bv 64 (lden E x) := by
  rw [← Z_to_bv_unsigned (edenot E (unlin x))]
  exact eqm_Z_to_bv (unlin_sound E x)

/-- A linear form `c + Σ` that `lin_nowrap_l` accepts denotes exactly its
    `Z` value (`unlin` does not wrap). -/
theorem unlin_val_of_nowrap_l (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : Int) (rts : List (Int × expr))
    (Hkn : know_ok segs E M kn) (H : lin_nowrap_l kn c rts = true) :
    bv_unsigned (edenot E (unlin (c, rts))) = c + tden E rts := by
  have hrng := lin_range_sound E (erange kn)
    (fun a0 lo0 hi0 Ha => erange_sound segs E M kn a0 lo0 hi0 Hkn Ha) c rts
  cases hlr : lin_range (erange kn) c rts with
  | none =>
    rw [lin_nowrap_l, hlr] at H
    exact absurd H (by simp)
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [lin_nowrap_l, hlr] at H
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true ..).mp H
    have hlo : 0 ≤ lo := of_decide_eq_true h1
    have hhi : hi < 2 ^ 64 := by
      have h2' := of_decide_eq_true h2
      rw [two64_eq] at h2'
      exact h2'
    obtain ⟨hb1, hb2⟩ := hrng lo hi hlr
    obtain ⟨hu1, hu2⟩ := u64_range (edenot E (unlin (c, rts)))
    obtain ⟨q, hq⟩ := unlin_sound E (c, rts)
    -- the linear value is in `[0, 2^64)` too, so the quotient is `0`
    have hB1 : 0 ≤ c + tden E rts := by omega
    have hB2 : c + tden E rts < 2 ^ 64 := by omega
    have hm : (2 : Int) ^ 64 ≠ 0 := Int.ne_of_gt (two_pow_pos_int 64)
    have hq' : bv_unsigned (edenot E (unlin (c, rts))) = (c + tden E rts) + q * 2 ^ 64 := hq
    have h1 : bv_unsigned (edenot E (unlin (c, rts))) / 2 ^ 64 = q := by
      rw [hq', Int.add_mul_ediv_right _ _ hm, Int.ediv_eq_zero_of_lt hB1 hB2, Int.zero_add]
    have h2 : bv_unsigned (edenot E (unlin (c, rts))) / 2 ^ 64 = 0 :=
      Int.ediv_eq_zero_of_lt hu1 hu2
    have hz : q = 0 := by rw [← h1, h2]
    rw [hz, Int.zero_mul, Int.add_zero] at hq'
    exact hq'

/-- `mkSrl_denot`: the smart right shift denotes `ALU_SRL`. -/
theorem mkSrl_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (a : expr) (sh : Int) (y : word)
    (Hkn : know_ok segs E M kn) (Hy : bv_unsigned y % 64 = sh) :
    edenot E (mkSrl kn a sh) = alu64 .SRL (edenot E a) y := by
  have hs0 : 0 ≤ sh := by rw [← Hy]; exact Int.emod_nonneg _ (by decide)
  have hs1 : sh < 64 := by rw [← Hy]; exact Int.emod_lt_of_pos _ (by decide)
  have hp : 0 < zpow 2 sh := by
    unfold zpow
    exact two_pow_pos_int sh.toNat
  have hpne : zpow 2 sh ≠ 0 := Int.ne_of_gt hp
  have hup : bv_unsigned (Z_to_bv 64 sh) % 64 = sh :=
    u_lit_mod sh 64 ⟨hs0, by rw [two_pow_six]; exact hs1⟩ (Or.inl rfl) hs1
  have Hlit0 : edenot E (mkAlu .SRL a (.ELit sh)) = alu64 .SRL (edenot E a) y := by
    rw [mkAlu_denot]
    show alu64 .SRL (edenot E a) (Z_to_bv 64 sh) = alu64 .SRL (edenot E a) y
    exact alu_srl_amt _ _ _ (by rw [hup, Hy])
  have Hlit : edenot E (mkAlu .SRL a (.ELit sh))
      = Z_to_bv 64 (bv_unsigned (edenot E a) / zpow 2 sh) := by
    rw [Hlit0, alu_srl_div (edenot E a) y sh Hy]
  -- the `lsplit_divc` permutation: the divisible part keeps the sum
  have SPLIT : ∀ (ts : List (Int × expr)) (d r : List (Int × expr)),
      lsplit_divc (zpow 2 sh) ts = (d, r) →
      coeffs_div (zpow 2 sh) d = true ∧ ∀ E0, tden E0 ts = tden E0 d + tden E0 r := by
    intro ts
    induction ts with
    | nil =>
      intro d r H
      obtain ⟨h1, h2⟩ := Prod.mk.inj (by simpa only [lsplit_divc] using H)
      subst h1; subst h2
      exact ⟨rfl, fun E0 => by simp only [tden_nil, Int.add_zero]⟩
    | cons hd rest ih =>
      obtain ⟨k, a0⟩ := hd
      intro d r H
      cases hs : lsplit_divc (zpow 2 sh) rest with
      | mk d0 r0 =>
        rw [lsplit_divc, hs] at H
        simp only [] at H
        obtain ⟨hdv, hsum0⟩ := ih d0 r0 hs
        by_cases hk : (k % zpow 2 sh == 0) = true
        · rw [ite_eq_left hk] at H
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj H
          refine ⟨by rw [coeffs_div, hk, hdv]; rfl, fun E0 => ?_⟩
          rw [tden_cons, tden_cons, hsum0 E0]
          omega
        · rw [ite_eq_right hk] at H
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj H
          refine ⟨hdv, fun E0 => ?_⟩
          rw [tden_cons, tden_cons, hsum0 E0]
          omega
  rw [alu_srl_div (edenot E a) y sh Hy]
  unfold mkSrl
  try simp only []
  by_cases hc : (!(lin_trivial (lin_of a)) && coeffs_div (zpow 2 sh) (lin_of a).2
      && lin_nowrap kn a) = true
  · rw [ite_eq_left hc]
    obtain ⟨hcd, hnw⟩ := (Bool.and_eq_true ..).mp hc
    obtain ⟨-, hdiv⟩ := (Bool.and_eq_true ..).mp hcd
    have hx : bv_unsigned (edenot E a) = (lin_of a).1 + tden E (lin_of a).2 :=
      lin_nowrap_sound segs E M kn a Hkn hnw
    have hsum : tden E (lin_of a).2
        = zpow 2 sh * tden E (ldiv_terms (zpow 2 sh) (lin_of a).2) :=
      ldiv_terms_sound E (zpow 2 sh) (lin_of a).2 hp hdiv
    have harith : bv_unsigned (edenot E a) / zpow 2 sh
        = (lin_of a).1 / zpow 2 sh + tden E (ldiv_terms (zpow 2 sh) (lin_of a).2) := by
      rw [hx, hsum, Int.mul_comm (zpow 2 sh) (tden E (ldiv_terms (zpow 2 sh) (lin_of a).2)),
        Int.add_mul_ediv_right _ _ hpne]
    show edenot E (unlin ((lin_of a).1 / zpow 2 sh, ldiv_terms (zpow 2 sh) (lin_of a).2))
      = Z_to_bv 64 (bv_unsigned (edenot E a) / zpow 2 sh)
    rw [edenot_unlin, harith]
    rfl
  · rw [ite_eq_right hc]
    by_cases hc2 : (!(lin_trivial (lin_of a)) && lin_nowrap kn a) = true
    · rw [ite_eq_left hc2]
      obtain ⟨-, hnw⟩ := (Bool.and_eq_true ..).mp hc2
      cases hsp : lsplit_divc (zpow 2 sh) (lin_of a).2 with
      | mk dts rts =>
        try simp only []
        cases hd : dts with
        | nil => exact Hlit
        | cons d1 dts' =>
          cases hr : rts with
          | nil => exact Hlit
          | cons r1 rts' =>
            try simp only []
            by_cases hn : lin_nowrap_l kn (lin_of a).1 (r1 :: rts') = true
            · rw [ite_eq_left hn]
              cases her : erange kn (unlin ((lin_of a).1, r1 :: rts')) with
              | none => exact Hlit
              | some p =>
                obtain ⟨lo, hi⟩ := p
                try simp only []
                by_cases hq : (lo / zpow 2 sh == hi / zpow 2 sh) = true
                · rw [ite_eq_left hq]
                  have hqe : lo / zpow 2 sh = hi / zpow 2 sh := beq_iff_eq.mp hq
                  have hsp' : lsplit_divc (zpow 2 sh) (lin_of a).2
                      = (d1 :: dts', r1 :: rts') := by rw [hsp, hd, hr]
                  obtain ⟨hdv, hsum⟩ := SPLIT (lin_of a).2 (d1 :: dts') (r1 :: rts') hsp'
                  have hA : tden E (d1 :: dts')
                      = zpow 2 sh * tden E (ldiv_terms (zpow 2 sh) (d1 :: dts')) :=
                    ldiv_terms_sound E (zpow 2 sh) (d1 :: dts') hp hdv
                  have hx : bv_unsigned (edenot E a) = (lin_of a).1 + tden E (lin_of a).2 :=
                    lin_nowrap_sound segs E M kn a Hkn hnw
                  have hT := unlin_val_of_nowrap_l segs E M kn (lin_of a).1 (r1 :: rts') Hkn hn
                  have hbr : lo ≤ (lin_of a).1 + tden E (r1 :: rts')
                      ∧ (lin_of a).1 + tden E (r1 :: rts') ≤ hi := by
                    have hs := erange_sound segs E M kn (unlin ((lin_of a).1, r1 :: rts')) lo hi Hkn her
                    rwa [hT] at hs
                  have hex : ((lin_of a).1 + tden E (r1 :: rts')) / zpow 2 sh
                      = lo / zpow 2 sh := by
                    have h1 : lo / zpow 2 sh
                        ≤ ((lin_of a).1 + tden E (r1 :: rts')) / zpow 2 sh :=
                      Int.ediv_le_ediv hp hbr.1
                    have h2 : ((lin_of a).1 + tden E (r1 :: rts')) / zpow 2 sh
                        ≤ hi / zpow 2 sh :=
                      Int.ediv_le_ediv hp hbr.2
                    omega
                  have harith : bv_unsigned (edenot E a) / zpow 2 sh
                      = lo / zpow 2 sh + tden E (ldiv_terms (zpow 2 sh) (d1 :: dts')) := by
                    rw [hx, hsum E, hA,
                      Int.mul_comm (zpow 2 sh) (tden E (ldiv_terms (zpow 2 sh) (d1 :: dts')))]
                    rw [show (lin_of a).1 + (tden E (ldiv_terms (zpow 2 sh) (d1 :: dts')) * zpow 2 sh
                          + tden E (r1 :: rts'))
                        = ((lin_of a).1 + tden E (r1 :: rts'))
                          + tden E (ldiv_terms (zpow 2 sh) (d1 :: dts')) * zpow 2 sh
                        from by omega]
                    rw [Int.add_mul_ediv_right _ _ hpne, hex]
                  show edenot E (unlin (lo / zpow 2 sh, ldiv_terms (zpow 2 sh) (d1 :: dts')))
                      = Z_to_bv 64 (bv_unsigned (edenot E a) / zpow 2 sh)
                  rw [edenot_unlin, harith]
                  rfl
                · rw [ite_eq_right hq]
                  exact Hlit
            · rw [ite_eq_right hn]
              exact Hlit
    · rw [ite_eq_right hc2]
      try simp only []
      exact Hlit

/-- `2 ^ k < 2 ^ j` for `k < j` (`Int` spelling of `Z.pow_lt_mono_r`). -/
theorem int_pow_lt_pow (k j : Nat) (h : k < j) : (2 : Int) ^ k < (2 : Int) ^ j := by
  have h1 : 2 ^ k < 2 ^ j := Nat.pow_lt_pow_right (by decide) h
  have h2 : ((2 ^ k : Nat) : Int) < ((2 ^ j : Nat) : Int) := Int.ofNat_lt.mpr h1
  rwa [Int.natCast_pow, Int.natCast_pow] at h2

/-- `and_highmask_srl` (R6): `x & -2^j = 2^j * (x >> j)` when the
    shift is `mkSrl`'d at `j`. -/
theorem and_highmask_srl (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (a : expr) (j : Int)
    (Hkn : know_ok segs E M kn) (Hj : 0 ≤ j) (Hj64 : j < 64) :
    edenot E (mkMd .MUL (.ELit (zpow 2 j)) (mkSrl kn a j))
      = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j) := by
  have hjlit : bv_unsigned (Z_to_bv 64 j) % 64 = j := by
    rw [u_small ⟨Hj, by omega⟩]
    exact Int.emod_eq_of_lt Hj Hj64
  have hmpos : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hmlt : zpow 2 j < 2 ^ 64 := by
    unfold zpow
    exact int_pow_lt_pow j.toNat 64 (by omega)
  have hx1 : 0 ≤ bv_unsigned (edenot E a) := (u64_range _).1
  have hx2 : bv_unsigned (edenot E a) < 2 ^ 64 := (u64_range _).2
  have hq1 : 0 ≤ bv_unsigned (edenot E a) / zpow 2 j :=
    Int.ediv_nonneg hx1 (Int.le_of_lt hmpos)
  have hq2 : bv_unsigned (edenot E a) / zpow 2 j < 2 ^ 64 := by
    have h := Int.ediv_le_self (zpow 2 j) hx1
    omega
  rw [mkMd_denot]
  show mul_div .MUL (Z_to_bv 64 (zpow 2 j)) (edenot E (mkSrl kn a j))
    = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j)
  rw [mkSrl_denot segs E M kn a j (Z_to_bv 64 j) Hkn hjlit, m_mul]
  rw [alu_srl_div (edenot E a) (Z_to_bv 64 j) j hjlit]
  show Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (zpow 2 j))
        * bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E a) / zpow 2 j)))
    = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j)
  rw [u_small ⟨Int.le_of_lt hmpos, hmlt⟩, u_small ⟨hq1, hq2⟩]
  have harg : zpow 2 j * (bv_unsigned (edenot E a) / zpow 2 j)
      = bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j := by
    have hdm := Int.ediv_mul_add_emod (bv_unsigned (edenot E a)) (zpow 2 j)
    rw [Int.mul_comm] at hdm
    omega
  rw [harg]

/-!  This tree has no bit test on `Int`, so the work
    is done on the `Nat` representative (`Nat.eq_of_testBit_eq`,
    `Nat.testBit_and/or/xor`, `Nat.testBit_mod_two_pow`) and lifted through
    `Int.natCast_emod`.  DEVIATION: this tree's `zland`/`zlor`/`zlxor` are
    the 64-bit WINDOW of `Z.land`/`lor`/`lxor`, so the lift carries
    `0 ≤ x`, `0 ≤ y` (all uses read `bv_unsigned` values or nonnegative
    literals) and `j ≤ 64` for the window. -/

theorem and_mod_pow2_nat_gen (X Y W J : Nat) (hW : J ≤ W) :
    (X % 2 ^ W &&& Y % 2 ^ W) % 2 ^ J = (X % 2 ^ J) &&& (Y % 2 ^ J) := by
  have hdvd : 2 ^ J ∣ 2 ^ W := Nat.pow_dvd_pow 2 hW
  have h1 : (X % 2 ^ W &&& Y % 2 ^ W) % 2 ^ J
      = ((X % 2 ^ W) % 2 ^ J) &&& ((Y % 2 ^ W) % 2 ^ J) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_and]
    by_cases h : i < J <;> simp [h]
  rw [h1, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]

theorem or_mod_pow2_nat_gen (X Y W J : Nat) (hW : J ≤ W) :
    (X % 2 ^ W ||| Y % 2 ^ W) % 2 ^ J = (X % 2 ^ J) ||| (Y % 2 ^ J) := by
  have hdvd : 2 ^ J ∣ 2 ^ W := Nat.pow_dvd_pow 2 hW
  have h1 : (X % 2 ^ W ||| Y % 2 ^ W) % 2 ^ J
      = ((X % 2 ^ W) % 2 ^ J) ||| ((Y % 2 ^ W) % 2 ^ J) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_or]
    by_cases h : i < J <;> simp [h]
  rw [h1, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]

theorem xor_mod_pow2_nat_gen (X Y W J : Nat) (hW : J ≤ W) :
    (X % 2 ^ W ^^^ Y % 2 ^ W) % 2 ^ J = (X % 2 ^ J) ^^^ (Y % 2 ^ J) := by
  have hdvd : 2 ^ J ∣ 2 ^ W := Nat.pow_dvd_pow 2 hW
  have h1 : (X % 2 ^ W ^^^ Y % 2 ^ W) % 2 ^ J
      = ((X % 2 ^ W) % 2 ^ J) ^^^ ((Y % 2 ^ W) % 2 ^ J) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases h : i < J <;> simp [h]
  rw [h1, Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]

/-- Lifting a `Nat` low-bits identity to an `Int` `zland`-shaped operation
    on the 64-bit window. -/
theorem zop_mod_pow2 (Z : Int → Int → Int) (op : Nat → Nat → Nat) (x y j : Int)
    (Hz : ∀ X Y : Nat, Z (X : Int) (Y : Int)
      = ((op (X % 2 ^ 64) (Y % 2 ^ 64) : Nat) : Int))
    (Hop : ∀ X Y W J, J ≤ W →
      (op (X % 2 ^ W) (Y % 2 ^ W)) % 2 ^ J = op (X % 2 ^ J) (Y % 2 ^ J))
    (Hx : 0 ≤ x) (Hy : 0 ≤ y) (Hj : 0 ≤ j) (Hj64 : j ≤ 64) :
    Z x y % zpow 2 j = Z (x % zpow 2 j) (y % zpow 2 j) := by
  obtain ⟨X, rfl⟩ : ∃ X : Nat, x = (X : Int) := ⟨x.toNat, (Int.toNat_of_nonneg Hx).symm⟩
  obtain ⟨Y, rfl⟩ : ∃ Y : Nat, y = (Y : Int) := ⟨y.toNat, (Int.toNat_of_nonneg Hy).symm⟩
  have hJ : j.toNat ≤ 64 := by omega
  have h64 : (0 : Int) ≤ 2 ^ 64 := Int.le_of_lt (two_pow_pos_int 64)
  have h2j : zpow 2 j = ((2 ^ j.toNat : Nat) : Int) := (Int.natCast_pow 2 j.toNat).symm
  have hT : ∀ (m : Nat), ((m : Int) % 2 ^ 64).toNat = m % 2 ^ 64 := by
    intro m
    rw [Int.toNat_emod (Int.natCast_nonneg m) h64]
    have h2 : ((2 : Int) ^ 64).toNat = 2 ^ 64 := by
      rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from (Int.natCast_pow 2 64).symm,
        Int.toNat_natCast]
    rw [h2, Int.toNat_natCast]
  have he : ∀ (m : Nat), ((m : Int) % ((2 ^ j.toNat : Nat) : Int))
      = ((m % 2 ^ j.toNat : Nat) : Int) := by
    intro m
    rw [Int.natCast_emod]
  have hsmall : ∀ a : Nat, a % 2 ^ j.toNat % 2 ^ 64 = a % 2 ^ j.toNat := by
    intro a
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) hJ))
  rw [h2j, Hz]
  simp only [he]
  rw [Hz]
  apply Int.natCast_inj.mpr
  rw [hsmall, hsmall]
  exact Hop X Y 64 j.toNat hJ
theorem land_mod_pow2 (x y j : Int) (Hx : 0 ≤ x) (Hy : 0 ≤ y) (Hj : 0 ≤ j) (Hj64 : j ≤ 64) :
    AxSymExec3.zland x y % zpow 2 j
      = AxSymExec3.zland (x % zpow 2 j) (y % zpow 2 j) :=
  have hz : ∀ X Y : Nat, AxSymExec3.zland (X : Int) (Y : Int)
      = ((X % 2 ^ 64 &&& Y % 2 ^ 64 : Nat) : Int) := by
    intro X Y
    have h64 : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := (Int.natCast_pow 2 64).symm
    simp only [AxSymExec3.zland, two64_eq, h64]
    rw [← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast]
  zop_mod_pow2 AxSymExec3.zland (fun a b => a &&& b) x y j hz
    (fun X Y W J hW => and_mod_pow2_nat_gen X Y W J hW) Hx Hy Hj Hj64
theorem lor_mod_pow2 (x y j : Int) (Hx : 0 ≤ x) (Hy : 0 ≤ y) (Hj : 0 ≤ j) (Hj64 : j ≤ 64) :
    AxSymExec3.zlor x y % zpow 2 j
      = AxSymExec3.zlor (x % zpow 2 j) (y % zpow 2 j) :=
  have hz : ∀ X Y : Nat, AxSymExec3.zlor (X : Int) (Y : Int)
      = ((X % 2 ^ 64 ||| Y % 2 ^ 64 : Nat) : Int) := by
    intro X Y
    have h64 : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := (Int.natCast_pow 2 64).symm
    simp only [AxSymExec3.zlor, two64_eq, h64]
    rw [← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast]
  zop_mod_pow2 AxSymExec3.zlor (fun a b => a ||| b) x y j hz
    (fun X Y W J hW => or_mod_pow2_nat_gen X Y W J hW) Hx Hy Hj Hj64
theorem lxor_mod_pow2 (x y j : Int) (Hx : 0 ≤ x) (Hy : 0 ≤ y) (Hj : 0 ≤ j) (Hj64 : j ≤ 64) :
    AxSymExec3.zlxor x y % zpow 2 j
      = AxSymExec3.zlxor (x % zpow 2 j) (y % zpow 2 j) :=
  have hz : ∀ X Y : Nat, AxSymExec3.zlxor (X : Int) (Y : Int)
      = ((X % 2 ^ 64 ^^^ Y % 2 ^ 64 : Nat) : Int) := by
    intro X Y
    have h64 : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := (Int.natCast_pow 2 64).symm
    simp only [AxSymExec3.zlxor, two64_eq, h64]
    rw [← Int.natCast_emod, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast]
  zop_mod_pow2 AxSymExec3.zlxor (fun a b => a ^^^ b) x y j hz
    (fun X Y W J hW => xor_mod_pow2_nat_gen X Y W J hW) Hx Hy Hj Hj64

/-- `mod_pow2_mod_pow2`: a `2^k` reduction is invisible to a
    `2^j` reduction for `j ≤ k`. -/
theorem mod_pow2_mod_pow2 (x j k : Int) (H : 0 ≤ j ∧ j ≤ k) :
    (x % zpow 2 k) % zpow 2 j = x % zpow 2 j := by
  have hdvd : zpow 2 j ∣ zpow 2 k := by
    obtain ⟨d, hd⟩ : ∃ d : Nat, k.toNat = j.toNat + d := ⟨(k - j).toNat, by omega⟩
    refine ⟨(2 : Int) ^ d, ?_⟩
    unfold zpow
    rw [hd, Int.pow_add]
  exact Int.emod_emod_of_dvd x hdvd

/-- `a mod m` may be reduced before multiplying. -/
theorem mul_mod_idem (a b m : Int) : ((a % m) * b) % m = (a * b) % m := by
  rw [Int.mul_emod a b m, Int.mul_emod (a % m) b m, Int.emod_emod a m]

/-- `lowbits_sound` (P-c): the low-`j`-bits computation is sound.
    DEVIATION: `land_mod_pow2`/`lor_mod_pow2`/`lxor_mod_pow2` carry their
    nonnegativity side conditions, discharged here from `bv_unsigned` and
    `Int.emod_nonneg`. -/
theorem lowbits_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (j : Int)
    (Hkn : know_ok segs E M kn) (Hj : 0 ≤ j ∧ j ≤ 64) :
    ∀ v : Int, lowbits kn e j = some v → bv_unsigned (edenot E e) % zpow 2 j = v := by
  have hmpos : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have Hdflt : ∀ (e' : expr) (v : Int),
      (if j ≤ ealign kn e' then some 0 else lin_lowbits_kn kn e' j) = some v →
      bv_unsigned (edenot E e') % zpow 2 j = v := by
    intro e' v H'
    by_cases hle : j ≤ ealign kn e'
    · rw [ite_eq_left hle] at H'
      have hv : v = 0 := (Option.some.inj H').symm
      rw [hv]
      obtain ⟨-, hdv⟩ := ealign_sound segs E M kn e' Hkn
      exact Int.emod_eq_zero_of_dvd (Int.dvd_trans (pow2_divide_le j (ealign kn e') ⟨Hj.1, hle⟩) hdv)
    · rw [ite_eq_right hle] at H'
      exact (lin_lowbits_kn_sound segs E M kn e' j v Hkn Hj H').1
  have Hlit : ∀ c : Int, bv_unsigned (edenot E (.ELit c)) % zpow 2 j
      = (c % two64) % zpow 2 j := by
    intro c
    show bv_unsigned (Z_to_bv 64 c) % zpow 2 j = (c % two64) % zpow 2 j
    rw [u_lit64]
  have M64 : ∀ x : Int, (x % 2 ^ 64) % zpow 2 j = x % zpow 2 j := fun x =>
    mod_pow2_mod_pow2 x j 64 ⟨Hj.1, Hj.2⟩
  have M64b : ∀ x : Int, (x % two64) % zpow 2 j = x % zpow 2 j := by
    intro x; rw [two64_eq]; exact M64 x
  have hc0 : ∀ c : Int, 0 ≤ c % two64 := fun c => Int.emod_nonneg c two64_ne
  have hb0 : ∀ u : word, 0 ≤ bv_unsigned u := fun u => (u64_range u).1
  induction e with
  | ELit z =>
    intro v H
    simp only [lowbits] at H
    have hv : v = (z % two64) % zpow 2 j := (Option.some.inj H).symm
    rw [hv, Hlit]
  | EVar n => intro v H; exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EAluw op a b iha ihb => intro v H; exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EExt sx lo n a iha => intro v H; exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EBlob sx k i n => intro v H; exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EAlu op a b iha ihb =>
    intro v H
    cases op with
    | ADD =>
      simp only [lowbits] at H
      cases ha : lowbits kn a j with
      | none => exact Hdflt _ _ (by simpa only [ha] using H)
      | some x =>
        cases hb : lowbits kn b j with
        | none => exact Hdflt _ _ (by simpa only [ha, hb] using H)
        | some y =>
          simp only [ha, hb] at H
          have hv : v = (x + y) % zpow 2 j := (Option.some.inj H).symm
          have hx := iha x ha
          have hy := ihb y hb
          rw [hv]
          show bv_unsigned (edenot E a + edenot E b) % zpow 2 j = (x + y) % zpow 2 j
          rw [u_add64, M64, Int.add_emod, hx, hy]
    | SUB =>
      simp only [lowbits] at H
      cases ha : lowbits kn a j with
      | none => exact Hdflt _ _ (by simpa only [ha] using H)
      | some x =>
        cases hb : lowbits kn b j with
        | none => exact Hdflt _ _ (by simpa only [ha, hb] using H)
        | some y =>
          simp only [ha, hb] at H
          have hv : v = (x - y) % zpow 2 j := (Option.some.inj H).symm
          have hx := iha x ha
          have hy := ihb y hb
          rw [hv]
          show bv_unsigned (edenot E a - edenot E b) % zpow 2 j = (x - y) % zpow 2 j
          rw [u_sub64, M64, Int.sub_emod, hx, hy]
    | AND =>
      cases b with
      | ELit c =>
        simp only [lowbits] at H
        by_cases hz : ((c % two64) % zpow 2 j == 0) = true
        · rw [ite_eq_left hz] at H
          have hv : v = 0 := (Option.some.inj H).symm
          rw [hv]
          have hz0 : (c % two64) % zpow 2 j = 0 := beq_iff_eq.mp hz
          show bv_unsigned (alu64 .AND (edenot E a) (Z_to_bv 64 c)) % zpow 2 j = 0
          rw [u_and64, u_lit64,
            land_mod_pow2 (bv_unsigned (edenot E a)) (c % two64) j
              (hb0 _) (hc0 c) Hj.1 Hj.2, hz0]
          simp [AxSymExec3.zland]
        · rw [ite_eq_right hz] at H
          cases ha : lowbits kn a j with
          | none => exact Hdflt _ _ (by simpa only [ha] using H)
          | some x =>
            simp only [ha] at H
            have hv : v = AxSymExec3.zland x ((c % two64) % zpow 2 j) := (Option.some.inj H).symm
            have hx := iha x ha
            rw [hv]
            show bv_unsigned (alu64 .AND (edenot E a) (Z_to_bv 64 c)) % zpow 2 j
              = AxSymExec3.zland x ((c % two64) % zpow 2 j)
            rw [u_and64, u_lit64,
              land_mod_pow2 (bv_unsigned (edenot E a)) (c % two64) j
                (hb0 _) (hc0 c) Hj.1 Hj.2, hx]
      | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
    | OR =>
      cases b with
      | ELit c =>
        simp only [lowbits] at H
        cases ha : lowbits kn a j with
        | none => exact Hdflt _ _ (by simpa only [ha] using H)
        | some x =>
          simp only [ha] at H
          have hv : v = AxSymExec3.zlor x ((c % two64) % zpow 2 j) := (Option.some.inj H).symm
          have hx := iha x ha
          rw [hv]
          show bv_unsigned (alu64 .OR (edenot E a) (Z_to_bv 64 c)) % zpow 2 j
            = AxSymExec3.zlor x ((c % two64) % zpow 2 j)
          rw [u_or64, u_lit64,
            lor_mod_pow2 (bv_unsigned (edenot E a)) (c % two64) j
              (hb0 _) (hc0 c) Hj.1 Hj.2, hx]
      | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
    | XOR =>
      cases b with
      | ELit c =>
        simp only [lowbits] at H
        cases ha : lowbits kn a j with
        | none => exact Hdflt _ _ (by simpa only [ha] using H)
        | some x =>
          simp only [ha] at H
          have hv : v = AxSymExec3.zlxor x ((c % two64) % zpow 2 j) := (Option.some.inj H).symm
          have hx := iha x ha
          rw [hv]
          show bv_unsigned (alu64 .XOR (edenot E a) (Z_to_bv 64 c)) % zpow 2 j
            = AxSymExec3.zlxor x ((c % two64) % zpow 2 j)
          rw [u_xor64, u_lit64,
            lxor_mod_pow2 (bv_unsigned (edenot E a)) (c % two64) j
              (hb0 _) (hc0 c) Hj.1 Hj.2, hx]
      | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
    | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EMd op a b iha ihb =>
    intro v H
    cases op with
    | MUL =>
      cases a with
      | ELit c =>
        simp only [lowbits] at H
        by_cases hz : ((c % two64) % zpow 2 j == 0) = true
        · rw [ite_eq_left hz] at H
          have hv : v = 0 := (Option.some.inj H).symm
          rw [hv]
          have hz0 : (c % two64) % zpow 2 j = 0 := beq_iff_eq.mp hz
          show bv_unsigned (mul_div .MUL (Z_to_bv 64 c) (edenot E b)) % zpow 2 j = 0
          rw [eqm_mod_pow2 _ _ j Hj (u_mul_eqm (Z_to_bv 64 c) (edenot E b)), u_lit64,
            Int.mul_emod, hz0, Int.zero_mul, Int.zero_emod]
        · rw [ite_eq_right hz] at H
          cases hb : lowbits kn b j with
          | none => exact Hdflt _ _ (by simpa only [hb] using H)
          | some y =>
            simp only [hb] at H
            have hv : v = (c * y) % zpow 2 j := (Option.some.inj H).symm
            have hy := ihb y hb
            rw [hv]
            show bv_unsigned (mul_div .MUL (Z_to_bv 64 c) (edenot E b)) % zpow 2 j
              = (c * y) % zpow 2 j
            rw [eqm_mod_pow2 _ _ j Hj (u_mul_eqm (Z_to_bv 64 c) (edenot E b)), u_lit64,
              Int.mul_emod, hy, M64b, mul_mod_idem]
      | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
    | _ => exact Hdflt _ _ (by simpa only [lowbits] using H)
  | EMdw op a b iha ihb => intro v H; exact Hdflt _ _ (by simpa only [lowbits] using H)

/-! ## Part P4f: the `mkAnd` split

    `lsplit_div_sound`, `split_mod_core`, `and_high_split_denot`,
    `and_low_split_denot`. -/

/-- `lsplit_div_sound`: the aligned/residual split keeps the sum,
    and the aligned part passes the `coeffs_divk` test. -/
theorem lsplit_div_sound (kn : List kentry) (m : Int) :
    ∀ (ts dts rts : List (Int × expr)),
      lsplit_div kn m ts = (dts, rts) →
      coeffs_divk kn m dts = true ∧ ∀ E, tden E ts = tden E dts + tden E rts := by
  intro ts
  induction ts with
  | nil =>
    intro dts rts H
    obtain ⟨h1, h2⟩ := Prod.mk.inj (by simpa only [lsplit_div] using H)
    subst h1; subst h2
    exact ⟨rfl, fun E => by simp only [tden_nil, Int.add_zero]⟩
  | cons hd rest ih =>
    obtain ⟨k, a0⟩ := hd
    intro dts rts H
    cases hs : lsplit_div kn m rest with
    | mk d0 r0 =>
      rw [lsplit_div, hs] at H
      simp only [] at H
      obtain ⟨hdv, hsum0⟩ := ih d0 r0 hs
      by_cases hk : (k % m == 0 || (k * zpow 2 (ealign kn a0)) % m == 0) = true
      · rw [ite_eq_left hk] at H
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj H
        refine ⟨by rw [coeffs_divk, hk, hdv]; rfl, fun E => ?_⟩
        rw [tden_cons, tden_cons, hsum0 E]
        omega
      · rw [ite_eq_right hk] at H
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj H
        refine ⟨hdv, fun E => ?_⟩
        rw [tden_cons, tden_cons, hsum0 E]
        omega

/-- `split_mod_core`: if `SA ≡ 0 (mod 2^j)` and `ua ≡ SA + ur`, the
    low `j` bits of `ua` and `ur` agree. -/
theorem split_mod_core (ua ur SA : Int) (j : Int) (Hj : 0 ≤ j ∧ j ≤ 64)
    (HSA : SA % zpow 2 j = 0) (Heq : eqm ua (SA + ur)) :
    ua % zpow 2 j = ur % zpow 2 j := by
  rw [eqm_mod_pow2 ua (SA + ur) j Hj Heq, Int.add_emod, HSA, Int.zero_add, Int.emod_emod]

/-- `and_high_split_denot`: the `-2^j` half of the `mkAnd` split. -/
theorem and_high_split_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (bk : expr) (j c : Int) (dts rts : List (Int × expr)) (a : expr)
    (Hkn : know_ok segs E base kn) (Hj0 : 0 ≤ j) (Hj64 : j < 64)
    (Hbk : edenot E bk = Z_to_bv 64 (-(zpow 2 j)))
    (Hdiv : coeffs_divk kn (zpow 2 j) dts = true)
    (Ha : eqm (uE E a) (c + tden E dts + tden E rts)) :
    edenot E (and_high_split kn bk j c dts rts)
      = alu64 .AND (edenot E a) (Z_to_bv 64 (-(zpow 2 j))) := by
  have hmpos : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hJ64 : j ≤ 64 := by omega
  rw [and_highmask_val (edenot E a) j Hj0 Hj64]
  unfold and_high_split
  simp only []
  have HSA : (c - c % zpow 2 j + tden E dts) % zpow 2 j = 0 := by
    have hcd : tden E dts % zpow 2 j = 0 :=
      coeffs_divk_sound segs E base kn (zpow 2 j) dts Hkn hmpos Hdiv
    rw [Int.add_emod, hcd, Int.add_zero, Int.sub_emod, Int.emod_emod c, Int.sub_self]
    exact Int.zero_emod _
  have Hr : eqm (uE E (unlin (c % zpow 2 j, rts))) (c % zpow 2 j + tden E rts) := by
    have h := unlin_sound E (c % zpow 2 j, rts)
    simpa only [uE, lden] using h
  have Har : eqm (uE E a)
      ((c - c % zpow 2 j + tden E dts) + uE E (unlin (c % zpow 2 j, rts))) := by
    refine eqm_trans Ha ?_
    refine eqm_trans (⟨0, by omega⟩ : eqm (c + tden E dts + tden E rts)
      ((c - c % zpow 2 j + tden E dts) + (c % zpow 2 j + tden E rts))) ?_
    exact eqm_add (eqm_refl _) (eqm_sym Hr)
  have Hmod := split_mod_core (uE E a) (uE E (unlin (c % zpow 2 j, rts)))
    (c - c % zpow 2 j + tden E dts) j ⟨Hj0, hJ64⟩ HSA Har
  have GOAL : ∀ res : expr, eqm (uE E res)
      ((c - c % zpow 2 j + tden E dts)
        + (uE E (unlin (c % zpow 2 j, rts))
          - uE E (unlin (c % zpow 2 j, rts)) % zpow 2 j)) →
      edenot E res = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j) := by
    intro res Hres
    rw [← Z_to_bv_unsigned (edenot E res)]
    apply eqm_Z_to_bv
    refine eqm_trans Hres ?_
    have Hmod' : bv_unsigned (edenot E a) % zpow 2 j
        = uE E (unlin (c % zpow 2 j, rts)) % zpow 2 j := Hmod
    rw [Hmod']
    obtain ⟨q, hq⟩ := Har
    have hq' : bv_unsigned (edenot E a)
        = (c - c % zpow 2 j + tden E dts)
          + uE E (unlin (c % zpow 2 j, rts)) + q * 2 ^ 64 := hq
    refine ⟨-q, ?_⟩
    rw [Int.neg_mul, hq']
    omega
  have RES : edenot E (mkAlu .ADD (unlin (c - c % zpow 2 j, dts))
        (mkAlu .AND (unlin (c % zpow 2 j, rts)) bk))
      = Z_to_bv 64 (bv_unsigned (edenot E a) - bv_unsigned (edenot E a) % zpow 2 j) := by
    apply GOAL
    have h1 : uE E (mkAlu .ADD (unlin (c - c % zpow 2 j, dts))
          (mkAlu .AND (unlin (c % zpow 2 j, rts)) bk))
        = bv_unsigned (alu64 .ADD (edenot E (unlin (c - c % zpow 2 j, dts)))
            (edenot E (mkAlu .AND (unlin (c % zpow 2 j, rts)) bk))) := by
      simp only [uE, mkAlu_denot]
    rw [h1]
    refine eqm_trans (u_add_eqm _ _) (eqm_add ?_ ?_)
    · have h := unlin_sound E (c - c % zpow 2 j, dts)
      simpa only [uE, lden] using h
    · rw [mkAlu_denot, Hbk, and_highmask_val _ j Hj0 Hj64]
      exact eqm_u_lit _
  cases her : erange kn (unlin (c % zpow 2 j, rts)) with
  | none => exact RES
  | some p =>
    obtain ⟨lo, hi⟩ := p
    try simp only []
    by_cases hq : (lo / zpow 2 j == hi / zpow 2 j) = true
    · rw [ite_eq_left hq]
      apply GOAL
      have hqe : lo / zpow 2 j = hi / zpow 2 j := beq_iff_eq.mp hq
      have hbr : lo ≤ uE E (unlin (c % zpow 2 j, rts))
          ∧ uE E (unlin (c % zpow 2 j, rts)) ≤ hi :=
        erange_sound segs E base kn _ lo hi Hkn her
      have hex : uE E (unlin (c % zpow 2 j, rts)) / zpow 2 j = lo / zpow 2 j := by
        have h1 := Int.ediv_le_ediv hmpos hbr.1
        have h2 := Int.ediv_le_ediv hmpos hbr.2
        omega
      have hmul : lo / zpow 2 j * zpow 2 j
          = uE E (unlin (c % zpow 2 j, rts))
            - uE E (unlin (c % zpow 2 j, rts)) % zpow 2 j := by
        have hdm := Int.ediv_mul_add_emod (uE E (unlin (c % zpow 2 j, rts))) (zpow 2 j)
        rw [hex] at hdm
        omega
      refine eqm_trans (unlin_sound E
        (c - c % zpow 2 j + lo / zpow 2 j * zpow 2 j, dts)) ?_
      refine ⟨0, ?_⟩
      rw [hmul]
      simp only [lden]
      omega
    · rw [ite_eq_right hq]
      exact RES

/-- `and_low_split_denot`: the `2^j - 1` half of the `mkAnd` split. -/
theorem and_low_split_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (bk : expr) (j c : Int) (dts rts : List (Int × expr)) (a : expr)
    (Hkn : know_ok segs E base kn) (Hj0 : 0 ≤ j) (Hj64 : j < 64)
    (Hbk : edenot E bk = Z_to_bv 64 (zpow 2 j - 1))
    (Hdiv : coeffs_divk kn (zpow 2 j) dts = true)
    (Ha : eqm (uE E a) (c + tden E dts + tden E rts)) :
    edenot E (and_low_split kn bk j c rts)
      = alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 j - 1)) := by
  have hmpos : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hJ64 : j ≤ 64 := by omega
  rw [and_lowmask_val (edenot E a) j Hj0 hJ64]
  unfold and_low_split
  simp only []
  have HSA : (c - c % zpow 2 j + tden E dts) % zpow 2 j = 0 := by
    have hcd : tden E dts % zpow 2 j = 0 :=
      coeffs_divk_sound segs E base kn (zpow 2 j) dts Hkn hmpos Hdiv
    rw [Int.add_emod, hcd, Int.add_zero, Int.sub_emod, Int.emod_emod c, Int.sub_self]
    exact Int.zero_emod _
  have Hr : eqm (bv_unsigned (edenot E (unlin (c % zpow 2 j, rts))))
      (c % zpow 2 j + tden E rts) := by
    have h := unlin_sound E (c % zpow 2 j, rts)
    simpa only [uE, lden] using h
  have Ha' : eqm (bv_unsigned (edenot E a)) (c + tden E dts + tden E rts) := Ha
  have Har : eqm (bv_unsigned (edenot E a))
      ((c - c % zpow 2 j + tden E dts)
        + bv_unsigned (edenot E (unlin (c % zpow 2 j, rts)))) := by
    refine eqm_trans Ha' ?_
    refine eqm_trans (⟨0, by omega⟩ : eqm (c + tden E dts + tden E rts)
      ((c - c % zpow 2 j + tden E dts) + (c % zpow 2 j + tden E rts))) ?_
    exact eqm_add (eqm_refl _) (eqm_sym Hr)
  have Hmod := split_mod_core (bv_unsigned (edenot E a))
    (bv_unsigned (edenot E (unlin (c % zpow 2 j, rts))))
    (c - c % zpow 2 j + tden E dts) j ⟨Hj0, hJ64⟩ HSA Har
  have RES : edenot E (mkAlu .AND (unlin (c % zpow 2 j, rts)) bk)
      = Z_to_bv 64 (bv_unsigned (edenot E a) % zpow 2 j) := by
    rw [← Z_to_bv_unsigned (edenot E (mkAlu .AND (unlin (c % zpow 2 j, rts)) bk))]
    apply eqm_Z_to_bv
    rw [mkAlu_denot, Hbk, and_lowmask_val _ j Hj0 hJ64, ← Hmod]
    exact eqm_u_lit _
  cases her : erange kn (unlin (c % zpow 2 j, rts)) with
  | none => exact RES
  | some p =>
    obtain ⟨lo, hi⟩ := p
    try simp only []
    by_cases hq : (lo / zpow 2 j == hi / zpow 2 j) = true
    · rw [ite_eq_left hq]
      rw [← Z_to_bv_unsigned (edenot E
        (unlin (c % zpow 2 j - lo / zpow 2 j * zpow 2 j, rts)))]
      apply eqm_Z_to_bv
      have hqe : lo / zpow 2 j = hi / zpow 2 j := beq_iff_eq.mp hq
      have hbr : lo ≤ bv_unsigned (edenot E (unlin (c % zpow 2 j, rts)))
          ∧ bv_unsigned (edenot E (unlin (c % zpow 2 j, rts))) ≤ hi :=
        erange_sound segs E base kn _ lo hi Hkn her
      have hex : bv_unsigned (edenot E (unlin (c % zpow 2 j, rts))) / zpow 2 j
          = lo / zpow 2 j := by
        have h1 := Int.ediv_le_ediv hmpos hbr.1
        have h2 := Int.ediv_le_ediv hmpos hbr.2
        omega
      have hurd : bv_unsigned (edenot E (unlin (c % zpow 2 j, rts)))
          - lo / zpow 2 j * zpow 2 j
          = bv_unsigned (edenot E (unlin (c % zpow 2 j, rts))) % zpow 2 j := by
        have hdm := Int.ediv_mul_add_emod
          (bv_unsigned (edenot E (unlin (c % zpow 2 j, rts)))) (zpow 2 j)
        rw [hex] at hdm
        omega
      obtain ⟨q, hq'⟩ := eqm_sym Hr
      refine eqm_trans (unlin_sound E
        (c % zpow 2 j - lo / zpow 2 j * zpow 2 j, rts)) ?_
      refine ⟨q, ?_⟩
      rw [Hmod, ← hurd]
      simp only [lden]
      omega
    · rw [ite_eq_right hq]
      exact RES

/-! ## Part P4g: interval branch decisions

    `itv_ltu_sound`, `cond_on_eq_sound`.   -/

/-- `itv_ltu_sound`: an interval decision for unsigned `<` is
    correct. -/
theorem itv_ltu_sound (al ah bl bh : Int) (x y : word) (t : Bool)
    (Hx : al ≤ bv_unsigned x ∧ bv_unsigned x ≤ ah)
    (Hy : bl ≤ bv_unsigned y ∧ bv_unsigned y ≤ bh)
    (H : itv_ltu al ah bl bh = some t) : bv_ltu x y = t := by
  unfold itv_ltu at H
  split at H
  · rename_i h1
    have ht : t = true := (Option.some.inj H).symm
    rw [ht, bv_ltu_eq_true]
    omega
  · split at H
    · rename_i h2
      have ht : t = false := (Option.some.inj H).symm
      rw [ht]
      cases hb : bv_ltu x y with
      | false => rfl
      | true => rw [bv_ltu_eq_true] at hb; omega
    · exact absurd H (by simp)

/-- `cond_on_eq_sound`: comparing a value with itself decides the
    branch by `cond_on_eq` alone. -/
theorem cond_on_eq_sound (c : BranchCond) (v : word) :
    branch_taken c v v = cond_on_eq c := by
  cases c <;>
    simp [branch_taken, cond_on_eq, bv_eqb, bv_lts, bv_ltu]

/-! ### The signed half of `itv_lts`

    Local glue: on one half of the word range signed and unsigned `<`
    agree, so `itv_lts` reduces to `itv_ltu` there. -/

theorem zpow_two63 : zpow 2 63 = ((2 ^ 63 : Nat) : Int) := natCast_pow_two 63

/-- Below `2^63` the signed reading is the unsigned one. -/
theorem bv_lts_eq_ltu_small (x y : word)
    (hx : bv_unsigned x < zpow 2 63) (hy : bv_unsigned y < zpow 2 63) :
    bv_lts x y = bv_ltu x y := by
  have hx' : x.toNat < 2 ^ 63 := by
    have h := hx
    rw [zpow_two63] at h
    exact_mod_cast h
  have hy' : y.toNat < 2 ^ 63 := by
    have h := hy
    rw [zpow_two63] at h
    exact_mod_cast h
  unfold bv_lts bv_ltu
  rw [bv_signed_small x hx', bv_signed_small y hy']
  by_cases h : x.toNat < y.toNat
  · have h' : (x.toNat : Int) < (y.toNat : Int) := by exact_mod_cast h
    rw [decide_eq_true h', decide_eq_true h]
  · have h' : ¬ ((x.toNat : Int) < (y.toNat : Int)) := by exact_mod_cast h
    rw [decide_eq_false h', decide_eq_false h]

/-- At or above `2^63` both readings are shifted by the same `2^64`. -/
theorem bv_lts_eq_ltu_hi (x y : word)
    (hx : zpow 2 63 ≤ bv_unsigned x) (hy : zpow 2 63 ≤ bv_unsigned y) :
    bv_lts x y = bv_ltu x y := by
  have hx' : 2 ^ 63 ≤ x.toNat := by
    have h := hx
    rw [zpow_two63] at h
    exact_mod_cast h
  have hy' : 2 ^ 63 ≤ y.toNat := by
    have h := hy
    rw [zpow_two63] at h
    exact_mod_cast h
  unfold bv_lts bv_ltu
  rw [bv_signed_hi x hx', bv_signed_hi y hy']
  by_cases h : x.toNat < y.toNat
  · have h' : (x.toNat : Int) - 2 ^ 64 < (y.toNat : Int) - 2 ^ 64 := by
      have := Int.ofNat_lt.mpr h
      omega
    rw [decide_eq_true h', decide_eq_true h]
  · have h' : ¬ ((x.toNat : Int) - 2 ^ 64 < (y.toNat : Int) - 2 ^ 64) := by
      have := Int.ofNat_le.mpr (Nat.le_of_not_lt h)
      omega
    rw [decide_eq_false h', decide_eq_false h]

/-- `itv_lts_sound`: an interval decision for signed `<` is
    correct. -/
theorem itv_lts_sound (al ah bl bh : Int) (x y : word) (t : Bool)
    (Hx : al ≤ bv_unsigned x ∧ bv_unsigned x ≤ ah)
    (Hy : bl ≤ bv_unsigned y ∧ bv_unsigned y ≤ bh)
    (H : itv_lts al ah bl bh = some t) : bv_lts x y = t := by
  have Hx' : al ≤ bv_unsigned x ∧ bv_unsigned x ≤ ah := Hx
  have Hy' : bl ≤ bv_unsigned y ∧ bv_unsigned y ≤ bh := Hy
  unfold itv_lts at H
  try simp only [] at H
  split at H
  · rename_i hc
    rw [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · rw [Bool.and_eq_true] at hc
      have ha1 : ah < zpow 2 63 := of_decide_eq_true hc.1
      have ha2 : bh < zpow 2 63 := of_decide_eq_true hc.2
      have hxs : bv_unsigned x < zpow 2 63 := by omega
      have hys : bv_unsigned y < zpow 2 63 := by omega
      rw [bv_lts_eq_ltu_small x y hxs hys]
      exact itv_ltu_sound al ah bl bh x y t Hx' Hy' H
    · rw [Bool.and_eq_true] at hc
      have ha1 : zpow 2 63 ≤ al := of_decide_eq_true hc.1
      have ha2 : zpow 2 63 ≤ bl := of_decide_eq_true hc.2
      have hxs : zpow 2 63 ≤ bv_unsigned x := by omega
      have hys : zpow 2 63 ≤ bv_unsigned y := by omega
      rw [bv_lts_eq_ltu_hi x y hxs hys]
      exact itv_ltu_sound al ah bl bh x y t Hx' Hy' H
  · split at H
    · rename_i hc
      rw [Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      have ha1 : zpow 2 63 ≤ al := of_decide_eq_true h1
      have ha2 : bh < zpow 2 63 := of_decide_eq_true h2
      have ht : t = true := (Option.some.inj H).symm
      rw [ht]
      have hxs : zpow 2 63 ≤ bv_unsigned x := by omega
      have hys : bv_unsigned y < zpow 2 63 := by omega
      have hxs' : 2 ^ 63 ≤ x.toNat := by
        have h := hxs; rw [zpow_two63] at h; exact_mod_cast h
      have hys' : y.toNat < 2 ^ 63 := by
        have h := hys; rw [zpow_two63] at h; exact_mod_cast h
      unfold bv_lts
      rw [bv_signed_hi x hxs', bv_signed_small y hys']
      rw [decide_eq_true_eq]
      have hx2 : (x.toNat : Int) < 2 ^ 64 := by
        have := x.isLt; omega
      have hy2 : (0 : Int) ≤ (y.toNat : Int) := Int.natCast_nonneg _
      omega
    · split at H
      · rename_i hc
        rw [Bool.and_eq_true] at hc
        obtain ⟨h1, h2⟩ := hc
        have ha1 : ah < zpow 2 63 := of_decide_eq_true h1
        have ha2 : zpow 2 63 ≤ bl := of_decide_eq_true h2
        have ht : t = false := (Option.some.inj H).symm
        rw [ht]
        have hxs : bv_unsigned x < zpow 2 63 := by omega
        have hys : zpow 2 63 ≤ bv_unsigned y := by omega
        have hxs' : x.toNat < 2 ^ 63 := by
          have h := hxs; rw [zpow_two63] at h; exact_mod_cast h
        have hys' : 2 ^ 63 ≤ y.toNat := by
          have h := hys; rw [zpow_two63] at h; exact_mod_cast h
        unfold bv_lts
        rw [bv_signed_small x hxs', bv_signed_hi y hys']
        exact decide_eq_false (by
          have hx2 : (0 : Int) ≤ (x.toNat : Int) := Int.natCast_nonneg _
          have hy2 : (2 : Int) ^ 63 ≤ (y.toNat : Int) := by exact_mod_cast hys'
          omega)
      · exact absurd H (by simp)

/-- `range_branch_sound`: an interval branch decision is correct. -/
theorem range_branch_sound (c : BranchCond) (al ah bl bh : Int) (x y : word) (t : Bool)
    (Hx : al ≤ bv_unsigned x ∧ bv_unsigned x ≤ ah)
    (Hy : bl ≤ bv_unsigned y ∧ bv_unsigned y ≤ bh)
    (H : range_branch c al ah bl bh = some t) : branch_taken c x y = t := by
  have Hx' := Hx
  have Hy' := Hy
  cases c with
  | EQ =>
    unfold range_branch at H
    try simp only [] at H
    split at H
    · rename_i hc
      have ht : t = false := (Option.some.inj H).symm
      rw [ht]
      rw [Bool.or_eq_true] at hc
      have hne : x ≠ y := by
        intro he
        subst he
        rcases hc with hc | hc
        · have h1 : ah < bl := of_decide_eq_true hc
          omega
        · have h1 : bh < al := of_decide_eq_true hc
          omega
      exact bv_eqb_neq x y hne
    · split at H
      · rename_i hc
        have ht : t = true := (Option.some.inj H).symm
        rw [ht]
        rw [Bool.and_eq_true] at hc
        obtain ⟨hc1, hc3⟩ := hc
        rw [Bool.and_eq_true] at hc1
        obtain ⟨hc1, hc2⟩ := hc1
        have e1 : al = ah := beq_iff_eq.mp hc1
        have e2 : bl = bh := beq_iff_eq.mp hc2
        have e3 : al = bl := beq_iff_eq.mp hc3
        have hux : bv_unsigned x = bv_unsigned y := by omega
        have hxy : x = y := word_eq_of_bv_unsigned hux
        rw [hxy]
        exact cond_on_eq_sound .EQ y
      · exact absurd H (by simp)
  | NE =>
    unfold range_branch at H
    try simp only [] at H
    split at H
    · rename_i hc
      have ht : t = true := (Option.some.inj H).symm
      rw [ht]
      rw [Bool.or_eq_true] at hc
      have hne : x ≠ y := by
        intro he
        subst he
        rcases hc with hc | hc
        · have h1 : ah < bl := of_decide_eq_true hc
          omega
        · have h1 : bh < al := of_decide_eq_true hc
          omega
      show (!(bv_eqb x y)) = true
      rw [bv_eqb_neq x y hne]
      rfl
    · split at H
      · rename_i hc
        have ht : t = false := (Option.some.inj H).symm
        rw [ht]
        rw [Bool.and_eq_true] at hc
        obtain ⟨hc1, hc3⟩ := hc
        rw [Bool.and_eq_true] at hc1
        obtain ⟨hc1, hc2⟩ := hc1
        have e1 : al = ah := beq_iff_eq.mp hc1
        have e2 : bl = bh := beq_iff_eq.mp hc2
        have e3 : al = bl := beq_iff_eq.mp hc3
        have hux : bv_unsigned x = bv_unsigned y := by omega
        have hxy : x = y := word_eq_of_bv_unsigned hux
        rw [hxy]
        exact cond_on_eq_sound .NE y
      · exact absurd H (by simp)
  | LTU =>
    unfold range_branch at H
    exact itv_ltu_sound al ah bl bh x y t Hx' Hy' H
  | GEU =>
    unfold range_branch at H
    cases hi : itv_ltu al ah bl bh with
    | none => rw [hi] at H; exact absurd H (by simp)
    | some t' =>
      rw [hi] at H
      simp only [Option.map] at H
      have ht : t = !t' := (Option.some.inj H).symm
      rw [ht]
      have hl := itv_ltu_sound al ah bl bh x y t' Hx' Hy' hi
      show (!(bv_ltu x y)) = !t'
      rw [hl]
  | LT =>
    unfold range_branch at H
    exact itv_lts_sound al ah bl bh x y t Hx' Hy' H
  | GE =>
    unfold range_branch at H
    cases hi : itv_lts al ah bl bh with
    | none => rw [hi] at H; exact absurd H (by simp)
    | some t' =>
      rw [hi] at H
      simp only [Option.map] at H
      have ht : t = !t' := (Option.some.inj H).symm
      rw [ht]
      have hl := itv_lts_sound al ah bl bh x y t' Hx' Hy' hi
      show (!(bv_lts x y)) = !t'
      rw [hl]
/-!  The missing pieces are built here on the `Nat`
    representative (`Nat.testBit`, `Nat.log2_eq_iff`,
    `Nat.testBit_two_pow_sub_one`, `Nat.and_lt_two_pow`) and lifted at the
    `bv_unsigned` boundary.  The arms of the proof are local lemmas
    (`mkAnd0_high_id`, `mkAnd0_high_coeffs`, `mkAnd0_low_zero`,
    `mkAnd0_low_bits`, `mkAnd0_low_kn`, `mkAnd0_lit_mask`) so that the
    top-level case bash only peels the executor's `if`/`match` chain; the
    two split arms reuse the already-proved `and_high_split_denot` /
    `and_low_split_denot` and the R6 fallbacks `and_highmask_srl` /
    `and_highmask_val`. -/

/-- `testbit_pow_sub` (`Z` version): the bits of `2^a - 2^i` are
    exactly the positions `i <= n < a`.  Lean core has no bit test on `Int`,
    so this tree states it on the `Nat` representative with `Nat` indices. -/
theorem testbit_pow_sub {a i : Nat} (hia : i ≤ a) (n : Nat) :
    Nat.testBit (2 ^ a - 2 ^ i) n = (decide (i ≤ n) && decide (n < a)) := by
  have hm : 2 ^ a - 2 ^ i = 2 ^ i * (2 ^ (a - i) - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hia]
  rw [hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  simp only [ge_iff_le]
  by_cases hin : i ≤ n
  · have hsub : decide (n - i < a - i) = decide (n < a) := by
      apply decide_eq_decide.mpr
      omega
    simp [hin, hsub]
  · simp [hin]

/-- `land_mask_narrow` (`Z` version): a value already below `2^j`
    cannot see bits `>= j`, so masking it with `2^j - 2^i` and with
    `2^64 - 2^i` agree.  This is what `mkAnd`'s `narrow_mask` case needs
    (a mask `2^j - 2^i` is the alignment mask `-2^i` under `xhi`). -/
theorem land_mask_narrow {x i j : Nat} (hij : i ≤ j) (hj : j ≤ 64) (hx : x < 2 ^ j) :
    x &&& (2 ^ j - 2 ^ i) = x &&& (2 ^ 64 - 2 ^ i) := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and, Nat.testBit_and, testbit_pow_sub hij n, testbit_pow_sub (by omega) n]
  by_cases hnj : n < j
  · have h64 : n < 64 := by omega
    simp [hnj, h64]
  · have hxbit : Nat.testBit x n = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hxbit]
    rfl

/-- `2^64 - 2^j` and `-2^j` are the same word. -/
theorem Z_to_bv64_two64_sub_pow (j : Int) (hj0 : 0 ≤ j) (hj64 : j < 64) :
    Z_to_bv 64 (two64 - zpow 2 j) = Z_to_bv 64 (-(zpow 2 j)) := by
  apply word_eq_of_bv_unsigned
  have hpos : (0 : Int) < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hlt : zpow 2 j < 2 ^ 64 := by
    unfold zpow
    exact int_pow_lt_pow j.toNat 64 (by rw [Int.toNat_lt hj0]; exact hj64)
  rw [two64_eq, u_small ⟨by omega, by omega⟩, bv_unsigned_neg_pow2 j hj0 hj64]

theorem mkAnd0_high_id (E : env) (a : expr) (j : Int) (hj0 : 0 ≤ j) (hj64 : j < 64)
    (hmod : bv_unsigned (edenot E a) % zpow 2 j = 0) :
    edenot E a = alu64 .AND (edenot E a) (Z_to_bv 64 (-(zpow 2 j))) :=
  (and_mask_id (edenot E a) j hj0 hj64 hmod).symm

theorem mkAnd0_high_coeffs (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a : expr) (j : Int) (Hkn : know_ok segs E base kn)
    (hj0 : 0 ≤ j) (hj64 : j < 64)
    (Hdiv : coeffs_divk kn (zpow 2 j) (lin_of a).2 = true) :
    edenot E (unlin ((lin_of a).1 - (lin_of a).1 % zpow 2 j, (lin_of a).2))
      = alu64 .AND (edenot E a) (Z_to_bv 64 (-(zpow 2 j))) := by
  have hmpos : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hJ64 : j ≤ 64 := by omega
  rw [and_highmask_val (edenot E a) j hj0 hj64]
  have hcd : tden E (lin_of a).2 % zpow 2 j = 0 :=
    coeffs_divk_sound segs E base kn (zpow 2 j) (lin_of a).2 Hkn hmpos Hdiv
  have hsplit : lden E (lin_of a) % zpow 2 j = (lin_of a).1 % zpow 2 j := by
    simp only [lden]
    rw [Int.add_emod, hcd, Int.add_zero, Int.emod_emod]
  have hmod : bv_unsigned (edenot E a) % zpow 2 j = (lin_of a).1 % zpow 2 j :=
    (eqm_mod_pow2 (lden E (lin_of a)) (uE E a) j ⟨hj0, hJ64⟩ (lin_of_sound E a)).symm.trans hsplit
  rw [← Z_to_bv_unsigned (edenot E (unlin ((lin_of a).1 - (lin_of a).1 % zpow 2 j, (lin_of a).2)))]
  apply eqm_Z_to_bv
  refine eqm_trans (unlin_sound E ((lin_of a).1 - (lin_of a).1 % zpow 2 j, (lin_of a).2)) ?_
  obtain ⟨q, hq⟩ := lin_of_sound E a
  have hconv : uE E a = bv_unsigned (edenot E a) := rfl
  rw [hconv] at hq
  refine ⟨q, ?_⟩
  simp only [lden] at hq ⊢
  rw [hmod]
  omega

/-- `k < 2^(log2 k + 1)` for `k > 0` (the upper half of `Nat.log2`'s spec). -/
theorem zlog2_lt_pow_succ {k : Int} (hk : 0 < k) : k < zpow 2 (AxSymExec3.zlog2 k + 1) := by
  have hk0 : 0 ≤ k := by omega
  have hkn : k.toNat ≠ 0 := by
    intro h
    have h1 : k.toNat = 0 := h
    omega
  have hz : AxSymExec3.zlog2 k = (Nat.log2 k.toNat : Int) := by
    unfold AxSymExec3.zlog2
    rw [ite_eq_right (by omega)]
  have hlog0 : 0 ≤ (Nat.log2 k.toNat : Int) := Int.natCast_nonneg _
  rw [hz, zpow, Int.toNat_add (Int.natCast_nonneg _) (by decide), natCast_pow_two,
    ← Int.toNat_of_nonneg hk0]
  simp only [Int.toNat_natCast]
  have hspec := (Nat.log2_eq_iff hkn).mp rfl
  exact Int.ofNat_lt.mpr hspec.2

theorem mkAnd0_low_zero (E : env) (a : expr) (j : Int) (hj0 : 0 ≤ j) (hj64 : j < 64)
    (hmod : bv_unsigned (edenot E a) % zpow 2 j = 0) :
    Z_to_bv 64 0 = alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 j - 1)) := by
  rw [and_lowmask_val (edenot E a) j hj0 (by omega), hmod]

theorem mkAnd0_low_bits (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a : expr) (j : Int) (Hkn : know_ok segs E base kn)
    (hj0 : 0 ≤ j) (hj64 : j < 64) (v : Int) (H : lowbits kn a j = some v) :
    Z_to_bv 64 v = alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 j - 1)) := by
  rw [and_lowmask_val (edenot E a) j hj0 (by omega),
    lowbits_sound segs E base kn a j Hkn ⟨hj0, by omega⟩ v H]

theorem mkAnd0_low_kn (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a : expr) (j : Int) (Hkn : know_ok segs E base kn)
    (hj0 : 0 ≤ j) (hj64 : j < 64) (v : Int) (H : lin_lowbits_kn kn a j = some v) :
    Z_to_bv 64 v = alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 j - 1)) := by
  rw [and_lowmask_val (edenot E a) j hj0 (by omega),
    (lin_lowbits_kn_sound segs E base kn a j v Hkn ⟨hj0, by omega⟩ H).1]

/-- The J3e arm of `mkAnd0`: for a general literal mask `k` (below `2^64`,
    with `k < 2^j3` where `j3 = log2 k + 1`), the low `j3` bits decide the
    `AND`. -/
theorem mkAnd0_lit_mask (E : env) (kn : List kentry) (a : expr) (k v : Int)
    (hk0 : 0 < k) (hklt : k < 2 ^ 64) (hj3 : AxSymExec3.zlog2 k + 1 ≤ 64)
    (hmod : bv_unsigned (edenot E a) % zpow 2 (AxSymExec3.zlog2 k + 1) = v)
    (hv0 : 0 ≤ v) (hvlt : v < zpow 2 (AxSymExec3.zlog2 k + 1)) :
    Z_to_bv 64 (AxSymExec3.zland v k) = alu64 .AND (edenot E a) (Z_to_bv 64 k) := by
  have hj30 : 0 ≤ AxSymExec3.zlog2 k + 1 := by
    have := zlog2_nonneg k; omega
  have hzlt : zpow 2 (AxSymExec3.zlog2 k + 1) ≤ 2 ^ 64 := by
    unfold zpow
    exact int_pow_le_pow _ _ (by rw [Int.toNat_le]; omega)
  have hkj : k < zpow 2 (AxSymExec3.zlog2 k + 1) := zlog2_lt_pow_succ hk0
  apply word_eq_of_bv_unsigned
  have hua0 : 0 ≤ bv_unsigned (edenot E a) := (u64_range _).1
  have hualt : bv_unsigned (edenot E a) < 2 ^ 64 := (u64_range _).2
  have huam : bv_unsigned (edenot E a) % two64 = bv_unsigned (edenot E a) :=
    u_small_id _ ⟨hua0, hualt⟩
  have hkm : k % two64 = k := u_small_id _ ⟨by omega, hklt⟩
  have hvm : v % two64 = v := u_small_id _ ⟨hv0, by omega⟩
  -- the low `j3` bits of `a` and of `v` agree
  have hj3n : (AxSymExec3.zlog2 k + 1).toNat = Nat.log2 k.toNat + 1 := by
    have hz : AxSymExec3.zlog2 k = (Nat.log2 k.toNat : Int) := by
      unfold AxSymExec3.zlog2
      rw [ite_eq_right (by omega)]
    rw [hz]
    show ((Nat.log2 k.toNat : Int) + ((1 : Nat) : Int)).toNat = Nat.log2 k.toNat + 1
    rw [Int.toNat_add_nat (Int.natCast_nonneg _), Int.toNat_natCast]
  have hmodNat : v.toNat
      = (bv_unsigned (edenot E a)).toNat % 2 ^ (Nat.log2 k.toNat + 1) := by
    have h1 : v = bv_unsigned (edenot E a) % ((2 ^ (AxSymExec3.zlog2 k + 1).toNat : Nat) : Int) := by
      rw [← natCast_pow_two]; exact hmod.symm
    rw [h1, hj3n, Int.toNat_emod hua0 (Int.natCast_nonneg _)]
    rfl
  have hkjNat : k.toNat < 2 ^ (Nat.log2 k.toNat + 1) := by
    have h1 : k.toNat < (zpow 2 (AxSymExec3.zlog2 k + 1)).toNat := (Int.toNat_lt (by omega : (0:Int) ≤ k)).mpr hkj
    rwa [zpow, natCast_pow_two, Int.toNat_natCast, hj3n] at h1
  have hnat : v.toNat &&& k.toNat = (bv_unsigned (edenot E a)).toNat &&& k.toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_and, hmodNat]
    by_cases hi : i < Nat.log2 k.toNat + 1
    · simp [Nat.testBit_mod_two_pow, hi]
    · have hkbit : Nat.testBit k.toNat i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hkjNat
          (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hkbit]
      simp
  have hzland : AxSymExec3.zland v k = ((v.toNat &&& k.toNat : Nat) : Int) := by
    unfold AxSymExec3.zland
    rw [hvm, hkm]
  have hzland2 : AxSymExec3.zland (bv_unsigned (edenot E a)) (k % two64)
      = (((bv_unsigned (edenot E a)).toNat &&& k.toNat : Nat) : Int) := by
    unfold AxSymExec3.zland
    rw [huam]
    have hk2 : k % two64 % two64 = k := by rw [Int.emod_emod, hkm]
    rw [hk2]
  have hzlt2 : AxSymExec3.zland v k < 2 ^ 64 := by
    rw [hzland]
    have h1 : (v.toNat &&& k.toNat) < 2 ^ 64 :=
      Nat.and_lt_two_pow _ (Nat.lt_of_lt_of_le hkjNat (Nat.pow_le_pow_right (by decide) (by omega)))
    exact_mod_cast h1
  have hz0 : 0 ≤ AxSymExec3.zland v k := by
    rw [hzland]; exact Int.natCast_nonneg _
  rw [u_small ⟨hz0, hzlt2⟩, u_and64, u_lit64, hzland, hzland2, hnat]
/-- `mkAnd0_denot`: the smart AND constructor denotes the AND.
    The case bash peels `mkAnd0`'s `if`/`match` chain and hands each arm to
    the local arm lemma; the J3e arm is `mkAnd0_lit_mask`, whose `Nat`
    bit argument is this tree's replacement for `Z.log2_land` /
    `Z.bits_above_log2`. -/
theorem mkAnd0_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a b : expr) (Hkn : know_ok segs E base kn) :
    edenot E (mkAnd0 kn a b) = alu64 .AND (edenot E a) (edenot E b) := by
  obtain ⟨-, hEdiv⟩ := ealign_sound segs E base kn a Hkn
  cases b with
  | ELit k =>
    unfold mkAnd0
    try simp only []
    have hk'lt : k % two64 < 2 ^ 64 := by
      have h := Int.emod_lt_of_pos k two64_pos
      rw [two64_eq] at h ⊢
      exact h
    have Hbk : Z_to_bv 64 k = Z_to_bv 64 (k % two64) := (Z_to_bv_emod64 k).symm
    split
    · rename_i hc
      obtain ⟨hpwb, hj64b⟩ := (Bool.and_eq_true ..).mp hc
      have hpw : two64 - k % two64 = zpow 2 (AxSymExec3.zlog2 (two64 - k % two64)) := beq_iff_eq.mp hpwb
      have hj64 : AxSymExec3.zlog2 (two64 - k % two64) < 64 := of_decide_eq_true hj64b
      have hj0 : 0 ≤ AxSymExec3.zlog2 (two64 - k % two64) := zlog2_nonneg _
      have Hbmask : edenot E (.ELit k)
          = Z_to_bv 64 (-(zpow 2 (AxSymExec3.zlog2 (two64 - k % two64)))) := by
        show Z_to_bv 64 k = Z_to_bv 64 (-(zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))))
        rw [Hbk]
        have hk'eq : k % two64
            = two64 - zpow 2 (AxSymExec3.zlog2 (two64 - k % two64)) := by omega
        conv => lhs; rw [hk'eq]
        exact Z_to_bv64_two64_sub_pow _ hj0 hj64
      split
      · rename_i hle
        rw [Hbmask]
        exact mkAnd0_high_id E a _ hj0 hj64
          (Int.emod_eq_zero_of_dvd (Int.dvd_trans (pow2_divide_le _ _ ⟨hj0, hle⟩) hEdiv))
      · split
        · rename_i hcd
          have hcd2 : coeffs_divk kn (zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))) (lin_of a).2 = true :=
            (Bool.and_eq_true ..).mp hcd |>.2
          rw [Hbmask]
          exact mkAnd0_high_coeffs segs E base kn a _ Hkn hj0 hj64 hcd2
        · rw [Hbmask]
          have R6 : edenot E (mkMd .MUL (.ELit (zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))))
              (mkSrl kn a (AxSymExec3.zlog2 (two64 - k % two64))))
              = alu64 .AND (edenot E a) (Z_to_bv 64 (-(zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))))) := by
            rw [and_highmask_val (edenot E a) _ hj0 hj64]
            exact and_highmask_srl segs E base kn a _ Hkn hj0 hj64
          cases hsp : (if lin_trivial (lin_of a) = true then ([], (lin_of a).2)
              else lsplit_div kn (zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))) (lin_of a).2) with
          | mk dts rts =>
            try simp only []
            cases dts with
            | nil => exact R6
            | cons d1 dts' =>
              cases rts with
              | nil => exact R6
              | cons r1 rts' =>
                obtain ⟨-, hsp'⟩ : lin_trivial (lin_of a) = false ∧
                    lsplit_div kn (zpow 2 (AxSymExec3.zlog2 (two64 - k % two64))) (lin_of a).2
                      = (d1 :: dts', r1 :: rts') := by
                  cases hb : lin_trivial (lin_of a) with
                  | false =>
                    rw [hb] at hsp
                    exact ⟨rfl, by simpa using hsp⟩
                  | true =>
                    rw [hb] at hsp
                    exact absurd hsp (by simp)
                obtain ⟨hdiv, hsum⟩ := lsplit_div_sound kn (zpow 2 (AxSymExec3.zlog2 (two64 - k % two64)))
                  (lin_of a).2 (d1 :: dts') (r1 :: rts') hsp'
                refine and_high_split_denot segs E base kn (.ELit k)
                  (AxSymExec3.zlog2 (two64 - k % two64)) (lin_of a).1 (d1 :: dts') (r1 :: rts') a
                  Hkn hj0 hj64 Hbmask hdiv ?_
                have hsf := lin_of_sound E a
                simp only [lden] at hsf
                rw [hsum E] at hsf
                exact eqm_trans (eqm_sym hsf) ⟨0, by omega⟩
    · rename_i hcB
      try simp only []
      split
      · rename_i hc2
        obtain ⟨hpwb, hj64b⟩ := (Bool.and_eq_true ..).mp hc2
        have hpw2 : k % two64 + 1 = zpow 2 (AxSymExec3.zlog2 (k % two64 + 1)) := beq_iff_eq.mp hpwb
        have hj264 : AxSymExec3.zlog2 (k % two64 + 1) < 64 := of_decide_eq_true hj64b
        have hj20 : 0 ≤ AxSymExec3.zlog2 (k % two64 + 1) := zlog2_nonneg _
        have Hbmask2 : edenot E (.ELit k)
            = Z_to_bv 64 (zpow 2 (AxSymExec3.zlog2 (k % two64 + 1)) - 1) := by
          show Z_to_bv 64 k = Z_to_bv 64 (zpow 2 (AxSymExec3.zlog2 (k % two64 + 1)) - 1)
          rw [Hbk]
          congr 1
          omega
        split
        · rename_i hle
          rw [Hbmask2]
          exact mkAnd0_low_zero E a _ hj20 hj264
            (Int.emod_eq_zero_of_dvd (Int.dvd_trans (pow2_divide_le _ _ ⟨hj20, hle⟩) hEdiv))
        · cases hlow : lowbits kn a (AxSymExec3.zlog2 (k % two64 + 1)) with
          | some v =>
            try simp only []
            rw [Hbmask2]
            exact mkAnd0_low_bits segs E base kn a _ Hkn hj20 hj264 v hlow
          | none =>
            try simp only []
            split
            · rw [mkAlu_denot]
            · cases hlb : lin_lowbits_kn kn a (AxSymExec3.zlog2 (k % two64 + 1)) with
              | some v =>
                try simp only []
                rw [Hbmask2]
                exact mkAnd0_low_kn segs E base kn a _ Hkn hj20 hj264 v hlb
              | none =>
                try simp only []
                cases hsp : lsplit_div kn (zpow 2 (AxSymExec3.zlog2 (k % two64 + 1))) (lin_of a).2 with
                | mk dts rts =>
                  try simp only []
                  cases dts with
                  | nil => rw [mkAlu_denot]
                  | cons d1 dts' =>
                    cases rts with
                    | nil => rw [mkAlu_denot]
                    | cons r1 rts' =>
                      rw [Hbmask2]
                      obtain ⟨hdiv, hsum⟩ := lsplit_div_sound kn (zpow 2 (AxSymExec3.zlog2 (k % two64 + 1)))
                        (lin_of a).2 (d1 :: dts') (r1 :: rts') hsp
                      refine and_low_split_denot segs E base kn (.ELit k)
                        (AxSymExec3.zlog2 (k % two64 + 1)) (lin_of a).1 (d1 :: dts') (r1 :: rts') a
                        Hkn hj20 hj264 Hbmask2 hdiv ?_
                      have hsf := lin_of_sound E a
                      simp only [lden] at hsf
                      rw [hsum E] at hsf
                      exact eqm_trans (eqm_sym hsf) ⟨0, by omega⟩
      · rename_i hcJ
        split
        · rename_i hc3
          obtain ⟨hc31, hntr⟩ := (Bool.and_eq_true ..).mp hc3
          obtain ⟨hk0b, hj3b⟩ := (Bool.and_eq_true ..).mp hc31
          have hk0 : 0 < k % two64 := of_decide_eq_true hk0b
          have hj3 : AxSymExec3.zlog2 (k % two64) + 1 ≤ 64 := of_decide_eq_true hj3b
          cases hlb : lin_lowbits_kn kn a (AxSymExec3.zlog2 (k % two64) + 1) with
          | none => rw [mkAlu_denot]
          | some v =>
            try simp only []
            have hspec := lin_lowbits_kn_sound segs E base kn a _ v Hkn ⟨by have := zlog2_nonneg (k % two64); omega, hj3⟩ hlb
            show Z_to_bv 64 (AxSymExec3.zland v (k % two64)) = alu64 .AND (edenot E a) (Z_to_bv 64 k)
            rw [Hbk]
            exact mkAnd0_lit_mask E kn a (k % two64) v hk0 hk'lt hj3 hspec.1 hspec.2.1 hspec.2.2
        · rw [mkAlu_denot]
  | EVar n => exact mkAlu_denot E .AND a _
  | EAlu op a1 b1 => exact mkAlu_denot E .AND a _
  | EAluw op a1 b1 => exact mkAlu_denot E .AND a _
  | EMd op a1 b1 => exact mkAlu_denot E .AND a _
  | EMdw op a1 b1 => exact mkAlu_denot E .AND a _
  | EExt sx lo n a1 => exact mkAlu_denot E .AND a _
  | EBlob sx k i n => exact mkAlu_denot E .AND a _
/-! ## Part P4i: `land_mask_narrow` and the `mkAnd` denotation


    `mkAnd`'s `narrow_mask` pre-case rewrites a mask `2^j - 2^i` into the
    plain alignment mask `2^64 - 2^i` (sound because the operand is below
    `2^j`, from `xhi`). -/

/-- `zland` already reduces its second argument mod `2^64`. -/
theorem zland_emod (x y : Int) : AxSymExec3.zland x (y % two64) = AxSymExec3.zland x y := by
  unfold AxSymExec3.zland
  rw [Int.emod_emod]

/-- `2^64 - 2^i` and `2^j - 2^i` are the same `Nat` difference at `Int`. -/
theorem two64_sub_pow_natCast (i : Int) (hi64 : i ≤ 64) :
    two64 - zpow 2 i = ((2 ^ 64 - 2 ^ i.toNat : Nat) : Int) := by
  have hiN : i.toNat ≤ 64 := by
    have h := Int.toNat_le_toNat hi64
    simpa using h
  unfold zpow
  rw [two64_eq_natCast, natCast_pow_two]
  exact (Int.natCast_sub (Nat.pow_le_pow_right (by decide) hiN)).symm

/-- The `Nat` `land_mask_narrow`, lifted to `zland`: a value below `2^j`
    cannot tell the masks `2^64 - 2^i` and `2^j - 2^i` apart. -/
theorem zland_mask_narrow (x i j : Int) (hij : i ≤ j) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j)
    (hj64 : j ≤ 64) (hx : 0 ≤ x ∧ x < zpow 2 j) :
    AxSymExec3.zland x (two64 - zpow 2 i) = AxSymExec3.zland x (zpow 2 j - zpow 2 i) := by
  have i64 : i ≤ 64 := by omega
  have hpi : 0 < zpow 2 i := by unfold zpow; exact two_pow_pos_int i.toNat
  have hpj : 0 < zpow 2 j := by unfold zpow; exact two_pow_pos_int j.toNat
  have hjle : zpow 2 j ≤ 2 ^ 64 := by
    unfold zpow
    exact int_pow_le_pow _ _ (by rw [Int.toNat_le]; omega)
  have hile : zpow 2 i ≤ zpow 2 j := by
    unfold zpow
    exact int_pow_le_pow _ _ (Int.toNat_le_toNat hij)
  have hA : (two64 - zpow 2 i) % two64 = two64 - zpow 2 i := by
    rw [two64_eq]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hB : (zpow 2 j - zpow 2 i) % two64 = zpow 2 j - zpow 2 i := by
    rw [two64_eq]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hx64 : x % two64 = x := by
    rw [two64_eq]
    exact Int.emod_eq_of_lt hx.1 (by omega)
  have e1 : (two64 - zpow 2 i).toNat = 2 ^ 64 - 2 ^ i.toNat := by
    rw [two64_sub_pow_natCast i i64, Int.toNat_natCast]
  have e2 : (zpow 2 j - zpow 2 i).toNat = 2 ^ j.toNat - 2 ^ i.toNat := by
    have hjN : j.toNat ≤ 64 := by
      have h := Int.toNat_le_toNat hj64
      simpa using h
    have he : zpow 2 j - zpow 2 i = ((2 ^ j.toNat - 2 ^ i.toNat : Nat) : Int) := by
      unfold zpow
      rw [natCast_pow_two, natCast_pow_two]
      exact (Int.natCast_sub (Nat.pow_le_pow_right (by decide) (by omega))).symm
    rw [he, Int.toNat_natCast]
  unfold AxSymExec3.zland
  rw [hx64, hA, hB, e1, e2]
  have hxN : x.toNat < 2 ^ j.toNat := by
    have h := hx.2
    rw [zpow, natCast_pow_two] at h
    have h1 : (x.toNat : Int) < ((2 ^ j.toNat : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hx.1]; exact h
    exact Int.ofNat_lt.mp h1
  have hiN : i.toNat ≤ j.toNat := Int.toNat_le_toNat hij
  have hjN : j.toNat ≤ 64 := by
    have h := Int.toNat_le_toNat hj64
    simpa using h
  exact_mod_cast (land_mask_narrow hiN hjN hxN).symm

theorem mkAnd_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a b : expr) (Hkn : know_ok segs E base kn) :
    edenot E (mkAnd kn a b) = alu64 .AND (edenot E a) (edenot E b) := by
  cases b with
  | ELit k =>
    unfold mkAnd
    try simp only []
    cases Hn : narrow_mask kn a (k % two64) with
    | none => exact mkAnd0_denot segs E base kn a (.ELit k) Hkn
    | some mval =>
      try simp only []
      unfold narrow_mask at Hn
      try simp only [] at Hn
      split at Hn
      · rename_i hc
        obtain ⟨hc1, hj64b⟩ := (Bool.and_eq_true ..).mp hc
        obtain ⟨hk0b, hpwb⟩ := (Bool.and_eq_true ..).mp hc1
        have hk0 : 0 < k % two64 := of_decide_eq_true hk0b
        have hj64 : AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64))) < 64 :=
          of_decide_eq_true hj64b
        have hpw : k % two64 + zpow 2 (ctz64 (k % two64))
            = zpow 2 (AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64)))) :=
          beq_iff_eq.mp hpwb
        split at Hn
        · rename_i hval Hxhi
          split at Hn
          · rename_i hlt
            have hmval : mval = two64 - zpow 2 (ctz64 (k % two64)) := by
              injection Hn with h
              omega
            have hj0 : 0 ≤ AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64))) :=
              zlog2_nonneg _
            have hi0 : 0 ≤ ctz64 (k % two64) := (ctz64_sound (k % two64)).1.1
            have huaj : bv_unsigned (edenot E a)
                < zpow 2 (AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64)))) := by
              have h1 := xhi_sound segs E base kn a hval Hkn Hxhi
              omega
            have hpij : zpow 2 (ctz64 (k % two64))
                < zpow 2 (AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64)))) := by omega
            have hij : ctz64 (k % two64)
                < AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64))) := by
              have hN : (2 : Nat) ^ (ctz64 (k % two64)).toNat
                  < 2 ^ (AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64)))).toNat := by
                have h := hpij
                unfold zpow at h
                rw [natCast_pow_two, natCast_pow_two] at h
                exact_mod_cast h
              have h2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hN
              have h3 : ctz64 (k % two64)
                  < ((AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64)))).toNat : Nat) :=
                (Int.toNat_lt hi0).mp h2
              rwa [Int.toNat_of_nonneg hj0] at h3
            rw [mkAnd0_denot segs E base kn a (.ELit mval) Hkn]
            change alu64 .AND (edenot E a) (Z_to_bv 64 mval)
              = alu64 .AND (edenot E a) (Z_to_bv 64 k)
            rw [hmval]
            have hbk : Z_to_bv 64 k = Z_to_bv 64 (k % two64) := (Z_to_bv_emod64 k).symm
            have hk'eq : k % two64
                = zpow 2 (AxSymExec3.zlog2 (k % two64 + zpow 2 (ctz64 (k % two64))))
                  - zpow 2 (ctz64 (k % two64)) := by omega
            rw [hbk]
            conv => rhs; rw [hk'eq]
            apply word_eq_of_bv_unsigned
            rw [u_and64, u_and64, u_lit64, u_lit64, zland_emod, zland_emod]
            exact zland_mask_narrow _ _ _ (by omega) hi0 hj0 (by omega)
              ⟨(u64_range _).1, huaj⟩
          · exact absurd Hn (by simp)
        · exact absurd Hn (by simp)
      · exact absurd Hn (by simp)
  | EVar n => exact mkAnd0_denot segs E base kn a (.EVar n) Hkn
  | EAlu op a1 b1 => exact mkAnd0_denot segs E base kn a (.EAlu op a1 b1) Hkn
  | EAluw op a1 b1 => exact mkAnd0_denot segs E base kn a (.EAluw op a1 b1) Hkn
  | EMd op a1 b1 => exact mkAnd0_denot segs E base kn a (.EMd op a1 b1) Hkn
  | EMdw op a1 b1 => exact mkAnd0_denot segs E base kn a (.EMdw op a1 b1) Hkn
  | EExt sx lo n a1 => exact mkAnd0_denot segs E base kn a (.EExt sx lo n a1) Hkn
  | EBlob sx k i n => exact mkAnd0_denot segs E base kn a (.EBlob sx k i n) Hkn
/-! ## Part P4j: `mkAndK`

    `mkAndK` merges the mask of `x & m1` with a following literal mask, in
    both the plain `.EAlu .AND` spelling and the R6 spelling
    `2^i * (x >> i)` of `x & -2^i`.  Both cases are instances of the
    MERGE step (`mkAnd_denot` + `zland` associativity); the R6 value
    identity is `r6_mul_srl_val`. -/

/-- `zland` values are in the 64-bit window. -/
theorem zland_lt (x y : Int) :
    0 ≤ AxSymExec3.zland x y ∧ AxSymExec3.zland x y < 2 ^ 64 := by
  have hy : (y % two64).toNat < 2 ^ 64 := by
    rw [two64_eq]
    exact (Int.toNat_lt (Int.emod_nonneg _ two64_ne)).mpr (Int.emod_lt_of_pos _ two64_pos)
  have e : AxSymExec3.zland x y = ((x % two64).toNat &&& (y % two64).toNat : Nat) := rfl
  rw [e]
  constructor
  · exact Int.natCast_nonneg _
  · have h : ((x % two64).toNat &&& (y % two64).toNat) < 2 ^ 64 := Nat.and_lt_two_pow _ hy
    exact_mod_cast h

/-- `zland` is associative (the `Nat` `&&&` is). -/
theorem zland_assoc (x y z : Int) :
    AxSymExec3.zland (AxSymExec3.zland x y) z
      = AxSymExec3.zland x (AxSymExec3.zland y z) := by
  have hy : (y % two64).toNat < 2 ^ 64 := by
    rw [two64_eq]
    exact (Int.toNat_lt (Int.emod_nonneg _ two64_ne)).mpr (Int.emod_lt_of_pos _ two64_pos)
  have hz : (z % two64).toNat < 2 ^ 64 := by
    rw [two64_eq]
    exact (Int.toNat_lt (Int.emod_nonneg _ two64_ne)).mpr (Int.emod_lt_of_pos _ two64_pos)
  have hA : ((x % two64).toNat &&& (y % two64).toNat) < 2 ^ 64 := Nat.and_lt_two_pow _ hy
  have hB : ((y % two64).toNat &&& (z % two64).toNat) < 2 ^ 64 := Nat.and_lt_two_pow _ hz
  have hmod : (↑((x % two64).toNat &&& (y % two64).toNat) : Int) % two64
      = ↑((x % two64).toNat &&& (y % two64).toNat) := by
    rw [two64_eq]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hA)
  have hmod2 : (↑((y % two64).toNat &&& (z % two64).toNat) : Int) % two64
      = ↑((y % two64).toNat &&& (z % two64).toNat) := by
    rw [two64_eq]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hB)
  have e1 : AxSymExec3.zland x y = ((x % two64).toNat &&& (y % two64).toNat : Nat) := rfl
  have e2 : AxSymExec3.zland y z = ((y % two64).toNat &&& (z % two64).toNat : Nat) := rfl
  rw [e1, e2]
  unfold AxSymExec3.zland
  rw [hmod, hmod2, Int.toNat_natCast, Int.toNat_natCast, Nat.and_assoc]

/-- The R6 spelling of `x & -2^i`: `2^i * (x >> i)` has the high-mask value. -/
theorem r6_mul_srl_val (x : word) (m i : Int)
    (hi0 : 0 ≤ i % two64 % 64) (hi64 : i % two64 % 64 < 64)
    (hm : m % two64 = zpow 2 (i % two64 % 64)) :
    bv_unsigned (mul_div .MUL (Z_to_bv 64 m) (alu64 .SRL x (Z_to_bv 64 i)))
      = AxSymExec3.zland (bv_unsigned x) (two64 - zpow 2 (i % two64 % 64)) := by
  have hbm : bv_unsigned (Z_to_bv 64 m) = zpow 2 (i % two64 % 64) := by
    rw [u_lit64, hm]
  have hbvi : bv_unsigned (Z_to_bv 64 i) % 64 = i % two64 % 64 := by rw [u_lit64]
  have hsrl : bv_unsigned (alu64 .SRL x (Z_to_bv 64 i))
      = bv_unsigned x / zpow 2 (i % two64 % 64) := by
    rw [u_srl64, hbvi]
    rfl
  have hd : 0 < zpow 2 (i % two64 % 64) := by unfold zpow; exact two_pow_pos_int _
  have hx0 : 0 ≤ bv_unsigned x := (u64_range x).1
  have hxlt : bv_unsigned x < 2 ^ 64 := (u64_range x).2
  have hmle : bv_unsigned x % zpow 2 (i % two64 % 64) ≤ bv_unsigned x :=
    emod_le_self _ _ hx0 hd
  have hm0 : 0 ≤ bv_unsigned x % zpow 2 (i % two64 % 64) := Int.emod_nonneg _ (by omega)
  have hY : AxSymExec3.zland (bv_unsigned x) (two64 - zpow 2 (i % two64 % 64))
      = bv_unsigned x - bv_unsigned x % zpow 2 (i % two64 % 64) :=
    land_highmask _ _ ⟨hi0, hi64⟩ ⟨hx0, hxlt⟩
  have hE : eqm (bv_unsigned (mul_div .MUL (Z_to_bv 64 m) (alu64 .SRL x (Z_to_bv 64 i))))
      (bv_unsigned x - bv_unsigned x % zpow 2 (i % two64 % 64)) := by
    refine eqm_trans (u_mul_eqm (Z_to_bv 64 m) (alu64 .SRL x (Z_to_bv 64 i))) ?_
    rw [hbm, hsrl]
    refine ⟨0, ?_⟩
    have hdm := Int.ediv_mul_add_emod (bv_unsigned x) (zpow 2 (i % two64 % 64))
    rw [Int.mul_comm (zpow 2 (i % two64 % 64)) (bv_unsigned x / zpow 2 (i % two64 % 64))]
    omega
  have hY0 : 0 ≤ bv_unsigned x - bv_unsigned x % zpow 2 (i % two64 % 64) := by omega
  have hYlt : bv_unsigned x - bv_unsigned x % zpow 2 (i % two64 % 64) < 2 ^ 64 := by omega
  have hmod := eqm_mod_pow2 _ _ 64 ⟨by omega, by omega⟩ hE
  rw [hY]
  rw [show zpow 2 (64 : Int) = 2 ^ 64 from rfl] at hmod
  rw [Int.emod_eq_of_lt (u64_range _).1 (u64_range _).2,
    Int.emod_eq_of_lt hY0 hYlt] at hmod
  exact hmod

/-- `mkAndK_denot`: the mask-merge constructor denotes the AND. -/
theorem mkAndK_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a b : expr) (Hkn : know_ok segs E base kn) :
    edenot E (mkAndK kn a b) = alu64 .AND (edenot E a) (edenot E b) := by
  have MERGE : ∀ (x : expr) (M1 k : Int) (aw : word), 0 ≤ M1 → M1 < two64 →
      bv_unsigned aw = AxSymExec3.zland (bv_unsigned (edenot E x)) M1 →
      edenot E (mkAnd kn x (.ELit (AxSymExec3.zland M1 (k % two64))))
        = alu64 .AND aw (Z_to_bv 64 k) := by
    intro x M1 k aw hM10 hM1lt Ha
    rw [mkAnd_denot segs E base kn x (.ELit (AxSymExec3.zland M1 (k % two64))) Hkn]
    change alu64 .AND (edenot E x) (Z_to_bv 64 (AxSymExec3.zland M1 (k % two64)))
      = alu64 .AND aw (Z_to_bv 64 k)
    apply word_eq_of_bv_unsigned
    rw [u_and64, u_and64, u_lit64, u_lit64, Ha]
    conv => lhs; rw [zland_emod]
    exact (zland_assoc (bv_unsigned (edenot E x)) M1 (k % two64)).symm
  unfold mkAndK
  split
  · rename_i ha hb x m1 k
    refine MERGE x (m1 % two64) k (edenot E (.EAlu .AND x (.ELit m1)))
      (Int.emod_nonneg _ two64_ne) ?_ ?_
    · have h := Int.emod_lt_of_pos m1 two64_pos
      rw [two64_eq] at h ⊢
      exact h
    · show bv_unsigned (alu64 .AND (edenot E x) (Z_to_bv 64 m1))
        = AxSymExec3.zland (bv_unsigned (edenot E x)) (m1 % two64)
      rw [u_and64, u_lit64]
  · rename_i ha hb m x i k
    try simp only []
    split
    · rename_i hm
      have hmem : m % two64 = zpow 2 (i % two64 % 64) := beq_iff_eq.mp hm
      have hi0 : 0 ≤ i % two64 % 64 := Int.emod_nonneg _ (by decide)
      have hi64 : i % two64 % 64 < 64 := by
        have h := Int.emod_lt_of_pos (i % two64) (by decide : (0 : Int) < 64)
        simpa using h
      refine MERGE x (two64 - zpow 2 (i % two64 % 64)) k
        (edenot E (.EMd .MUL (.ELit m) (.EAlu .SRL x (.ELit i)))) ?_ ?_ ?_
      · have hp : 0 < zpow 2 (i % two64 % 64) := by unfold zpow; exact two_pow_pos_int _
        have h2 : zpow 2 (i % two64 % 64) ≤ 2 ^ 64 := by
          unfold zpow
          exact int_pow_le_pow _ _ (by rw [Int.toNat_le]; omega)
        have h3 : zpow 2 (i % two64 % 64) ≤ two64 := by rwa [← two64_eq] at h2
        omega
      · have hp : 0 < zpow 2 (i % two64 % 64) := by unfold zpow; exact two_pow_pos_int _
        omega
      · exact r6_mul_srl_val (edenot E x) m i hi0 hi64 hmem
    · exact mkAnd_denot segs E base kn _ (.ELit k) Hkn
  · exact mkAnd_denot segs E base kn a b Hkn
/-! ## Part P4k: the exact linear comparison

    `lin_branch_sound`: `lin_branch` (the `EQ`/`NE` linear-arithmetic step
    and the `LT`/`GE`/`LTU`/`GEU` unsigned comparison, with the signed
    cases reduced to the unsigned one on one half) decides the branch.
    The arm facts are the local `Hltu` (from `lin_ge0_sound`), `Hsgn`
    (`bv_lts_eq_ltu_small`), `Hne` and `Heq` (from `lin_ge0_sound` on both
    directions). -/

/-- `lin_branch_sound`: the exact linear comparison decides the
    branch. -/
theorem lin_branch_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (c : BranchCond) (a b : expr) (t : Bool)
    (Hkn : know_ok segs E base kn) (H : lin_branch kn c a b = some t) :
    branch_taken c (edenot E a) (edenot E b) = t := by
  have Hltu : ∀ t', (if lin_ge0 kn [(b, -1)] [(a, 0)] then some true
      else if lin_ge0 kn [(a, 0)] [(b, 0)] then some false else none) = some t' →
      bv_ltu (edenot E a) (edenot E b) = t' := by
    intro t' Ht
    split at Ht
    · rename_i g1
      have ht : t' = true := (Option.some.inj Ht).symm
      rw [ht, bv_ltu_eq_true]
      have L := lin_ge0_sound segs E base kn [(b, -1)] [(a, 0)] Hkn g1
      simp only [xt_den] at L
      omega
    · split at Ht
      · rename_i g2
        have ht : t' = false := (Option.some.inj Ht).symm
        rw [ht]
        cases hb : bv_ltu (edenot E a) (edenot E b) with
        | false => rfl
        | true =>
          rw [bv_ltu_eq_true] at hb
          have L := lin_ge0_sound segs E base kn [(a, 0)] [(b, 0)] Hkn g2
          simp only [xt_den] at L
          omega
      · exact absurd Ht (by simp)
  have Hsgn : ∀ (al ah bl bh : Int), erange kn a = some (al, ah) →
      erange kn b = some (bl, bh) → (ah < zpow 2 63 && bh < zpow 2 63) = true →
      bv_lts (edenot E a) (edenot E b) = bv_ltu (edenot E a) (edenot E b) := by
    intro al ah bl bh Ha Hb Hc
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true ..).mp Hc
    have h1' : ah < zpow 2 63 := of_decide_eq_true h1
    have h2' : bh < zpow 2 63 := of_decide_eq_true h2
    have Ra := erange_sound segs E base kn a al ah Hkn Ha
    have Rb := erange_sound segs E base kn b bl bh Hkn Hb
    exact bv_lts_eq_ltu_small _ _ (by omega) (by omega)
  have Hne : (lin_ge0 kn [(b, -1)] [(a, 0)] || lin_ge0 kn [(a, -1)] [(b, 0)]) = true →
      bv_eqb (edenot E a) (edenot E b) = false := by
    intro Hor
    have hne : bv_unsigned (edenot E a) ≠ bv_unsigned (edenot E b) := by
      rw [Bool.or_eq_true] at Hor
      intro he
      rcases Hor with G | G
      · have L := lin_ge0_sound segs E base kn [(b, -1)] [(a, 0)] Hkn G
        simp only [xt_den] at L
        omega
      · have L := lin_ge0_sound segs E base kn [(a, -1)] [(b, 0)] Hkn G
        simp only [xt_den] at L
        omega
    have hw : edenot E a ≠ edenot E b := by
      intro hw'
      exact hne (by rw [hw'])
    exact bv_eqb_neq _ _ hw
  have Heq : lin_ge0 kn [(a, 0)] [(b, 0)] = true → lin_ge0 kn [(b, 0)] [(a, 0)] = true →
      bv_eqb (edenot E a) (edenot E b) = true := by
    intro G1 G2
    have L1 := lin_ge0_sound segs E base kn [(a, 0)] [(b, 0)] Hkn G1
    have L2 := lin_ge0_sound segs E base kn [(b, 0)] [(a, 0)] Hkn G2
    simp only [xt_den] at L1 L2
    have hux : bv_unsigned (edenot E a) = bv_unsigned (edenot E b) := by omega
    have hw : edenot E a = edenot E b := word_eq_of_bv_unsigned hux
    rw [bv_eqb, beq_iff_eq.mpr hw]
  unfold lin_branch at H
  try simp only [] at H
  cases c with
  | LTU => exact Hltu t H
  | GEU =>
    cases hl : (if lin_ge0 kn [(b, -1)] [(a, 0)] then some true
        else if lin_ge0 kn [(a, 0)] [(b, 0)] then some false else none) with
    | none => rw [hl] at H; simp at H
    | some t' =>
      rw [hl] at H
      simp only [Option.map] at H
      have ht : t = !t' := (Option.some.inj H).symm
      rw [ht]
      have h1 := Hltu t' hl
      show (!(bv_ltu (edenot E a) (edenot E b))) = !t'
      rw [h1]
  | LT =>
    cases ha : erange kn a with
    | none => rw [ha] at H; simp at H
    | some p =>
      obtain ⟨al, ah⟩ := p
      cases hb : erange kn b with
      | none => rw [ha, hb] at H; simp at H
      | some q =>
        obtain ⟨bl, bh⟩ := q
        rw [ha, hb] at H
        try simp only [] at H
        split at H
        · rename_i hc
          have hs := Hsgn al ah bl bh ha hb hc
          show bv_lts (edenot E a) (edenot E b) = t
          rw [hs]
          exact Hltu t H
        · exact absurd H (by simp)
  | GE =>
    cases ha : erange kn a with
    | none => rw [ha] at H; simp at H
    | some p =>
      obtain ⟨al, ah⟩ := p
      cases hb : erange kn b with
      | none => rw [ha, hb] at H; simp at H
      | some q =>
        obtain ⟨bl, bh⟩ := q
        rw [ha, hb] at H
        try simp only [] at H
        split at H
        · rename_i hc
          have hs := Hsgn al ah bl bh ha hb hc
          cases hl : (if lin_ge0 kn [(b, -1)] [(a, 0)] then some true
              else if lin_ge0 kn [(a, 0)] [(b, 0)] then some false else none) with
          | none => rw [hl] at H; simp at H
          | some t' =>
            rw [hl] at H
            simp only [Option.map] at H
            have ht : t = !t' := (Option.some.inj H).symm
            rw [ht]
            have h1 := Hltu t' hl
            show (!(bv_lts (edenot E a) (edenot E b))) = !t'
            rw [hs, h1]
        · exact absurd H (by simp)
  | EQ =>
    try simp only [] at H
    by_cases hor : (lin_ge0 kn [(b, -1)] [(a, 0)] || lin_ge0 kn [(a, -1)] [(b, 0)]) = true
    · rw [ite_eq_left hor] at H
      try simp only [] at H
      have ht : t = false := (Option.some.inj H).symm
      rw [ht]
      exact Hne hor
    · rw [ite_eq_right hor] at H
      try simp only [] at H
      by_cases hC : lin_ge0 kn [(a, 0)] [(b, 0)] = true
      · rw [ite_eq_left hC] at H
        try simp only [] at H
        by_cases hD : lin_ge0 kn [(b, 0)] [(a, 0)] = true
        · rw [ite_eq_left hD] at H
          try simp only [] at H
          have ht : t = true := (Option.some.inj H).symm
          rw [ht]
          exact Heq hC hD
        · rw [ite_eq_right hD] at H
          exact absurd H (by simp)
      · rw [ite_eq_right hC] at H
        exact absurd H (by simp)
  | NE =>
    try simp only [] at H
    by_cases hor : (lin_ge0 kn [(b, -1)] [(a, 0)] || lin_ge0 kn [(a, -1)] [(b, 0)]) = true
    · rw [ite_eq_left hor] at H
      try simp only [] at H
      have ht : t = true := (Option.some.inj H).symm
      rw [ht]
      show (!(bv_eqb (edenot E a) (edenot E b))) = true
      rw [Hne hor]
      rfl
    · rw [ite_eq_right hor] at H
      try simp only [] at H
      by_cases hC : lin_ge0 kn [(a, 0)] [(b, 0)] = true
      · rw [ite_eq_left hC] at H
        try simp only [] at H
        by_cases hD : lin_ge0 kn [(b, 0)] [(a, 0)] = true
        · rw [ite_eq_left hD] at H
          try simp only [] at H
          have ht : t = false := (Option.some.inj H).symm
          rw [ht]
          show (!(bv_eqb (edenot E a) (edenot E b))) = false
          rw [Heq hC hD]
          rfl
        · rw [ite_eq_right hD] at H
          exact absurd H (by simp)
      · rw [ite_eq_right hC] at H
        exact absurd H (by simp)

/-! ## `decide_branch` soundness

    The branch decision: literal operands, equal operands, separated
    intervals, the difference literal, then exact linear arithmetic.

    `decide_branch`'s outer `match a, b with` has exactly two
    arms, so `split at H` after `unfold decide_branch at H` gives the
    literal/literal arm (with `x`, `y` `rename_i`-able) and the `_, _`
    fallback — no per-constructor bash over the eight `expr` forms.  The
    `diff_branch` half rewrites the *value* of the subtraction literal
    (`u_lit64` + `mkAlu_denot` + `u_sub64`) into `(x - y) % 2^64`; that is
    zero iff `x = y` (`sub_emod64_eq_zero`, from
    `Int.emod_eq_emod_iff_emod_sub_eq_zero`), and `bv_eqb` is
    `decide (· = ·)`, so both sides agree.  State the `decide` step with
    `decide_eq_false`: `simp` will NOT use a hypothesis written with `2^64`
    against a goal whose `% 2^64` has already been reduced to the numeral.
-/

theorem sub_emod64_eq_zero {x y : Int} (hx0 : 0 ≤ x) (hx1 : x < 2 ^ 64)
    (hy0 : 0 ≤ y) (hy1 : y < 2 ^ 64) (h : (x - y) % 2 ^ 64 = 0) : x = y := by
  have h2 : x % 2 ^ 64 = y % 2 ^ 64 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr h
  rwa [Int.emod_eq_of_lt hx0 hx1, Int.emod_eq_of_lt hy0 hy1] at h2

theorem decide_branch_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : BranchCond) (a b : expr) (t : Bool)
    (Hkn : know_ok segs E M kn) (H : decide_branch kn c a b = some t) :
    branch_taken c (edenot E a) (edenot E b) = t := by
  have Hsub0 : ∀ z : Int, is_lit (mkAlu .SUB a b) = some z →
      bv_eqb (edenot E a) (edenot E b) = (z % two64 == 0) := by
    intro z Hz
    have hz : mkAlu .SUB a b = .ELit z := is_lit_some Hz
    have Hm := mkAlu_denot E .SUB a b
    rw [hz] at Hm
    have Hu : z % two64 = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) % 2 ^ 64 := by
      have h1 := congrArg bv_unsigned Hm
      rw [show bv_unsigned (edenot E (.ELit z)) = z % two64 from u_lit64 z,
          show bv_unsigned (alu64 .SUB (edenot E a) (edenot E b))
            = (bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) % 2 ^ 64 from u_sub64 _ _] at h1
      exact h1
    have hx0 := (u64_range (edenot E a)).1
    have hx1 := (u64_range (edenot E a)).2
    have hy0 := (u64_range (edenot E b)).1
    have hy1 := (u64_range (edenot E b)).2
    rw [Hu]
    by_cases hxy : bv_unsigned (edenot E a) = bv_unsigned (edenot E b)
    · have hzero : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) % 2 ^ 64 == 0) = true := by
        rw [hxy]
        simp
      rw [hzero]
      have hw : edenot E a = edenot E b := word_eq_of_bv_unsigned hxy
      rw [hw, bv_eqb_refl]
    · have hzero : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) % 2 ^ 64 == 0) = false := by
        have hz' : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E b)) % 2 ^ 64) ≠ 0 :=
          fun h => hxy (sub_emod64_eq_zero hx0 hx1 hy0 hy1 h)
        exact decide_eq_false hz'
      rw [hzero]
      have hne : edenot E a ≠ edenot E b := fun h => hxy (congrArg bv_unsigned h)
      rw [bv_eqb_neq (edenot E a) (edenot E b) hne]
  have Hdiff : ∀ t', diff_branch c a b = some t' →
      branch_taken c (edenot E a) (edenot E b) = t' := by
    intro t' Hd
    cases c with
    | EQ =>
      unfold diff_branch at Hd
      try simp only [] at Hd
      generalize hz : is_lit (mkAlu .SUB a b) = q at Hd
      cases q with
      | none => simp only [] at Hd; exact absurd Hd (by simp)
      | some z =>
        simp only [] at Hd
        have ht : t' = (z % two64 == 0) := (Option.some.inj Hd).symm
        rw [ht]
        exact Hsub0 z hz
    | NE =>
      unfold diff_branch at Hd
      try simp only [] at Hd
      generalize hz : is_lit (mkAlu .SUB a b) = q at Hd
      cases q with
      | none => simp only [] at Hd; exact absurd Hd (by simp)
      | some z =>
        simp only [] at Hd
        have ht : t' = !(z % two64 == 0) := (Option.some.inj Hd).symm
        rw [ht]
        show (!(bv_eqb (edenot E a) (edenot E b))) = !(z % two64 == 0)
        rw [Hsub0 z hz]
    | LT => unfold diff_branch at Hd; exact absurd Hd (by simp)
    | GE => unfold diff_branch at Hd; exact absurd Hd (by simp)
    | LTU => unfold diff_branch at Hd; exact absurd Hd (by simp)
    | GEU => unfold diff_branch at Hd; exact absurd Hd (by simp)
  have Hrange : ∀ t', (match erange kn a, erange kn b with
      | some (al, ah), some (bl, bh) => range_branch c al ah bl bh
      | _, _ => none) = some t' → branch_taken c (edenot E a) (edenot E b) = t' := by
    intro t' Hr
    cases ha : erange kn a with
    | none => rw [ha] at Hr; exact absurd Hr (by simp)
    | some p =>
      obtain ⟨al, ah⟩ := p
      cases hb : erange kn b with
      | none => rw [ha, hb] at Hr; exact absurd Hr (by simp)
      | some q =>
        obtain ⟨bl, bh⟩ := q
        rw [ha, hb] at Hr
        try simp only [] at Hr
        exact range_branch_sound c al ah bl bh (edenot E a) (edenot E b) t'
          (erange_sound segs E M kn a al ah Hkn ha)
          (erange_sound segs E M kn b bl bh Hkn hb) Hr
  have Hrest : (if expr_eqb a b then some (cond_on_eq c)
                else match diff_branch c a b with
                     | some t => some t
                     | none =>
                       match (match erange kn a, erange kn b with
                              | some (al, ah), some (bl, bh) => range_branch c al ah bl bh
                              | _, _ => none) with
                       | some t => some t
                       | none => lin_branch kn c a b) = some t →
      branch_taken c (edenot E a) (edenot E b) = t := by
    intro H'
    by_cases he : expr_eqb a b = true
    · rw [ite_eq_left he] at H'
      have hab : a = b := expr_eqb_eq a b he
      have ht : t = cond_on_eq c := (Option.some.inj H').symm
      rw [ht, hab]
      exact cond_on_eq_sound c (edenot E b)
    · rw [ite_eq_right he] at H'
      cases hd : diff_branch c a b with
      | some t' =>
        rw [hd] at H'
        have ht : t = t' := (Option.some.inj H').symm
        rw [ht]
        exact Hdiff t' hd
      | none =>
        rw [hd] at H'
        generalize hr : (match erange kn a, erange kn b with
              | some (al, ah), some (bl, bh) => range_branch c al ah bl bh
              | _, _ => none) = r at H'
        cases r with
        | none =>
          simp only [] at H'
          exact lin_branch_sound segs E M kn c a b t Hkn H'
        | some t' =>
          simp only [] at H'
          have ht : t = t' := (Option.some.inj H').symm
          rw [ht]
          exact Hrange t' hr
  unfold decide_branch at H
  split at H
  · rename_i x y
    have ht : t = lit_branch c x y := (Option.some.inj H).symm
    rw [ht]
    exact (rfl : branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y) = lit_branch c x y)
  · exact Hrest H

/-!  The missing calculus was one
    `sx32` fact, built here from this tree's existing bridges:
    * `sx32` is `if r < 2^31 then r else r + (2^64 - 2^32)`;
    * `bv_swrap32_eq`: `bv_swrap 32 u % 2^64 = sx32 u` for
      `0 <= u < 2^32` (the two cases of `bv_swrap`'s half-modulus
      subtraction, each closed by `Int.emod_eq_of_lt` on a shifted
      representative — `Int.add_mul_emod_self_right` supplies the shift,
      which is why the numerals `2^31` / `2^32` are written explicitly);
    * `sext32_val`: `bv_unsigned (sext 64 w) = sx32 w.toNat`, from
      `sext32_unsigned` + the previous line;
    * `u_swrap32`: `bv_unsigned (Z_to_bv 64 (bv_swrap 32 t)) =
      sx32 (t % 4294967296)` (the periodicity of `bv_swrap` in
      `t mod 2^32` via `Int.add_emod`);
    * `zfastw_eq`: the four non-trivial `AluOp` cases (`ADD`, `SUB`, `SLL`,
      `SRL` — the other seven are `rfl`, since `zfastw` falls through to
      `zaluw`).  Each compares `sx32` of the masked value with `sx32` of
      the `BitVec 32` result's `toNat`, so the work is `BitVec.toNat_add`
      / `toNat_sub` / `toNat_shiftLeft` / `toNat_ushiftRight`,
      `low32_toNat`, and the `Int.natCast_*` cast lemmas.
      `exact_mod_cast`-free — the casts are pushed by hand, and the
      finishing `rfl` absorbs the `(↑4294967296 : Int)` vs `4294967296`
      spelling difference (they are the same term, but the `↑` survives
      the `natCast` rewrites).
    `bv_swrap` at width 32 has no degenerate case (`32 - 1 = 31`), so
    these carry NO side condition on the width, unlike `zext_fast_eq`.
-/

theorem half32 : ((2 ^ (32 - 1) : Nat) : Int) = 2147483648 := by decide
theorem mod32 : ((2 ^ 32 : Nat) : Int) = 4294967296 := by decide
theorem pow31 : (2 : Int) ^ 31 = 2147483648 := by decide
theorem pow32 : (2 : Int) ^ 32 = 4294967296 := by decide
theorem pow64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide

theorem sx32_eq_of_lt {u : Int} (h : u < 2 ^ 31) : sx32 u = u := by
  unfold AxSymExec3.sx32
  rw [pow31] at h
  exact ite_eq_left h

theorem sx32_eq_of_ge {u : Int} (h : 2 ^ 31 ≤ u) : sx32 u = u + 18446744069414584320 := by
  unfold AxSymExec3.sx32
  rw [pow31] at h
  exact ite_eq_right (by omega)

theorem bv_swrap32_eq (u : Int) (H0 : 0 ≤ u) (H1 : u < 4294967296) :
    bv_swrap 32 u % 2 ^ 64 = sx32 u := by
  unfold bv_swrap
  rw [half32, mod32]
  by_cases hu : u < 2147483648
  · rw [sx32_eq_of_lt (by rw [pow31]; exact hu)]
    have h1 : (u + 2147483648) % 4294967296 = u + 2147483648 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [h1]
    have h2 : u + 2147483648 - 2147483648 = u := by omega
    rw [h2]
    exact Int.emod_eq_of_lt H0 (by omega)
  · rw [sx32_eq_of_ge (by rw [pow31]; omega)]
    have h1 : (u + 2147483648) % 4294967296 = u - 2147483648 := by
      have he : u + 2147483648 = (u - 2147483648) + 1 * 4294967296 := by omega
      rw [he, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (a := u - 2147483648) (by omega) (by omega)]
    rw [h1]
    have h2 : u - 2147483648 - 2147483648 = u - 4294967296 := by omega
    rw [h2]
    have h3 : (u - 4294967296) % 2 ^ 64 = u + 18446744069414584320 := by
      have h4 : u - 4294967296 = (u + 18446744069414584320) + (-1) * 2 ^ 64 := by
        rw [pow64]; omega
      rw [h4, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (a := u + 18446744069414584320) (by omega) (by omega)]
    exact h3

theorem sext32_val (w : BitVec 32) : bv_unsigned (sext 64 w) = sx32 (w.toNat : Int) := by
  show ((sext 64 w).toNat : Int) = sx32 (w.toNat : Int)
  rw [sext32_unsigned]
  exact bv_swrap32_eq (w.toNat : Int) (by omega) (by rw [← pow32]; exact_mod_cast w.isLt)

theorem u_swrap32 (t : Int) :
    bv_unsigned (Z_to_bv 64 (bv_swrap 32 t)) = sx32 (t % 4294967296) := by
  have ht0 : 0 ≤ t % 4294967296 := Int.emod_nonneg _ (by decide)
  have ht1 : t % 4294967296 < 4294967296 := Int.emod_lt_of_pos _ (by decide)
  have hsw : bv_swrap 32 t = bv_swrap 32 (t % 4294967296) := by
    unfold bv_swrap
    rw [half32, mod32, Int.add_emod,
      show (2147483648 : Int) % 4294967296 = 2147483648 from
        Int.emod_eq_of_lt (by decide) (by decide)]
  rw [u_lit64a, hsw, bv_swrap32_eq _ ht0 ht1]

theorem nat_two_pow32 : (2 : Nat) ^ 32 = 4294967296 := by decide

theorem toNat_bitvec64 (x : Int) (H : 0 ≤ x ∧ x < 2 ^ 64) : (Z_to_bv 64 x).toNat = x.toNat := by
  have h1 : ((Z_to_bv 64 x).toNat : Int) = x := u_small H
  have h2 : ((Z_to_bv 64 x).toNat : Int) = ((x.toNat : Nat) : Int) := by
    rw [h1, Int.toNat_of_nonneg H.1]
  exact_mod_cast h2

theorem zfastw_eq (op : AluOp) (x y : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hy : 0 ≤ y ∧ y < 2 ^ 64) :
    zfastw op x y = zaluw op x y := by
  have hXN : ((Z_to_bv 64 x).toNat : Int) = x := u_small Hx
  have hYN : ((Z_to_bv 64 y).toNat : Int) = y := u_small Hy
  have hYN2 : (Z_to_bv 64 y).toNat = y.toNat := toNat_bitvec64 y Hy
  have hK : (AxSymExec3.zland y 31).toNat = (low32 (Z_to_bv 64 y) &&& BitVec.ofInt 32 31).toNat := by
    rw [land_31, Int.toNat_emod Hy.1 (by decide : (0 : Int) ≤ 32),
      show ((32 : Int)).toNat = 32 from rfl]
    rw [regamt32_mask, hYN2]
  cases op with
  | ADD =>
    show sx32 (land32 (x + y)) = bv_unsigned (sext 64 (low32 (Z_to_bv 64 x) + low32 (Z_to_bv 64 y)))
    rw [land32_eq, sext32_val]
    congr 1
    have e : ((low32 (Z_to_bv 64 x) + low32 (Z_to_bv 64 y)).toNat : Int)
        = ((Z_to_bv 64 x).toNat % 4294967296 + (Z_to_bv 64 y).toNat % 4294967296) % 4294967296 := by
      rw [BitVec.toNat_add, low32_toNat, low32_toNat, nat_two_pow32,
        Int.natCast_emod, Int.natCast_add, Int.natCast_emod, Int.natCast_emod]
      rfl
    rw [e, hXN, hYN, ← Int.add_emod]
  | SUB =>
    show sx32 (land32 (x - y)) = bv_unsigned (sext 64 (low32 (Z_to_bv 64 x) - low32 (Z_to_bv 64 y)))
    rw [land32_eq, sext32_val]
    congr 1
    have hb : (low32 (Z_to_bv 64 y)).toNat ≤ 4294967296 := by
      have h := (low32 (Z_to_bv 64 y)).isLt
      omega
    have e : ((low32 (Z_to_bv 64 x) - low32 (Z_to_bv 64 y)).toNat : Int)
        = ((Z_to_bv 64 x).toNat % 4294967296 + (4294967296 - (Z_to_bv 64 y).toNat % 4294967296))
          % 4294967296 := by
      rw [BitVec.toNat_sub, low32_toNat, low32_toNat, nat_two_pow32,
        Int.natCast_emod, Int.natCast_add, Int.natCast_sub (by omega),
        Int.natCast_emod, Int.natCast_emod, Int.add_comm]
      rfl
    rw [e, hXN, hYN]
    have hstep : ((x % 4294967296) + (4294967296 - y % 4294967296)) % 4294967296
        = ((x % 4294967296) - y % 4294967296) % 4294967296 := by
      have hB : y % 4294967296 ≤ 4294967296 := by
        have h := Int.emod_lt_of_pos y (by decide : (0 : Int) < 4294967296)
        omega
      have he : (x % 4294967296) + (4294967296 - y % 4294967296)
          = ((x % 4294967296) - y % 4294967296) + 1 * 4294967296 := by omega
      rw [he, Int.add_mul_emod_self_right]
    rw [hstep, ← Int.sub_emod]
  | SLL =>
    show sx32 (land32 (AxSymExec3.zshiftl (land32 x) (AxSymExec3.zland y 31).toNat)) =
      bv_unsigned (sext 64 (low32 (Z_to_bv 64 x) <<< (low32 (Z_to_bv 64 y) &&& BitVec.ofInt 32 31).toNat))
    rw [sext32_val]
    congr 1
    rw [land32_eq,
      show AxSymExec3.zshiftl (land32 x) (AxSymExec3.zland y 31).toNat
        = land32 x * 2 ^ (AxSymExec3.zland y 31).toNat from rfl,
      show land32 x = x % 4294967296 from land32_eq x,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, nat_two_pow32, hK,
      Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, low32_toNat, nat_two_pow32,
      Int.natCast_emod, hXN]
    rfl
  | SRL =>
    show sx32 (AxSymExec3.zshiftr (land32 x) (AxSymExec3.zland y 31).toNat) =
      bv_unsigned (sext 64 (low32 (Z_to_bv 64 x) >>> (low32 (Z_to_bv 64 y) &&& BitVec.ofInt 32 31).toNat))
    rw [sext32_val]
    congr 1
    rw [show AxSymExec3.zshiftr (land32 x) (AxSymExec3.zland y 31).toNat
        = land32 x / 2 ^ (AxSymExec3.zland y 31).toNat from rfl,
      show land32 x = x % 4294967296 from land32_eq x,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hK,
      Int.natCast_ediv, Int.natCast_pow, low32_toNat, Int.natCast_emod, hXN]
    rfl
  | SRA => rfl
  | SLT => rfl
  | SLTU => rfl
  | AND => rfl
  | OR => rfl
  | XOR => rfl

/-!  the
     `assert (Hsh : ... match is_lit b with ...)` cannot be reused
    across the `is_lit a` case split here: `cases ha : is_lit a` rewrites
    the goal but NOT the hypotheses, so `Hsh`'s own `match is_lit a` would
    stay unreduced.  Parameterising by `g` sidesteps that entirely.
    `w_shift_amt` (stated) does the actual shift-amount swap, through
    `u_lit_mod` on the literal side.
-/

theorem zaluw_l_eq (op : AluOp) (x y : Int) : zaluw_l op x y = zaluw op x y := by
  unfold zaluw_l
  rw [zfastw_eq op _ _ (wrap64_range x) (wrap64_range y)]
  show bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 (wrap64 x)))
      (low32 (Z_to_bv 64 (wrap64 y)))))
    = bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))
  rw [Z_to_bv_wrap64, Z_to_bv_wrap64]

theorem mkAluw_denot (E : env) (op : AluOp) (a b : expr) :
    edenot E (mkAluw op a b) =
      sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
  have Hsh : ∀ (g : Int → expr), (op = .SLL ∨ op = .SRL ∨ op = .SRA) →
      (∀ s, edenot E (g s)
        = sext 64 (alu32 op (low32 (edenot E a)) (low32 (Z_to_bv 64 s)))) →
      edenot E (match shamt_of b 5 with
                | some s => g s
                | none => .EAluw op a b) =
        sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
    intro g Hop Hg
    cases hs : shamt_of b 5 with
    | none => rfl
    | some s =>
      simp only []
      rw [Hg s]
      obtain ⟨Hm, Hs0, Hs1⟩ := shamt_of_sound E b 5 s (by decide) hs
      have Hm' : bv_unsigned (edenot E b) % 32 = s := Hm
      have Heq : sext 64 (alu32 op (low32 (edenot E a)) (low32 (Z_to_bv 64 s)))
          = sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
        apply w_shift_amt op _ _ _ Hop
        rw [u_lit_mod s 32 ⟨Hs0, by omega⟩ (Or.inr rfl) (by omega), Hm']
      exact Heq
  unfold mkAluw
  cases ha : is_lit a with
  | some x =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      rw [is_lit_some ha, is_lit_some hb]
      show Z_to_bv 64 (zaluw_l op x y)
        = sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y)))
      rw [zaluw_l_eq]
      exact ofInt_toNat _
    | none =>
      simp only []
      cases op with
      | SLL =>
        simp only []
        exact Hsh (fun s => .ELit (zaluw_l .SLL x s)) (Or.inl rfl) (by
          intro s
          rw [is_lit_some ha]
          show Z_to_bv 64 (zaluw_l .SLL x s)
            = sext 64 (alu32 .SLL (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 s)))
          rw [zaluw_l_eq]
          exact ofInt_toNat _)
      | SRL =>
        simp only []
        exact Hsh (fun s => .ELit (zaluw_l .SRL x s)) (Or.inr (Or.inl rfl)) (by
          intro s
          rw [is_lit_some ha]
          show Z_to_bv 64 (zaluw_l .SRL x s)
            = sext 64 (alu32 .SRL (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 s)))
          rw [zaluw_l_eq]
          exact ofInt_toNat _)
      | SRA =>
        simp only []
        exact Hsh (fun s => .ELit (zaluw_l .SRA x s)) (Or.inr (Or.inr rfl)) (by
          intro s
          rw [is_lit_some ha]
          show Z_to_bv 64 (zaluw_l .SRA x s)
            = sext 64 (alu32 .SRA (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 s)))
          rw [zaluw_l_eq]
          exact ofInt_toNat _)
      | ADD => rfl
      | SUB => rfl
      | SLT => rfl
      | SLTU => rfl
      | AND => rfl
      | OR => rfl
      | XOR => rfl
  | none =>
    cases hb : is_lit b with
    | some y =>
      simp only []
      cases op <;> rfl
    | none =>
      simp only []
      cases op with
      | SLL =>
        simp only []
        exact Hsh (fun s => .EAluw .SLL a (.ELit s)) (Or.inl rfl) (by intro s; rfl)
      | SRL =>
        simp only []
        exact Hsh (fun s => .EAluw .SRL a (.ELit s)) (Or.inr (Or.inl rfl)) (by intro s; rfl)
      | SRA =>
        simp only []
        exact Hsh (fun s => .EAluw .SRA a (.ELit s)) (Or.inr (Or.inr rfl)) (by intro s; rfl)
      | ADD => rfl
      | SUB => rfl
      | SLT => rfl
      | SLTU => rfl
      | AND => rfl
      | OR => rfl
      | XOR => rfl

/-! ## The `eval_closed` layer

    The concrete-evaluation layer: a CLOSED expression evaluates to its own
    denotation (`eval_closed_sound`), substituting a denotationally equal
    expression preserves the denotation (`esubst_sound`), the enumeration
    sweep `all_eval_to` really does pin every point of `[lo, lo + cnt)`
    (`all_eval_to_sound`), and every `eval_closed` result is a canonical
    literal (`eval_closed_range`).  This is the machinery behind
    `concretize`/`foldK`. -/

/-- `eval_closed_sound`: a closed expression evaluates to its own
    denotation. -/
theorem eval_closed_sound (E : env) (e : expr) (v : Int) (H : eval_closed e = some v) :
    edenot E e = Z_to_bv 64 v := by
  induction e generalizing v with
  | ELit z =>
    simp only [eval_closed] at H
    injection H with hv
    subst hv
    show Z_to_bv 64 z = Z_to_bv 64 (z % two64)
    rw [two64_eq]
    exact (Z_to_bv_emod64 z).symm
  | EVar n => simp only [eval_closed] at H; exact absurd H (by simp)
  | EBlob sx k i n => simp only [eval_closed] at H; exact absurd H (by simp)
  | EAlu op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show alu64 op (edenot E a) (edenot E b) = Z_to_bv 64 (zalu op x y)
        rw [ih1 x ha, ih2 y hb]
        exact (Z_to_bv_unsigned _).symm
  | EAluw op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
          = Z_to_bv 64 (zaluw op x y)
        rw [ih1 x ha, ih2 y hb]
        exact (Z_to_bv_unsigned _).symm
  | EMd op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show mul_div op (edenot E a) (edenot E b) = Z_to_bv 64 (zmd op x y)
        rw [ih1 x ha, ih2 y hb]
        exact (Z_to_bv_unsigned _).symm
  | EMdw op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
          = Z_to_bv 64 (zmdw op x y)
        rw [ih1 x ha, ih2 y hb]
        exact (Z_to_bv_unsigned _).symm
  | EExt sx lo n a ih =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      rw [ha] at H
      injection H with hv
      subst hv
      show ext_val sx lo n (edenot E a) = Z_to_bv 64 (zext_lit sx lo n x)
      rw [ih x ha]
      exact (Z_to_bv_unsigned _).symm

/-- `esubst_sound`: substitution of a denotationally equal
    expression preserves the denotation. -/
theorem esubst_sound (E : env) (s r : expr) (Hr : edenot E r = edenot E s) (e : expr) :
    edenot E (esubst s r e) = edenot E e := by
  induction e with
  | ELit z =>
    simp only [esubst]
    by_cases h : expr_eqb (.ELit z) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go]
  | EVar n =>
    simp only [esubst]
    by_cases h : expr_eqb (.EVar n) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go]
  | EBlob sx k i n =>
    simp only [esubst]
    by_cases h : expr_eqb (.EBlob sx k i n) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go]
  | EAlu op a b ih1 ih2 =>
    simp only [esubst]
    by_cases h : expr_eqb (.EAlu op a b) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go, edenot, ih1, ih2]
  | EAluw op a b ih1 ih2 =>
    simp only [esubst]
    by_cases h : expr_eqb (.EAluw op a b) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go, edenot, ih1, ih2]
  | EMd op a b ih1 ih2 =>
    simp only [esubst]
    by_cases h : expr_eqb (.EMd op a b) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go, edenot, ih1, ih2]
  | EMdw op a b ih1 ih2 =>
    simp only [esubst]
    by_cases h : expr_eqb (.EMdw op a b) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go, edenot, ih1, ih2]
  | EExt sx lo n a ih =>
    simp only [esubst]
    by_cases h : expr_eqb (.EExt sx lo n a) s = true
    · rw [ite_eq_left h, expr_eqb_eq _ _ h]; exact Hr
    · rw [ite_eq_right h]; simp only [esubst_go, edenot, ih]

/-- `all_eval_to_sound`: if `eval_closed (e[s := lo + i])` is `v`
    for every `i < cnt`, then it is `v` at every `z` in the window. -/
theorem all_eval_to_sound (s e : expr) (v : Int) (cnt : Nat) :
    ∀ lo, all_eval_to s e v lo cnt = true → ∀ z, lo ≤ z → z < lo + (cnt : Int) →
      eval_closed (esubst s (.ELit z) e) = some v := by
  induction cnt with
  | zero =>
    intro lo H z h1 h2
    omega
  | succ c ih =>
    intro lo H z h1 h2
    simp only [all_eval_to] at H
    cases hw : eval_closed (esubst s (.ELit lo) e) with
    | none => rw [hw] at H; exact absurd H (by simp)
    | some w =>
      rw [hw] at H
      simp only [] at H
      by_cases hv : (w == v) = true
      · rw [ite_eq_left hv] at H
        by_cases hz : z = lo
        · subst hz
          rw [beq_iff_eq] at hv
          rw [hv] at hw
          exact hw
        · refine ih (lo + 1) H z (by omega) ?_
          have hc : ((c + 1 : Nat) : Int) = (c : Int) + 1 := by simp
          rw [hc] at h2
          omega
      · rw [ite_eq_right hv] at H; exact absurd H (by simp)

/-- `eval_closed_range`: every `eval_closed` result is a canonical
    literal. -/
theorem eval_closed_range (e : expr) (v : Int) (H : eval_closed e = some v) :
    0 ≤ v ∧ v < two64 := by
  induction e generalizing v with
  | ELit z =>
    simp only [eval_closed] at H
    injection H with hv
    subst hv
    exact ⟨Int.emod_nonneg _ (by rw [two64_eq]; decide),
           Int.emod_lt_of_pos _ (by rw [two64_eq]; decide)⟩
  | EVar n => simp only [eval_closed] at H; exact absurd H (by simp)
  | EBlob sx k i n => simp only [eval_closed] at H; exact absurd H (by simp)
  | EAlu op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show 0 ≤ zalu op x y ∧ zalu op x y < two64
        have h := u64_range (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y))
        rw [two64_eq]
        exact h
  | EAluw op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show 0 ≤ zaluw op x y ∧ zaluw op x y < two64
        have h := u64_range
          (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))
        rw [two64_eq]
        exact h
  | EMd op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show 0 ≤ zmd op x y ∧ zmd op x y < two64
        have h := u64_range (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y))
        rw [two64_eq]
        exact h
  | EMdw op a b ih1 ih2 =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      cases hb : eval_closed b with
      | none => rw [ha, hb] at H; exact absurd H (by simp)
      | some y =>
        rw [ha, hb] at H
        injection H with hv
        subst hv
        show 0 ≤ zmdw op x y ∧ zmdw op x y < two64
        have h := u64_range
          (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))
        rw [two64_eq]
        exact h
  | EExt sx lo n a ih =>
    simp only [eval_closed] at H
    cases ha : eval_closed a with
    | none => rw [ha] at H; exact absurd H (by simp)
    | some x =>
      rw [ha] at H
      injection H with hv
      subst hv
      show 0 ≤ zext_lit sx lo n x ∧ zext_lit sx lo n x < two64
      have h := u64_range (ext_val sx lo n (Z_to_bv 64 x))
      rw [two64_eq]
      exact h

/-!  This tree's `bv_swrap` spells the half modulus
    with `Nat` subtraction, so the old `zext_fast` disagreed at
    `sx = true, n = 0`; `AxSymExec3.zext_fast` now special-cases `n = 0`
    to `wrap64 (u - 1)`, which makes BOTH cases of the old side condition
    (`sx = false ∨ 1 ≤ n`, `n ≤ 8`) removable:
    * `n = 0, sx = true`: both sides are `2^64 - 1` (`zext_fast_zero`,
      `zext_lit_zero`);
    * `1 ≤ n ≤ 8`: the already-proved `zext_fast_eq`;
    * `8n > 64`: `zones (8n)` is all-ones below bit 64, so both sides are
      the slice `x / 2^(8*lo)` itself (`zland_zones_ge`,
      `bv_swrap_emod_pow`, `two_pow_sub_two64`).
    `rw` rewrites
    only the FIRST matching occurrence here, and `evalS s _ e` and
    `esubst s _ e` share their `expr_eqb e s` condition, so the idiom is
    `rw [ite_eq_left h, ite_eq_left h]` (`ite_eq_right` likewise). -/

/-- `bv_swrap m z` at a width `m ≥ 64` is `z` modulo `2^64`. -/
theorem bv_swrap_emod_pow (m : Nat) (hm : 64 ≤ m) (z : Int) :
    bv_swrap m z % 2 ^ 64 = z % 2 ^ 64 := by
  have hA : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := by push_cast; rfl
  have hdvd : (2 : Int) ^ 64 ∣ (2 : Int) ^ m :=
    ⟨(2 : Int) ^ (m - 64), by rw [← Int.pow_add]; congr 1; omega⟩
  have hmod : bv_swrap m z % ((2 ^ m : Nat) : Int) = z % ((2 ^ m : Nat) : Int) := by
    unfold bv_swrap
    rw [Int.sub_eq_add_neg, Int.add_emod, Int.emod_emod, ← Int.add_emod]
    have hz : z + ((2 ^ (m - 1) : Nat) : Int) + -((2 ^ (m - 1) : Nat) : Int) = z := by omega
    rw [hz]
  rw [hA] at hmod
  rw [← Int.emod_emod_of_dvd (bv_swrap m z) hdvd, hmod, Int.emod_emod_of_dvd z hdvd]

theorem zland_zones_ge (w : Int) (m : Nat) (Hw : 0 ≤ w ∧ w < 2 ^ 64) (Hm : 64 ≤ m) :
    AxSymExec3.zland w (zones m) = w := by
  have hz : zones m = ((2 : Int) ^ 64 - 1) + ((2 : Int) ^ (m - 64) - 1) * 2 ^ 64 := by
    unfold zones
    have hp : (2 : Int) ^ m = (2 : Int) ^ 64 * (2 : Int) ^ (m - 64) := by
      rw [← Int.pow_add]; congr 1; omega
    rw [hp, Int.mul_comm ((2 : Int) ^ 64) ((2 : Int) ^ (m - 64))]
    have hexp : ((2 : Int) ^ (m - 64) * (2 : Int) ^ 64 - 1)
        = ((2 : Int) ^ 64 - 1) + ((2 : Int) ^ (m - 64) - 1) * 2 ^ 64 := by
      rw [Int.sub_mul, Int.one_mul]
      omega
    exact hexp
  have hem : zones m % two64 = (2 : Int) ^ 64 - 1 := by
    rw [hz, two64_eq, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hem64 : zones 64 % two64 = (2 : Int) ^ 64 - 1 := by
    unfold zones
    rw [two64_eq]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hstep : AxSymExec3.zland w (zones m) = AxSymExec3.zland w (zones 64) := by
    unfold AxSymExec3.zland
    rw [hem, hem64]
  rw [hstep, show zones 64 = (2 : Int) ^ 64 - 1 from rfl, zland_ones w 64 (by omega)]
  exact Int.emod_eq_of_lt Hw.1 Hw.2

theorem zland_zero (a : Int) : AxSymExec3.zland a 0 = 0 := by
  unfold AxSymExec3.zland
  simp

theorem two_pow_sub_two64 (m : Nat) (hm : 64 ≤ m) :
    (2 : Int) ^ m - 2 ^ 64 = ((2 : Int) ^ (m - 64) - 1) * 2 ^ 64 := by
  have hp : (2 : Int) ^ m = (2 : Int) ^ (m - 64) * (2 : Int) ^ 64 := by
    rw [Int.mul_comm, ← Int.pow_add]; congr 1; omega
  rw [hp, Int.sub_mul, Int.one_mul]

/-- `zext_lit` at width 0 (the `bv_swrap`-at-`0` corner). -/
theorem zext_lit_zero (lo : Nat) (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    zext_lit true lo 0 x = (2 : Int) ^ 64 - 1 := by
  have hbx : bv_unsigned (Z_to_bv 64 x) = x := by
    rw [u_lit64a]; exact Int.emod_eq_of_lt Hx.1 Hx.2
  unfold zext_lit ext_val ext_Z
  rw [hbx, u_lit64a]
  simp only [Nat.mul_zero, ite_true, Int.pow_zero]
  rw [Int.emod_one, show bv_swrap 0 (0 : Int) = -1 from by decide,
    mod_wrap_neg (-1) (by omega) (by omega)]
  omega

/-- `zext_fast` at width 0 (the `bv_swrap`-at-`0` corner now AGREES). -/
theorem zext_fast_zero (lo : Nat) (x : Int) :
    zext_fast true lo 0 x = (2 : Int) ^ 64 - 1 := by
  simp only [zext_fast, Nat.mul_zero, ite_true, zones, Int.pow_zero, Int.sub_self,
    zland_zero, Int.zero_sub]
  rw [wrap64_mod, two64_eq, mod_wrap_neg (-1) (by omega) (by omega)]
  omega

/-- `zext_fast = zext_lit` at a byte width of at least 8: both sides are the
    slice as a canonical literal (the mask `zones m` with `m ≥ 64` cannot
    see below bit 64). -/
theorem zext_fast_eq_ge (sx : Bool) (lo n : Nat) (x : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hm : 64 ≤ 8 * n) :
    zext_fast sx lo n x = zext_lit sx lo n x := by
  have hw : 0 ≤ x / (2 : Int) ^ (8 * lo) ∧ x / (2 : Int) ^ (8 * lo) < 2 ^ 64 := by
    refine ⟨Int.ediv_nonneg Hx.1 (by have := two_pow_pos_int (8 * lo); omega), ?_⟩
    have h1 := Int.ediv_le_self ((2 : Int) ^ (8 * lo)) Hx.1
    omega
  have hld : (2 : Int) ^ 64 ≤ (2 : Int) ^ (8 * n) := int_pow_le_pow 64 (8 * n) Hm
  have hzw : AxSymExec3.zland (AxSymExec3.zshiftr x (8 * lo)) (zones (8 * n))
      = x / (2 : Int) ^ (8 * lo) := by
    show AxSymExec3.zland (x / (2 : Int) ^ (8 * lo)) (zones (8 * n)) = _
    exact zland_zones_ge _ _ hw Hm
  have hmod : x / (2 : Int) ^ (8 * lo) % two64 = x / (2 : Int) ^ (8 * lo) :=
    Int.emod_eq_of_lt hw.1 (by rw [two64_eq]; exact hw.2)
  have hn0 : n ≠ 0 := by omega
  have hzl : zext_lit sx lo n x = x / (2 : Int) ^ (8 * lo) := by
    have hbx : bv_unsigned (Z_to_bv 64 x) = x := by
      rw [u_lit64a]; exact Int.emod_eq_of_lt Hx.1 Hx.2
    unfold zext_lit ext_val ext_Z
    rw [hbx, u_lit64a]
    simp only []
    have hu : x / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n) = x / (2 : Int) ^ (8 * lo) :=
      Int.emod_eq_of_lt hw.1 (by omega)
    rw [hu]
    cases sx with
    | false => exact hmod
    | true =>
      rw [ite_eq_left rfl, bv_swrap_emod_pow (8 * n) Hm]
      exact hmod
  have hzf : zext_fast sx lo n x = x / (2 : Int) ^ (8 * lo) := by
    cases n with
    | zero => exact absurd rfl hn0
    | succ n' =>
      have hk : (8 * ((n' + 1 : Nat) : Int)).toNat = 8 * (n' + 1) := by
        have h : 8 * ((n' + 1 : Nat) : Int) = ((8 * (n' + 1) : Nat) : Int) := by
          push_cast; rfl
        rw [h, Int.toNat_natCast]
      by_cases hsx : sx = true
      · simp only [zext_fast, hsx, ite_true]
        try simp only []
        rw [hzw]
        by_cases hc : x / (2 : Int) ^ (8 * lo) < AxSymExec3.zshiftl 1
            (8 * ((n' + 1 : Nat) : Int) - 1).toNat
        · rw [ite_eq_left hc, wrap64_mod]
          exact hmod
        · rw [ite_eq_right hc, wrap64_mod, two64_eq]
          rw [show AxSymExec3.zshiftl 1 (8 * ((n' + 1 : Nat) : Int)).toNat
              = (2 : Int) ^ (8 * (n' + 1)) from by
            rw [hk]; show (1 : Int) * (2 : Int) ^ (8 * (n' + 1)) = _; rw [Int.one_mul]]
          rw [show x / (2 : Int) ^ (8 * lo) - (2 : Int) ^ (8 * (n' + 1)) + 2 ^ 64
              = x / (2 : Int) ^ (8 * lo) - ((2 : Int) ^ (8 * (n' + 1)) - 2 ^ 64) from by
            omega]
          rw [two_pow_sub_two64 (8 * (n' + 1)) (by omega), Int.sub_emod,
            Int.mul_comm ((2 : Int) ^ (8 * (n' + 1) - 64) - 1) (2 ^ 64),
            Int.mul_emod_right, Int.sub_zero, Int.emod_emod]
          exact hmod
      · simp only [zext_fast, hsx, Bool.false_eq_true, ite_false]
        rw [hzw, wrap64_mod]
        exact hmod
  rw [hzf, hzl]

/-- `zext_fast = zext_lit` at EVERY width . -/
theorem zext_fast_eq_all (sx : Bool) (lo n : Nat) (x : Int)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    zext_fast sx lo n x = zext_lit sx lo n x := by
  by_cases h8 : 8 * n ≤ 64
  · by_cases hn : sx = false ∨ 1 ≤ n
    · exact zext_fast_eq sx lo n x Hx (by omega) hn
    · have hsx : sx = true := by
        cases sx with
        | false => exact absurd (Or.inl rfl) hn
        | true => rfl
      have hn0 : n = 0 := by omega
      subst hsx
      subst hn0
      rw [zext_fast_zero lo x, zext_lit_zero lo x Hx]
  · exact zext_fast_eq_ge sx lo n x Hx (by omega)

theorem evalS_eq (s : expr) (z : Int) (e : expr) :
    evalS s (wrap64 z) e = eval_closed (esubst s (.ELit z) e) := by
  induction e with
  | ELit w =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.ELit w) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]; simp only [evalS_go, esubst_go, eval_closed, wrap64_mod]
  | EVar n =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EVar n) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]; simp only [evalS_go, esubst_go, eval_closed]
  | EBlob sx k i n =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EBlob sx k i n) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]; simp only [evalS_go, esubst_go, eval_closed]
  | EAlu op a b ih1 ih2 =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EAlu op a b) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [evalS_go, esubst_go, eval_closed, ih1, ih2]
      cases h1 : eval_closed (esubst s (.ELit z) a) with
      | none => simp only [h1]
      | some x =>
        cases h2 : eval_closed (esubst s (.ELit z) b) with
        | none => simp only [h1, h2]
        | some y =>
          simp only [h1, h2]
          have hx := eval_closed_range _ _ h1
          have hy := eval_closed_range _ _ h2
          rw [zfast_eq op x y hx hy]
  | EAluw op a b ih1 ih2 =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EAluw op a b) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [evalS_go, esubst_go, eval_closed, ih1, ih2]
      cases h1 : eval_closed (esubst s (.ELit z) a) with
      | none => simp only [h1]
      | some x =>
        cases h2 : eval_closed (esubst s (.ELit z) b) with
        | none => simp only [h1, h2]
        | some y =>
          simp only [h1, h2]
          have hx := eval_closed_range _ _ h1
          have hy := eval_closed_range _ _ h2
          rw [zfastw_eq op x y hx hy]
  | EMd op a b ih1 ih2 =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EMd op a b) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [evalS_go, esubst_go, eval_closed, ih1, ih2]
      cases h1 : eval_closed (esubst s (.ELit z) a) with
      | none => simp only [h1]
      | some x =>
        cases h2 : eval_closed (esubst s (.ELit z) b) with
        | none => simp only [h1, h2]
        | some y =>
          simp only [h1, h2]
          have hx := eval_closed_range _ _ h1
          have hy := eval_closed_range _ _ h2
          rw [zfastm_eq op x y hx hy]
  | EMdw op a b ih1 ih2 =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EMdw op a b) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [evalS_go, esubst_go, eval_closed, ih1, ih2]
      cases h1 : eval_closed (esubst s (.ELit z) a) with
      | none => simp only [h1]
      | some x =>
        cases h2 : eval_closed (esubst s (.ELit z) b) with
        | none => simp only [h1, h2]
        | some y => simp only [h1, h2]
  | EExt sx lo n a ih =>
    simp only [evalS, esubst]
    by_cases h : expr_eqb (.EExt sx lo n a) s = true
    · rw [ite_eq_left h, ite_eq_left h]; simp only [eval_closed, wrap64_mod]
    · rw [ite_eq_right h, ite_eq_right h]
      simp only [evalS_go, esubst_go, eval_closed, ih]
      cases h1 : eval_closed (esubst s (.ELit z) a) with
      | none => simp only [h1]
      | some x =>
        simp only [h1]
        have hx := eval_closed_range _ _ h1
        rw [zext_fast_eq_all sx lo n x hx]

/-! ## `all_eval_toS_eq`, `probeS_eq`, and `conc_try_sound`/`concretize_sound`


    With `evalS_eq` in hand the sweep `all_eval_toS` is the reference
    sweep `all_eval_to` (`all_eval_toS_eq`), `probeS` is the reference
    probe (`probeS_eq`), and the concretization sweep is sound: whatever
    `conc_try` pins down IS the value of `edenot` (`conc_try_sound`), so
    `concretize` (the closed case plus the sweep) is sound
    (`concretize_sound`).

    `conc_try`'s body is one long `match`/`if` chain; each
    failure branch of the chain (`closedb`, `evalS_def`, `erange`,
    `conc_limit`, `evalS`, the probe, `all_eval_toS`) simply recurses into
    the tail list, so `ih` closes it, and only the success branch carries
    information.  `cases hr : erange kn c` needs a following
    `simp only []` before the `if`s can be rewritten (the match on
    `some (lo,hi)` is left unreduced by `cases`). -/

theorem all_eval_toS_eq (s e : expr) (v lo : Int) (cnt : Nat) :
    all_eval_toS s e v lo cnt = all_eval_to s e v lo cnt := by
  induction cnt generalizing lo with
  | zero => rfl
  | succ c ih =>
    simp only [all_eval_toS, all_eval_to, evalS_eq]
    cases h1 : eval_closed (esubst s (.ELit lo) e) with
    | none => simp only [h1]
    | some w =>
      by_cases hv : (w == v) = true
      · simp only [h1, ite_eq_left hv, ih]
      · simp only [h1, ite_eq_right hv]

theorem probeS_eq (s e : expr) (v z : Int) :
    probeS s e v z
      = (match eval_closed (esubst s (.ELit z) e) with | some w => (w == v) | none => false) := by
  unfold probeS
  rw [evalS_eq]
  rfl

theorem conc_try_sound (segs : List MemImageType.Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (cands : List expr) (v : Int)
    (Hkn : know_ok segs E M kn) (H : conc_try kn e cands = some v) :
    edenot E e = Z_to_bv 64 v := by
  induction cands generalizing v with
  | nil => simp only [conc_try] at H; exact absurd H (by simp)
  | cons c rest ih =>
    simp only [conc_try] at H
    by_cases hcl : closedb c = true
    · rw [ite_eq_left hcl] at H; exact ih v H
    · rw [ite_eq_right hcl] at H
      by_cases hdf : (!evalS_def c e) = true
      · rw [ite_eq_left hdf] at H; exact ih v H
      · rw [ite_eq_right hdf] at H
        cases hr : erange kn c with
        | none => rw [hr] at H; exact ih v H
        | some p =>
          obtain ⟨lo, hi⟩ := p
          rw [hr] at H
          simp only [] at H
          by_cases hlim : hi - lo ≤ conc_limit
          · rw [ite_eq_left hlim] at H
            rw [evalS_eq] at H
            cases hv : eval_closed (esubst c (.ELit lo) e) with
            | none => rw [hv] at H; exact ih v H
            | some w =>
              rw [hv] at H
              simp only [] at H
              by_cases hprobe : (if hi < lo then true
                  else if probeS c e w hi then probeS c e w (lo + (hi - lo) / 2) else false) = true
              · rw [ite_eq_left hprobe] at H
                rw [all_eval_toS_eq] at H
                cases hall : all_eval_to c e w lo (hi - lo + 1).toNat with
                | false => rw [hall] at H; exact ih v H
                | true =>
                  rw [hall] at H
                  simp only [] at H
                  injection H with hvw
                  have hb := erange_sound segs E M kn c lo hi Hkn hr
                  have hcnt : (((hi - lo + 1).toNat : Nat) : Int) = hi - lo + 1 :=
                    Int.toNat_of_nonneg (by omega)
                  have Hall := all_eval_to_sound c e w ((hi - lo + 1).toNat) lo hall
                    (bv_unsigned (edenot E c)) (by omega) (by rw [hcnt]; omega)
                  rw [← hvw]
                  rw [← esubst_sound E c (.ELit (bv_unsigned (edenot E c))) (by
                    show Z_to_bv 64 (bv_unsigned (edenot E c)) = edenot E c
                    exact Z_to_bv_unsigned _) e]
                  exact eval_closed_sound E _ w Hall
              · rw [ite_eq_right hprobe] at H; exact ih v H
          · rw [ite_eq_right hlim] at H; exact ih v H

theorem concretize_sound (segs : List MemImageType.Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (v : Int)
    (Hkn : know_ok segs E M kn) (H : concretize kn e = some v) :
    edenot E e = Z_to_bv 64 v := by
  unfold concretize at H
  by_cases hcl : closedb e = true
  · rw [ite_eq_left hcl] at H; exact eval_closed_sound E e v H
  · rw [ite_eq_right hcl] at H
    exact conc_try_sound segs E M kn e (nubE (subexprs e)) v Hkn H

/-- `foldK_denot`: folding a single-point range (or a successful
    concretization) does not change the denotation. -/
theorem foldK_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E base kn) :
    edenot E (foldK kn e) = edenot E e := by
  cases e with
  | ELit z => rfl
  | EVar n =>
    have CC : edenot E (match concretize kn (.EVar n) with
        | some v => .ELit v | none => (.EVar n)) = edenot E (.EVar n) := by
      cases hc : concretize kn (.EVar n) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (.EVar n)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (.EVar n) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (.EVar n) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (.EVar n) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (.EVar n)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (.EVar n)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EBlob sx k i n =>
    have CC : edenot E (match concretize kn (.EBlob sx k i n) with
        | some v => .ELit v | none => (.EBlob sx k i n)) = edenot E (.EBlob sx k i n) := by
      cases hc : concretize kn (.EBlob sx k i n) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (.EBlob sx k i n)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (.EBlob sx k i n) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (.EBlob sx k i n) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (.EBlob sx k i n) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (.EBlob sx k i n)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (.EBlob sx k i n)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EAlu op a b =>
    have CC : edenot E (match concretize kn (.EAlu op a b) with
        | some v => .ELit v | none => (.EAlu op a b)) = edenot E (.EAlu op a b) := by
      cases hc : concretize kn (.EAlu op a b) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (.EAlu op a b)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (.EAlu op a b) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (.EAlu op a b) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (.EAlu op a b) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (.EAlu op a b)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (.EAlu op a b)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EAluw op a b =>
    have CC : edenot E (match concretize kn (.EAluw op a b) with
        | some v => .ELit v | none => (.EAluw op a b)) = edenot E (.EAluw op a b) := by
      cases hc : concretize kn (.EAluw op a b) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (.EAluw op a b)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (.EAluw op a b) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (.EAluw op a b) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (.EAluw op a b) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (.EAluw op a b)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (.EAluw op a b)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EMd op a b =>
    have CC : edenot E (match concretize kn (expr.EMd op a b) with
        | some v => .ELit v | none => (expr.EMd op a b)) = edenot E (expr.EMd op a b) := by
      cases hc : concretize kn (expr.EMd op a b) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (expr.EMd op a b)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (expr.EMd op a b) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (expr.EMd op a b) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (expr.EMd op a b) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (expr.EMd op a b)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (expr.EMd op a b)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EMdw op a b =>
    have CC : edenot E (match concretize kn (.EMdw op a b) with
        | some v => .ELit v | none => (.EMdw op a b)) = edenot E (.EMdw op a b) := by
      cases hc : concretize kn (.EMdw op a b) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (.EMdw op a b)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (.EMdw op a b) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (.EMdw op a b) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (.EMdw op a b) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (.EMdw op a b)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (.EMdw op a b)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC
  | EExt sx lo n a =>
    have CC : edenot E (match concretize kn (expr.EExt sx lo n a) with
        | some v => .ELit v | none => (expr.EExt sx lo n a)) = edenot E (expr.EExt sx lo n a) := by
      cases hc : concretize kn (expr.EExt sx lo n a) with
      | none => rfl
      | some v =>
        show edenot E (.ELit v) = edenot E (expr.EExt sx lo n a)
        rw [show edenot E (.ELit v) = Z_to_bv 64 v from rfl]
        exact (concretize_sound segs E base kn (expr.EExt sx lo n a) v Hkn hc).symm
    unfold foldK
    simp only []
    cases hr : erange kn (expr.EExt sx lo n a) with
    | none => simp only []; exact CC
    | some p =>
      obtain ⟨rlo, rhi⟩ := p
      simp only []
      by_cases hq : (rlo == rhi) = true
      · rw [ite_eq_left hq]
        have hb := erange_sound segs E base kn (expr.EExt sx lo n a) rlo rhi Hkn hr
        rw [beq_iff_eq] at hq
        have hu : bv_unsigned (edenot E (expr.EExt sx lo n a)) = rlo := by omega
        show edenot E (.ELit rlo) = edenot E (expr.EExt sx lo n a)
        rw [show edenot E (.ELit rlo) = Z_to_bv 64 rlo from rfl, ← hu]
        exact Z_to_bv_unsigned _
      · rw [ite_eq_right hq]; exact CC

/-! ## The `zlnot`/OR block

     order is `land_aligned_small` (4380), `or_disjoint_sound`
    (4404), `or_as_and_not_plus` (4436), `or_R1` (4448), `mkOr_denot`
    (4467), `lxor_ones64` (4489), and only THEN the `eval_closed` block
    (4503).  This this tree places them after `foldK_denot` because they are
    first NEEDED by `mkAluK0_denot` (4647); their -visible
    dependencies (`erange_sound`, `ealign_sound`, `mkAlu_denot`,
    `mkAndK_denot`) are already in place either way.
 This tree has no such lemma, so the identity is built
    from scratch on the `Nat` representative: `nat_or_eq_add_of_and_zero`
    splits both operands at bit 0 (`Nat.two_pow_add_eq_or_of_lt`,
    `Nat.and_div_two`) and halves, with `and_mod_two_zero` supplying the
    "not both odd" side condition.  `two_mul_or` is
    `Nat.shiftLeft_or_distrib` at `i = 1`, and the two `|||`-trees are
    re-associated by `or_or_or_swap` (explicit-argument `rw`: plain `rw`
    picks the wrong `Z.or_assoc` occurrence).
    DEVIATION (`land_aligned_small`).  Carries `x < 2^64` and
    `k ≤ 64`: this tree's `zland` is the 64-bit window of `Z.land`.
    Both call-site facts are at hand (`bv_unsigned`, `ealign_sound`).
    DEVIATION (`or_disjoint_sound`, `zlor_eq_add_of_zland`): stated at
    `zlor` (the window) rather than `Z.lor`, hence the `x, y < 2^64`
    side conditions. -/

theorem two_mul_or (a b : Nat) : 2 * a ||| 2 * b = 2 * (a ||| b) := by
  have h := Nat.shiftLeft_or_distrib (a := a) (b := b) (i := 1)
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.shiftLeft_eq, Nat.pow_one] at h
  rw [Nat.mul_comm (a ||| b) 2, Nat.mul_comm a 2, Nat.mul_comm b 2] at h
  exact h.symm

theorem or_or_or_swap (A z B w : Nat) : (A ||| z) ||| (B ||| w) = (A ||| B) ||| (z ||| w) := by
  rw [Nat.or_assoc A z (B ||| w)]
  rw [← Nat.or_assoc z B w]
  rw [Nat.or_comm z B]
  rw [Nat.or_assoc B z w]
  rw [← Nat.or_assoc A B (z ||| w)]

theorem and_mod_two_zero {u c : Nat} (h : u &&& c = 0) : (u % 2) &&& (c % 2) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one u with hu | hu <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · rw [hu, hc]; simp
  · rw [hu]; simp
  · rw [hc]; simp
  · exfalso
    have h2 : (u &&& c) % 2 = 1 := Nat.and_mod_two_eq_one.mpr ⟨hu, hc⟩
    rw [h] at h2
    omega

theorem nat_or_eq_add_of_and_zero (u c : Nat) (h : u &&& c = 0) : u ||| c = u + c := by
  have key : ∀ n, ∀ u c : Nat, u + c = n → u &&& c = 0 → u ||| c = u + c := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro u c hn h
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu; simp
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp
      have hd : u / 2 &&& c / 2 = 0 := by
        have h1 := Nat.and_div_two (a := u) (b := c)
        rw [h] at h1
        simp at h1
        exact h1.symm
      have hlt : u / 2 + c / 2 < n := by
        have h1 : u / 2 < u := Nat.div_lt_self hu (by decide)
        have h2 : c / 2 ≤ c := Nat.div_le_self c 2
        omega
      have hIH : u / 2 ||| c / 2 = u / 2 + c / 2 := ih _ hlt _ _ rfl hd
      have hz2 : u % 2 ||| c % 2 = u % 2 + c % 2 := by
        have h0 := and_mod_two_zero h
        rcases Nat.mod_two_eq_zero_or_one u with a | a <;>
        rcases Nat.mod_two_eq_zero_or_one c with b | b
        · rw [a, b]; simp
        · rw [a, b]; simp
        · rw [a, b]; simp
        · rw [a, b] at h0; simp at h0
      have hsum : u + c = 2 * (u / 2 + c / 2) + (u % 2 + c % 2) := by
        have h1 := Nat.div_add_mod u 2
        have h2 := Nat.div_add_mod c 2
        omega
      have hu2 : 2 * (u / 2) + u % 2 = u := Nat.div_add_mod u 2
      have hc2 : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
      have hzu : u % 2 < 2 := Nat.mod_lt _ (by decide)
      have hzc : c % 2 < 2 := Nat.mod_lt _ (by decide)
      have hz : u % 2 ||| c % 2 < 2 := by
        have h := Nat.or_lt_two_pow (n := 1) hzu hzc
        rwa [Nat.pow_one] at h
      have h1 : 2 * (u / 2) + u % 2 = 2 * (u / 2) ||| (u % 2) := by
        have h := Nat.two_pow_add_eq_or_of_lt (i := 1) hzu (u / 2)
        rwa [Nat.pow_one] at h
      have h2 : 2 * (c / 2) + c % 2 = 2 * (c / 2) ||| (c % 2) := by
        have h := Nat.two_pow_add_eq_or_of_lt (i := 1) hzc (c / 2)
        rwa [Nat.pow_one] at h
      have h3 : 2 * (u / 2 ||| c / 2) + (u % 2 ||| c % 2)
          = 2 * (u / 2 ||| c / 2) ||| (u % 2 ||| c % 2) := by
        have h := Nat.two_pow_add_eq_or_of_lt (i := 1) hz (u / 2 ||| c / 2)
        rwa [Nat.pow_one] at h
      have hor : u ||| c = 2 * (u / 2 ||| c / 2) + (u % 2 ||| c % 2) := by
        have hL : u ||| c = (2 * (u / 2) ||| (u % 2)) ||| (2 * (c / 2) ||| (c % 2)) := by
          conv => lhs; rw [← hu2, ← hc2]
          rw [h1, h2]
        rw [hL, or_or_or_swap, two_mul_or, h3]
      rw [hor, hIH, hz2, ← hsum]
  exact key (u + c) u c rfl h

/-- `zland x y = 0` makes `zlor` the plain sum (no carry). -/
theorem zlor_eq_add_of_zland (x y : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hy : 0 ≤ y ∧ y < 2 ^ 64)
    (H : AxSymExec3.zland x y = 0) : AxSymExec3.zlor x y = x + y := by
  have hx : x % two64 = x := Int.emod_eq_of_lt Hx.1 (by rw [two64_eq]; exact Hx.2)
  have hy : y % two64 = y := Int.emod_eq_of_lt Hy.1 (by rw [two64_eq]; exact Hy.2)
  have hz : x.toNat &&& y.toNat = 0 := by
    have h := H
    unfold AxSymExec3.zland at h
    rw [hx, hy] at h
    omega
  have hor : x.toNat ||| y.toNat = x.toNat + y.toNat := nat_or_eq_add_of_and_zero _ _ hz
  unfold AxSymExec3.zlor
  rw [hx, hy, hor]
  have h3 : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg Hx.1
  have h4 : ((y.toNat : Nat) : Int) = y := Int.toNat_of_nonneg Hy.1
  rw [Int.natCast_add, h3, h4]

/-- A multiple of `2^k` has no bits below `k`, so `zland` with anything
    below `2^k` is `0`.   -/
theorem land_aligned_small (x b k : Int) (Hk64 : k.toNat ≤ 64)
    (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hdiv : (2 ^ k.toNat : Int) ∣ x)
    (Hb : 0 ≤ b ∧ b < 2 ^ k.toNat) :
    AxSymExec3.zland x b = 0 := by
  obtain ⟨q, Hq⟩ := Hdiv
  have hp : (0 : Int) < 2 ^ k.toNat := two_pow_pos_int _
  have hq0 : 0 ≤ q := by
    by_cases h : 0 ≤ q
    · exact h
    · have hneg : (2 : Int) ^ k.toNat * q < 0 := Int.mul_neg_of_pos_of_neg hp (by omega)
      omega
  have hX : x.toNat = 2 ^ k.toNat * q.toNat := by
    rw [Hq, Int.toNat_mul (by omega) hq0]
    push_cast
    rfl
  have hB : b.toNat < 2 ^ k.toNat := by
    have : ((b.toNat : Nat) : Int) < 2 ^ k.toNat := by
      rw [Int.toNat_of_nonneg Hb.1]; exact Hb.2
    exact_mod_cast this
  have hone : b.toNat = b.toNat &&& (2 ^ k.toNat - 1) := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hB]
  have hstep : x.toNat &&& b.toNat = (x.toNat &&& (2 ^ k.toNat - 1)) &&& b.toNat := by
    rw [Nat.and_assoc, Nat.and_comm (2 ^ k.toNat - 1) b.toNat, ← hone]
  have hz : x.toNat &&& (2 ^ k.toNat - 1) = 0 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_zero_of_dvd ⟨q.toNat, hX⟩]
  have hx64 : x % two64 = x := Int.emod_eq_of_lt Hx.1 (by rw [two64_eq]; exact Hx.2)
  have hb64 : b % two64 = b := Int.emod_eq_of_lt Hb.1 (by
    rw [two64_eq]
    have := int_pow_le_pow k.toNat 64 Hk64
    omega)
  unfold AxSymExec3.zland
  rw [hx64, hb64, hstep, hz]
  simp

/-- `or_disjoint_sound`: when the range of `b` sits below the
    alignment of `a`, the OR is the plain sum. -/
theorem or_disjoint_sound (segs : List MemImageType.Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (a b : expr) (Hkn : know_ok segs E M kn)
    (H : or_disjoint kn a b = true) :
    AxSymExec3.zlor (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))
      = bv_unsigned (edenot E a) + bv_unsigned (edenot E b) := by
  unfold or_disjoint at H
  cases hr : erange kn b with
  | none => rw [hr] at H; exact absurd H (by simp)
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [hr] at H
    simp only [] at H
    rw [Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    rw [decide_eq_true_eq] at H1
    rw [decide_eq_true_eq] at H2
    rw [show zpow 2 (ealign kn a) = (2 : Int) ^ (ealign kn a).toNat from rfl] at H2
    have Hb := erange_sound segs E M kn b lo hi Hkn hr
    obtain ⟨⟨Hk0, Hk64⟩, Hdiv⟩ := ealign_sound segs E M kn a Hkn
    refine zlor_eq_add_of_zland _ _ (u64_range _) (u64_range _) ?_
    have Hk64' : (ealign kn a).toNat ≤ 64 := by
      have : ((ealign kn a).toNat : Int) = ealign kn a := Int.toNat_of_nonneg Hk0
      omega
    refine land_aligned_small _ _ (ealign kn a) Hk64' (u64_range _) Hdiv ⟨by omega, by omega⟩


/-! ### The all-ones complement primitive

    `or_as_and_not_plus` and `lxor_ones64` both need the same fact: for
    `c < 2^k`, `2^k - 1 - c` is the bitwise complement of `c` in the low
    `k` bits.  Lean core has NO `Nat.testBit_sub`, but it does have
    `Nat.testBit_two_pow_sub_succ`
    (`testBit (2^n - (x+1)) i = (decide (i < n) && ! testBit x i)`), which
    IS that fact; the whole primitive is then three
    `Nat.eq_of_testBit_eq` proofs.  This is a much shorter route than the
    halving induction sketched in the file header (kept there as history:
    it was written before `Nat.testBit_two_pow_sub_succ` was found).

    The `Int` layer is bookkeeping: `zlnot c % 2^64 = 2^64 - 1 - c` for
    `0 ≤ c < 2^64` (`zlnot_emod_pow`), and the `Nat` identity
    `nat_or_eq_and_ones_sub_add` lifted through the 64-bit window
    (`or_as_and_not_plus`).  `lxor_ones64` is the same complement fact
    read as an exclusive OR (`lxor_all_ones_sub`).

    Almost every step here must be stated at `2 ^ 64`, not
    `two64`: `omega` does not know `two64 = 2 ^ 64`, so a hypothesis
    `c < 2 ^ 64` and a goal `... % two64` are unrelated atoms for it
    (the pitfalls list in the header).  The `two64` forms are recovered by
    `rw [two64_eq]` at the points where `zland`/`zlor`/`zlxor` have been
    unfolded.  Also note the `(2 ^ 64 : Int)` ascription: in a bare
    `have h : 2 ^ 64 - 1 = ...` Lean elaborates the `2` at `Nat`.
-/

theorem testBit_ones_sub {x n i : Nat} (hx : x < 2 ^ n) :
    Nat.testBit (2 ^ n - 1 - x) i = (decide (i < n) && !Nat.testBit x i) := by
  rw [Nat.sub_sub, Nat.add_comm]
  exact Nat.testBit_two_pow_sub_succ hx i

theorem land_ones_sub_eq_zero {c k : Nat} (hc : c < 2 ^ k) :
    c &&& (2 ^ k - 1 - c) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_ones_sub hc]
  by_cases hi : i < k
  · simp only [hi, decide_true, Bool.true_and, Nat.zero_testBit]
    cases Nat.testBit c i <;> rfl
  · have hx : Nat.testBit c i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
    simp only [hi, decide_false, Bool.false_and, hx, Bool.and_false, Nat.zero_testBit]

theorem lor_ones_sub {c k : Nat} (hc : c < 2 ^ k) :
    c ||| (2 ^ k - 1 - c) = 2 ^ k - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_ones_sub hc, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < k
  · simp only [hi, decide_true, Bool.true_and]
    cases Nat.testBit c i <;> rfl
  · have hx : Nat.testBit c i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
    simp only [hi, decide_false, Bool.false_and, hx, Bool.or_false]

theorem lxor_all_ones_sub {x k : Nat} (hx : x < 2 ^ k) :
    x ^^^ (2 ^ k - 1) = 2 ^ k - 1 - x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_ones_sub hx]
  by_cases hi : i < k
  · simp only [hi, decide_true, Bool.true_and]
    cases Nat.testBit x i <;> rfl
  · have hc : Nat.testBit x i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    simp only [hi, decide_false, Bool.false_and, hc, Bool.xor_false]

theorem nat_or_eq_and_ones_sub_add (x c k : Nat) (hx : x < 2 ^ k) (hc : c < 2 ^ k) :
    x ||| c = (x &&& (2 ^ k - 1 - c)) + c := by
  have hd : (x &&& (2 ^ k - 1 - c)) &&& c = 0 := by
    rw [Nat.and_assoc, Nat.and_comm (2 ^ k - 1 - c) c, land_ones_sub_eq_zero hc, Nat.and_zero]
  have h1 := nat_or_eq_add_of_and_zero (x &&& (2 ^ k - 1 - c)) c hd
  rw [← h1, Nat.or_and_distrib_right]
  rw [show (2 ^ k - 1 - c) ||| c = 2 ^ k - 1 from by rw [Nat.or_comm]; exact lor_ones_sub hc]
  exact (Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.or_lt_two_pow hx hc)).symm

theorem pow64_toNat : (2 ^ 64 : Int).toNat = 2 ^ 64 := by
  have h : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := by rw [← two64_eq, two64_eq_natCast]
  rw [h, Int.toNat_natCast]

theorem natCast_pow64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by
  rw [← two64_eq_natCast, two64_eq]

theorem natCast_pow64_sub_one : ((2 ^ 64 - 1 : Nat) : Int) = (2 ^ 64 - 1 : Int) := by
  rw [Int.natCast_sub (by decide : (1 : Nat) ≤ 2 ^ 64), natCast_pow64]
  simp

theorem toNat_pow_sub_one : (2 ^ 64 - 1 : Int).toNat = 2 ^ 64 - 1 := by
  rw [Int.toNat_sub'' (by omega) (by decide), pow64_toNat]
  rfl

theorem zlnot_emod_pow (c : Int) (Hc : 0 ≤ c ∧ c < 2 ^ 64) :
    AxSymExec3.zlnot c % (2 ^ 64 : Int) = 2 ^ 64 - 1 - c := by
  have h1 : AxSymExec3.zlnot c = (2 ^ 64 - 1 - c) - 2 ^ 64 := by
    show -c - 1 = 2 ^ 64 - 1 - c - 2 ^ 64
    omega
  rw [h1, Int.sub_emod_right]
  apply Int.emod_eq_of_lt <;> omega

theorem zlnot_emod_toNat (c : Int) (Hc : 0 ≤ c ∧ c < 2 ^ 64) :
    (AxSymExec3.zlnot c % (2 ^ 64 : Int)).toNat = 2 ^ 64 - 1 - c.toNat := by
  rw [zlnot_emod_pow c Hc, Int.toNat_sub'' (by omega) Hc.1, toNat_pow_sub_one]

theorem toNat_lt_two64_of (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) : x.toNat < 2 ^ 64 := by
  have h : ((x.toNat : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [Int.toNat_of_nonneg Hx.1]; exact Hx.2
  exact_mod_cast h

theorem or_as_and_not_plus (x c : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hc : 0 ≤ c ∧ c < 2 ^ 64) :
    AxSymExec3.zlor x c = AxSymExec3.zland x (AxSymExec3.zlnot c) + c := by
  have hxeq : x % (2 ^ 64 : Int) = x := by rw [← two64_eq]; exact u_small_id x Hx
  have hceq : c % (2 ^ 64 : Int) = c := by rw [← two64_eq]; exact u_small_id c Hc
  have hxN := toNat_lt_two64_of x Hx
  have hcN := toNat_lt_two64_of c Hc
  have hkey := nat_or_eq_and_ones_sub_add x.toNat c.toNat 64 hxN hcN
  have hcn : ((c.toNat : Nat) : Int) = c := Int.toNat_of_nonneg Hc.1
  have hcn' : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg Hx.1
  have hM : (AxSymExec3.zlnot c % (2 ^ 64 : Int)).toNat = 2 ^ 64 - 1 - c.toNat :=
    zlnot_emod_toNat c Hc
  have hR : ((x.toNat ||| c.toNat : Nat) : Int)
      = ((x.toNat &&& (2 ^ 64 - 1 - c.toNat) : Nat) : Int) + c := by
    simp only [hkey, Int.natCast_add, hcn]
  unfold AxSymExec3.zlor AxSymExec3.zland
  rw [two64_eq, hxeq, hceq, hM, ← hR]

theorem lxor_ones64 (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    AxSymExec3.zlxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x := by
  have hxeq : x % (2 ^ 64 : Int) = x := by rw [← two64_eq]; exact u_small_id x Hx
  have hp : (0 : Int) < 2 ^ 64 := by rw [← two64_eq]; exact two64_pos
  have hp64 : (0 : Int) < two64 := two64_pos
  have h1 : (2 ^ 64 - 1 : Int) % 2 ^ 64 = 2 ^ 64 - 1 := by
    rw [← two64_eq]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hxN := toNat_lt_two64_of x Hx
  have hxn : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg Hx.1
  unfold AxSymExec3.zlxor
  rw [two64_eq, hxeq, h1, toNat_pow_sub_one, lxor_all_ones_sub hxN]
  rw [Int.natCast_sub (Nat.le_sub_one_of_lt hxN), hxn, natCast_pow64_sub_one]


theorem or_R1 (segs : List Segment) (E : env) (M : word → Option byte) (kn : List kentry)
    (a0 : expr) (c : Int) (Hkn : know_ok segs E M kn) :
    edenot E (mkAlu .ADD (mkAndK kn a0 (.ELit (zlnot (c % two64)))) (.ELit c))
      = alu64 .OR (edenot E a0) (edenot E (.ELit c)) := by
  rw [mkAlu_denot, mkAndK_denot segs E M kn a0 (.ELit (zlnot (c % two64))) Hkn]
  apply word_eq_of_bv_unsigned
  show bv_unsigned (alu64 .AND (edenot E a0) (Z_to_bv 64 (zlnot (c % two64))) + Z_to_bv 64 c)
      = bv_unsigned (alu64 .OR (edenot E a0) (Z_to_bv 64 c))
  rw [u_add64, u_and64, u_or64]
  simp only [u_lit64]
  obtain ⟨hx0, hxlt⟩ := u64_range (edenot E a0)
  have hc0 : 0 ≤ c % two64 := Int.emod_nonneg _ two64_ne
  have hclt : c % two64 < 2 ^ 64 := by
    have h := Int.emod_lt_of_pos c two64_pos
    rw [two64_eq] at h ⊢
    exact h
  rw [show AxSymExec3.zland (bv_unsigned (edenot E a0)) (zlnot (c % two64) % two64)
      = AxSymExec3.zland (bv_unsigned (edenot E a0)) (zlnot (c % two64))
    from zland_emod _ _]
  rw [show AxSymExec3.zland (bv_unsigned (edenot E a0)) (zlnot (c % two64)) + (c % two64)
      = AxSymExec3.zlor (bv_unsigned (edenot E a0)) (c % two64)
    from (or_as_and_not_plus _ _ ⟨hx0, hxlt⟩ ⟨hc0, hclt⟩).symm]
  rw [two64_eq]
  apply Int.emod_eq_of_lt
  · show (0 : Int) ≤ AxSymExec3.zlor (bv_unsigned (edenot E a0)) (c % two64)
    unfold AxSymExec3.zlor
    exact Int.natCast_nonneg _
  · exact zlor_lt_two64 _ _

theorem zlor_comm_int (x y : Int) : AxSymExec3.zlor x y = AxSymExec3.zlor y x := by
  unfold AxSymExec3.zlor
  rw [Nat.or_comm]

theorem mkOr_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (a b : expr) (Hkn : know_ok segs E M kn) :
    edenot E (mkOr kn a b) = alu64 .OR (edenot E a) (edenot E b) := by
  have Hcomm : ∀ u v : word, alu64 .OR u v = alu64 .OR v u := by
    intro u v
    show u ||| v = v ||| u
    exact BitVec.or_comm u v
  have DISJ : ∀ (u v : expr), or_disjoint kn u v = true →
      edenot E (mkAlu .ADD u v) = alu64 .OR (edenot E u) (edenot E v) := by
    intro u v huv
    have hd := or_disjoint_sound segs E M kn u v Hkn huv
    rw [mkAlu_denot]
    apply word_eq_of_bv_unsigned
    show bv_unsigned (edenot E u + edenot E v)
        = bv_unsigned (alu64 .OR (edenot E u) (edenot E v))
    rw [u_add64, u_or64]
    have hsum : bv_unsigned (edenot E u) + bv_unsigned (edenot E v)
        = AxSymExec3.zlor (bv_unsigned (edenot E u)) (bv_unsigned (edenot E v)) := hd.symm
    rw [hsum]
    apply Int.emod_eq_of_lt
    · unfold AxSymExec3.zlor; exact Int.natCast_nonneg _
    · exact zlor_lt_two64 _ _
  have DISJ' : ∀ (u v : expr), or_disjoint kn v u = true →
      edenot E (mkAlu .ADD u v) = alu64 .OR (edenot E u) (edenot E v) := by
    intro u v huv
    have hd := or_disjoint_sound segs E M kn v u Hkn huv
    rw [mkAlu_denot]
    apply word_eq_of_bv_unsigned
    show bv_unsigned (edenot E u + edenot E v)
        = bv_unsigned (alu64 .OR (edenot E u) (edenot E v))
    rw [u_add64, u_or64]
    have hsum : bv_unsigned (edenot E u) + bv_unsigned (edenot E v)
        = AxSymExec3.zlor (bv_unsigned (edenot E u)) (bv_unsigned (edenot E v)) := by
      rw [zlor_comm_int, Int.add_comm]; exact hd.symm
    rw [hsum]
    apply Int.emod_eq_of_lt
    · unfold AxSymExec3.zlor; exact Int.natCast_nonneg _
    · exact zlor_lt_two64 _ _
  unfold mkOr
  cases ha : is_lit a with
  | some x =>
    cases hb : is_lit b with
    | some y =>
      rw [is_lit_some ha, is_lit_some hb]
      show Z_to_bv 64 (zalu .OR x y) = alu64 .OR (Z_to_bv 64 x) (Z_to_bv 64 y)
      unfold zalu
      exact ofInt_toNat _
    | none =>
      by_cases h1 : or_disjoint kn a b = true
      · rw [ite_eq_left h1]; exact DISJ a b h1
      · rw [ite_eq_right h1]
        by_cases h2 : or_disjoint kn b a = true
        · rw [ite_eq_left h2]; exact DISJ' a b h2
        · rw [ite_eq_right h2, is_lit_some ha]
          cases b with
          | ELit y => simp [is_lit] at hb
          | EVar n =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EAlu op u v =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EAluw op u v =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EMd op u v =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EMdw op u v =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EExt sx lo n e =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
          | EBlob sx k i n =>
            rw [or_R1 segs E M kn _ x Hkn]; exact Hcomm _ _
  | none =>
    cases hb : is_lit b with
    | some y =>
      by_cases h1 : or_disjoint kn a b = true
      · rw [ite_eq_left h1]; exact DISJ a b h1
      · rw [ite_eq_right h1]
        by_cases h2 : or_disjoint kn b a = true
        · rw [ite_eq_left h2]; exact DISJ' a b h2
        · rw [ite_eq_right h2, is_lit_some hb]
          rw [or_R1 segs E M kn a y Hkn]
    | none =>
      by_cases h1 : or_disjoint kn a b = true
      · rw [ite_eq_left h1]; exact DISJ a b h1
      · rw [ite_eq_right h1]
        by_cases h2 : or_disjoint kn b a = true
        · rw [ite_eq_left h2]; exact DISJ' a b h2
        · rw [ite_eq_right h2]
          cases b with
          | ELit y => simp [is_lit] at hb
          | EVar n =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EAlu op u v =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EAluw op u v =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EMd op u v =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EMdw op u v =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EExt sx lo n e =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl
          | EBlob sx k i n =>
            cases a with
            | ELit z => simp [is_lit] at ha
            | _ => rfl

/-! ### The knowledge-aware ALU constructors

    `mkSlt_denot` (SLT/SLTU decided like branches) and `mkAluK0_denot`
    (the per-operator case bash: SLT/SLTU via `mkSlt`, XOR via the
    all-ones complement `lxor_ones64`, OR via `mkOr`, AND via
    `mkAnd`/`mkAndK`, SRL via `mkSrl`).

    `unfold mkAluK0` then `cases op` leaves
    the goal's `match` UNREDUCED; each arm needs `simp only []` to
    iota-reduce it (the header's pitfall).  The same holds after
    `cases b` inside the XOR arm.  `split` is NOT usable for the XOR
    arm's `(is_lit a, b)` match: it generalizes `b` to an inaccessible
    `b✝`, so the fallback arm cannot name it — `cases b` with eight arms
    is the predictable spelling (`exact mkAlu_denot E .XOR a _` covers
    the seven non-literal ones).
    `omega` treats
    `bv_unsigned w` and `↑(w.toNat)` as DIFFERENT atoms, so a bound
    obtained from `u64_range` (`↑(w.toNat)`) will not discharge a goal
    phrased at `bv_unsigned`.  `simp only [bv_unsigned] at *` before
    `omega` normalises both to the coercion form. -/

theorem mkSlt_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : BranchCond) (op : AluOp) (a b : expr)
    (Hkn : know_ok segs E M kn)
    (Hop : ∀ x y : word, alu64 op x y
      = if branch_taken c x y then Z_to_bv 64 1 else Z_to_bv 64 0) :
    edenot E (mkSlt kn c op a b) = alu64 op (edenot E a) (edenot E b) := by
  have Hd : ∀ t : Bool, decide_branch kn c a b = some t →
      edenot E (if t then .ELit 1 else .ELit 0) = alu64 op (edenot E a) (edenot E b) := by
    intro t Ht
    rw [Hop, decide_branch_sound segs E M kn c a b t Hkn Ht]
    cases t <;> rfl
  unfold mkSlt
  split
  · exact mkAlu_denot E op _ _
  · split
    · rename_i h; exact Hd true h
    · rename_i h; exact Hd false h
    · exact mkAlu_denot E op _ _

theorem mkAluK0_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (op : AluOp) (a b : expr) (Hkn : know_ok segs E M kn) :
    edenot E (mkAluK0 kn op a b) = alu64 op (edenot E a) (edenot E b) := by
  have HcommOR : ∀ u v : word, alu64 .OR u v = alu64 .OR v u := by
    intro u v
    show u ||| v = v ||| u
    exact BitVec.or_comm u v
  have HcommAND : ∀ u v : word, alu64 .AND u v = alu64 .AND v u := by
    intro u v
    show u &&& v = v &&& u
    exact BitVec.and_comm u v
  unfold mkAluK0
  cases op with
  | SLT => simp only []; exact mkSlt_denot segs E M kn .LT .SLT a b Hkn (fun x y => rfl)
  | SLTU => simp only []; exact mkSlt_denot segs E M kn .LTU .SLTU a b Hkn (fun x y => rfl)
  | ADD => simp only []; exact mkAlu_denot E .ADD a b
  | SUB => simp only []; exact mkAlu_denot E .SUB a b
  | SLL => simp only []; exact mkAlu_denot E .SLL a b
  | SRA => simp only []; exact mkAlu_denot E .SRA a b
  | XOR =>
    simp only []
    by_cases Heq : expr_eqb a b = true
    · rw [ite_eq_left Heq]
      have hab : b = a := (expr_eqb_eq a b Heq).symm
      rw [hab]
      show Z_to_bv 64 0 = alu64 .XOR (edenot E a) (edenot E a)
      show Z_to_bv 64 0 = (edenot E a ^^^ edenot E a)
      rw [BitVec.xor_self]
      rfl
    · rw [ite_eq_right Heq]
      cases ha : is_lit a with
      | some x => simp only []; exact mkAlu_denot E .XOR a b
      | none =>
        cases b with
        | ELit k =>
          simp only []
          by_cases hk : (k % two64 == two64 - 1) = true
          · rw [ite_eq_left hk]
            rw [mkAlu_denot]
            apply word_eq_of_bv_unsigned
            show bv_unsigned (Z_to_bv 64 (two64 - 1) - edenot E a)
                = bv_unsigned (alu64 .XOR (edenot E a) (Z_to_bv 64 k))
            rw [u_sub64, u_xor64, u_lit64, u_lit64]
            obtain ⟨hx0, hxlt⟩ := u64_range (edenot E a)
            have hkk : k % two64 = 2 ^ 64 - 1 := beq_iff_eq.mp hk
            have hpow : (two64 - 1) % two64 = 2 ^ 64 - 1 := by
              rw [two64_eq]
              exact Int.emod_eq_of_lt (by omega) (by omega)
            rw [hpow, hkk, lxor_ones64 _ ⟨hx0, hxlt⟩]
            simp only [bv_unsigned] at *
            apply Int.emod_eq_of_lt <;> omega
          · rw [ite_eq_right hk]; exact mkAlu_denot E .XOR a _
        | EVar n => exact mkAlu_denot E .XOR a _
        | EAlu o x y => exact mkAlu_denot E .XOR a _
        | EAluw o x y => exact mkAlu_denot E .XOR a _
        | EMd o x y => exact mkAlu_denot E .XOR a _
        | EMdw o x y => exact mkAlu_denot E .XOR a _
        | EExt sx lo n e => exact mkAlu_denot E .XOR a _
        | EBlob sx kk i n => exact mkAlu_denot E .XOR a _
  | SRL =>
    simp only []
    cases ha : is_lit a with
    | some x => simp only []; exact mkAlu_denot E .SRL a b
    | none =>
      try simp only []
      cases hs : shamt_of b 6 with
      | none => try simp only []; exact mkAlu_denot E .SRL a b
      | some s =>
        try simp only []
        have h8 := (shamt_of_sound E b 6 s ⟨by decide, by decide⟩ hs).1
        have h6 : zpow 2 6 = (64 : Int) := by decide
        rw [h6] at h8
        exact mkSrl_denot segs E M kn a s (edenot E b) Hkn h8
  | OR =>
    simp only []
    by_cases Heq : expr_eqb a b = true
    · rw [ite_eq_left Heq]
      have hab : b = a := (expr_eqb_eq a b Heq).symm
      rw [hab]
      show edenot E a = alu64 .OR (edenot E a) (edenot E a)
      show edenot E a = (edenot E a ||| edenot E a)
      rw [BitVec.or_self]
    · rw [ite_eq_right Heq]
      exact mkOr_denot segs E M kn a b Hkn
  | AND =>
    simp only []
    split
    · exact mkAnd_denot segs E M kn _ _ Hkn
    · rw [mkAndK_denot segs E M kn _ _ Hkn]; exact HcommAND _ _
    · exact mkAndK_denot segs E M kn _ _ Hkn

/-! ### The knowledge-aware M constructor

    `mkAluK_denot` (the `foldK` wrapper), `pow2_log_sound` (the
    power-of-two recogniser) and `mkMdK_denot` (DIVU/REMU by a literal
    `2^k` are a right shift / a low-bit mask).

    Local helpers: `zpow2_bounds` (`0 < 2^k < 2^64` for `k < 64`),
    `zpow2_toNat`, `zpow2_sub_one_toNat`, `zpow2_sub_one_mod_toNat` /
    `_mod_mod_toNat` (the `.toNat` of `2^k - 1`, in the two mod-spellings
    the `zland` window produces). -/

theorem mkAluK_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (op : AluOp) (a b : expr) (Hkn : know_ok segs E M kn) :
    edenot E (mkAluK kn op a b) = alu64 op (edenot E a) (edenot E b) := by
  unfold mkAluK
  rw [foldK_denot segs E M kn _ Hkn]
  exact mkAluK0_denot segs E M kn op a b Hkn

theorem pow2_log_sound (m k : Int) (H : pow2_log m = some k) :
    0 ≤ k ∧ k < 64 ∧ m % two64 = zpow 2 k := by
  unfold pow2_log at H
  simp only [] at H
  split at H
  · rename_i hb
    have hk : AxSymExec3.zlog2 (m % two64) = k := Option.some.inj H
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    rw [decide_eq_true_eq] at h1 h3
    rw [beq_iff_eq] at h2
    rw [← hk]
    exact ⟨zlog2_nonneg _, h3, h2⟩
  · exact absurd H (by simp)

theorem zpow2_bounds {k : Int} (hk0 : 0 ≤ k) (hk64 : k < 64) :
    (0:Int) < zpow 2 k ∧ zpow 2 k < 2 ^ 64 := by
  unfold zpow
  refine ⟨two_pow_pos_int _, ?_⟩
  have hle : (2:Int) ^ k.toNat ≤ 2 ^ 63 := int_pow_le_pow _ _ (by omega)
  have h63 : (2:Int) ^ 64 = 2 * 2 ^ 63 := by
    rw [show (64 : Nat) = 63 + 1 from rfl, Int.pow_succ, Int.mul_comm]
  have hp := two_pow_pos_int 63
  omega

theorem zpow2_toNat {k : Int} (hk0 : 0 ≤ k) :
    (zpow 2 k).toNat = 2 ^ k.toNat := by
  unfold zpow
  exact int_pow_toNat _

theorem zpow2_sub_one_toNat {k : Int} (hk0 : 0 ≤ k) (hk64 : k < 64) :
    (zpow 2 k - 1).toNat = 2 ^ k.toNat - 1 := by
  rw [Int.toNat_sub'' (Int.le_of_lt (zpow2_bounds hk0 hk64).1) (by decide),
    zpow2_toNat hk0]
  rfl

theorem zpow2_sub_one_mod_toNat {k : Int} (hk0 : 0 ≤ k) (hk64 : k < 64) :
    ((zpow 2 k - 1) % two64).toNat = 2 ^ k.toNat - 1 := by
  have hb := zpow2_bounds hk0 hk64
  have hsub : (zpow 2 k - 1) % two64 = zpow 2 k - 1 := by
    rw [two64_eq]; exact u_small_id _ ⟨by omega, by omega⟩
  rw [hsub, zpow2_sub_one_toNat hk0 hk64]

theorem zpow2_sub_one_mod_mod_toNat {k : Int} (hk0 : 0 ≤ k) (hk64 : k < 64) :
    (((zpow 2 k - 1) % two64) % two64).toNat = 2 ^ k.toNat - 1 := by
  rw [Int.emod_emod, zpow2_sub_one_mod_toNat hk0 hk64]

theorem mkMdK_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (op : MulOp) (a b : expr) (Hkn : know_ok segs E M kn) :
    edenot E (mkMdK kn op a b) = mul_div op (edenot E a) (edenot E b) := by
  have KEY : ∀ (k m : Int), 0 ≤ k → k < 64 → m % two64 = zpow 2 k →
      bv_unsigned (Z_to_bv 64 m) = zpow 2 k := by
    intro k m hk0 hk64 hm
    rw [u_lit64, hm]
  have HREMU : ∀ (k : Int), 0 ≤ k → k < 64 →
      bv_unsigned (alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 k - 1)))
        = bv_unsigned (edenot E a) % zpow 2 k := by
    intro k hk0 hk64
    have hb := zpow2_bounds hk0 hk64
    have hsub : (zpow 2 k - 1) % two64 = zpow 2 k - 1 := by
      rw [two64_eq]; exact u_small_id _ ⟨by omega, by omega⟩
    have hxid0 : bv_unsigned (edenot E a) % two64 = bv_unsigned (edenot E a) :=
      u_small_id _ (u64_range (edenot E a))
    have hzp : zpow 2 k = ((2 ^ k.toNat : Nat) : Int) := by
      unfold zpow; exact natCast_pow_two _
    rw [u_and64, u_lit64]
    unfold AxSymExec3.zland
    rw [hxid0, zpow2_sub_one_mod_mod_toNat hk0 hk64, Nat.and_two_pow_sub_one_eq_mod, hzp,
      ← Int.natCast_emod]
    rfl
  have HDIVU : ∀ (k : Int), 0 ≤ k → k < 64 →
      bv_unsigned (alu64 .SRL (edenot E a) (Z_to_bv 64 k))
        = bv_unsigned (edenot E a) / zpow 2 k := by
    intro k hk0 hk64
    have hb := zpow2_bounds hk0 hk64
    have hklt : k < 2 ^ 64 := by have := hb.2; unfold zpow at this; omega
    have Hy : bv_unsigned (Z_to_bv 64 k) % 64 = k := by
      rw [u_lit64, u_small_id k ⟨hk0, hklt⟩]
      exact Int.emod_eq_of_lt hk0 hk64
    have hx0 : 0 ≤ bv_unsigned (edenot E a) := (u64_range (edenot E a)).1
    have hxlt : bv_unsigned (edenot E a) < 2 ^ 64 := (u64_range (edenot E a)).2
    rw [alu_srl_div _ _ k Hy, u_lit64]
    have h0 : 0 ≤ bv_unsigned (edenot E a) / zpow 2 k := Int.ediv_nonneg hx0 (Int.le_of_lt hb.1)
    have h1 : bv_unsigned (edenot E a) / zpow 2 k ≤ bv_unsigned (edenot E a) :=
      Int.ediv_le_self _ hx0
    rw [u_small_id _ ⟨h0, by omega⟩]
  unfold mkMdK
  try simp only []
  cases ha : is_lit a with
  | some x => try simp only []; exact mkMd_denot E op a b
  | none =>
    cases op with
    | DIVU =>
      cases b with
      | ELit m =>
        try simp only []
        cases hp : pow2_log m with
        | none => try simp only []; exact mkMd_denot E .DIVU a _
        | some k =>
          try simp only []
          obtain ⟨hk0, hk64, hm⟩ := pow2_log_sound m k hp
          rw [mkAluK_denot segs E M kn .SRL a (.ELit k) Hkn]
          apply word_eq_of_bv_unsigned
          show bv_unsigned (alu64 .SRL (edenot E a) (Z_to_bv 64 k))
              = bv_unsigned (mul_div .DIVU (edenot E a) (Z_to_bv 64 m))
          have hpos : 0 < bv_unsigned (Z_to_bv 64 m) := by
            rw [KEY k m hk0 hk64 hm]; exact (zpow2_bounds hk0 hk64).1
          rw [HDIVU k hk0 hk64, u_divu64 _ _ hpos, KEY k m hk0 hk64 hm]
      | EVar n => try simp only []; exact mkMd_denot E .DIVU a _
      | EAlu o x y => try simp only []; exact mkMd_denot E .DIVU a _
      | EAluw o x y => try simp only []; exact mkMd_denot E .DIVU a _
      | EMd o x y => try simp only []; exact mkMd_denot E .DIVU a _
      | EMdw o x y => try simp only []; exact mkMd_denot E .DIVU a _
      | EExt sx lo n e => try simp only []; exact mkMd_denot E .DIVU a _
      | EBlob sx kk i n => try simp only []; exact mkMd_denot E .DIVU a _
    | REMU =>
      cases b with
      | ELit m =>
        try simp only []
        cases hp : pow2_log m with
        | none => try simp only []; exact mkMd_denot E .REMU a _
        | some k =>
          try simp only []
          obtain ⟨hk0, hk64, hm⟩ := pow2_log_sound m k hp
          rw [mkAluK_denot segs E M kn .AND a (.ELit (zpow 2 k - 1)) Hkn]
          apply word_eq_of_bv_unsigned
          show bv_unsigned (alu64 .AND (edenot E a) (Z_to_bv 64 (zpow 2 k - 1)))
              = bv_unsigned (mul_div .REMU (edenot E a) (Z_to_bv 64 m))
          have hpos : 0 < bv_unsigned (Z_to_bv 64 m) := by
            rw [KEY k m hk0 hk64 hm]; exact (zpow2_bounds hk0 hk64).1
          rw [HREMU k hk0 hk64, u_remu64 _ _ hpos, KEY k m hk0 hk64 hm]
      | EVar n => try simp only []; exact mkMd_denot E .REMU a _
      | EAlu o x y => try simp only []; exact mkMd_denot E .REMU a _
      | EAluw o x y => try simp only []; exact mkMd_denot E .REMU a _
      | EMd o x y => try simp only []; exact mkMd_denot E .REMU a _
      | EMdw o x y => try simp only []; exact mkMd_denot E .REMU a _
      | EExt sx lo n e => try simp only []; exact mkMd_denot E .REMU a _
      | EBlob sx kk i n => try simp only []; exact mkMd_denot E .REMU a _
    | MUL => try simp only []; exact mkMd_denot E .MUL a _
    | MULH => try simp only []; exact mkMd_denot E .MULH a _
    | MULHSU => try simp only []; exact mkMd_denot E .MULHSU a _
    | MULHU => try simp only []; exact mkMd_denot E .MULHU a _
    | DIV => try simp only []; exact mkMd_denot E .DIV a _
    | REM => try simp only []; exact mkMd_denot E .REM a _

/-! ### `swrap32_neg`

    `bv_swrap 32` is the identity on `[2^64 - 2^31, 2^64)` (the negative
    half of a sign-extended 32-bit value).  Proved from `u_swrap32` +
    `sx32_eq_of_ge`; the congruence step rewrites `v` as
    `(v - (2^64 - 2^32)) + (2^64 - 2^32)` and uses
    `sub_emod_emod`/`add_mul_emod_self_right` (NOT a direct `rw [h]`,
    which would also rewrite the `v` inside `v - X`) — see the pitfall
    about rewrite-inside-subterms.  the `2^64`/`2^31`
    numerals must be named (`by decide`) before `omega`, otherwise it
    treats the powers as opaque atoms. -/

theorem swrap32_neg (v : Int) (Hv : 2 ^ 64 - 2 ^ 31 ≤ v ∧ v < 2 ^ 64) :
    Z_to_bv 64 (bv_swrap 32 v) = Z_to_bv 64 v := by
  have h64 : (2:Int) ^ 64 = 18446744073709551616 := by decide
  have h31 : (2:Int) ^ 31 = 2147483648 := by decide
  rw [h64, h31] at Hv
  apply word_eq_of_bv_unsigned
  rw [u_swrap32, u_lit64]
  have h1 : v % 4294967296 = v - 18446744069414584320 := by
    have h3 : (v - 18446744069414584320) % 4294967296 = v % 4294967296 := by
      rw [← Int.sub_emod_emod (m := v) (n := 18446744069414584320) (k := 4294967296),
        show (18446744069414584320 : Int) % 4294967296 = 0 from by decide]
      simp
    rw [← h3, Int.emod_eq_of_lt (a := v - 18446744069414584320) (b := 4294967296) (by omega) (by omega)]
  rw [h1, sx32_eq_of_ge (by omega)]
  rw [show (v - 18446744069414584320) + 18446744069414584320 = v from by omega]
  rw [two64_eq]
  exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

/-! ### The 32-bit ALU denotations

    `mkAluwK0_denot` / `mkAluwK_denot`, with the two prerequisites this tree
    owed: `sx32_stable_sound` (a symbolic range whose 64-bit interval cannot
    cross the 32-bit wrap is a fixed point of `bv_swrap 32`) and
    `zband32_sound` (an INTEGER linear form inside `(-2^31, 2^31)`, which is
    where a symbolic base cancels on both sides, is one too).  Both are
    stated in the same "the denotation is a fixed point of `bv_swrap 32`"
    form so the two arms of `mkAluwK0` are one `rw`.

    GLUE. -/

theorem swrap32_mod64 (t : Int) : bv_swrap 32 t = bv_swrap 32 (t % 2 ^ 64) := by
  have h64 : (2 : Int) ^ 64 = (2 : Int) ^ 32 * (2 : Int) ^ 32 := by decide
  have h1 : t % 2 ^ 64 + (2 : Int) ^ 32 * (2 : Int) ^ 32 * (t / 2 ^ 64) = t := by
    have h0 := Int.emod_add_mul_ediv t (2 ^ 64)
    rw [h64] at h0
    exact h0
  have ht : t % 2 ^ 64 + (t / 2 ^ 64 * (2 : Int) ^ 32) * (2 : Int) ^ 32 = t := by
    calc t % 2 ^ 64 + (t / 2 ^ 64 * (2 : Int) ^ 32) * (2 : Int) ^ 32
        = t % 2 ^ 64 + (2 : Int) ^ 32 * (2 : Int) ^ 32 * (t / 2 ^ 64) := by ac_rfl
      _ = t := h1
  conv => lhs; rw [← ht]
  exact swrap32_shift _ _

theorem swrap32_small_signed (t : Int) (Ht : -(2 ^ 31) ≤ t ∧ t < 2 ^ 31) :
    bv_swrap 32 t = t := by
  unfold bv_swrap
  rw [show ((2 ^ (32 - 1) : Nat) : Int) = ((2 ^ 31 : Nat) : Int) from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem sx32_stable_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (d : expr) (lo hi : Int)
    (Hkn : know_ok segs E M kn) (Hr : erange kn d = some (lo, hi))
    (Hs : sx32_stable lo hi = true) :
    edenot E d = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (edenot E d))) := by
  obtain ⟨Hb1, Hb2⟩ := erange_sound segs E M kn d lo hi Hkn Hr
  obtain ⟨Hu0, Hu1⟩ := u64_range (edenot E d)
  simp only [bv_unsigned] at *
  have h31 : zpow 2 31 = (2147483648 : Int) := by unfold zpow; decide
  have h64 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  unfold sx32_stable at Hs
  simp only [Bool.or_eq_true, decide_eq_true_eq] at Hs
  rcases Hs with h | h
  · rw [h31] at h
    rw [show bv_swrap 32 (bv_unsigned (edenot E d)) = bv_unsigned (edenot E d)
        from swrap32_small _ ⟨Hu0, Int.lt_of_le_of_lt Hb2 h⟩]
    exact (Z_to_bv_unsigned _).symm
  · rw [h31, two64_eq, h64] at h
    conv => lhs; rw [← Z_to_bv_unsigned (edenot E d)]
    exact (swrap32_neg _ ⟨Int.le_trans h Hb1, Hu1⟩).symm

theorem zband32_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (d : expr) (Hkn : know_ok segs E M kn)
    (Hz : zband32 kn d = true) :
    edenot E d = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (edenot E d))) := by
  unfold zband32 at Hz
  try simp only [] at Hz
  cases hl : lin_range (erange kn) (lin_of d).1 (lin_of d).2 with
  | none =>
    rw [hl] at Hz
    exact absurd Hz (by simp)
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [hl] at Hz
    try simp only [] at Hz
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hz
    obtain ⟨Hz1, Hz2⟩ := Hz
    obtain ⟨HL1, HL2⟩ := lin_range_sound E (erange kn)
      (fun a lo hi Ha => erange_sound segs E M kn a lo hi Hkn Ha)
      (lin_of d).1 (lin_of d).2 lo hi hl
    obtain ⟨q, Hq⟩ := lin_of_sound E d
    have h64 : (2 : Int) ^ 64 = (2 : Int) ^ 32 * (2 : Int) ^ 32 := by decide
    have h31 : zpow 2 31 = (2147483648 : Int) := by unfold zpow; decide
    rw [h31] at Hz1 Hz2
    have hu1 : bv_unsigned (edenot E d) = lden E (lin_of d) + (-q) * 2 ^ 64 := by
      rw [Hq, Int.neg_mul, Int.add_neg_cancel_right]
      rfl
    have hu2 : bv_unsigned (edenot E d)
        = lden E (lin_of d) + ((-q) * (2 : Int) ^ 32) * (2 : Int) ^ 32 := by
      rw [hu1, h64, ← Int.mul_assoc]
    have hL1 : -(2 ^ 31) ≤ lden E (lin_of d) := by
      show -(2 ^ 31) ≤ (lin_of d).1 + tden E (lin_of d).2
      omega
    have hL2 : lden E (lin_of d) < 2 ^ 31 := by
      show (lin_of d).1 + tden E (lin_of d).2 < 2 ^ 31
      omega
    have hswL : bv_swrap 32 (bv_unsigned (edenot E d)) = lden E (lin_of d) := by
      rw [hu2, swrap32_shift]
      exact swrap32_small_signed _ ⟨hL1, hL2⟩
    have hZu : Z_to_bv 64 (bv_unsigned (edenot E d)) = Z_to_bv 64 (lden E (lin_of d)) := by
      have h1 : bv_unsigned (edenot E d) % 2 ^ 64 = lden E (lin_of d) % 2 ^ 64 := by
        rw [hu1]
        exact Int.add_mul_emod_self_right _ _ _
      rw [← Z_to_bv64_mod (bv_unsigned (edenot E d)), ← Z_to_bv64_mod (lden E (lin_of d)), h1]
    rw [hswL, ← Z_to_bv_unsigned (edenot E d)]
    exact hZu

theorem mkAluwK0_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (op : AluOp) (a b : expr) (Hkn : know_ok segs E base kn) :
    edenot E (mkAluwK0 kn op a b) =
      sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
  have Hgen : ∀ (f : Int → Int → Int),
      (∀ x y : word, sext 64 (alu32 op (low32 x) (low32 y))
        = Z_to_bv 64 (bv_swrap 32 (f (bv_unsigned x) (bv_unsigned y)))) →
      (∀ x y : word, bv_unsigned (alu64 op x y)
        = (f (bv_unsigned x) (bv_unsigned y)) % 2 ^ 64) →
      edenot E (let d := mkAlu op a b
                match is_lit d with
                | some v => .ELit (zsx32 v)
                | none =>
                    match erange kn d with
                    | some (lo, hi) =>
                        if sx32_stable lo hi then d
                        else if zband32 kn d then d else mkAluw op a b
                    | none => if zband32 kn d then d else mkAluw op a b) =
        sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
    intro f Hw Hu
    have Hd : edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b) :=
      mkAlu_denot E op a b
    have Hcongr : bv_swrap 32 (f (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)))
        = bv_swrap 32 (bv_unsigned (edenot E (mkAlu op a b))) := by
      rw [Hd, Hu (edenot E a) (edenot E b), swrap32_mod64]
    have CloseFix : edenot E (mkAlu op a b)
        = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (edenot E (mkAlu op a b)))) →
        edenot E (mkAlu op a b) =
          sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
      intro Hfix
      rw [Hw (edenot E a) (edenot E b), Hcongr]
      exact Hfix
    show edenot E (match is_lit (mkAlu op a b) with
          | some v => .ELit (zsx32 v)
          | none => match erange kn (mkAlu op a b) with
                    | some (lo, hi) => if sx32_stable lo hi then mkAlu op a b
                        else if zband32 kn (mkAlu op a b) then mkAlu op a b else mkAluw op a b
                    | none => if zband32 kn (mkAlu op a b) then mkAlu op a b else mkAluw op a b) =
      sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
    cases hl : is_lit (mkAlu op a b) with
    | some v =>
      try simp only []
      have HV : bv_swrap 32 v
          = bv_swrap 32 (f (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b))) := by
        have h1 : v % 2 ^ 64
            = f (bv_unsigned (edenot E a)) (bv_unsigned (edenot E b)) % 2 ^ 64 := by
          have h2 : bv_unsigned (edenot E (.ELit v))
              = bv_unsigned (alu64 op (edenot E a) (edenot E b)) := by
            rw [← is_lit_some hl]
            exact congrArg bv_unsigned Hd
          have hA : v % 2 ^ 64 = bv_unsigned (edenot E (.ELit v)) := by
            show v % 2 ^ 64 = bv_unsigned (Z_to_bv 64 v)
            exact (u_lit64a v).symm
          rw [hA, h2, Hu (edenot E a) (edenot E b)]
        rw [swrap32_mod64 v, h1, ← swrap32_mod64 (f _ _)]
      rw [Hw (edenot E a) (edenot E b)]
      show Z_to_bv 64 (zsx32 v) = Z_to_bv 64 (bv_swrap 32 (f _ _))
      rw [show zsx32 v = bv_swrap 32 v % 2 ^ 64 from rfl, Z_to_bv64_mod, HV]
    | none =>
      try simp only []
      cases hr : erange kn (mkAlu op a b) with
      | none =>
        try simp only []
        by_cases hzb : zband32 kn (mkAlu op a b) = true
        · rw [ite_eq_left hzb]
          exact CloseFix (zband32_sound segs E base kn _ Hkn hzb)
        · rw [ite_eq_right hzb]
          exact mkAluw_denot E op a b
      | some p =>
        obtain ⟨lo, hi⟩ := p
        try simp only []
        by_cases hsx : sx32_stable lo hi = true
        · rw [ite_eq_left hsx]
          exact CloseFix (sx32_stable_sound segs E base kn _ lo hi Hkn hr hsx)
        · rw [ite_eq_right hsx]
          by_cases hzb : zband32 kn (mkAlu op a b) = true
          · rw [ite_eq_left hzb]
            exact CloseFix (zband32_sound segs E base kn _ Hkn hzb)
          · rw [ite_eq_right hzb]
            exact mkAluw_denot E op a b
  cases op with
  | ADD =>
    unfold mkAluwK0
    try simp only []
    exact Hgen (fun x y => x + y) (by intro x y; rw [w_addw]; rfl)
      (fun x y => u_add64 x y)
  | SUB =>
    unfold mkAluwK0
    try simp only []
    exact Hgen (fun x y => x - y) (by intro x y; rw [w_subw]; rfl)
      (fun x y => u_sub64 x y)
  | SLL => unfold mkAluwK0; exact mkAluw_denot E .SLL a b
  | SLT => unfold mkAluwK0; exact mkAluw_denot E .SLT a b
  | SLTU => unfold mkAluwK0; exact mkAluw_denot E .SLTU a b
  | XOR => unfold mkAluwK0; exact mkAluw_denot E .XOR a b
  | SRL => unfold mkAluwK0; exact mkAluw_denot E .SRL a b
  | SRA => unfold mkAluwK0; exact mkAluw_denot E .SRA a b
  | OR => unfold mkAluwK0; exact mkAluw_denot E .OR a b
  | AND => unfold mkAluwK0; exact mkAluw_denot E .AND a b

theorem mkAluwK_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (op : AluOp) (a b : expr) (Hkn : know_ok segs E base kn) :
    edenot E (mkAluwK kn op a b) =
      sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b))) := by
  unfold mkAluwK
  rw [foldK_denot segs E base kn _ Hkn]
  exact mkAluwK0_denot segs E base kn op a b Hkn

theorem extK0_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (v : expr) (Hkn : know_ok segs E base kn) :
    edenot E (extK0 kn v) = edenot E v := by
  unfold extK0
  cases v with
  | EVar n => rfl
  | ELit z => rfl
  | EAlu op a b => rfl
  | EAluw op a b => rfl
  | EMd op a b => rfl
  | EMdw op a b => rfl
  | EBlob sx k i n => rfl
  | EExt sx lo n e =>
    cases lo with
    | zero =>
      try simp only []
      by_cases hn : n ≤ 7
      · rw [ite_eq_left hn]
        cases hr : erange kn e with
        | none => rfl
        | some p =>
          obtain ⟨lo', hi'⟩ := p
          try simp only []
          by_cases hhi : hi' < (if sx then zpow 2 (8 * (n : Int)) / 2
                                else zpow 2 (8 * (n : Int)))
          · rw [ite_eq_left hhi]
            symm
            apply word_eq_of_bv_unsigned
            obtain ⟨Hb1, Hb2⟩ := erange_sound segs E base kn e lo' hi' Hkn hr
            cases sx with
            | false =>
              try simp only [] at hhi
              rw [zpow_two_8n] at hhi
              exact u_ext_zx0_small n (edenot E e) (Int.lt_of_le_of_lt Hb2 hhi)
            | true =>
              try simp only [] at hhi
              rw [zpow_two_8n] at hhi
              exact u_ext_sx0_small n (edenot E e) (Int.lt_of_le_of_lt Hb2 hhi)
          · rw [ite_eq_right hhi]
      · rw [ite_eq_right hn]
    | succ k => rfl

theorem extK_denot (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (v : expr) (Hkn : know_ok segs E base kn) :
    edenot E (extK kn v) = edenot E v := by
  unfold extK
  rw [foldK_denot segs E base kn _ Hkn]
  exact extK0_denot segs E base kn v Hkn

theorem beq_eq_ltu_sub_one (x y : word) :
    (x == y) = bv_ltu (x - y) (Z_to_bv 64 1) := by
  by_cases h : x = y
  · subst h
    rw [BitVec.sub_self, show (x == x) = true from beq_iff_eq.mpr rfl]
    exact (show bv_ltu (0#64) (Z_to_bv 64 1) = true from by decide).symm
  · have hne : (x == y) = false := beq_eq_false_iff_ne.mpr h
    have hsub : x - y ≠ 0 := by
      intro h0
      rw [BitVec.sub_eq_iff_eq_add] at h0
      exact h (by simpa using h0)
    have h2 : (x - y).toNat ≠ 0 := by
      intro hz
      exact hsub (BitVec.toNat_eq.mpr hz)
    have h1 : (Z_to_bv 64 1 : word).toNat = 1 := by decide
    have hlt : bv_ltu (x - y) (Z_to_bv 64 1) = false := by
      unfold bv_ltu
      rw [h1, decide_eq_false_iff_not]
      omega
    rw [hne, hlt]

theorem probe_one_zero (bl : Bool) :
    (bv_unsigned (if bl then Z_to_bv 64 1 else Z_to_bv 64 0) == 0) = !bl := by
  cases bl with
  | true => decide
  | false => decide

theorem enum_branch_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (c : BranchCond) (a b : expr) (t : Bool)
    (Hkn : know_ok segs E M kn) (H : enum_branch kn c a b = some t) :
    branch_taken c (edenot E a) (edenot E b) = t := by
  unfold enum_branch at H
  try simp only [] at H
  generalize hp : cond_probe c a b = p at H
  obtain ⟨e, pos⟩ := p
  try simp only [] at H
  cases hc : concretize kn e with
  | none => rw [hc] at H; exact absurd H (by simp)
  | some v =>
    rw [hc] at H
    try simp only [] at H
    injection H with Ht
    have Hv := concretize_sound segs E M kn e v Hkn hc
    have Huv : bv_unsigned (edenot E e) = v % two64 := by rw [Hv]; exact u_lit64 v
    cases c with
    | EQ =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_ltu (edenot E a - edenot E b) (Z_to_bv 64 1)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show bv_eqb (edenot E a) (edenot E b) = !((v % two64) == 0)
      rw [show bv_eqb (edenot E a) (edenot E b)
          = bv_ltu (edenot E a - edenot E b) (Z_to_bv 64 1) from beq_eq_ltu_sub_one _ _,
        hz, Bool.not_not]
    | NE =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_ltu (edenot E a - edenot E b) (Z_to_bv 64 1)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show (!(bv_eqb (edenot E a) (edenot E b))) = ((v % two64) == 0)
      rw [show bv_eqb (edenot E a) (edenot E b)
          = bv_ltu (edenot E a - edenot E b) (Z_to_bv 64 1) from beq_eq_ltu_sub_one _ _, hz]
    | LT =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_lts (edenot E a) (edenot E b)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show bv_lts (edenot E a) (edenot E b) = !((v % two64) == 0)
      rw [hz, Bool.not_not]
    | GE =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_lts (edenot E a) (edenot E b)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show (!(bv_lts (edenot E a) (edenot E b))) = ((v % two64) == 0)
      rw [hz]
    | LTU =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_ltu (edenot E a) (edenot E b)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show bv_ltu (edenot E a) (edenot E b) = !((v % two64) == 0)
      rw [hz, Bool.not_not]
    | GEU =>
      injection hp with he hpos
      subst he; subst hpos
      have hz : (v % two64 == 0) = !(bv_ltu (edenot E a) (edenot E b)) := by
        rw [← Huv]; exact probe_one_zero _
      rw [← Ht]
      show (!(bv_ltu (edenot E a) (edenot E b))) = ((v % two64) == 0)
      rw [hz]

theorem conc_expr_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (Hkn : know_ok segs E M kn) :
    edenot E (conc_expr kn e) = edenot E e := by
  have Hg : ∀ e' : expr,
      edenot E (match concretize kn e' with | some v => .ELit v | none => e')
        = edenot E e' := by
    intro e'
    cases hc : concretize kn e' with
    | none => rfl
    | some v =>
      try simp only []
      exact (concretize_sound segs E M kn e' v Hkn hc).symm
  unfold conc_expr
  cases e with
  | ELit z => rfl
  | EVar n => exact Hg _
  | EAlu op a b => exact Hg _
  | EAluw op a b => exact Hg _
  | EMd op a b => exact Hg _
  | EMdw op a b => exact Hg _
  | EExt sx lo n a => exact Hg _
  | EBlob sx k i n => exact Hg _

theorem flat_sc_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (kn : List kentry) (a : saddr) (n : Nat) (rest : List sidecond)
    (Hkn : know_ok segs E base kn) (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8)
    (H : scs_denot segs base E (flat_sc kn a n ++ rest)) :
    flat E a (n : Int) ∧ scs_denot segs base E rest := by
  unfold flat_sc at H
  cases hb : base_range kn a.a_base with
  | none =>
    rw [hb] at H
    try simp only [] at H
    simp only [List.singleton_append] at H
    rw [scs_denot_cons] at H
    obtain ⟨Hf, Hr⟩ := H
    simp only [sc_denot] at Hf
    rw [elenZ_elen E n Hn8] at Hf
    exact ⟨Hf, Hr⟩
  | some p =>
    obtain ⟨lo, hi⟩ := p
    rw [hb] at H
    try simp only [] at H
    by_cases hc : (0 ≤ lo + a.a_off && hi + a.a_off + (n : Int) ≤ 2 ^ 64) = true
    · rw [ite_eq_left hc] at H
      simp only [List.nil_append] at H
      obtain ⟨A, B⟩ := base_range_sound segs E base kn a.a_base lo hi Hkn hb
      obtain ⟨hc1, hc2⟩ := (Bool.and_eq_true ..).mp hc
      rw [decide_eq_true_eq] at hc1 hc2
      refine ⟨?_, H⟩
      unfold flat estart
      refine ⟨by omega, by omega, by omega, by omega⟩
    · rw [ite_eq_right hc] at H
      try simp only [] at H
      simp only [List.singleton_append] at H
      rw [scs_denot_cons] at H
      obtain ⟨Hf, Hr⟩ := H
      simp only [sc_denot] at Hf
      rw [elenZ_elen E n Hn8] at Hf
      exact ⟨Hf, Hr⟩

theorem bv_unsigned_lit0 (E : env) : bv_unsigned (edenot E (.ELit 0)) = (0 : Int) := by
  show bv_unsigned (Z_to_bv 64 0) = (0 : Int)
  rw [u_lit64a]
  decide

theorem adenot_SA_lit0 (E : env) (v : Int) : adenot E (SA (.ELit 0) v) = Z_to_bv 64 v := by
  show v_addi (edenot E (.ELit 0)) v = Z_to_bv 64 v
  show Z_to_bv 64 (bv_unsigned (edenot E (.ELit 0)) + v) = Z_to_bv 64 v
  rw [bv_unsigned_lit0 E, Int.zero_add]

theorem to_saddrK_denot (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (imm : Int) (Hkn : know_ok segs E M kn) :
    adenot E (to_saddrK kn e imm) = v_addi (edenot E e) imm := by
  have CONC : adenot E (match concretize kn (mkAlu .ADD e (.ELit imm)) with
                        | some v => SA (.ELit 0) v
                        | none => to_saddr e imm) = v_addi (edenot E e) imm := by
    cases hc : concretize kn (mkAlu .ADD e (.ELit imm)) with
    | none => try simp only []; exact to_saddr_denot E e imm
    | some v =>
      try simp only []
      have Hv := concretize_sound segs E M kn (mkAlu .ADD e (.ELit imm)) v Hkn hc
      rw [adenot_SA_lit0, ← Hv, mkAlu_denot]
      show edenot E e + edenot E (.ELit imm) = v_addi (edenot E e) imm
      show edenot E e + edenot E (.ELit imm)
        = Z_to_bv 64 (bv_unsigned (edenot E e) + imm)
      apply word_eq_of_bv_unsigned
      rw [u_add64,
        show bv_unsigned (edenot E (.ELit imm)) = imm % 2 ^ 64 from by
          show bv_unsigned (Z_to_bv 64 imm) = imm % 2 ^ 64
          exact u_lit64a imm, u_lit64a]
      have h2 := Int.add_emod (bv_unsigned (edenot E e)) (imm % 2 ^ 64) (2 ^ 64)
      rw [Int.emod_emod] at h2
      exact h2.trans (Int.add_emod _ _ _).symm
  unfold to_saddrK
  cases hs : split_lit e with
  | mk b k =>
    try simp only []
    cases b with
    | ELit z => try simp only []; exact to_saddr_denot E e imm
    | EVar n => exact CONC
    | EAlu op a b => exact CONC
    | EAluw op a b => exact CONC
    | EMd op a b => exact CONC
    | EMdw op a b => exact CONC
    | EExt sx lo n a => exact CONC
    | EBlob sx k2 i n => exact CONC

/-! ### `sym_read_sound`

    The shared read resolution: under its side conditions the `n` bytes at
    `a` are readable in the block's current memory (`mem_denot E base
    (s_log ss)`) and denote `v`.  This is the lemma every load path of
    `sym_step_sound` consumes.
 The
    fallback's value is `match scr.sc_reads with | [] => EVar i | e :: _ =>
    e`, so it is factored through one `FB` helper (stated at an explicit
    `rv`/`reads'` pair) and instantiated twice — the executor's `let`
    cannot be `cases`-ed in place without losing the equation.
-/

theorem sym_read_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (ss : sym_state) (scr : scripts) (a : saddr) (n : Nat) (sx' : Bool)
    (v : expr) (scs : List sidecond) (scr' : scripts) (nx' : Nat)
    (Hs : sym_read segs ss (facts_of ss.s_know) scr a n sx' = some (v, scs, scr', nx'))
    (Hsc : scs_denot segs base E scs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) :
    flat E a (n : Int) ∧
      ∃ bs, rdn segs (mem_denot E base ss.s_log) (adenot E a) n = some bs ∧
        bs.length = n ∧
        Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  have HL := log_lookup_sound segs E (facts_of ss.s_know) ss.s_log base a.a_base a.a_off n sx'
    scr.sc_hints [] Hfk Hlf Hn1 Hn8
  unfold sym_read at Hs
  cases hl : log_lookup (facts_of ss.s_know) ss.s_log a.a_base a.a_off n sx' scr.sc_hints [] with
  | LStuck => rw [hl] at Hs; exact absurd Hs (by simp)
  | LHit v0 lscs lh =>
    rw [hl] at Hs
    try simp only [] at Hs
    have Hsinj := Option.some.inj Hs
    simp only [Prod.mk.injEq] at Hsinj
    obtain ⟨h1, h2, h3, h4⟩ := Hsinj
    rw [← h2] at Hsc
    obtain ⟨Hfl, Hlscs⟩ := flat_sc_sound segs E base (facts_of ss.s_know) a n lscs Hfk Hn1 Hn8 Hsc
    rw [hl] at HL
    simp only [log_hit_ok] at HL
    obtain ⟨bs, Hrd, Hlen, Hval⟩ := HL Hlscs Hfl
    refine ⟨Hfl, bs, Hrd, Hlen, ?_⟩
    rw [← h1, extK_denot segs E base (facts_of ss.s_know) v0 Hfk]
    exact Hval
  | LMiss lscs lh =>
    rw [hl] at Hs
    try simp only [] at Hs
    rw [hl] at HL
    simp only [log_hit_ok] at HL
    have HK := know_lookupA_sound (facts_of ss.s_know) segs ss.s_know E base base
      a.a_base a.a_off n sx' lh lscs Hfk Hkn Hn1 Hn8
    have HKacc := know_lookupA_acc (facts_of ss.s_know) segs ss.s_know
      a.a_base a.a_off n sx' lh lscs
    cases hk : know_lookupA (facts_of ss.s_know) segs ss.s_know a.a_base a.a_off n sx' lh lscs with
    | LStuck => rw [hk] at Hs; exact absurd Hs (by simp)
    | LHit v0 kscs kh =>
      rw [hk] at HK HKacc
      simp only [hit_ok] at HK
      try simp only [] at HKacc
      obtain ⟨pre, hpre⟩ := HKacc
      rw [hk] at Hs
      try simp only [] at Hs
      have Hsinj := Option.some.inj Hs
      simp only [Prod.mk.injEq] at Hsinj
      obtain ⟨h1, h2, h3, h4⟩ := Hsinj
      rw [← h2] at Hsc
      obtain ⟨Hfl, Hkscs⟩ := flat_sc_sound segs E base (facts_of ss.s_know) a n kscs Hfk Hn1 Hn8 Hsc
      have Hlscs : scs_denot segs base E lscs := by
        rw [hpre] at Hkscs
        exact ((scs_denot_app segs base E pre lscs).mp Hkscs).2
      obtain ⟨bs, Hrd, Hlen, Hval⟩ := HK Hkscs Hfl
      refine ⟨Hfl, bs, ?_, Hlen, ?_⟩
      · rw [HL Hlscs Hfl]
        exact Hrd
      · rw [← h1, extK_denot segs E base (facts_of ss.s_know) v0 Hfk]
        exact Hval
    | LMiss kscs kh =>
      rw [hk] at HK HKacc
      simp only [hit_ok] at HK
      try simp only [] at HKacc
      obtain ⟨pre, hpre⟩ := HKacc
      rw [hk] at Hs
      try simp only [] at Hs
      have FB : ∀ (rv : expr) (reads' : List expr),
          (match scr.sc_reads with | [] => expr.EVar ss.s_next | e :: _ => e) = rv →
          (match scr.sc_reads with | [] => [] | _ :: t => t) = reads' →
          some (rv, flat_sc (facts_of ss.s_know) a n ++ sidecond.SCReadBase a n sx' rv :: kscs,
              SCR scr.sc_dirs reads' kh, ss.s_next + 1)
            = some (v, scs, scr', nx') →
          flat E a (n : Int) ∧
            ∃ bs, rdn segs (mem_denot E base ss.s_log) (adenot E a) n = some bs ∧
              bs.length = n ∧ Z_to_bv 64 (extz sx' n (bytes_le_to_Z bs)) = edenot E v := by
        intro rv reads' hrv hreads Hs'
        have Hsinj := Option.some.inj Hs'
        simp only [Prod.mk.injEq] at Hsinj
        obtain ⟨h1, h2, _, _⟩ := Hsinj
        rw [← h2] at Hsc
        obtain ⟨Hfl, Hkscs⟩ := flat_sc_sound segs E base (facts_of ss.s_know) a n
          (sidecond.SCReadBase a n sx' rv :: kscs) Hfk Hn1 Hn8 Hsc
        rw [scs_denot_cons] at Hkscs
        obtain ⟨Hrb, Hkscs⟩ := Hkscs
        simp only [sc_denot] at Hrb
        obtain ⟨bs, Hrd, Hval⟩ := Hrb
        have Hlscs : scs_denot segs base E lscs := by
          rw [hpre] at Hkscs
          exact ((scs_denot_app segs base E pre lscs).mp Hkscs).2
        refine ⟨Hfl, bs, ?_, rdn_length segs base n (adenot E a) bs Hrd, ?_⟩
        · rw [HL Hlscs Hfl]
          exact Hrd
        · rw [← h1]
          exact Hval
      cases hr : scr.sc_reads with
      | nil =>
        rw [hr] at Hs
        try simp only [] at Hs
        exact FB (.EVar ss.s_next) [] (by rw [hr]) (by rw [hr]) Hs
      | cons e t =>
        rw [hr] at Hs
        try simp only [] at Hs
        exact FB e t (by rw [hr]) (by rw [hr]) Hs

/-! ### Writability / reservation bookkeeping

    `storeok_sc_sound`: a store whose side conditions are discharged really is
    `store_ok` at the base address, either because a `KWr` window covers it
    (`wr_covered_sound`, the induction over the knowledge list, each covering
    `KWr` resolved by `xlo_sound`/`xinside_sound` through `flat_u`) or
    because the `SCStoreOk` obligation was emitted.

    `resv_inval_sound`: the reservation bookkeeping of a store/AMO at `a` is
    sound.  The syntactic `saddr_eqb`/`expr_eqb` tests are turned into the
    semantic ones (`saddr_eqb_eq`, `expr_eqb_eq`); the "same base, offsets
    different mod `2^64`" case is the one place where the `Int`-level
    `(ra.off - a.off) % two64 ≠ 0` has to be recovered from the `Nat`
    comparison `resv_inval_w` performs on `adenot` (via `u_lit64a` and
    `Int.sub_emod`).
-/

theorem wr_covered_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (allkn kn : List kentry) (a : saddr) (n : Nat)
    (Hall : know_ok segs E base allkn) (Hkn : know_ok segs E base kn)
    (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) (H : wr_covered allkn kn a n = true) :
    store_ok segs base (adenot E a) n = true := by
  induction kn with
  | nil => simp only [wr_covered] at H; exact absurd H (by decide)
  | cons K rest IH =>
    have HK : kentry_ok segs E base K := Hkn K (List.mem_cons_self ..)
    have Hrest : know_ok segs E base rest :=
      fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    cases K with
    | KWr ka len =>
      obtain ⟨kb, kk⟩ := ka
      simp only [wr_covered] at H
      obtain ⟨Hflat, Hwr⟩ := HK
      have hA0 : adenot E a = Z_to_bv 64 (estart E a) := rfl
      have hlen : elenZ E (.ELit (n : Int)) = (n : Int) := by
        show elenZ E (elen n) = (n : Int)
        exact elenZ_elen E n Hn8
      have HSTORE : ∀ (d : Int), 0 ≤ d → d + (n : Int) ≤ elenZ E len →
          estart E (SA kb kk) + d = estart E a →
          store_ok segs base (adenot E a) n = true := by
        intro d h0 h1 hidx
        rw [hA0, ← hidx]
        exact Hwr d n h0 h1
      have HXIN : xinside allkn a.a_base a.a_off (.ELit (n : Int)) kb kk len = true →
          store_ok segs base (adenot E a) n = true := by
        intro hxi
        obtain ⟨J1, J2⟩ := xinside_sound segs E base allkn a.a_base a.a_off (.ELit (n : Int))
          kb kk len Hall hxi
        have I1 : estart E (SA kb kk) ≤ estart E a := J1
        have I2 : estart E a + (n : Int) ≤ estart E (SA kb kk) + elenZ E len := by
          rw [hlen] at J2
          exact J2
        exact HSTORE (estart E a - estart E (SA kb kk)) (by omega) (by omega) (by omega)
      split at H
      · rename_i hc
        split at H
        · rename_i lv hxl
          obtain ⟨hc1, hc2⟩ := (Bool.and_eq_true ..).mp hc
          rw [decide_eq_true_eq] at hc2
          have hb : a.a_base = kb := expr_eqb_eq _ _ hc1
          have hl : lv ≤ elenZ E len := xlo_sound segs E base allkn len lv Hall hxl
          by_cases hdec : a.a_off + (n : Int) ≤ kk + lv
          · exact HSTORE (a.a_off - kk) (by omega) (by omega) (by
              show bv_unsigned (edenot E kb) + kk + (a.a_off - kk)
                = bv_unsigned (edenot E a.a_base) + a.a_off
              rw [hb]; omega)
          · rw [ite_eq_right (show ¬((decide (a.a_off + (n : Int) ≤ kk + lv)) = true) from by
              intro h2; exact hdec (of_decide_eq_true h2))] at H
            split at H
            · rename_i hxi
              exact HXIN hxi
            · exact IH Hrest H
        · split at H
          · rename_i hfalse
            exact absurd hfalse (by decide)
          · split at H
            · rename_i hxi
              exact HXIN hxi
            · exact IH Hrest H
      · split at H
        · rename_i hfalse
          exact absurd hfalse (by decide)
        · split at H
          · rename_i hxi
            exact HXIN hxi
          · exact IH Hrest H
    | KWord sa w v => exact IH Hrest H
    | KZero sa sn => exact IH Hrest H
    | KBlob sa sn sk => exact IH Hrest H
    | KImg lo hi => exact IH Hrest H
    | KAlign e m => exact IH Hrest H
    | KRange e lo hi => exact IH Hrest H
    | KDisj a1 n1 a2 n2 => exact IH Hrest H
    | KFill sa sn c => exact IH Hrest H
    | KUnk sa sn => exact IH Hrest H

theorem storeok_sc_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (fk : List kentry) (a : saddr) (n : Nat)
    (Hfk : know_ok segs E base fk) (Hfl : flat E a (n : Int)) (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8)
    (Hsc : scs_denot segs base E (storeok_sc fk a n)) :
    store_ok segs base (adenot E a) n = true := by
  unfold storeok_sc at Hsc
  by_cases hw : wr_covered fk fk a n = true
  · rw [ite_eq_left hw] at Hsc
    exact wr_covered_sound segs E base fk fk a n Hfk Hfk Hn1 Hn8 hw
  · rw [ite_eq_right hw] at Hsc
    rw [scs_denot_cons] at Hsc
    exact Hsc.1

theorem resv_inval_sound (E : env) (r : Option saddr) (a : saddr) (r' : Option saddr)
    (H : resv_inval r a = some r') :
    resv_inval_w (resv_denot E r) (adenot E a) = resv_denot E r' := by
  unfold resv_inval at H
  cases r with
  | none =>
    rw [Option.some.injEq] at H
    rw [← H]
    rfl
  | some ra =>
    try simp only [] at H
    by_cases heq : saddr_eqb ra a = true
    · rw [ite_eq_left heq] at H
      rw [Option.some.injEq] at H
      rw [← H]
      have hra : ra = a := saddr_eqb_eq heq
      show resv_inval_w (some (adenot E ra)) (adenot E a) = none
      rw [resv_inval_w_some, hra]
      rw [ite_eq_left (by rw [beq_iff_eq])]
    · rw [ite_eq_right heq] at H
      by_cases hkeep : (expr_eqb ra.a_base a.a_base && !((ra.a_off - a.a_off) % two64 == 0)) = true
      · rw [ite_eq_left hkeep] at H
        rw [Option.some.injEq] at H
        rw [← H]
        obtain ⟨hb, hnn⟩ := (Bool.and_eq_true ..).mp hkeep
        have hbase : ra.a_base = a.a_base := expr_eqb_eq _ _ hb
        have hbf : ((ra.a_off - a.a_off) % two64 == 0) = false := by simpa using hnn
        have hne0 : (ra.a_off - a.a_off) % two64 ≠ 0 := beq_eq_false_iff_ne.mp hbf
        show resv_inval_w (some (adenot E ra)) (adenot E a) = some (adenot E ra)
        rw [resv_inval_w_some]
        rw [ite_eq_right]
        intro hcontra
        exfalso
        apply hne0
        have hbw : bv_unsigned (adenot E ra) = bv_unsigned (adenot E a) := by
          show ((adenot E ra).toNat : Int) = ((adenot E a).toNat : Int)
          rw [beq_iff_eq.mp hcontra]
        have h1 : bv_unsigned (adenot E ra) = estart E ra % two64 := u_lit64a _
        have h2 : bv_unsigned (adenot E a) = estart E a % two64 := u_lit64a _
        have h3 : (estart E ra - estart E a) % two64 = 0 := by
          have h4 : estart E ra % two64 = estart E a % two64 := by rw [← h1, ← h2, hbw]
          rw [Int.sub_emod, h4, Int.sub_self]
          exact Int.zero_emod _
        have h5 : estart E ra - estart E a = ra.a_off - a.a_off := by
          show bv_unsigned (edenot E ra.a_base) + ra.a_off
              - (bv_unsigned (edenot E a.a_base) + a.a_off) = ra.a_off - a.a_off
          rw [hbase]; omega
        rw [h5] at h3
        exact h3
      · rw [ite_eq_right hkeep] at H
        exact absurd H (by simp)

/-! ### AMO helpers

    `amo_alignedb_sound` (the alignment test is a real `mod amo_bytes wd`
    statement, through `lin_lowbits_kn_sound`; the per-width instantiation
    is a generic `amo_alignedb_gen` because casing on `wd` inside the
    `lin_lowbits_kn` argument would generalise the `match`), and the three
    `amo_val_*` bridging lemmas (`amo_aluop`'s `SWAP`/`ADD`/`XOR`/`AND`/`OR`
    are exactly the value language's, and the rest do not exist).
-/

theorem amo_alignedb_gen (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (k : Int) (nb : Int)
    (Hkn : know_ok segs E M kn) (Hk : 0 ≤ k ∧ k ≤ 64) (Hnb : nb = zpow 2 k)
    (H : (match lin_lowbits_kn kn e k with | some r => r == 0 | none => false) = true) :
    bv_unsigned (edenot E e) % nb = 0 := by
  cases hl : lin_lowbits_kn kn e k with
  | none => rw [hl] at H; exact absurd H (by simp [amo_aluop])
  | some r =>
    rw [hl] at H
    obtain ⟨Hm, _, _⟩ := lin_lowbits_kn_sound segs E M kn e k r Hkn Hk hl
    rw [beq_iff_eq] at H
    rw [Hnb, ← H]
    exact Hm

theorem amo_alignedb_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (e : expr) (wd : AWidth)
    (Hkn : know_ok segs E M kn) (H : amo_alignedb kn e wd = true) :
    bv_unsigned (edenot E e) % amo_bytes wd = 0 := by
  cases wd with
  | W =>
    exact amo_alignedb_gen segs E M kn e 2 4 Hkn (by decide)
      (by unfold zpow; decide) H
  | D =>
    exact amo_alignedb_gen segs E M kn e 3 8 Hkn (by decide)
      (by unfold zpow; decide) H

theorem amo_val_alu32 (op : AmoOp) (o : AluOp) (a b : BitVec 32)
    (H : amo_aluop op = some (some o)) : amo_val op a b = alu32 o a b := by
  cases op with
  | ADD => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | XOR => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | AND => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | OR => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | SWAP => exact absurd H (by simp [amo_aluop])
  | MIN => exact absurd H (by simp [amo_aluop])
  | MAX => exact absurd H (by simp [amo_aluop])
  | MINU => exact absurd H (by simp [amo_aluop])
  | MAXU => exact absurd H (by simp [amo_aluop])

theorem amo_val_alu64 (op : AmoOp) (o : AluOp) (a b : word)
    (H : amo_aluop op = some (some o)) : amo_val op a b = alu64 o a b := by
  cases op with
  | ADD => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | XOR => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | AND => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | OR => simp only [amo_aluop, Option.some.injEq] at H; subst H; rfl
  | SWAP => exact absurd H (by simp [amo_aluop])
  | MIN => exact absurd H (by simp [amo_aluop])
  | MAX => exact absurd H (by simp [amo_aluop])
  | MINU => exact absurd H (by simp [amo_aluop])
  | MAXU => exact absurd H (by simp [amo_aluop])

theorem amo_val_swap (op : AmoOp) (n : Nat) (a b : BitVec n)
    (H : amo_aluop op = some none) : amo_val op a b = b := by
  cases op with
  | SWAP => rfl
  | ADD => exact absurd H (by simp [amo_aluop])
  | XOR => exact absurd H (by simp [amo_aluop])
  | AND => exact absurd H (by simp [amo_aluop])
  | OR => exact absurd H (by simp [amo_aluop])
  | MIN => exact absurd H (by simp [amo_aluop])
  | MAX => exact absurd H (by simp [amo_aluop])
  | MINU => exact absurd H (by simp [amo_aluop])
  | MAXU => exact absurd H (by simp [amo_aluop])

/-! ### `amo_store_bytes_newval`

    The bytes an AMO writes are the low bytes of `amo_newval`: the `.W`
    case needs the `mkAluwK` (32-bit) denotation plus `low32 ∘ sext 64 = id`,
    the `.D` case the 64-bit one, and the `SWAP` arm (`aop = none`) is the
    `store_bytes_low32` identity. -/

theorem amo_store_bytes_newval (segs : List Segment) (E : env) (M : word → Option byte)
    (fk : List kentry) (op : AmoOp) (aop : Option AluOp) (wd : AWidth) (bs : List byte)
    (vold src : expr) (Hfk : know_ok segs E M fk) (Hop : amo_aluop op = some aop)
    (Hlen : bs.length = AxSymExec3.msize_bytes (amo_sz wd))
    (Hold : edenot E vold = load_result (amo_sz wd) true bs) :
    amo_store_bytes op wd bs (edenot E src) =
      word_to_le_bytes (AxSymExec3.msize_bytes (amo_sz wd))
        (edenot E (amo_newval fk wd aop vold src)) := by
  unfold amo_store_bytes amo_newval
  cases wd with
  | W =>
    simp only [amo_sz, AxSymExec3.msize_bytes]
    cases aop with
    | none =>
      simp only []
      rw [amo_val_swap op 32 _ _ Hop]
      exact SeqExec.store_bytes_low32 (edenot E src)
    | some o =>
      simp only []
      rw [mkAluwK_denot segs E M fk o vold src Hfk, Hold]
      show Z_to_le_bytes 4
            ((amo_val op (bits 0 32 (le_bytes_to_word bs)) (low32 (edenot E src))).toNat : Int) =
        word_to_le_bytes 4 (sext 64 (alu32 o
          (low32 (sext 64 (bits 0 32 (le_bytes_to_word bs)))) (low32 (edenot E src))))
      rw [low32_sext64_32, amo_val_alu32 op o _ _ Hop]
      rw [← SeqExec.store_bytes_low32 (sext 64 (alu32 o (bits 0 32 (le_bytes_to_word bs))
        (low32 (edenot E src))))]
      rw [low32_sext64_32]
  | D =>
    simp only [amo_sz, AxSymExec3.msize_bytes]
    cases aop with
    | none =>
      simp only []
      rw [amo_val_swap op 64 _ _ Hop]
      rfl
    | some o =>
      simp only []
      rw [mkAluK_denot segs E M fk o vold src Hfk, Hold]
      show Z_to_le_bytes 8
            ((amo_val op (bits 0 64 (le_bytes_to_word bs)) (edenot E src)).toNat : Int) =
        word_to_le_bytes 8 (alu64 o (bits 0 64 (le_bytes_to_word bs)) (edenot E src))
      rw [amo_val_alu64 op o _ _ Hop]
      rfl

/-! ### `sym_step_sound_load`

    The `Load` arm of the per-class step soundness: `sym_read` resolves the
    `n` bytes at `to_saddrK fk rs imm`, `sym_read_sound` turns that into a
    real `rdn` of the block memory and the value the register gets, and
    `stepR_load` is the machine step.  The reservation is untouched. -/

theorem sym_step_sound_load (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (sz : MSize) (sx : Bool) (rd rs : reg)
    (imm : BitVec 12) (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts)
    (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.load sz sx rd rs imm, 4))
    (Hs : sym_step segs (Instr.load sz sx rd rs imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  obtain ⟨Hn1, Hn8⟩ := msize_bytes_range sz
  have Hadr : adenot E (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs) (bv_signed imm))
      = v_addi (getr regs rs) (bv_signed imm) := by
    rw [to_saddrK_denot segs E base (facts_of ss.s_know) _ _ Hfk, Hregs rs]
  unfold sym_step at Hs
  try simp only [] at Hs
  split at Hs
  · exact absurd Hs (by simp)
  · rename_i xg v scs0 scr0 nx heq
    injection Hs with h1 h2 h3
    subst h1
    subst h2
    subst h3
    have Hrs := sym_read_sound segs E base ss scr _ _ _ v scs0 scr0 nx heq Hsc Hlf Hkn Hn1 Hn8
    obtain ⟨Hfl, bs, Hrd, Hlen, Hval⟩ := Hrs
    rw [Hadr] at Hrd
    rw [← msize_bytes_R] at Hlen Hval
    have Hv : edenot E v = load_result sz sx bs := by
      rw [load_result_val sz sx bs Hlen, ← Hval]
      rfl
    have Hstep := stepR_load segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
      (resv_denot E ss.s_resv) w sz sx rd rs imm bs Hf He Hd Hrd
    rw [SymExec.v_addi_lit] at Hstep
    refine ⟨_, Hstep, ?_⟩
    unfold st_okR
    refine ⟨if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs),
      rfl, ?_, Hlf, Hkn⟩
    exact regs_ok_upd E ss.s_regs regs rd (load_result sz sx bs) v Hregs Hv

/-! ### `sym_step_sound_store` -/

theorem sym_step_sound_store (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (sz : MSize) (rs1 rs2 : reg)
    (imm : BitVec 12) (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts)
    (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.store sz rs1 rs2 imm, 4))
    (Hs : sym_step segs (Instr.store sz rs1 rs2 imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  obtain ⟨Hn1, Hn8⟩ := msize_bytes_range sz
  have Hadr : adenot E (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) (bv_signed imm))
      = v_addi (getr regs rs1) (bv_signed imm) := by
    rw [to_saddrK_denot segs E base (facts_of ss.s_know) _ _ Hfk, Hregs rs1]
  unfold sym_step at Hs
  try simp only [] at Hs
  split at Hs
  · exact absurd Hs (by simp)
  · rename_i xg r' hri
    injection Hs with h1 h2 h3
    subst h1
    subst h2
    subst h3
    obtain ⟨Hfl, Hsc'⟩ := flat_sc_sound segs E base (facts_of ss.s_know) _ _ _ Hfk Hn1 Hn8 Hsc
    have Hok := storeok_sc_sound segs E base (facts_of ss.s_know) _ _ Hfk Hfl Hn1 Hn8 Hsc'
    have hri' := resv_inval_sound E ss.s_resv
      (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) (bv_signed imm)) r' hri
    have Hok' : store_ok segs (mem_denot E base ss.s_log)
        (v_addi (getr regs rs1) (bv_signed imm)) (AxSymExec3.msize_bytes sz) = true := by
      rw [← Hadr]
      exact store_ok_mono segs _ base (mem_denot E base ss.s_log) _
        (mem_denot_grows E base ss.s_log) Hok
    have Hstep := stepR_store segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
      (resv_denot E ss.s_resv) w sz rs1 rs2 imm Hf He Hd Hok'
    rw [SymExec.v_addi_lit] at Hstep
    refine ⟨_, Hstep, ?_⟩
    unfold st_okR
    refine ⟨regs, ?_, Hregs, ?_, Hkn⟩
    · rw [mem_denot_cons, ← hri', ← Hadr, ← Hregs rs2, ← msize_bytes_R]
    · rw [log_flat_cons]
      exact ⟨Hn8, Hfl, Hlf⟩

/-! ### `sym_step_sound_lr` -/

theorem sym_step_sound_lr (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (wd : AWidth) (aq rl : Bool) (rd rs : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.lr wd aq rl rd rs, 4))
    (Hs : sym_step segs (Instr.lr wd aq rl rd rs) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  obtain ⟨Hn1, Hn8⟩ := msize_bytes_range (amo_sz wd)
  have Hadr : adenot E (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs) 0) = getr regs rs := by
    rw [to_saddrK_denot segs E base (facts_of ss.s_know) _ _ Hfk, Hregs rs, v_addi_0]
  have h1 : eff_sx (amo_msize wd) true = amo_sx wd := by cases wd <;> rfl
  have h2 : SymStepR.msize_bytes (amo_msize wd) = AxSymExec3.msize_bytes (amo_sz wd) := by
    rw [amo_msize_sz]; exact msize_bytes_R (amo_sz wd)
  unfold sym_step at Hs
  try simp only [] at Hs
  split at Hs
  · rename_i hal
    try simp only [] at Hs
    split at Hs
    · exact absurd Hs (by simp)
    · rename_i xg2 v scs0 scr0 nx0 heq
      injection Hs with h4 h5 h6
      subst h4
      subst h5
      subst h6
      have Hrs := sym_read_sound segs E base ss scr _ _ _ v scs0 scr0 nx0 heq Hsc Hlf Hkn Hn1 Hn8
      obtain ⟨Hfl, bs, Hrd, Hlen, Hval⟩ := Hrs
      rw [Hadr] at Hrd
      rw [← amo_nbytes_sz] at Hrd
      have HA := amo_alignedb_sound segs E base (facts_of ss.s_know) (sr_get ss.s_regs rs) wd Hfk hal
      rw [← Hregs rs] at HA
      have Hstep := stepR_lr segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
        (resv_denot E ss.s_resv) w wd aq rl rd rs bs Hf He Hd HA Hrd
      rw [SymExec.v_addi_lit] at Hstep
      have hlen : bs.length = SymStepR.msize_bytes (amo_msize wd) := by
        rw [Hlen]; exact h2.symm
      have Hv : edenot E v = load_result (amo_msize wd) true bs := by
        rw [load_result_val (amo_msize wd) true bs hlen, ← Hval, h1, h2]
      refine ⟨_, Hstep, ?_⟩
      unfold st_okR
      refine ⟨if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs),
        ?_, ?_, Hlf, Hkn⟩
      · simp only [resv_denot, Hadr]
      · exact regs_ok_upd E ss.s_regs regs rd (load_result (amo_msize wd) true bs) v Hregs Hv
  · exact absurd Hs (by simp)

/-! ### `sym_step_sound_sc` -/

theorem sym_step_sound_sc (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (wd : AWidth) (aq rl : Bool) (rd rs1 rs2 : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.sc wd aq rl rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.sc wd aq rl rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  obtain ⟨Hn1, Hn8⟩ := msize_bytes_range (amo_sz wd)
  have Hadr : adenot E (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) 0)
      = getr regs rs1 := by
    rw [to_saddrK_denot segs E base (facts_of ss.s_know) _ _ Hfk, Hregs rs1, v_addi_0]
  unfold sym_step at Hs
  try simp only [] at Hs
  by_cases hal : amo_alignedb (facts_of ss.s_know) (sr_get ss.s_regs rs1) wd = true
  · rw [ite_eq_left hal] at Hs
    try simp only [] at Hs
    split at Hs
    · rename_i xg r hrv
      try simp only [] at Hs
      by_cases heq : saddr_eqb r (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) 0) = true
      · rw [ite_eq_left heq] at Hs
        try simp only [] at Hs
        have hra : r = to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) 0 :=
          saddr_eqb_eq heq
        subst hra
        injection Hs with h4 h5 h6
        subst h4
        subst h5
        subst h6
        obtain ⟨Hfl, Hsc'⟩ := flat_sc_sound segs E base (facts_of ss.s_know) _ _ _ Hfk Hn1 Hn8 Hsc
        have Hok := storeok_sc_sound segs E base (facts_of ss.s_know) _ _ Hfk Hfl Hn1 Hn8 Hsc'
        have Hok' : store_ok segs (mem_denot E base ss.s_log) (getr regs rs1)
            (AxSymExec3.msize_bytes (amo_sz wd)) = true := by
          rw [← Hadr]
          exact store_ok_mono segs _ base (mem_denot E base ss.s_log) _
            (mem_denot_grows E base ss.s_log) Hok
        rw [← amo_nbytes_sz] at Hok'
        have HA := amo_alignedb_sound segs E base (facts_of ss.s_know) (sr_get ss.s_regs rs1) wd Hfk hal
        rw [← Hregs rs1] at HA
        have hrv2 : resv_denot E ss.s_resv = some (getr regs rs1) := by
          rw [hrv]
          simp only [resv_denot, Hadr]
        have Hstep := stepR_sc_ok segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          w wd aq rl rd rs1 rs2 (getr regs rs1) Hf He Hd HA rfl Hok'
        rw [SymExec.v_addi_lit] at Hstep
        rw [hrv2]
        refine ⟨_, Hstep, ?_⟩
        unfold st_okR
        refine ⟨if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0), ?_, ?_, ?_, Hkn⟩
        · simp only [resv_denot, mem_denot_cons, ← Hadr, ← Hregs rs2, ← amo_nbytes_sz]
        · exact regs_ok_upd E ss.s_regs regs rd (Z_to_bv 64 0) (.ELit 0) Hregs rfl
        · rw [log_flat_cons]
          exact ⟨Hn8, Hfl, Hlf⟩
      · rw [ite_eq_right heq] at Hs
        try simp only [] at Hs
        exact absurd Hs (by simp)
    · try simp only [] at Hs
      exact absurd Hs (by simp)
  · rw [ite_eq_right hal] at Hs
    try simp only [] at Hs
    exact absurd Hs (by simp)

/-! ### `sym_step_sound_amo` -/

theorem sym_step_sound_amo (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AmoOp) (wd : AWidth) (aq rl : Bool)
    (rd rs1 rs2 : reg) (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts)
    (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.amo op wd aq rl rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.amo op wd aq rl rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  obtain ⟨Hn1, Hn8⟩ := msize_bytes_range (amo_sz wd)
  have Hadr : adenot E (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) 0)
      = getr regs rs1 := by
    rw [to_saddrK_denot segs E base (facts_of ss.s_know) _ _ Hfk, Hregs rs1, v_addi_0]
  have h1 : eff_sx (amo_msize wd) true = amo_sx wd := by cases wd <;> rfl
  have h2 : SymStepR.msize_bytes (amo_msize wd) = AxSymExec3.msize_bytes (amo_sz wd) := by
    rw [amo_msize_sz]; exact msize_bytes_R (amo_sz wd)
  unfold sym_step at Hs
  try simp only [] at Hs
  split at Hs
  · exact absurd Hs (by simp)
  · rename_i aop hop
    try simp only [] at Hs
    by_cases hal : amo_alignedb (facts_of ss.s_know) (sr_get ss.s_regs rs1) wd = true
    · rw [ite_eq_left hal] at Hs
      try simp only [] at Hs
      split at Hs
      · try simp only [] at Hs
        exact absurd Hs (by simp)
      · rename_i xg r' hri
        try simp only [] at Hs
        split at Hs
        · exact absurd Hs (by simp)
        · rename_i xg2 vold scs0 scr0 nx heq
          injection Hs with h4 h5 h6
          subst h4
          subst h5
          subst h6
          obtain ⟨Hsc0, Hsok⟩ := (scs_denot_app segs base E scs0 _).mp Hsc
          have Hrs := sym_read_sound segs E base ss scr _ _ _ vold scs0 scr0 nx heq
            Hsc0 Hlf Hkn Hn1 Hn8
          obtain ⟨Hfl, bs, Hrd, Hlen, Hval⟩ := Hrs
          have Hok := storeok_sc_sound segs E base (facts_of ss.s_know) _ _ Hfk Hfl Hn1 Hn8 Hsok
          have Hok' : store_ok segs (mem_denot E base ss.s_log) (getr regs rs1)
              (AxSymExec3.msize_bytes (amo_sz wd)) = true := by
            rw [← Hadr]
            exact store_ok_mono segs _ base (mem_denot E base ss.s_log) _
              (mem_denot_grows E base ss.s_log) Hok
          rw [Hadr] at Hrd
          rw [← amo_nbytes_sz] at Hrd Hok'
          have HA := amo_alignedb_sound segs E base (facts_of ss.s_know)
            (sr_get ss.s_regs rs1) wd Hfk hal
          rw [← Hregs rs1] at HA
          have hlen : bs.length = SymStepR.msize_bytes (amo_msize wd) := by
            rw [Hlen]; exact h2.symm
          have Hold : edenot E vold = load_result (amo_msize wd) true bs := by
            rw [load_result_val (amo_msize wd) true bs hlen, ← Hval, h1, h2]
          have hri' := resv_inval_sound E ss.s_resv
            (to_saddrK (facts_of ss.s_know) (sr_get ss.s_regs rs1) 0) r' hri
          have Hstep := stepR_amo segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
            (resv_denot E ss.s_resv) w op wd aq rl rd rs1 rs2 bs Hf He Hd HA Hrd Hok'
          rw [SymExec.v_addi_lit] at Hstep
          refine ⟨_, Hstep, ?_⟩
          unfold st_okR
          refine ⟨if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs),
            ?_, ?_, ?_, Hkn⟩
          · rw [mem_denot_cons, ← hri', ← Hadr, Hregs rs2,
              ← amo_store_bytes_newval segs E base (facts_of ss.s_know) op aop wd bs vold
                (sr_get ss.s_regs rs2) Hfk hop Hlen Hold]
          · exact regs_ok_upd E ss.s_regs regs rd (load_result (amo_msize wd) true bs) vold Hregs Hold
          · rw [log_flat_cons]
            exact ⟨Hn8, Hfl, Hlf⟩
    · rw [ite_eq_right hal] at Hs
      try simp only [] at Hs
      exact absurd Hs (by simp)

/-! ### `sym_step_soundR`

    The general one-step theorem: from the general relation `st_okR` (a live
    reservation is allowed) every instruction class that the executor does
    NOT stop on has a machine step that lands in `st_okR` again.  The five
    memory classes are the lemmas above; the ALU / control classes are the
    `stepR_*_gen` lemmas of `SymStepR` plus the corresponding denotation
    lemma, and the classes the executor stops on (`ecall`/`ebreak`, the FP
    and CSR families, a stuck `jalr`/`branch`) give a contradiction.

    The two helpers below package the `st_okR` half of every
    register-writing and pc-only arm: the state is a structure literal, so
    the machine-state equality holds by projection reduction and the only
    real content is `regs_ok_upd`. -/

theorem st_okR_sset (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd : reg) (e : expr) (v : word) (p : Int)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) (Hv : edenot E e = v) :
    st_okR segs E base rom (sset ss rd e p)
      (mkstR (if bv_eqb rd 0 then regs else regupd regs rd v) (BitVec.ofInt 64 p)
        (mem_denot E base ss.s_log) rom (resv_denot E ss.s_resv)) := by
  unfold st_okR sset
  exact ⟨_, rfl, regs_ok_upd E ss.s_regs regs rd v e Hregs Hv, Hlf, Hkn⟩

theorem st_okR_sjump (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (p : Int)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    st_okR segs E base rom (sjump ss p)
      (mkstR regs (BitVec.ofInt 64 p) (mem_denot E base ss.s_log) rom
        (resv_denot E ss.s_resv)) := by
  unfold st_okR sjump
  exact ⟨regs, rfl, Hregs, Hlf, Hkn⟩

theorem sext_lit_denot (E : env) {n : Nat} (b : BitVec n) (hn : n ≤ 64) :
    edenot E (expr.ELit (bv_signed b)) = sext 64 b := by
  show Z_to_bv 64 b.toInt = sext 64 b
  rw [SymExec.sext64_lit b hn]

theorem zext_lit_denot (E : env) {n : Nat} (b : BitVec n) (hn : n ≤ 64) :
    edenot E (expr.ELit (bv_unsigned b)) = zext 64 b := by
  show Z_to_bv 64 (b.toNat : Int) = zext 64 b
  rw [SymExec.zext64_lit b hn]

theorem sym_step_sound_opimm (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AluOp) (rd rs : reg) (imm : BitVec 12)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm op rd rs imm, 4))
    (Hs : sym_step segs (Instr.opImm op rd rs imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkAluK (facts_of ss.s_know) op (sr_get ss.s_regs rs) (.ELit (bv_signed imm)))
      = alu64 op (getr regs rs) (sext 64 imm) := by
    rw [mkAluK_denot segs E base (facts_of ss.s_know) op _ _ Hfk, ← Hregs rs,
      sext_lit_denot E imm (by decide)]
  have Hstep := stepR_opimm_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs imm Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

/-!  Here
    each class is its own lemma, because Lean's `cases i` has to rebuild the
    whole 30-arm motive at once; one lemma per class keeps the work
    incremental and lets `sym_step_soundR` be a dispatch.  Every arm has the
    same shape: `Hs` is `SOk (sset ss rd e (p+4)) [] scr = SOk ss' scs scr'`
    (or the `sjump` form), so `injection`+`subst` names `ss'`, the denotation
    of `e` is the `stepR_*_gen` register value, and `st_okR_sset` /
    `st_okR_sjump` finish. -/

theorem sym_step_sound_shiftimm (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AluOp) (rd rs : reg) (sh : BitVec 6)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.shiftImm op rd rs sh, 4))
    (Hs : sym_step segs (Instr.shiftImm op rd rs sh) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkAluK (facts_of ss.s_know) op (sr_get ss.s_regs rs)
        (.ELit (bv_unsigned sh))) = alu64 op (getr regs rs) (zext 64 sh) := by
    rw [mkAluK_denot segs E base (facts_of ss.s_know) op _ _ Hfk, ← Hregs rs,
      zext_lit_denot E sh (by decide)]
  have Hstep := stepR_shiftimm_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs sh Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_op (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AluOp) (rd rs1 rs2 : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op op rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.op op rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkAluK (facts_of ss.s_know) op (sr_get ss.s_regs rs1)
        (sr_get ss.s_regs rs2)) = alu64 op (getr regs rs1) (getr regs rs2) := by
    rw [mkAluK_denot segs E base (facts_of ss.s_know) op _ _ Hfk, ← Hregs rs1, ← Hregs rs2]
  have Hstep := stepR_op_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs1 rs2 Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_opimm32 (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd rs : reg) (imm : BitVec 12)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm32 rd rs imm, 4))
    (Hs : sym_step segs (Instr.opImm32 rd rs imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have h2 : low32 (edenot E (.ELit (bv_signed imm))) = sext 32 imm := by
    show low32 (Z_to_bv 64 imm.toInt) = sext 32 imm
    rw [← SymExec.sext32_low32 imm (by decide)]
  have Hv : edenot E (mkAluwK (facts_of ss.s_know) .ADD (sr_get ss.s_regs rs)
        (.ELit (bv_signed imm)))
      = sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm)) := by
    rw [mkAluwK_denot segs E base (facts_of ss.s_know) .ADD _ _ Hfk, ← Hregs rs, h2]
  have Hstep := stepR_opimm32_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w rd rs imm Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_shiftimm32 (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AluOp) (rd rs : reg) (sh : BitVec 5)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.shiftImm32 op rd rs sh, 4))
    (Hs : sym_step segs (Instr.shiftImm32 op rd rs sh) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have h2 : low32 (edenot E (.ELit (bv_unsigned sh))) = zext 32 sh := by
    show low32 (Z_to_bv 64 (sh.toNat : Int)) = zext 32 sh
    rw [← SymExec.zext32_low32 sh (by decide)]
  have Hv : edenot E (mkAluw op (sr_get ss.s_regs rs) (.ELit (bv_unsigned sh)))
      = sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh)) := by
    rw [mkAluw_denot, ← Hregs rs, h2]
  have Hstep := stepR_shiftimm32_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs sh Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_op32 (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : AluOp) (rd rs1 rs2 : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op32 op rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.op32 op rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkAluwK (facts_of ss.s_know) op (sr_get ss.s_regs rs1)
        (sr_get ss.s_regs rs2))
      = sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2))) := by
    rw [mkAluwK_denot segs E base (facts_of ss.s_know) op _ _ Hfk, ← Hregs rs1, ← Hregs rs2]
  have Hstep := stepR_op32_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs1 rs2 Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_mul (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : MulOp) (rd rs1 rs2 : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul op rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.mul op rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkMdK (facts_of ss.s_know) op (sr_get ss.s_regs rs1)
        (sr_get ss.s_regs rs2)) = mul_div op (getr regs rs1) (getr regs rs2) := by
    rw [mkMdK_denot segs E base (facts_of ss.s_know) op _ _ Hfk, ← Hregs rs1, ← Hregs rs2]
  have Hstep := stepR_mul_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs1 rs2 Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_mul32 (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (op : MulOp) (rd rs1 rs2 : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul32 op rd rs1 rs2, 4))
    (Hs : sym_step segs (Instr.mul32 op rd rs1 rs2) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (mkMdw op (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2))
      = sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2))) := by
    rw [mkMdw_denot, ← Hregs rs1, ← Hregs rs2]
  have Hstep := stepR_mul32_gen segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w op rd rs1 rs2 Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

/-- the two `zshiftl`s in the tree agree. -/
theorem zshiftl_bridge (a : Int) (k : Nat) :
    AxSymExec3.zshiftl a k = PropExec.zshiftl a k := by
  unfold AxSymExec3.zshiftl PropExec.zshiftl
  congr 1

theorem sym_step_sound_lui (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd : reg) (imm : BitVec 20)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.lui rd imm, 4))
    (Hs : sym_step segs (Instr.lui rd imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (.ELit (bv_unsigned (Z_to_bv 64
        (AxSymExec3.zshiftl (bv_signed imm) 12)))) = v_lui (PropExec.zshiftl imm.toInt 12) := by
    show Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl imm.toInt 12)))
      = v_lui (PropExec.zshiftl imm.toInt 12)
    rw [Z_to_bv64_u, zshiftl_bridge]
    rfl
  have Hstep := stepR_lui segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w rd imm Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_auipc (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd : reg) (imm : BitVec 20)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.auipc rd imm, 4))
    (Hs : sym_step segs (Instr.auipc rd imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (.ELit (bv_unsigned (Z_to_bv 64
        (AxSymExec3.zshiftl (bv_signed imm) 12 + ss.s_pc))))
      = v_auipc (Z_to_bv 64 ss.s_pc) (PropExec.zshiftl imm.toInt 12) := by
    show Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (AxSymExec3.zshiftl imm.toInt 12 + ss.s_pc)))
      = v_auipc (Z_to_bv 64 ss.s_pc) (PropExec.zshiftl imm.toInt 12)
    rw [Z_to_bv64_u, zshiftl_bridge]
    exact (SymExec.v_auipc_lit ss.s_pc (PropExec.zshiftl imm.toInt 12)).symm
  have Hstep := stepR_auipc segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w rd imm Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd _ _ (ss.s_pc + 4) Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_fence (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (fm pred succ : BitVec 4) (rd rs : reg)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fence fm pred succ rd rs, 4))
    (Hs : sym_step segs (Instr.fence fm pred succ rd rs) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hstep := stepR_fence segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w fm pred succ rd rs Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sjump segs E base rom ss regs (ss.s_pc + 4) Hregs Hlf Hkn⟩

theorem sym_step_sound_fencei (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd rs : reg) (imm : BitVec 12)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fenceI rd rs imm, 4))
    (Hs : sym_step segs (Instr.fenceI rd rs imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hstep := stepR_fencei segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w rd rs imm Hf He Hd
  rw [SymExec.v_addi_lit] at Hstep
  exact ⟨_, Hstep, st_okR_sjump segs E base rom ss regs (ss.s_pc + 4) Hregs Hlf Hkn⟩

theorem sym_step_sound_jal (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd : reg) (imm : BitVec 21)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.jal rd imm, 4))
    (Hs : sym_step segs (Instr.jal rd imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_step at Hs
  try simp only [] at Hs
  injection Hs with h1 h2 h3
  subst h1
  subst h2
  subst h3
  have Hv : edenot E (.ELit (ss.s_pc + 4)) = v_addi (Z_to_bv 64 ss.s_pc) 4 := by
    show Z_to_bv 64 (ss.s_pc + 4) = v_addi (Z_to_bv 64 ss.s_pc) 4
    rw [SymExec.v_addi_lit]
  have hpc : btgt (Z_to_bv 64 ss.s_pc) imm.toInt
      = BitVec.ofInt 64 (bv_unsigned (Z_to_bv 64 (ss.s_pc + bv_signed imm))) := by
    rw [SymExec.btgt_lit]
    exact (Z_to_bv64_u (ss.s_pc + bv_signed imm)).symm
  have Hstep := stepR_jal_link segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
    rom (resv_denot E ss.s_resv) w rd imm Hf He Hd
  rw [hpc] at Hstep
  exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd (.ELit (ss.s_pc + 4))
    (v_addi (Z_to_bv 64 ss.s_pc) 4) (bv_unsigned (Z_to_bv 64 (ss.s_pc + bv_signed imm)))
    Hregs Hlf Hkn Hv⟩

theorem sym_step_sound_jalr (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (rd rs1 : reg) (imm : BitVec 12)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.jalr rd rs1 imm, 4))
    (Hs : sym_step segs (Instr.jalr rd rs1 imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  unfold sym_step at Hs
  try simp only [] at Hs
  split at Hs
  · rename_i eg z heq
    try simp only [] at Hs
    injection Hs with h1 h2 h3
    subst h1
    subst h2
    subst h3
    have Hce := conc_expr_sound segs E base (facts_of ss.s_know) (sr_get ss.s_regs rs1) Hfk
    rw [heq] at Hce
    have hz : Z_to_bv 64 z = getr regs rs1 := by
      show edenot E (.ELit z) = getr regs rs1
      rw [Hce, ← Hregs rs1]
    have hbw : bv_wrap 64 z = ((getr regs rs1).toNat : Int) := by
      rw [← hz]
      exact (u_lit64a z).symm
    have Hv : edenot E (.ELit (ss.s_pc + 4)) = v_addi (Z_to_bv 64 ss.s_pc) 4 := by
      show Z_to_bv 64 (ss.s_pc + 4) = v_addi (Z_to_bv 64 ss.s_pc) 4
      rw [SymExec.v_addi_lit]
    have hpc : Z_to_bv 64 (AxSymExec3.zland_m2 (bv_wrap 64 z + bv_signed imm) % 2 ^ 64)
        = SeqExec.v_jalr (getr regs rs1) imm.toInt := by
      show Z_to_bv 64 (AxSymExec3.zland_m2 (bv_wrap 64 z + imm.toInt) % 2 ^ 64)
        = Z_to_bv 64 (AxSymExec3.zland_m2 ((getr regs rs1).toNat + imm.toInt))
      rw [Z_to_bv_emod64, hbw]
    have Hstep := stepR_jalr segs regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log)
      rom (resv_denot E ss.s_resv) w rd rs1 imm Hf He Hd
    rw [← hpc] at Hstep
    exact ⟨_, Hstep, st_okR_sset segs E base rom ss regs rd (.ELit (ss.s_pc + 4))
      (v_addi (Z_to_bv 64 ss.s_pc) 4)
      (AxSymExec3.zland_m2 (bv_wrap 64 z + bv_signed imm) % 2 ^ 64) Hregs Hlf Hkn Hv⟩
  · exact absurd Hs (by simp)

theorem sym_step_sound_branch (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (regs : BvMap word) (c : BranchCond) (rs1 rs2 : reg) (imm : BitVec 13)
    (ss' : sym_state) (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.branch c rs1 rs2 imm, 4))
    (Hs : sym_step segs (Instr.branch c rs1 rs2 imm) ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hregs : regs_ok E ss.s_regs regs) (Hlf : log_flat E ss.s_log)
    (Hkn : know_ok segs E base ss.s_know) :
    ∃ ms', RiscvSemantics.step segs
        (mkstR regs (Z_to_bv 64 ss.s_pc) (mem_denot E base ss.s_log) rom
          (resv_denot E ss.s_resv)) = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  have Hcond : ∀ t : Bool, branch_taken c (getr regs rs1) (getr regs rs2) = t →
      ∃ ms', RiscvSemantics.step segs (mkstR regs (Z_to_bv 64 ss.s_pc)
          (mem_denot E base ss.s_log) rom (resv_denot E ss.s_resv)) = .MachineOk ms'
        ∧ st_okR segs E base rom
            (sjump ss (if t then bv_unsigned (Z_to_bv 64 (ss.s_pc + bv_signed imm))
              else ss.s_pc + 4)) ms' := by
    intro t Ht
    cases t with
    | true =>
      have Hstep := stepR_branch_tk_gen segs regs (Z_to_bv 64 ss.s_pc)
        (mem_denot E base ss.s_log) rom (resv_denot E ss.s_resv) w c rs1 rs2 imm Hf He Hd Ht
      have hpc : btgt (Z_to_bv 64 ss.s_pc) imm.toInt
          = BitVec.ofInt 64 (bv_unsigned (Z_to_bv 64 (ss.s_pc + bv_signed imm))) := by
        rw [SymExec.btgt_lit]
        exact (Z_to_bv64_u (ss.s_pc + bv_signed imm)).symm
      rw [hpc] at Hstep
      exact ⟨_, Hstep, st_okR_sjump segs E base rom ss regs _ Hregs Hlf Hkn⟩
    | false =>
      have Hstep := stepR_branch_ft_gen segs regs (Z_to_bv 64 ss.s_pc)
        (mem_denot E base ss.s_log) rom (resv_denot E ss.s_resv) w c rs1 rs2 imm Hf He Hd Ht
      rw [SymExec.v_addi_lit] at Hstep
      exact ⟨_, Hstep, st_okR_sjump segs E base rom ss regs _ Hregs Hlf Hkn⟩
  unfold sym_step at Hs
  try simp only [] at Hs
  generalize hdb : decide_branch (facts_of ss.s_know) c (sr_get ss.s_regs rs1)
    (sr_get ss.s_regs rs2) = d1 at Hs
  cases d1 with
  | some t =>
    try simp only [] at Hs
    injection Hs with h4 h5 h6
    subst h4
    subst h5
    subst h6
    exact Hcond t (by rw [Hregs rs1, Hregs rs2]
                      exact decide_branch_sound segs E base (facts_of ss.s_know) c
                        (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2) t Hfk hdb)
  | none =>
    try simp only [] at Hs
    generalize hdb2 : decide_branch (facts_of ss.s_know) c
      (conc_expr (facts_of ss.s_know) (sr_get ss.s_regs rs1))
      (conc_expr (facts_of ss.s_know) (sr_get ss.s_regs rs2)) = d2 at Hs
    cases d2 with
    | some t =>
      try simp only [] at Hs
      injection Hs with h4 h5 h6
      subst h4
      subst h5
      subst h6
      refine Hcond t ?_
      rw [Hregs rs1, Hregs rs2,
        ← conc_expr_sound segs E base (facts_of ss.s_know) (sr_get ss.s_regs rs1) Hfk,
        ← conc_expr_sound segs E base (facts_of ss.s_know) (sr_get ss.s_regs rs2) Hfk]
      exact decide_branch_sound segs E base (facts_of ss.s_know) c
        (conc_expr (facts_of ss.s_know) (sr_get ss.s_regs rs1))
        (conc_expr (facts_of ss.s_know) (sr_get ss.s_regs rs2)) t Hfk hdb2
    | none =>
      try simp only [] at Hs
      generalize hdb3 : enum_branch (facts_of ss.s_know) c (sr_get ss.s_regs rs1)
        (sr_get ss.s_regs rs2) = d3 at Hs
      cases d3 with
      | some t =>
        try simp only [] at Hs
        injection Hs with h4 h5 h6
        subst h4
        subst h5
        subst h6
        exact Hcond t (by rw [Hregs rs1, Hregs rs2]
                          exact enum_branch_sound segs E base (facts_of ss.s_know) c
                            (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2) t Hfk hdb3)
      | none =>
        try simp only [] at Hs
        split at Hs
        · exact absurd Hs (by simp)
        · rename_i xg t dirs' hdirs
          try simp only [] at Hs
          injection Hs with h4 h5 h6
          subst h4
          subst h5
          subst h6
          obtain ⟨Hbr, _⟩ := (scs_denot_cons segs base E _ _).mp Hsc
          simp only [sc_denot] at Hbr
          exact Hcond t (by rw [Hregs rs1, Hregs rs2]; exact Hbr)

/-! ### `sym_step_soundR`: the dispatch over the instruction set -/

theorem sym_step_soundR (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (i : Instr) (ss' : sym_state)
    (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (i, 4))
    (Hs : sym_step segs i ss scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hok : st_okR segs E base rom ss ms) :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' := by
  obtain ⟨regs, hms, Hregs, Hlf, Hkn⟩ := Hok
  subst hms
  cases i with
  | load sz sx rd rs imm =>
    exact sym_step_sound_load segs E base rom ss regs sz sx rd rs imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | store sz rs1 rs2 imm =>
    exact sym_step_sound_store segs E base rom ss regs sz rs1 rs2 imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | lr wd aq rl rd rs =>
    exact sym_step_sound_lr segs E base rom ss regs wd aq rl rd rs ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | sc wd aq rl rd rs1 rs2 =>
    exact sym_step_sound_sc segs E base rom ss regs wd aq rl rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | amo op wd aq rl rd rs1 rs2 =>
    exact sym_step_sound_amo segs E base rom ss regs op wd aq rl rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | opImm op rd rs imm =>
    exact sym_step_sound_opimm segs E base rom ss regs op rd rs imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | shiftImm op rd rs sh =>
    exact sym_step_sound_shiftimm segs E base rom ss regs op rd rs sh ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | op op rd rs1 rs2 =>
    exact sym_step_sound_op segs E base rom ss regs op rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | opImm32 rd rs imm =>
    exact sym_step_sound_opimm32 segs E base rom ss regs rd rs imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | shiftImm32 op rd rs sh =>
    exact sym_step_sound_shiftimm32 segs E base rom ss regs op rd rs sh ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | op32 op rd rs1 rs2 =>
    exact sym_step_sound_op32 segs E base rom ss regs op rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | mul op rd rs1 rs2 =>
    exact sym_step_sound_mul segs E base rom ss regs op rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | mul32 op rd rs1 rs2 =>
    exact sym_step_sound_mul32 segs E base rom ss regs op rd rs1 rs2 ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | lui rd imm =>
    exact sym_step_sound_lui segs E base rom ss regs rd imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | auipc rd imm =>
    exact sym_step_sound_auipc segs E base rom ss regs rd imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | jal rd imm =>
    exact sym_step_sound_jal segs E base rom ss regs rd imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | jalr rd rs1 imm =>
    exact sym_step_sound_jalr segs E base rom ss regs rd rs1 imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | branch c rs1 rs2 imm =>
    exact sym_step_sound_branch segs E base rom ss regs c rs1 rs2 imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | fence fm pred succ rd rs =>
    exact sym_step_sound_fence segs E base rom ss regs fm pred succ rd rs ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | fenceI rd rs imm =>
    exact sym_step_sound_fencei segs E base rom ss regs rd rs imm ss' scs scr scr' w
      Hf He Hd Hs Hsc Hregs Hlf Hkn
  | ecall =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | ebreak =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | csr op rd rs1 csr =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | csrI op rd uimm csr =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fLoad fmt rd rs1 imm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fStore fmt rs1 rs2 imm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fma op fmt rd rs1 rs2 rs3 rm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fari op fmt rd rs1 rs2 rm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fsqrt fmt rd rs1 rm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fsgnj op fmt rd rs1 rs2 =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fminmax op fmt rd rs1 rs2 =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fcmp op fmt rd rs1 rs2 =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fcvt dst src rd rs1 rm =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fmv dir fmt rd rs1 =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)
  | fclass fmt rd rs1 =>
    exact absurd (show (stepres.SStop = stepres.SOk ss' scs scr') from Hs) (by simp)

/-- The historical statement: block-boundary `st_ok` in, general out. -/
theorem sym_step_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (i : Instr) (ss' : sym_state)
    (scs : List sidecond) (scr scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (i, 4))
    (Hs : sym_step segs i (clr ss) scr = .SOk ss' scs scr')
    (Hsc : scs_denot segs base E scs)
    (Hok : st_ok segs E base rom ss ms) :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ st_okR segs E base rom ss' ms' :=
  sym_step_soundR segs E base rom (clr ss) ms i ss' scs scr scr' w Hf He Hd Hs Hsc
    (st_ok_R segs E base rom ss ms Hok)

/-! ## Part 2: the `ExecSound` drivers

    `sym_exec_go_sound` is the induction over the scripted loop: at each
    iteration the step's side conditions are folded into the accumulator
    (`sc_add`) and the machine is moved by `sym_step_soundR`; the loop backs
    off to its checkpoint rather than return a state between an `lr` and its
    `sc`.  The three consumers (`sym_exec_soundR`/`_sound`/`_ex`, the strict
    `sym_execS_*`, the table-driven `sym_execT_*` and the `_resv` facts) are
    then immediate.
 The stop arms
    collapse to `go_stop_ok`/`sgo_stop_ok`: `by_cases hc : s_clean ss = true`
    then `rw [ite_eq_left hc]` (the invariant is `s_clean_None` + `mst_refl`) or
    `rw [ite_eq_right hc]` (the result IS the checkpoint).
    Three Lean-specific steps inside the induction:
    * after `cases hf : fetch_word …` the goal keeps the stuck
      `match some w with`, so `simp only []` (iota only) is needed before
      the next `rw [ite_eq_left]/[ite_eq_right]` — likewise after `decodeAny`; but
      `cases h : sym_step …` already reduces its match, and a `simp only []`
      there errors with "no progress".
    * `!(sz == 4) = true` gives `sz = 4` through `beq_iff_eq`
      (`sym_exec_sz_eq`), and `sym_step_soundR` wants `is_ecall w = false`
      where `by_cases` hands out `¬(is_ecall w = true)`
      (`cases h : is_ecall w <;> simp_all`).
    * `mst_step` needs `ms.ms_svc_pending = none`: destruct the `st_okR`
      witness and `subst` the machine equation, then `rfl` (`mkstR` pins
      the slot).
    `sym_execT_go` neither fetches nor decodes — the table does — so the
    fetch/ecall/decode facts `sym_step_soundR` needs are read back off
    `itab_entry` (`itab_entry_parts`). -/

def go_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (acc : List sidecond)
    (p : sym_state × List sidecond × scripts) : Prop :=
  p.1.s_resv = none ∧
    (scs_denot segs base E p.2.1 → scs_denot segs base E acc) ∧
    (∀ ms, scs_denot segs base E p.2.1 → st_okR segs E base rom ss ms →
      ∃ mr, CatSim.msteps segs ms mr ∧ st_okR segs E base rom p.1 mr)

theorem go_stop_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (acc : List sidecond) (scr : scripts)
    (ck : sym_state × List sidecond × scripts) :
    (if s_clean ss then (ss, acc, scr) else ck) = ck ∨
      go_ok segs E base rom ss acc (if s_clean ss then (ss, acc, scr) else ck) := by
  by_cases hc : s_clean ss = true
  · rw [ite_eq_left hc]
    right
    refine ⟨(s_clean_None ss).mp hc, fun H => H, ?_⟩
    intro ms Hsc Hst
    exact ⟨ms, CatSim.msteps.mst_refl ms, Hst⟩
  · rw [ite_eq_right hc]
    left; rfl

theorem sym_exec_sz_eq (sz : Int) (h : ¬(!(sz == 4)) = true) : sz = 4 := by
  have h4 : (sz == 4) = true := by
    cases hh : (sz == 4) <;> simp_all
  exact beq_iff_eq.mp h4

theorem sym_exec_go_sound (segs : List Segment) (E : env) (base rom : word → Option byte) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (scr : scripts) (ss : sym_state)
      (acc : List sidecond) (ck : sym_state × List sidecond × scripts),
      sym_exec_go segs fuel first stops scr ss acc ck = ck ∨
        go_ok segs E base rom ss acc (sym_exec_go segs fuel first stops scr ss acc ck) := by
  intro fuel
  induction fuel with
  | zero =>
    intro first stops scr ss acc ck
    simp only [sym_exec_go]
    exact go_stop_ok segs E base rom ss acc scr ck
  | succ f ih =>
    intro first stops scr ss acc ck
    simp only [sym_exec_go]
    by_cases hstop : (!first && stops.any (· == ss.s_pc)) = true
    · rw [ite_eq_left hstop]
      exact go_stop_ok segs E base rom ss acc scr ck
    · rw [ite_eq_right hstop]
      cases hf : fetch_word segs (Z_to_bv 64 ss.s_pc) with
      | none =>
        simp only []
        exact go_stop_ok segs E base rom ss acc scr ck
      | some w =>
        simp only []
        by_cases he : is_ecall w = true
        · rw [ite_eq_left he]; exact go_stop_ok segs E base rom ss acc scr ck
        · rw [ite_eq_right he]
          have hef : is_ecall w = false := by
            cases h : is_ecall w <;> simp_all
          cases hd : decodeAny w with
          | none =>
            simp only []
            exact go_stop_ok segs E base rom ss acc scr ck
          | some p =>
            obtain ⟨i, sz⟩ := p
            simp only []
            by_cases hsz : (!(sz == 4)) = true
            · rw [ite_eq_left hsz]; exact go_stop_ok segs E base rom ss acc scr ck
            · rw [ite_eq_right hsz]
              cases hs : sym_step segs i ss scr with
              | SStop =>
                exact go_stop_ok segs E base rom ss acc scr ck
              | SOk ss' scs scr' =>
                simp only []
                cases hgo : sym_exec_go segs f false stops scr' ss' (sc_add scs acc)
                    (if s_clean ss' then (ss', sc_add scs acc, scr') else ck) with
                | mk r rest =>
                  cases rest with
                  | mk accr scrr =>
                    have IH := ih false stops scr' ss' (sc_add scs acc)
                      (if s_clean ss' then (ss', sc_add scs acc, scr') else ck)
                    rw [hgo] at IH
                    rcases IH with hck | ⟨Hr, Hacc, Hrun⟩
                    · by_cases hc2 : s_clean ss' = true
                      · rw [ite_eq_left hc2] at hck
                        obtain ⟨h1, h2, h3⟩ :
                            r = ss' ∧ accr = sc_add scs acc ∧ scrr = scr' := by
                          simpa only [Prod.mk.injEq] using hck
                        rw [h1, h2, h3]
                        right
                        simp only [go_ok]
                        refine ⟨(s_clean_None ss').mp hc2, ?_, ?_⟩
                        · intro H
                          exact (sc_add_denot segs base E scs acc H).2
                        · intro ms Hsc0 HstR
                          obtain ⟨msA, hstepA, hstA⟩ :=
                            sym_step_soundR segs E base rom ss ms i ss' scs scr scr' w
                              hf hef (sym_exec_sz_eq sz hsz ▸ hd) hs
                              (sc_add_denot segs base E scs acc Hsc0).1 HstR
                          refine ⟨msA, ?_, hstA⟩
                          refine CatSim.msteps.mst_step ms msA msA ?_ hstepA
                            (CatSim.msteps.mst_refl msA)
                          obtain ⟨regs, hms, _⟩ := HstR
                          subst hms
                          rfl
                      · rw [ite_eq_right hc2] at hck
                        left
                        exact hck
                    · right
                      simp only [go_ok]
                      refine ⟨Hr, ?_, ?_⟩
                      · intro H
                        exact (sc_add_denot segs base E scs acc (Hacc H)).2
                      · intro ms Hsc0 HstR
                        obtain ⟨msA, hstepA, hstA⟩ :=
                          sym_step_soundR segs E base rom ss ms i ss' scs scr scr' w
                            hf hef (sym_exec_sz_eq sz hsz ▸ hd) hs
                            (sc_add_denot segs base E scs acc (Hacc Hsc0)).1 HstR
                        obtain ⟨mr, hmr, hstr⟩ := Hrun msA Hsc0 hstA
                        refine ⟨mr, CatSim.msteps.mst_step ms msA mr ?_ hstepA hmr, hstr⟩
                        obtain ⟨regs, hms, _⟩ := HstR
                        subst hms
                        rfl

/-- The accumulator only grows: the side conditions a run returns imply
    the ones handed in. -/
theorem sym_exec_acc (segs : List Segment) (E : env) (base : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (scr : scripts) (ss : sym_state)
    (acc : List sidecond) :
    scs_denot segs base E (sym_exec segs fuel first stops scr ss acc).2.1 →
      scs_denot segs base E acc := by
  unfold sym_exec
  have H := sym_exec_go_sound segs E base (fun _ => none) fuel first stops scr (clr ss) acc
    (clr ss, acc, scr)
  rcases H with Hck | ⟨_, Hacc, _⟩
  · rw [Hck]
    intro HH; exact HH
  · exact Hacc

theorem sym_exec_soundR (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (scr : scripts) (ss : sym_state)
    (acc : List sidecond) (ss' : sym_state) (scs : List sidecond) (scr' : scripts)
    (ms : machine_state)
    (Hex : sym_exec segs fuel first stops scr ss acc = (ss', scs, scr'))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok segs E base rom ss ms) :
    ss'.s_resv = none ∧
      ∃ ms', CatSim.msteps segs ms ms' ∧ st_okR segs E base rom ss' ms' := by
  unfold sym_exec at Hex
  have H := sym_exec_go_sound segs E base rom fuel first stops scr (clr ss) acc (clr ss, acc, scr)
  rcases H with Hck | ⟨Hr, Hacc, Hrun⟩
  · rw [Hex] at Hck
    obtain ⟨h1, h2, h3⟩ : ss' = clr ss ∧ scs = acc ∧ scr' = scr := by
      simpa only [Prod.mk.injEq] using Hck
    subst h1
    subst h2
    subst h3
    exact ⟨rfl, ms, CatSim.msteps.mst_refl ms, st_ok_R segs E base rom ss ms Hst⟩
  · rw [Hex] at Hr Hacc Hrun
    simp only [] at Hr Hacc Hrun
    refine ⟨Hr, ?_⟩
    obtain ⟨ms', hms, hst⟩ := Hrun ms Hsc (st_ok_R segs E base rom ss ms Hst)
    exact ⟨ms', hms, hst⟩

theorem sym_exec_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (scr : scripts) (ss : sym_state)
    (acc : List sidecond) (ss' : sym_state) (scs : List sidecond) (scr' : scripts)
    (ms : machine_state)
    (Hex : sym_exec segs fuel first stops scr ss acc = (ss', scs, scr'))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok segs E base rom ss ms) :
    ∃ ms', CatSim.msteps segs ms ms' ∧ st_ok segs E base rom ss' ms' := by
  obtain ⟨Hr, ms', hms, hstR⟩ :=
    sym_exec_soundR segs E base rom fuel first stops scr ss acc ss' scs scr' ms Hex Hsc Hst
  exact ⟨ms', hms, st_okR_ok segs E base rom ss' ms' hstR Hr⟩

theorem sym_exec_ex (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (scr : scripts) (ss : sym_state)
    (acc : List sidecond) (ss' : sym_state) (scs : List sidecond) (scr' : scripts)
    (ms : machine_state)
    (Hex : sym_exec segs fuel first stops scr ss acc = (ss', scs, scr'))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok segs E base rom ss ms) :
    ∃ R, regs_ok E ss'.s_regs R ∧ log_flat E ss'.s_log ∧
      CatSim.msteps segs ms
        (mkst R (Z_to_bv 64 ss'.s_pc) (mem_denot E base ss'.s_log) rom) := by
  obtain ⟨ms', hms, regs, hms', HR, HL, _HK⟩ :=
    sym_exec_sound segs E base rom fuel first stops scr ss acc ss' scs scr' ms Hex Hsc Hst
  subst hms'
  exact ⟨regs, HR, HL, hms⟩


/-! The S / T drivers: the same invariant without side conditions. -/
def sgo_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (r : sym_state) : Prop :=
  r.s_resv = none ∧
    (∀ ms, st_okR segs E base rom ss ms →
      ∃ mr, CatSim.msteps segs ms mr ∧ st_okR segs E base rom r mr)

theorem sgo_stop_ok (segs : List Segment) (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ck : sym_state) :
    (if s_clean ss then ss else ck) = ck ∨
      sgo_ok segs E base rom ss (if s_clean ss then ss else ck) := by
  by_cases hc : s_clean ss = true
  · rw [ite_eq_left hc]
    right
    refine ⟨(s_clean_None ss).mp hc, ?_⟩
    intro ms Hst
    exact ⟨ms, CatSim.msteps.mst_refl ms, Hst⟩
  · rw [ite_eq_right hc]
    left; rfl

theorem sym_execS_go_sound (segs : List Segment) (E : env) (base rom : word → Option byte) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execS_go segs fuel first stops ss ck = ck ∨
        sgo_ok segs E base rom ss (sym_execS_go segs fuel first stops ss ck) := by
  intro fuel
  induction fuel with
  | zero =>
    intro first stops ss ck
    simp only [sym_execS_go]
    exact sgo_stop_ok segs E base rom ss ck
  | succ f ih =>
    intro first stops ss ck
    simp only [sym_execS_go]
    by_cases hstop : (!first && stops.any (· == ss.s_pc)) = true
    · rw [ite_eq_left hstop]
      exact sgo_stop_ok segs E base rom ss ck
    · rw [ite_eq_right hstop]
      cases hf : fetch_word segs (Z_to_bv 64 ss.s_pc) with
      | none =>
        simp only []
        exact sgo_stop_ok segs E base rom ss ck
      | some w =>
        simp only []
        by_cases he : is_ecall w = true
        · rw [ite_eq_left he]; exact sgo_stop_ok segs E base rom ss ck
        · rw [ite_eq_right he]
          have hef : is_ecall w = false := by
            cases h : is_ecall w <;> simp_all
          cases hd : decodeAny w with
          | none =>
            simp only []
            exact sgo_stop_ok segs E base rom ss ck
          | some p =>
            obtain ⟨i, sz⟩ := p
            simp only []
            by_cases hsz : (!(sz == 4)) = true
            · rw [ite_eq_left hsz]; exact sgo_stop_ok segs E base rom ss ck
            · rw [ite_eq_right hsz]
              cases hs : sym_step segs i ss scr_nil with
              | SStop =>
                exact sgo_stop_ok segs E base rom ss ck
              | SOk ss' scs scr' =>
                cases scs with
                | nil =>
                  simp only []
                  cases hgo : sym_execS_go segs f false stops ss'
                      (if s_clean ss' then ss' else ck) with
                  | mk r =>
                    have IH := ih false stops ss' (if s_clean ss' then ss' else ck)
                    rw [hgo] at IH
                    rcases IH with hck | ⟨Hr, Hrun⟩
                    · by_cases hc2 : s_clean ss' = true
                      · rw [ite_eq_left hc2] at hck
                        rw [hck]
                        right
                        refine ⟨(s_clean_None ss').mp hc2, ?_⟩
                        · intro ms HstR
                          have hsz4 : sz = 4 := by
                            have h4 : (sz == 4) = true := by
                              cases h : (sz == 4) <;> simp_all
                            exact beq_iff_eq.mp h4
                          obtain ⟨msA, hstepA, hstA⟩ :=
                            sym_step_soundR segs E base rom ss ms i ss' [] scr_nil scr' w
                              hf hef (hsz4 ▸ hd) hs
                              (fun s hs' => absurd hs' (by simp)) HstR
                          refine ⟨msA, ?_, hstA⟩
                          refine CatSim.msteps.mst_step ms msA msA ?_ hstepA
                            (CatSim.msteps.mst_refl msA)
                          obtain ⟨regs, hms, _⟩ := HstR
                          subst hms
                          rfl
                      · rw [ite_eq_right hc2] at hck
                        left
                        exact hck
                    · right
                      refine ⟨Hr, ?_⟩
                      intro ms HstR
                      have hsz4 : sz = 4 := by
                        have h4 : (sz == 4) = true := by
                          cases h : (sz == 4) <;> simp_all
                        exact beq_iff_eq.mp h4
                      obtain ⟨msA, hstepA, hstA⟩ :=
                        sym_step_soundR segs E base rom ss ms i ss' [] scr_nil scr' w
                          hf hef (hsz4 ▸ hd) hs
                          (fun s hs' => absurd hs' (by simp)) HstR
                      obtain ⟨mr, hmr, hstr⟩ := Hrun msA hstA
                      refine ⟨mr, CatSim.msteps.mst_step ms msA mr ?_ hstepA hmr, hstr⟩
                      obtain ⟨regs, hms, _⟩ := HstR
                      subst hms
                      rfl
                | cons x l =>
                  exact sgo_stop_ok segs E base rom ss ck



theorem sym_execS_soundR (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (ms : machine_state)
    (Hst : st_ok segs E base rom ss ms) :
    (sym_execS segs fuel first stops ss).s_resv = none ∧
      ∃ ms', CatSim.msteps segs ms ms' ∧
        st_okR segs E base rom (sym_execS segs fuel first stops ss) ms' := by
  unfold sym_execS
  have H := sym_execS_go_sound segs E base rom fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, Hrun⟩
  · rw [Hck]
    exact ⟨rfl, ms, CatSim.msteps.mst_refl ms, st_ok_R segs E base rom ss ms Hst⟩
  · exact ⟨Hr, Hrun ms (st_ok_R segs E base rom ss ms Hst)⟩

theorem sym_execS_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (ms : machine_state)
    (Hst : st_ok segs E base rom ss ms) :
    ∃ ms', CatSim.msteps segs ms ms' ∧
      st_ok segs E base rom (sym_execS segs fuel first stops ss) ms' := by
  obtain ⟨Hr, ms', hms, hstR⟩ := sym_execS_soundR segs E base rom fuel first stops ss ms Hst
  exact ⟨ms', hms, st_okR_ok segs E base rom _ ms' hstR Hr⟩

theorem sym_execS_ex (segs : List Segment) (E : env) (base rom : word → Option byte)
    (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state) (ms : machine_state)
    (Hst : st_ok segs E base rom ss ms) :
    ∃ R, regs_ok E (sym_execS segs fuel first stops ss).s_regs R ∧
      log_flat E (sym_execS segs fuel first stops ss).s_log ∧
      know_ok segs E base (sym_execS segs fuel first stops ss).s_know ∧
      CatSim.msteps segs ms
        (mkst R (Z_to_bv 64 (sym_execS segs fuel first stops ss).s_pc)
          (mem_denot E base (sym_execS segs fuel first stops ss).s_log) rom) := by
  obtain ⟨ms', hms, regs, hms', HR, HL, HK⟩ :=
    sym_execS_sound segs E base rom fuel first stops ss ms Hst
  subst hms'
  exact ⟨regs, HR, HL, HK, hms⟩

theorem sym_execS_resv (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (ss : sym_state) : (sym_execS segs fuel first stops ss).s_resv = none := by
  unfold sym_execS
  have H := sym_execS_go_sound segs ⟨fun _ => Z_to_bv 64 0, fun _ => []⟩
    (fun _ => none) (fun _ => none) fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, _⟩
  · rw [Hck]; rfl
  · exact Hr

theorem sym_exec_resv (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (scr : scripts) (ss : sym_state) (acc : List sidecond) :
    (sym_exec segs fuel first stops scr ss acc).1.s_resv = none := by
  unfold sym_exec
  have H := sym_exec_go_sound segs ⟨fun _ => Z_to_bv 64 0, fun _ => []⟩
    (fun _ => none) (fun _ => none) fuel first stops scr (clr ss) acc (clr ss, acc, scr)
  rcases H with Hck | ⟨Hr, _⟩
  · rw [Hck]; rfl
  · exact Hr

/-! The table-driven driver `sym_execT`: the table supplies the decoded
    instruction, so the fetch/decode facts `sym_step_soundR` needs are read
    off `itab_entry` (`itab_entry_parts`). -/
theorem itab_entry_parts (segs : List Segment) (pc : Int) (i : Instr)
    (H : itab_entry segs pc = some i) :
    ∃ w, fetch_word segs (Z_to_bv 64 pc) = some w ∧ is_ecall w = false ∧
      decodeAny w = some (i, 4) := by
  unfold itab_entry at H
  cases hf : fetch_word segs (Z_to_bv 64 pc) with
  | none => rw [hf] at H; simp at H
  | some w =>
    rw [hf] at H
    simp only [] at H
    by_cases he : is_ecall w = true
    · rw [ite_eq_left he] at H; simp at H
    · rw [ite_eq_right he] at H
      have hef : is_ecall w = false := by
        cases h : is_ecall w <;> simp_all
      refine ⟨w, rfl, hef, ?_⟩
      cases hd : decodeAny w with
      | none => rw [hd] at H; simp at H
      | some p =>
        obtain ⟨i', sz⟩ := p
        rw [hd] at H
        simp only [] at H
        by_cases h4 : (sz == 4) = true
        · rw [ite_eq_left h4] at H
          have hsz4 : sz = 4 := beq_iff_eq.mp h4
          simp only [Option.some.injEq] at H
          rw [← hsz4, ← H]
        · rw [ite_eq_right h4] at H; simp at H



theorem sym_execT_go_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (Ht : itab_sound segs t) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execT_go segs t fuel first stops ss ck = ck ∨
        sgo_ok segs E base rom ss (sym_execT_go segs t fuel first stops ss ck) := by
  intro fuel
  induction fuel with
  | zero =>
    intro first stops ss ck
    simp only [sym_execT_go]
    exact sgo_stop_ok segs E base rom ss ck
  | succ f ih =>
    intro first stops ss ck
    simp only [sym_execT_go]
    by_cases hstop : (!first && stops.any (· == ss.s_pc)) = true
    · rw [ite_eq_left hstop]
      exact sgo_stop_ok segs E base rom ss ck
    · rw [ite_eq_right hstop]
      cases hl : itab_lookup t ss.s_pc with
      | none =>
        simp only []
        exact sgo_stop_ok segs E base rom ss ck
      | some i =>
        simp only []
        obtain ⟨w, hf, hef, hd⟩ := itab_entry_parts segs ss.s_pc i (Ht ss.s_pc i hl)
        have he : ¬is_ecall w = true := by
          rw [hef]; simp
        cases hs : sym_step segs i ss scr_nil with
        | SStop =>
          exact sgo_stop_ok segs E base rom ss ck
        | SOk ss' scs scr' =>
          cases scs with
          | nil =>
            simp only []
            cases hgo : sym_execT_go segs t f false stops ss'
                (if s_clean ss' then ss' else ck) with
            | mk r =>
              have IH := ih false stops ss' (if s_clean ss' then ss' else ck)
              rw [hgo] at IH
              rcases IH with hck | ⟨Hr, Hrun⟩
              · by_cases hc2 : s_clean ss' = true
                · rw [ite_eq_left hc2] at hck
                  rw [hck]
                  right
                  refine ⟨(s_clean_None ss').mp hc2, ?_⟩
                  · intro ms HstR
                    obtain ⟨msA, hstepA, hstA⟩ :=
                      sym_step_soundR segs E base rom ss ms i ss' [] scr_nil scr' w
                        hf hef hd hs (fun s hs' => absurd hs' (by simp)) HstR
                    refine ⟨msA, ?_, hstA⟩
                    refine CatSim.msteps.mst_step ms msA msA ?_ hstepA
                      (CatSim.msteps.mst_refl msA)
                    obtain ⟨regs, hms, _⟩ := HstR
                    subst hms
                    rfl
                · rw [ite_eq_right hc2] at hck
                  left
                  exact hck
              · right
                refine ⟨Hr, ?_⟩
                intro ms HstR
                obtain ⟨msA, hstepA, hstA⟩ :=
                  sym_step_soundR segs E base rom ss ms i ss' [] scr_nil scr' w
                    hf hef hd hs (fun s hs' => absurd hs' (by simp)) HstR
                obtain ⟨mr, hmr, hstr⟩ := Hrun msA hstA
                refine ⟨mr, CatSim.msteps.mst_step ms msA mr ?_ hstepA hmr, hstr⟩
                obtain ⟨regs, hms, _⟩ := HstR
                subst hms
                rfl
          | cons x l =>
            exact sgo_stop_ok segs E base rom ss ck

theorem sym_execT_soundR (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state) (Ht : itab_sound segs t) (Hst : st_ok segs E base rom ss ms) :
    (sym_execT segs t fuel first stops ss).s_resv = none ∧
      ∃ ms', CatSim.msteps segs ms ms' ∧
        st_okR segs E base rom (sym_execT segs t fuel first stops ss) ms' := by
  unfold sym_execT
  have H := sym_execT_go_sound segs E base rom t Ht fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, Hrun⟩
  · rw [Hck]
    exact ⟨rfl, ms, CatSim.msteps.mst_refl ms, st_ok_R segs E base rom ss ms Hst⟩
  · exact ⟨Hr, Hrun ms (st_ok_R segs E base rom ss ms Hst)⟩

theorem sym_execT_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state) (Ht : itab_sound segs t) (Hst : st_ok segs E base rom ss ms) :
    ∃ ms', CatSim.msteps segs ms ms' ∧
      st_ok segs E base rom (sym_execT segs t fuel first stops ss) ms' := by
  obtain ⟨Hr, ms', hms, hstR⟩ := sym_execT_soundR segs E base rom t fuel first stops ss ms Ht Hst
  exact ⟨ms', hms, st_okR_ok segs E base rom _ ms' hstR Hr⟩

theorem sym_execT_ex (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state) (Ht : itab_sound segs t) (Hst : st_ok segs E base rom ss ms) :
    ∃ R, regs_ok E (sym_execT segs t fuel first stops ss).s_regs R ∧
      log_flat E (sym_execT segs t fuel first stops ss).s_log ∧
      know_ok segs E base (sym_execT segs t fuel first stops ss).s_know ∧
      CatSim.msteps segs ms
        (mkst R (Z_to_bv 64 (sym_execT segs t fuel first stops ss).s_pc)
          (mem_denot E base (sym_execT segs t fuel first stops ss).s_log) rom) := by
  obtain ⟨ms', hms, regs, hms', HR, HL, HK⟩ :=
    sym_execT_sound segs E base rom t fuel first stops ss ms Ht Hst
  subst hms'
  exact ⟨regs, HR, HL, HK, hms⟩

theorem sym_execT_resv (segs : List Segment) (t : itab) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) (Ht : itab_sound segs t) :
    (sym_execT segs t fuel first stops ss).s_resv = none := by
  unfold sym_execT
  have H := sym_execT_go_sound segs ⟨fun _ => Z_to_bv 64 0, fun _ => []⟩
    (fun _ => none) (fun _ => none) t Ht fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, _⟩
  · rw [Hck]; rfl
  · exact Hr


/-! ## Part P5c (cont.): the memory-knowledge coverage block

    Readability / overlay-definedness of a covered range.  The two
    `rdn`/`rd1` bridges come first (they are what "covered" MEANS
    operationally), then the per-entry lemmas (`zf_covers_sound`,
    `kentry_overlay_sound`, `kentry_readable_sound`), the bytewise sweep
    (`know_byte_cov_sound`, `know_bytes_cov_sound`) and the two list-level
    results the extension-mode step needs (`kn_readable_sound`,
    `kn_overlay_sound`).  `x_discharge_sound` and `cap_rd_sound` close the
    block by turning a discharged obligation into a `sc_denot` and by
    capping a register under an extension.

    Note this tree's `Forall` convention: `know_ok segs E base kn` is
    `∀ K ∈ kn, kentry_ok segs E base K`, so the
    `Forall_cons_iff`/`Forall_forall` steps become `List.mem_cons` and a
    direct application. -/

/-- Bytewise definedness of the `rd1` view gives a successful `rdn` of the
    whole range.     The `a + 1` wrap only happens when `bv_unsigned a + 1 = 2^64`, and then
    the bound forces `n = 0`, so no induction hypothesis is needed there. -/
theorem rdn_defined (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word), bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
      (∀ j, j < n → rd1 segs mem (Z_to_bv 64 (bv_unsigned a + (j : Int))) ≠ none) →
      ∃ bs, rdn segs mem a n = some bs ∧ bs.length = n := by
  induction n with
  | zero => intro a _ _; exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro a Hnw Hall
    push_cast at Hnw
    have h0eq : Z_to_bv 64 (bv_unsigned a + ((0 : Nat) : Int)) = a := by
      rw [show ((0 : Nat) : Int) = 0 from rfl, Int.add_zero, Z_to_bv_unsigned]
    have hb : ∃ b, SeqExec.rdn_byte segs mem a = some b := by
      have h := Hall 0 (Nat.succ_pos n)
      rw [h0eq] at h
      cases hx : SeqExec.rdn_byte segs mem a with
      | none => exact absurd hx h
      | some b => exact ⟨b, rfl⟩
    obtain ⟨b, hb⟩ := hb
    by_cases hlt : bv_unsigned a + 1 < 2 ^ 64
    · have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 a hlt
      have hbnd : bv_unsigned (a + 1) + (n : Int) ≤ 2 ^ 64 := by rw [hu1]; omega
      have hpt : ∀ j, j < n →
          rd1 segs mem (Z_to_bv 64 (bv_unsigned (a + 1) + (j : Int))) ≠ none := by
        intro j hj
        have h := Hall (j + 1) (by omega)
        have he : bv_unsigned a + ((j + 1 : Nat) : Int) = bv_unsigned a + 1 + (j : Int) := by
          push_cast; omega
        rw [he] at h
        rw [hu1]
        exact h
      obtain ⟨bs, Hbs, Hlen⟩ := ih (a + 1) hbnd hpt
      refine ⟨b :: bs, ?_, ?_⟩
      · rw [SeqExec.rdn_succ_byte segs mem a n b hb, Hbs]
        rfl
      · rw [List.length_cons, Hlen]
    · have hn0 : n = 0 := by omega
      subst hn0
      refine ⟨[b], ?_, rfl⟩
      rw [SeqExec.rdn_succ_byte segs mem a 0 b hb, SeqExec.rdn_zero]
      rfl

/-- Conversely, a successful `rdn` makes every byte of the range
    `rd1`-defined (read through the overlay or the image). -/
theorem rdn_rd1 (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (j : Nat) (H : rdn segs mem a n = some bs) (Hj : j < n) :
    rd1 segs mem (a + nat_to_word j) ≠ none := by
  intro hnone
  have hnone' : SeqExec.rdn_byte segs mem (a + nat_to_word j) = none := hnone
  have h1 : rdn segs mem (a + nat_to_word j) 1 = none :=
    SeqExec.rdn_succ_none segs mem (a + nat_to_word j) 0 hnone'
  rw [SeqExec.rdn_nth segs mem n a bs j H Hj] at h1
  exact absurd h1 (by simp)

/-- `zf_covers` soundness: the read range `rb+rk, +n` lies inside an
    entry's range `kb+kk, +len`.  Two ways to establish it, matching the
    `||`: a literal length and a literal-offset containment, or the exact
    linear comparison `xinside`. -/
theorem zf_covers_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn : List kentry) (rb : expr) (rk : Int) (n : Nat) (kb : expr) (kk : Int)
    (len : expr) (Hall : know_ok segs E M0 allkn) (Hn8 : n ≤ 8)
    (H : zf_covers allkn rb rk n kb kk len = true) :
    estart E (SA kb kk) ≤ estart E (SA rb rk) ∧
      estart E (SA rb rk) + (n : Int) ≤ estart E (SA kb kk) + elenZ E len := by
  have xin : xinside allkn rb rk (elen n) kb kk len = true →
      estart E (SA kb kk) ≤ estart E (SA rb rk) ∧
        estart E (SA rb rk) + (n : Int) ≤ estart E (SA kb kk) + elenZ E len := by
    intro Hx
    obtain ⟨A, B⟩ := xinside_sound segs E M0 allkn rb rk (elen n) kb kk len Hall Hx
    rw [elenZ_elen E n Hn8] at B
    exact ⟨A, B⟩
  unfold zf_covers at H
  rw [Bool.or_eq_true] at H
  rcases H with H | H
  · -- the literal-length arm: `len` must be `ELit l0` and `rel_lit` must be inside
    cases len with
    | ELit l0 =>
      simp only [] at H
      split at H
      · rename_i d hrel
        obtain ⟨-, hd, hkk, hrn, hst⟩ :=
          rel_lit_inside E rb rk (n : Int) kb kk (l0 % two64) d hrel
        rw [two64_eq] at hrn
        rw [elenZ_lit]
        refine ⟨?_, ?_⟩ <;> omega
      · exact absurd H (by decide)
    | EVar v => simp only [] at H; exact absurd H (by decide)
    | EAlu op a b => simp only [] at H; exact absurd H (by decide)
    | EAluw op a b => simp only [] at H; exact absurd H (by decide)
    | EMd op a b => simp only [] at H; exact absurd H (by decide)
    | EMdw op a b => simp only [] at H; exact absurd H (by decide)
    | EExt sx lo n' e => simp only [] at H; exact absurd H (by decide)
    | EBlob sx k i n' => simp only [] at H; exact absurd H (by decide)
  · exact xin H

/-- A covering entry whose bytes the OVERLAY defines makes the range
    overlay-defined (hence readable and writable). -/
theorem kentry_overlay_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn : List kentry) (base : word → Option byte) (rb : expr) (rk : Int) (n : Nat)
    (K : kentry) (Hall : know_ok segs E M0 allkn) (HK : kentry_ok segs E base K)
    (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) (H : kentry_overlay allkn rb rk n K = true) :
    flat E (SA rb rk) (n : Int) ∧
      ∀ j, j < n → base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
  have GEN : ∀ (kb : expr) (kk : Int) (len : expr) (P : Option byte → Prop),
      (∀ x, P x → x ≠ none) →
      flat E (SA kb kk) (elenZ E len) →
      (∀ i, 0 ≤ i → i < elenZ E len → P (base (Z_to_bv 64 (estart E (SA kb kk) + i)))) →
      zf_covers allkn rb rk n kb kk len = true →
      flat E (SA rb rk) (n : Int) ∧
        ∀ j, j < n → base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
    intro kb kk len P HP Hfl Hz Hc
    obtain ⟨A, B⟩ := zf_covers_sound segs E M0 allkn rb rk n kb kk len Hall Hn8 Hc
    obtain ⟨h1, h2, h3, h4⟩ := Hfl
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro j hj
    have hz := Hz (estart E (SA rb rk) - estart E (SA kb kk) + (j : Int)) (by omega) (by omega)
    rw [show estart E (SA kb kk) + (estart E (SA rb rk) - estart E (SA kb kk) + (j : Int))
          = estart E (SA rb rk) + (j : Int) from by omega] at hz
    exact HP _ hz
  unfold kentry_overlay at H
  cases K with
  | KUnk sa len =>
    obtain ⟨kb, kk⟩ := sa
    obtain ⟨hfl, hz⟩ := HK
    simpa only [] using GEN kb kk len (fun x => x ≠ none) (fun x hx => hx) hfl hz H
  | KZero sa len =>
    obtain ⟨kb, kk⟩ := sa
    obtain ⟨hfl, hz⟩ := HK
    simpa only [] using
      GEN kb kk len (fun x => x = some (Z_to_bv 8 0)) (fun x hx => by rw [hx]; simp)
        hfl hz H
  | KFill sa len c =>
    obtain ⟨kb, kk⟩ := sa
    obtain ⟨hfl, hz⟩ := HK
    simpa only [] using
      GEN kb kk len (fun x => x = some (Z_to_bv 8 c)) (fun x hx => by rw [hx]; simp)
        hfl hz H
  | KBlob sa len k =>
    obtain ⟨kb, kk⟩ := sa
    obtain ⟨hfl, hlen, hz⟩ := HK
    simpa only [] using
      GEN kb kk len (fun x => ∃ b, x = some b) (fun x hx => by obtain ⟨b, hb⟩ := hx; rw [hb]; simp)
        hfl (fun i hi hlt => ⟨_, hz i hi hlt⟩) H
  | KWord sa w v => simp only [] at H; exact absurd H (by decide)
  | KImg lo hi => simp only [] at H; exact absurd H (by decide)
  | KAlign e m => simp only [] at H; exact absurd H (by decide)
  | KRange e lo hi => simp only [] at H; exact absurd H (by decide)
  | KWr sa n' => simp only [] at H; exact absurd H (by decide)
  | KDisj a1 n1 a2 n2 => simp only [] at H; exact absurd H (by decide)

/-- A covering entry makes the range READABLE: `KWord` gives its bytes back
    (from the overlay or the image), every other covering kind is covered by
    `kentry_overlay_sound`.  The `KWord` arm walks the `rdn` list with
    `rdn_rd1` and moves the literal offset `d` of `rel_lit_inside` into the
    address with `w_add_nat` + `flat_u`.

    `kentry_ok`'s statement spells the entry's address as the
    destructured record, while `rel_lit_inside`/`estart` goals spell it
    `SA …`; the two are convertible but NOT syntactically equal, and `omega`
    sees distinct atoms.  Keeping the entry's address as the whole `saddr`
    (`sa`) and moving it with `hsa : SA sa.a_base sa.a_off = sa` keeps every
    `estart` atom identical. -/
theorem kentry_readable_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn : List kentry) (base : word → Option byte) (rb : expr) (rk : Int) (n : Nat)
    (K : kentry) (Hall : know_ok segs E M0 allkn) (HK : kentry_ok segs E base K)
    (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) (H : kentry_readable allkn rb rk n K = true) :
    flat E (SA rb rk) (n : Int) ∧
      ∀ j, j < n → rd1 segs base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
  have OV : kentry_overlay allkn rb rk n K = true →
      flat E (SA rb rk) (n : Int) ∧
        ∀ j, j < n → rd1 segs base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
    intro Hov
    obtain ⟨A, B⟩ := kentry_overlay_sound segs E M0 allkn base rb rk n K Hall HK Hn1 Hn8 Hov
    refine ⟨A, ?_⟩
    intro j hj hcontra
    apply B j hj
    cases hb : base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) with
    | some b =>
      unfold rd1 at hcontra
      rw [hb] at hcontra
      exact absurd hcontra (by simp)
    | none => rfl
  unfold kentry_readable at H
  cases K with
  | KWord sa w v =>
    obtain ⟨hw8, hfk, hrd⟩ := HK
    have hsa : (SA sa.a_base sa.a_off) = sa := rfl
    cases hrel : rel_lit rb rk (n : Int) sa.a_base sa.a_off (w : Int) with
    | RInside d =>
      obtain ⟨hbk, hd, hkk, hrn, hst⟩ :=
        rel_lit_inside E rb rk (n : Int) sa.a_base sa.a_off (w : Int) d hrel
      rw [hbk] at hst H ⊢
      rw [hsa] at hst
      have hdnn : 0 ≤ d := by omega
      have hdt : ((d.toNat : Nat) : Int) = d := Int.toNat_of_nonneg hdnn
      have hflat : flat E sa (w : Int) := hfk
      obtain ⟨f1, f2, f3, f4⟩ := hflat
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
      intro j hj
      have hjw : d.toNat + j < w := by
        have hjwi : ((d.toNat + j : Nat) : Int) < (w : Int) := by
          push_cast
          rw [hdt]
          omega
        omega
      have X := rdn_rd1 segs base w (adenot E sa) (word_to_le_bytes w (edenot E v))
        (d.toNat + j) hrd hjw
      rw [w_add_nat] at X
      have key : bv_unsigned (adenot E sa) + (((d.toNat + j : Nat)) : Int)
          = estart E (SA sa.a_base rk) + (j : Int) := by
        rw [flat_u E sa (w : Int) hfk]
        push_cast
        rw [hdt]
        omega
      rwa [key] at X
    | RDisjoint => simp only [hrel] at H; exact absurd H (by decide)
    | RPartial => simp only [hrel] at H; exact absurd H (by decide)
    | RUnknown => simp only [hrel] at H; exact absurd H (by decide)
  | KZero sa len => simpa only [] using OV H
  | KFill sa len c => simpa only [] using OV H
  | KBlob sa len k => simpa only [] using OV H
  | KUnk sa len => simpa only [] using OV H
  | KImg lo hi => simpa only [] using OV H
  | KAlign e m => simpa only [] using OV H
  | KRange e lo hi => simpa only [] using OV H
  | KWr sa n' => simpa only [] using OV H
  | KDisj a1 n1 a2 n2 => simpa only [] using OV H

/-! ### The bytewise coverage sweep

    `know_byte_cov_sound`: ONE byte of the range is `rd1`-defined (or
    overlay-defined, without `img`); `know_bytes_cov_sound`: all `n` of them.
 The `if` form is `know_byte_cov_sound` below.
    `know_byte_cov_cons` states the recursion equation with the `lit`
    helper zeta-expanded, so the case bash below has a syntactic handle on
    the entry match (see the `sum_facts_KRange_unfold` note in the header). -/

theorem know_byte_cov_cons (segs : List Segment) (img : Bool) (K : kentry) (rest : List kentry)
    (rb : expr) (rk : Int) :
    know_byte_cov segs img (K :: rest) rb rk
      = (((match K with
           | .KWord ⟨kb, kk⟩ w _ =>
               img && (match rel_lit rb rk 1 kb kk (w : Int) with
                       | .RInside _ => true
                       | _ => false)
           | .KZero ⟨kb, kk⟩ (.ELit l0) | .KFill ⟨kb, kk⟩ (.ELit l0) _
           | .KBlob ⟨kb, kk⟩ (.ELit l0) _ | .KUnk ⟨kb, kk⟩ (.ELit l0) =>
               (match rel_lit rb rk 1 kb kk (l0 % two64) with
                | .RInside _ => true
                | _ => false)
           | .KImg lo hi =>
               img && (match rb with
                       | .ELit 0 =>
                           lo ≤ rk && rk < hi &&
                             (match seg_rom segs (Z_to_bv 64 rk) with
                              | some _ => true
                              | none => false)
                       | _ => false)
           | _ => false)) || know_byte_cov segs img rest rb rk) := rfl

/-- The geometric content of a `lit` hit: the read range `rb+rk, +1` is flat
    and sits at offset `d` inside the entry's range. -/
theorem cov_lit_data (E : env) (rb : expr) (rk : Int) (ka : saddr) (l : Int)
    (Hfl : flat E ka l)
    (Hm : (match rel_lit rb rk 1 ka.a_base ka.a_off l with
           | .RInside _ => true
           | _ => false) = true) :
    flat E (SA rb rk) 1 ∧ ∃ d, estart E (SA rb rk) = estart E ka + d ∧ 0 ≤ d ∧ d < l := by
  have hsa : (SA ka.a_base ka.a_off) = ka := rfl
  split at Hm
  · rename_i d hrel
    obtain ⟨hbk, hd, hkk, hrn, hst⟩ := rel_lit_inside E rb rk 1 ka.a_base ka.a_off l d hrel
    rw [hsa] at hst
    obtain ⟨g1, g2, g3, g4⟩ := Hfl
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, d, hst, by omega, by omega⟩
  · exact absurd Hm (by decide)

/-- A `lit` hit whose entry proves every byte of the range `P` gives a
    defined byte at the read address (both through `base` and through
    `rd1`). -/
theorem cov_lit_sound (segs : List Segment) (E : env) (base : word → Option byte)
    (rb : expr) (rk : Int) (ka : saddr) (l : Int) (P : Option byte → Prop)
    (HP : ∀ x, P x → x ≠ none) (Hfl : flat E ka l)
    (Hz : ∀ i, 0 ≤ i → i < l → P (base (Z_to_bv 64 (estart E ka + i))))
    (Hm : (match rel_lit rb rk 1 ka.a_base ka.a_off l with
           | .RInside _ => true
           | _ => false) = true) :
    flat E (SA rb rk) 1 ∧ base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none ∧
      rd1 segs base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none := by
  obtain ⟨hfl, d, hst, hdnn, hdlt⟩ := cov_lit_data E rb rk ka l Hfl Hm
  have hb : base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none := by
    have hz := Hz d hdnn hdlt
    rw [← hst] at hz
    exact HP _ hz
  refine ⟨hfl, hb, ?_⟩
  intro hcontra
  unfold rd1 at hcontra
  cases hbx : base (Z_to_bv 64 (estart E (SA rb rk))) with
  | some b =>
    rw [hbx] at hcontra
    exact absurd hcontra (by simp)
  | none => exact hb hbx

/-! The per-ENTRY-SHAPE recursion equations.  `cases K` cannot rewrite the
    case bash's hypothesis when the hypothesis has already been UNFOLDED
    (its type is then a `match` on `K`, which `cases` leaves alone — see the
    header note), so the proof keeps `know_byte_cov … = true` FOLDED and
    rewrites it with one of the `rfl` equations below once `K`'s shape is
    known.  Each is `rfl`: its right-hand side is the definition's body at
    that constructor, with the `lit` helper zeta-expanded. -/

theorem know_byte_cov_word (segs : List Segment) (img : Bool) (sa : saddr) (w : Nat)
    (v : expr) (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KWord sa w v :: rest) rb rk
      = ((img && (match rel_lit rb rk 1 sa.a_base sa.a_off (w : Int) with
                  | .RInside _ => true
                  | _ => false)) || know_byte_cov segs img rest rb rk) := rfl

theorem know_byte_cov_zero (segs : List Segment) (img : Bool) (sa : saddr) (len : expr)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KZero sa len :: rest) rb rk
      = ((match len with
          | .ELit l0 =>
              (match rel_lit rb rk 1 sa.a_base sa.a_off (l0 % two64) with
               | .RInside _ => true
               | _ => false)
          | _ => false) || know_byte_cov segs img rest rb rk) := by
  cases len <;> rfl

theorem know_byte_cov_fill (segs : List Segment) (img : Bool) (sa : saddr) (len : expr)
    (c : Int) (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KFill sa len c :: rest) rb rk
      = ((match len with
          | .ELit l0 =>
              (match rel_lit rb rk 1 sa.a_base sa.a_off (l0 % two64) with
               | .RInside _ => true
               | _ => false)
          | _ => false) || know_byte_cov segs img rest rb rk) := by
  cases len <;> rfl

theorem know_byte_cov_blob (segs : List Segment) (img : Bool) (sa : saddr) (len : expr)
    (k : Nat) (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KBlob sa len k :: rest) rb rk
      = ((match len with
          | .ELit l0 =>
              (match rel_lit rb rk 1 sa.a_base sa.a_off (l0 % two64) with
               | .RInside _ => true
               | _ => false)
          | _ => false) || know_byte_cov segs img rest rb rk) := by
  cases len <;> rfl

theorem know_byte_cov_unk (segs : List Segment) (img : Bool) (sa : saddr) (len : expr)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KUnk sa len :: rest) rb rk
      = ((match len with
          | .ELit l0 =>
              (match rel_lit rb rk 1 sa.a_base sa.a_off (l0 % two64) with
               | .RInside _ => true
               | _ => false)
          | _ => false) || know_byte_cov segs img rest rb rk) := by
  cases len <;> rfl

theorem know_byte_cov_img (segs : List Segment) (img : Bool) (lo hi : Int)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KImg lo hi :: rest) rb rk
      = ((img && (match rb with
                  | .ELit 0 =>
                      lo ≤ rk && rk < hi &&
                        (match seg_rom segs (Z_to_bv 64 rk) with
                         | some _ => true
                         | none => false)
                  | _ => false)) || know_byte_cov segs img rest rb rk) := by
  cases rb <;> rfl

theorem know_byte_cov_align (segs : List Segment) (img : Bool) (e : expr) (m : Int)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KAlign e m :: rest) rb rk
      = know_byte_cov segs img rest rb rk := rfl

theorem know_byte_cov_range (segs : List Segment) (img : Bool) (e : expr) (lo hi : Int)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KRange e lo hi :: rest) rb rk
      = know_byte_cov segs img rest rb rk := rfl

theorem know_byte_cov_wr (segs : List Segment) (img : Bool) (sa : saddr) (n : expr)
    (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KWr sa n :: rest) rb rk
      = know_byte_cov segs img rest rb rk := rfl

theorem know_byte_cov_disj (segs : List Segment) (img : Bool) (a1 : saddr) (n1 : expr)
    (a2 : saddr) (n2 : expr) (rest : List kentry) (rb : expr) (rk : Int) :
    know_byte_cov segs img (.KDisj a1 n1 a2 n2 :: rest) rb rk
      = know_byte_cov segs img rest rb rk := rfl

/-- One byte of the covered range: the entry's bytes go through the overlay
    (`KZero`/`KFill`/`KBlob`/`KUnk`), through the image (`KWord`, `KImg`).
-/
theorem know_byte_cov_both (segs : List Segment) (img : Bool) (E : env)
    (base : word → Option byte) :
    ∀ (kn : List kentry) (rb : expr) (rk : Int), know_ok segs E base kn →
      know_byte_cov segs img kn rb rk = true →
      flat E (SA rb rk) 1 ∧
        (img = true → rd1 segs base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none) ∧
        (img = false → base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none) := by
  intro kn
  induction kn with
  | nil =>
    intro rb rk _ H
    simp only [know_byte_cov] at H
    exact absurd H (by decide)
  | cons K rest ih =>
    intro rb rk Hkn H
    have HK : kentry_ok segs E base K := Hkn K (List.mem_cons_self ..)
    have Hrest : know_ok segs E base rest := fun K' hK' => Hkn K' (List.mem_cons_of_mem _ hK')
    cases K with
    | KWord sa w v =>
      obtain ⟨hw8, hfk, hrd⟩ := HK
      rw [know_byte_cov_word] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · obtain ⟨himg, hlit⟩ := (Bool.and_eq_true ..).mp H
        obtain ⟨hfl, d, hst, hdnn, hdlt⟩ := cov_lit_data E rb rk sa (w : Int) hfk hlit
        refine ⟨hfl, ?_, ?_⟩
        · intro _
          have hdt : ((d.toNat : Nat) : Int) = d := Int.toNat_of_nonneg hdnn
          have hjw : d.toNat < w := by
            have hdj : ((d.toNat : Nat) : Int) < (w : Int) := by rw [hdt]; exact hdlt
            omega
          have X := rdn_rd1 segs base w (adenot E sa) (word_to_le_bytes w (edenot E v))
            d.toNat hrd hjw
          rw [w_add_nat] at X
          have key : bv_unsigned (adenot E sa) + ((d.toNat : Nat) : Int)
              = estart E (SA rb rk) := by
            rw [flat_u E sa (w : Int) hfk, hdt, ← hst]
          rwa [key] at X
        · intro hf
          rw [hf] at himg
          exact absurd himg (by decide)
      · exact ih rb rk Hrest H
    | KZero sa len =>
      obtain ⟨hfl, hz⟩ := HK
      rw [know_byte_cov_zero] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · cases hlen : len with
        | ELit l0 =>
          simp only [hlen] at H
          rw [hlen] at hfl hz
          rw [elenZ_lit] at hfl hz
          obtain ⟨h1, h2, h3⟩ := cov_lit_sound segs E base rb rk sa (l0 % two64)
            (fun x => x = some (Z_to_bv 8 0)) (fun x hx => by rw [hx]; simp) hfl hz H
          exact ⟨h1, fun _ => h3, fun _ => h2⟩
        | EVar v => simp only [hlen] at H; exact absurd H (by decide)
        | EAlu op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EAluw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMd op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMdw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EExt sx lo n' e => simp only [hlen] at H; exact absurd H (by decide)
        | EBlob sx k i n' => simp only [hlen] at H; exact absurd H (by decide)
      · exact ih rb rk Hrest H
    | KFill sa len c =>
      obtain ⟨hfl, hz⟩ := HK
      rw [know_byte_cov_fill] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · cases hlen : len with
        | ELit l0 =>
          simp only [hlen] at H
          rw [hlen] at hfl hz
          rw [elenZ_lit] at hfl hz
          obtain ⟨h1, h2, h3⟩ := cov_lit_sound segs E base rb rk sa (l0 % two64)
            (fun x => x = some (Z_to_bv 8 c)) (fun x hx => by rw [hx]; simp) hfl hz H
          exact ⟨h1, fun _ => h3, fun _ => h2⟩
        | EVar v => simp only [hlen] at H; exact absurd H (by decide)
        | EAlu op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EAluw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMd op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMdw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EExt sx lo n' e => simp only [hlen] at H; exact absurd H (by decide)
        | EBlob sx k i n' => simp only [hlen] at H; exact absurd H (by decide)
      · exact ih rb rk Hrest H
    | KBlob sa len k =>
      obtain ⟨hfl, hlen0, hz⟩ := HK
      rw [know_byte_cov_blob] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · cases hlen : len with
        | ELit l0 =>
          simp only [hlen] at H
          rw [hlen] at hfl hz
          rw [elenZ_lit] at hfl hz
          obtain ⟨h1, h2, h3⟩ := cov_lit_sound segs E base rb rk sa (l0 % two64)
            (fun x => ∃ b, x = some b) (fun x hx => by obtain ⟨b, hb⟩ := hx; rw [hb]; simp) hfl (fun i hi hlt => ⟨_, hz i hi hlt⟩) H
          exact ⟨h1, fun _ => h3, fun _ => h2⟩
        | EVar v => simp only [hlen] at H; exact absurd H (by decide)
        | EAlu op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EAluw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMd op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMdw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EExt sx lo n' e => simp only [hlen] at H; exact absurd H (by decide)
        | EBlob sx k i n' => simp only [hlen] at H; exact absurd H (by decide)
      · exact ih rb rk Hrest H
    | KUnk sa len =>
      obtain ⟨hfl, hz⟩ := HK
      rw [know_byte_cov_unk] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · cases hlen : len with
        | ELit l0 =>
          simp only [hlen] at H
          rw [hlen] at hfl hz
          rw [elenZ_lit] at hfl hz
          obtain ⟨h1, h2, h3⟩ := cov_lit_sound segs E base rb rk sa (l0 % two64)
            (fun x => x ≠ none) (fun x hx => hx) hfl hz H
          exact ⟨h1, fun _ => h3, fun _ => h2⟩
        | EVar v => simp only [hlen] at H; exact absurd H (by decide)
        | EAlu op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EAluw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMd op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EMdw op a b => simp only [hlen] at H; exact absurd H (by decide)
        | EExt sx lo n' e => simp only [hlen] at H; exact absurd H (by decide)
        | EBlob sx k i n' => simp only [hlen] at H; exact absurd H (by decide)
      · exact ih rb rk Hrest H
    | KImg lo hi =>
      obtain ⟨hlo, hhi, hnone⟩ := HK
      rw [know_byte_cov_img] at H
      rw [Bool.or_eq_true] at H
      rcases H with H | H
      · obtain ⟨himg, hrest⟩ := (Bool.and_eq_true ..).mp H
        split at hrest
        · rename_i heq
          obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp hrest
          obtain ⟨h1, h2⟩ := (Bool.and_eq_true ..).mp hA
          rw [decide_eq_true_eq] at h1 h2
          have hseg : (match seg_rom segs (Z_to_bv 64 rk) with
                       | some _ => true
                       | none => false) = true := hB
          refine ⟨?_, ?_, ?_⟩
          · unfold flat
            rw [estart_lit0]
            exact ⟨by omega, by omega, by omega, by omega⟩
          · intro _
            rw [estart_lit0]
            intro hcontra
            have hbn : base (Z_to_bv 64 rk) = none := hnone rk h1 (by omega)
            unfold rd1 at hcontra
            rw [hbn] at hcontra
            cases hs : seg_rom segs (Z_to_bv 64 rk) with
            | none => rw [hs] at hseg; exact absurd hseg (by decide)
            | some b => rw [hs] at hcontra; exact absurd hcontra (by simp)
          · intro hf
            rw [hf] at himg
            exact absurd himg (by decide)
        · exact absurd hrest (by decide)
      · exact ih rb rk Hrest H
    | KAlign e m =>
      rw [know_byte_cov_align] at H
      exact ih rb rk Hrest H
    | KRange e lo hi =>
      rw [know_byte_cov_range] at H
      exact ih rb rk Hrest H
    | KWr sa n' =>
      rw [know_byte_cov_wr] at H
      exact ih rb rk Hrest H
    | KDisj a1 n1 a2 n2 =>
      rw [know_byte_cov_disj] at H
      exact ih rb rk Hrest H

/-- `if`-form of `know_byte_cov_both`. -/
theorem know_byte_cov_sound (segs : List Segment) (img : Bool) (E : env)
    (base : word → Option byte) (kn : List kentry) (rb : expr) (rk : Int)
    (Hkn : know_ok segs E base kn) (H : know_byte_cov segs img kn rb rk = true) :
    flat E (SA rb rk) 1 ∧
      (if img then rd1 segs base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none
       else base (Z_to_bv 64 (estart E (SA rb rk))) ≠ none) := by
  obtain ⟨h1, h2, h3⟩ := know_byte_cov_both segs img E base kn rb rk Hkn H
  refine ⟨h1, ?_⟩
  cases img with
  | true => simpa using h2 rfl
  | false => simpa using h3 rfl

theorem know_bytes_cov_cons (segs : List Segment) (img : Bool) (kn : List kentry) (rb : expr)
    (rk : Int) (n : Nat) :
    know_bytes_cov segs img kn rb rk (n + 1)
      = (know_byte_cov segs img kn rb rk && know_bytes_cov segs img kn rb (rk + 1) n) := by
  rw [know_bytes_cov]

/-- All `n` bytes of the range: the conjunction form of  `if`
    statement (see `know_byte_cov_both`). -/
theorem know_bytes_cov_both (segs : List Segment) (img : Bool) (E : env)
    (base : word → Option byte) (kn : List kentry) (rb : expr) :
    ∀ (n : Nat) (rk : Int), know_ok segs E base kn →
      know_bytes_cov segs img kn rb rk n = true → 1 ≤ n →
      flat E (SA rb rk) (n : Int) ∧
        (img = true → ∀ j, j < n →
          rd1 segs base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none) ∧
        (img = false → ∀ j, j < n →
          base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none) := by
  intro n
  induction n with
  | zero =>
    intro rk _ _ Hn1
    omega
  | succ n ih =>
    intro rk Hkn H Hn1
    rw [know_bytes_cov_cons] at H
    rw [Bool.and_eq_true] at H
    obtain ⟨H1, H2⟩ := H
    obtain ⟨F1, B1t, B1f⟩ := know_byte_cov_both segs img E base kn rb rk Hkn H1
    have hstep : estart E (SA rb (rk + 1)) = estart E (SA rb rk) + 1 := by
      show bv_unsigned (edenot E rb) + (rk + 1) = bv_unsigned (edenot E rb) + rk + 1
      omega
    cases n with
    | zero =>
      have hF : flat E (SA rb rk) ((0 + 1 : Nat) : Int) := F1
      refine ⟨hF, ?_, ?_⟩
      · intro hi j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simpa using B1t hi
      · intro hi j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simpa using B1f hi
    | succ m =>
      obtain ⟨F2, B2t, B2f⟩ := ih (rk + 1) Hkn H2 (by omega)
      have hF : flat E (SA rb rk) (((m + 1) + 1 : Nat) : Int) := by
        obtain ⟨g1, g2, g3, g4⟩ := F1
        obtain ⟨h1, h2, h3, h4⟩ := F2
        refine ⟨by omega, by omega, by omega, by omega⟩
      have hidx : ∀ j' : Nat, estart E (SA rb (rk + 1)) + (j' : Int)
          = estart E (SA rb rk) + ((j' + 1 : Nat) : Int) := by
        intro j'
        rw [hstep]
        push_cast
        omega
      refine ⟨hF, ?_, ?_⟩
      · intro hi j hj
        cases j with
        | zero => simpa using B1t hi
        | succ j' =>
          have h := B2t hi j' (by omega)
          rwa [hidx j'] at h
      · intro hi j hj
        cases j with
        | zero => simpa using B1f hi
        | succ j' =>
          have h := B2f hi j' (by omega)
          rwa [hidx j'] at h

/-- `if`-form of `know_bytes_cov_both`. -/
theorem know_bytes_cov_sound (segs : List Segment) (img : Bool) (E : env)
    (base : word → Option byte) (kn : List kentry) (rb : expr) (n : Nat) (rk : Int)
    (Hkn : know_ok segs E base kn) (H : know_bytes_cov segs img kn rb rk n = true)
    (Hn1 : 1 ≤ n) :
    flat E (SA rb rk) (n : Int) ∧
      ∀ j, j < n →
        (if img then rd1 segs base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none
         else base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none) := by
  obtain ⟨h1, h2, h3⟩ := know_bytes_cov_both segs img E base kn rb n rk Hkn H Hn1
  refine ⟨h1, ?_⟩
  cases img with
  | true => simpa using h2 rfl
  | false => simpa using h3 rfl

/-- The range is readable: one covering entry (`kentry_readable_sound`) or
    the bytewise sweep, then `rdn_defined` turns bytewise definedness into a
    successful read. -/
theorem kn_readable_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn kn : List kentry) (base : word → Option byte) (rb : expr) (rk : Int) (n : Nat)
    (Hall : know_ok segs E M0 allkn) (Hkn : know_ok segs E base kn)
    (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) (H : kn_readable segs allkn kn rb rk n = true) :
    flat E (SA rb rk) (n : Int) ∧
      ∃ bs, rdn segs base (adenot E (SA rb rk)) n = some bs ∧ bs.length = n := by
  unfold kn_readable at H
  have PT : flat E (SA rb rk) (n : Int) ∧
      ∀ j, j < n → rd1 segs base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
    rw [Bool.or_eq_true] at H
    rcases H with H | H
    · obtain ⟨K, hKmem, hK⟩ := List.any_eq_true.mp H
      exact kentry_readable_sound segs E M0 allkn base rb rk n K Hall (Hkn K hKmem) Hn1 Hn8 hK
    · obtain ⟨h1, h2, _⟩ := know_bytes_cov_both segs true E base kn rb n rk Hkn H Hn1
      exact ⟨h1, h2 rfl⟩
  obtain ⟨Hfl, Hpt⟩ := PT
  refine ⟨Hfl, ?_⟩
  have hbound : bv_unsigned (adenot E (SA rb rk)) + (n : Int) ≤ 2 ^ 64 := by
    rw [flat_u E (SA rb rk) (n : Int) Hfl]
    obtain ⟨g1, g2, g3, g4⟩ := Hfl
    exact g4
  have Hpt' : ∀ j, j < n →
      rd1 segs base (Z_to_bv 64 (bv_unsigned (adenot E (SA rb rk)) + (j : Int))) ≠ none := by
    intro j hj
    rw [flat_u E (SA rb rk) (n : Int) Hfl]
    exact Hpt j hj
  exact rdn_defined segs base n (adenot E (SA rb rk)) hbound Hpt'

/-- The range is overlay-defined (hence writable): one covering entry
    (`kentry_overlay_sound`) or the bytewise sweep, then `store_ok_of_all`
    turns bytewise definedness of the overlay into `store_ok`. -/
theorem kn_overlay_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (allkn kn : List kentry) (base : word → Option byte) (rb : expr) (rk : Int) (n : Nat)
    (Hall : know_ok segs E M0 allkn) (Hkn : know_ok segs E base kn)
    (Hn1 : 1 ≤ n) (Hn8 : n ≤ 8) (H : kn_overlay segs allkn kn rb rk n = true) :
    flat E (SA rb rk) (n : Int) ∧
      store_ok segs base (adenot E (SA rb rk)) n = true := by
  unfold kn_overlay at H
  have PT : flat E (SA rb rk) (n : Int) ∧
      ∀ j, j < n → base (Z_to_bv 64 (estart E (SA rb rk) + (j : Int))) ≠ none := by
    rw [Bool.or_eq_true] at H
    rcases H with H | H
    · obtain ⟨K, hKmem, hK⟩ := List.any_eq_true.mp H
      exact kentry_overlay_sound segs E M0 allkn base rb rk n K Hall (Hkn K hKmem) Hn1 Hn8 hK
    · obtain ⟨h1, _, h3⟩ := know_bytes_cov_both segs false E base kn rb n rk Hkn H Hn1
      exact ⟨h1, h3 rfl⟩
  obtain ⟨Hfl, Hpt⟩ := PT
  refine ⟨Hfl, ?_⟩
  have hu : ((adenot E (SA rb rk)).toNat : Int) = estart E (SA rb rk) :=
    flat_u E (SA rb rk) (n : Int) Hfl
  apply store_ok_of_all segs base n (adenot E (SA rb rk)) ?_ ?_
  · rw [hu, ← two64_eq_natCast, two64_eq]
    obtain ⟨g1, g2, g3, g4⟩ := Hfl
    exact g4
  · intro x Hx1 Hx2
    rw [hu] at Hx1 Hx2
    have hd0 : 0 ≤ (x.toNat : Int) - estart E (SA rb rk) := by omega
    have hdn : ((x.toNat : Int) - estart E (SA rb rk)).toNat < n := by omega
    have hdt : ((((x.toNat : Int) - estart E (SA rb rk)).toNat : Nat) : Int)
        = (x.toNat : Int) - estart E (SA rb rk) := Int.toNat_of_nonneg hd0
    have hb := Hpt _ hdn
    have hxeq : Z_to_bv 64 (estart E (SA rb rk)
        + ((((x.toNat : Int) - estart E (SA rb rk)).toNat : Nat) : Int)) = x := by
      rw [hdt,
        show estart E (SA rb rk) + ((x.toNat : Int) - estart E (SA rb rk))
          = (x.toNat : Int) from by omega]
      exact Z_to_bv_unsigned x
    rw [hxeq] at hb
    intro hw
    have hbn : base x = none := by
      unfold wview at hw
      cases hbx : base x with
      | some b =>
        rw [hbx] at hw
        exact absurd hw (by simp)
      | none => rfl
    exact hb hbn

/-- A discharged obligation is true under the extended valuation: the
    knowledge decides flatness / writability (`kn_readable_sound`,
    `kn_overlay_sound`), and the fresh read variable of THIS step takes the
    bytes `Hrb` supplies under the base valuation `E0` (moved to `E` by
    `edenot_evars_lt`, since the address mentions only variables below
    `s_next`). -/
theorem x_discharge_sound (segs : List Segment) (E0 E : env) (base : word → Option byte)
    (ss ss' : sym_state) (rb : Option (saddr × Nat × Bool)) (sc : sidecond)
    (Hkn : know_ok segs E base ss.s_know)
    (Hag : eagree ss.s_next E0 E)
    (Hd : x_dischargeable segs ss ss' rb sc = true)
    (Hrb : ∀ (a : saddr) (n : Nat) (sx : Bool), rb = some (a, n, sx) →
      ∃ bs, rdn segs base (adenot E0 a) n = some bs ∧
        E.ev ss.s_next = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))) :
    sc_denot segs base E sc := by
  have Hfk : know_ok segs E base (facts_of ss.s_know) := facts_of_ok segs E base ss.s_know Hkn
  cases sc with
  | SCBr t c a b => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
  | SCFlat a n =>
    cases n with
    | ELit z =>
      simp only [x_dischargeable] at Hd
      obtain ⟨Hn, Hcov⟩ := (Bool.and_eq_true ..).mp Hd
      obtain ⟨Hz1, Hz8⟩ := (Bool.and_eq_true ..).mp Hn
      rw [decide_eq_true_eq] at Hz1 Hz8
      have hz0 : 0 ≤ z := by omega
      have hzt : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg hz0
      have hz1n : 1 ≤ z.toNat := by omega
      have hz8n : z.toNat ≤ 8 := by omega
      have hred := (kn_readable_sound segs E base (facts_of ss.s_know) ss.s_know
        base a.a_base a.a_off z.toNat Hfk Hkn hz1n hz8n Hcov).1
      have hsa : (SA a.a_base a.a_off) = a := rfl
      rw [hsa] at hred
      show flat E a (elenZ E (.ELit z))
      rw [show (elenZ E (.ELit z)) = ((z.toNat : Nat) : Int) from by
        rw [elenZ_lit,
          show z % 2 ^ 64 = ((z.toNat : Nat) : Int) from by
            rw [hzt]
            exact Int.emod_eq_of_lt hz0 (by omega)]]
      exact hred
    | EVar v => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EAlu o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EAluw o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EMd o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EMdw o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EExt sx lo nn e => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EBlob sx k i nn => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
  | SCDisj a1 n1 a2 n2 => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
  | SCInside a1 n1 a2 n2 => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
  | SCStoreOk a n =>
    simp only [x_dischargeable] at Hd
    obtain ⟨Hn, Hcov⟩ := (Bool.and_eq_true ..).mp Hd
    obtain ⟨Hn1, Hn8⟩ := (Bool.and_eq_true ..).mp Hn
    rw [decide_eq_true_eq] at Hn1 Hn8
    have hsa : (SA a.a_base a.a_off) = a := rfl
    have hso := (kn_overlay_sound segs E base (facts_of ss.s_know) ss.s_know
      base a.a_base a.a_off n Hfk Hkn Hn1 Hn8 Hcov).2
    rw [hsa] at hso
    exact hso
  | SCEq a b => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
  | SCReadBase a n sx e =>
    cases e with
    | EVar j =>
      simp only [x_dischargeable] at Hd
      obtain ⟨Hpre, _Hcov⟩ := (Bool.and_eq_true ..).mp Hd
      obtain ⟨Hpre2, Hn⟩ := (Bool.and_eq_true ..).mp Hpre
      obtain ⟨Hpre3, Hvar⟩ := (Bool.and_eq_true ..).mp Hpre2
      obtain ⟨Hpre4, Hjlt⟩ := (Bool.and_eq_true ..).mp Hpre3
      obtain ⟨Hrbm, Hj⟩ := (Bool.and_eq_true ..).mp Hpre4
      obtain ⟨Hn1, Hn8⟩ := (Bool.and_eq_true ..).mp Hn
      rw [beq_iff_eq] at Hj
      cases rb with
      | none =>
        simp only [x_dischargeable] at Hrbm
        exact absurd Hrbm (by decide)
      | some p =>
        obtain ⟨a', n', sx'⟩ := p
        simp only [] at Hrbm
        obtain ⟨Hpre5, Hsx⟩ := (Bool.and_eq_true ..).mp Hrbm
        obtain ⟨Hab, Hnb⟩ := (Bool.and_eq_true ..).mp Hpre5
        have ha' : a' = a := saddr_eqb_eq Hab
        rw [beq_iff_eq] at Hnb
        rw [beq_iff_eq] at Hsx
        obtain ⟨bs, Hbs, Hv⟩ := Hrb a n sx (by rw [ha', Hnb, Hsx])
        refine ⟨bs, ?_, ?_⟩
        · show rdn segs base (adenot E a) n = some bs
          rw [show adenot E a = adenot E0 a from by
            unfold adenot
            rw [edenot_evars_lt Hag Hvar]]
          exact Hbs
        · show Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = edenot E (.EVar j)
          rw [Hj]
          exact Hv.symm
    | ELit z => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EAlu o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EAluw o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EMd o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EMdw o x y => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EExt sx lo nn e => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)
    | EBlob sx k i nn => simp only [x_dischargeable] at Hd; exact absurd Hd (by decide)

/-- `cap_rd`'s successor branch, before the `rd_of`/`esize_le` tests: stated
    as a `rfl` equation so the proof can rewrite the goal (which mentions
    `cap_rd` twice) instead of fighting the stuck `match Nat.succ K' with`. -/
theorem cap_rd_succ (K' : Nat) (i : Instr) (ss : sym_state) :
    cap_rd (K' + 1) i ss
      = (match rd_of i with
         | none => ss
         | some rd =>
             if bv_eqb rd 0 = true then ss
             else if esize_le (sr_get ss.s_regs rd) (K' + 1) = true then ss
             else ⟨ss.s_pc, sr_upd ss.s_regs (ridx rd) (.EVar ss.s_next),
                   ss.s_log, ss.s_know, ss.s_next + 1, ss.s_resv⟩) := rfl

/-- The register cap preserves `st_okX`, at the price of a fresh variable:
the capped register becomes `EVar (s_next ss')` — which mentions only
variables below the new counter `s_next ss' + 1`, so the extension can name
it (`eupd`).  The three `ss'`-preserving branches keep the valuation `E1`
itself. -/
theorem cap_rd_sound (segs : List Segment) (K : Nat) (i : Instr) (E1 : env)
    (base rom : word → Option byte) (ss' : sym_state) (ms' : machine_state)
    (ALL : ∀ E'', eagree ss'.s_next E1 E'' → st_okR segs E'' base rom ss' ms') :
    ∃ E', eagree ss'.s_next E1 E' ∧ ss'.s_next ≤ (cap_rd K i ss').s_next ∧
      st_okX segs E' base rom (cap_rd K i ss') ms' := by
  have SAME : ∃ E', eagree ss'.s_next E1 E' ∧ ss'.s_next ≤ ss'.s_next ∧
      st_okX segs E' base rom ss' ms' :=
    ⟨E1, eagree_refl _ _, Nat.le_refl _, fun E'' Ha => ALL E'' Ha⟩
  cases K with
  | zero => exact SAME
  | succ K' =>
    rw [cap_rd_succ]
    cases hrd : rd_of i with
    | none => exact SAME
    | some rd =>
      simp only []
      by_cases h0 : bv_eqb rd 0 = true
      · rw [ite_eq_left h0]; exact SAME
      · rw [ite_eq_right h0]
        by_cases hsz : esize_le (sr_get ss'.s_regs rd) (K' + 1) = true
        · rw [ite_eq_left hsz]; exact SAME
        · rw [ite_eq_right hsz]
          refine ⟨eupd E1 ss'.s_next (edenot E1 (sr_get ss'.s_regs rd)),
            eagree_upd E1 ss'.s_next _, by show ss'.s_next ≤ ss'.s_next + 1; omega, ?_⟩
          intro E'' Ha''
          have Ha1 : eagree ss'.s_next E1 E'' :=
            eagree_trans (eagree_upd E1 ss'.s_next _)
              (eagree_le Ha'' (by show ss'.s_next ≤ ss'.s_next + 1; omega))
          obtain ⟨Hregs, _Hmem, Hlf, Hkn, Heq⟩ :=
            st_okR_parts segs E'' base rom ss' ms' (ALL E'' Ha1)
          obtain ⟨Hregs1, _⟩ :=
            st_okR_parts segs E1 base rom ss' ms' (ALL E1 (eagree_refl _ _))
          refine ⟨ms'.ms_regs, Heq, ?_, Hlf, Hkn⟩
          refine regs_ok_pin E'' ss'.s_regs ms'.ms_regs rd (.EVar ss'.s_next) Hregs ?_
          have Hvv : E''.ev ss'.s_next
              = (eupd E1 ss'.s_next (edenot E1 (sr_get ss'.s_regs rd))).ev ss'.s_next :=
            (Ha''.1 ss'.s_next (by show ss'.s_next < ss'.s_next + 1; omega)).symm
          rw [show edenot E'' (.EVar ss'.s_next) = E''.ev ss'.s_next from rfl, Hvv,
            eupd_at]
          exact Hregs1 rd

/-! ## Part P5c (cont.): the XSound entry lemmas and the extension-mode step


    `find_readbase_In` / `x_filter_nil` are the two small facts that let
    `sym_stepX_sound` pick the fresh read of THIS step out of the residual
    obligations; `sym_stepX_sound` itself composes them with the coverage
    block above (`kn_readable_sound`, `x_discharge_sound`) and the classic
    step lemma `sym_step_soundR`. -/

/-- The obligation `find_readbase` returns IS one of the list. -/
theorem find_readbase_In (i : Nat) (scs : List sidecond) (a : saddr) (n : Nat) (sx : Bool)
    (H : find_readbase i scs = some (a, n, sx)) :
    sidecond.SCReadBase a n sx (.EVar i) ∈ scs := by
  induction scs with
  | nil => simp only [find_readbase] at H; exact absurd H (by simp)
  | cons sc rest ih =>
    cases sc with
    | SCBr t c x y =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCFlat sa ne =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCDisj a1 n1 a2 n2 =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCInside a1 n1 a2 n2 =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCStoreOk sa ne =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCEq x y =>
      exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
    | SCReadBase sa ne sxb e =>
      cases e with
      | EVar j =>
        simp only [find_readbase] at H
        by_cases hj : (j == i) = true
        · rw [ite_eq_left hj] at H
          simp only [Option.some.injEq, Prod.mk.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          have hji : j = i := beq_iff_eq.mp hj
          subst hji
          exact List.mem_cons_self ..
        · rw [ite_eq_right hj] at H
          exact List.mem_cons_of_mem _ (ih H)
      | ELit z =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EAlu o x y =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EAluw o x y =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EMd o x y =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EMdw o x y =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EExt sx' lo nn e' =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))
      | EBlob sx' k i' nn =>
        exact List.mem_cons_of_mem _ (ih (by simpa only [find_readbase] using H))

/-- If `x_filter` dropped everything, every obligation it saw was
    dischargeable. -/
theorem x_filter_nil (segs : List Segment) (ss ss' : sym_state) (scs : List sidecond)
    (sc : sidecond) (H : x_filter segs ss ss' scs = []) (Hin : sc ∈ scs) :
    x_dischargeable segs ss ss' (find_readbase ss.s_next scs) sc = true := by
  cases scs with
  | nil => exact absurd Hin (by simp)
  | cons sc0 rest =>
    simp only [x_filter] at H
    have hf := (List.filter_eq_nil_iff.mp H) sc Hin
    cases hd : x_dischargeable segs ss ss' (find_readbase ss.s_next (sc0 :: rest)) sc with
    | true => rfl
    | false =>
      rw [hd] at hf
      exact absurd hf (by simp)

/-- What a discharged `SCReadBase` obligation of THIS step already tells us:
    the fresh variable moved the counter, the address mentions only variables
    below it, the length is `1..8`, and the knowledge proves the read.

    the extraction is done one conjunct at a time by CASE-SPLITTING
    the Boolean to `false` (which makes the whole `&&`-chain false, whatever
    its nesting) — the reduced chain's association is not worth depending on. -/
theorem x_dischargeable_read_base (segs : List Segment) (ss ss' : sym_state) (a : saddr)
    (n : Nat) (sx : Bool)
    (H : x_dischargeable segs ss ss' (some (a, n, sx))
          (sidecond.SCReadBase a n sx (.EVar ss.s_next)) = true) :
    ss.s_next < ss'.s_next ∧ evars_lt ss.s_next a.a_base = true ∧ 1 ≤ n ∧ n ≤ 8 ∧
      kn_readable segs (facts_of ss.s_know) ss.s_know a.a_base a.a_off n = true := by
  simp only [x_dischargeable] at H
  have hlt : decide (ss.s_next < ss'.s_next) = true := by
    cases h : decide (ss.s_next < ss'.s_next) with
    | false => rw [h] at H; exact absurd H (by simp)
    | true => rfl
  have hev : evars_lt ss.s_next a.a_base = true := by
    cases h : evars_lt ss.s_next a.a_base with
    | false => rw [h] at H; exact absurd H (by simp)
    | true => rfl
  have h1b : decide (1 ≤ n) = true := by
    cases h : decide (1 ≤ n) with
    | false => rw [h] at H; exact absurd H (by simp)
    | true => rfl
  have h8b : decide (n ≤ 8) = true := by
    cases h : decide (n ≤ 8) with
    | false => rw [h] at H; exact absurd H (by simp)
    | true => rfl
  have hkr : kn_readable segs (facts_of ss.s_know) ss.s_know a.a_base a.a_off n = true := by
    cases h : kn_readable segs (facts_of ss.s_know) ss.s_know a.a_base a.a_off n with
    | false => rw [h] at H; exact absurd H (by simp)
    | true => rfl
  exact ⟨of_decide_eq_true hlt, hev, of_decide_eq_true h1b, of_decide_eq_true h8b, hkr⟩

/-- `cap_rd` never lowers the fresh-variable counter. -/
theorem cap_rd_next_ge (K : Nat) (i : Instr) (ss : sym_state) :
    ss.s_next ≤ (cap_rd K i ss).s_next := by
  cases K with
  | zero => exact Nat.le_refl _
  | succ K' =>
    rw [cap_rd_succ]
    cases hrd : rd_of i with
    | none => exact Nat.le_refl _
    | some rd =>
      simp only []
      by_cases h0 : bv_eqb rd 0 = true
      · rw [ite_eq_left h0]; exact Nat.le_refl _
      · rw [ite_eq_right h0]
        by_cases hsz : esize_le (sr_get ss.s_regs rd) (K' + 1) = true
        · rw [ite_eq_left hsz]; exact Nat.le_refl _
        · rw [ite_eq_right hsz]
          show ss.s_next ≤ ss.s_next + 1
          omega

/-- The counter of an extension-mode step only grows.  The `sym_stepX`
    branch is peeled with `generalize` + `cases` (a `match`-hypothesis is not
    rewritten by `cases h : t`). -/
theorem sym_stepX_next_ge (segs : List Segment) (K : Nat) (i : Instr) (ss : sym_state)
    (scr : scripts) (ssx : sym_state) (scsx : List sidecond) (scrx : scripts)
    (H : sym_stepX segs K i ss scr = .SOk ssx scsx scrx) : ss.s_next ≤ ssx.s_next := by
  unfold sym_stepX at H
  generalize hst : sym_step segs i ss scr = r at H
  cases r with
  | SStop =>
    dsimp only at H
    exact absurd (show stepres.SStop = stepres.SOk ssx scsx scrx from H) (by simp)
  | SOk ss' scs scr2 =>
    dsimp only at H
    by_cases hle : ss.s_next ≤ ss'.s_next
    · rw [ite_eq_left hle] at H
      simp only [stepres.SOk.injEq] at H
      obtain ⟨hxx, -, -⟩ := H
      rw [← hxx]
      exact Nat.le_trans hle (cap_rd_next_ge K i ss')
    · rw [ite_eq_right hle] at H
      exact absurd (show stepres.SStop = stepres.SOk ssx scsx scrx from H) (by simp)

/-- **The extension-mode step is sound.**  The classic step lemma gives the
    machine step; the extra work is the VALUATION: this step's fresh read (if
    any) is named by `eupd` with the bytes the knowledge proves readable, and
    under every extension of that valuation the residual obligations hold
    (`x_discharge_sound`).  The destination register is then capped by
    `cap_rd_sound`. -/
theorem sym_stepX_sound (segs : List Segment) (K : Nat) (E : env)
    (base rom : word → Option byte) (ss : sym_state) (ms : machine_state)
    (i : Instr) (ssx : sym_state) (scr' : scripts) (w : BitVec 32)
    (Hf : fetch_word segs (Z_to_bv 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (i, 4))
    (Hs : sym_stepX segs K i ss scr_nil = .SOk ssx [] scr')
    (HX : st_okX segs E base rom ss ms) :
    ∃ E' ms', eagree ss.s_next E E' ∧ ss.s_next ≤ ssx.s_next ∧
      RiscvSemantics.step segs ms = .MachineOk ms' ∧ st_okX segs E' base rom ssx ms' := by
  obtain ⟨-, -, -, Hkn0, -⟩ :=
    st_okR_parts segs E base rom ss ms (st_okX_R segs E base rom ss ms HX)
  unfold sym_stepX at Hs
  generalize hst : sym_step segs i ss scr_nil = r at Hs
  cases r with
  | SStop =>
    dsimp only at Hs
    exact absurd (show stepres.SStop = stepres.SOk ssx [] scr' from Hs) (by simp)
  | SOk ss' scs scr2 =>
    dsimp only at Hs
    by_cases hle : ss.s_next ≤ ss'.s_next
    · rw [ite_eq_left hle] at Hs
      simp only [stepres.SOk.injEq] at Hs
      obtain ⟨hxx, hfil, -⟩ := Hs
      subst hxx
      -- the valuation: this step's fresh read is named
      have HV : ∃ E1, eagree ss.s_next E E1 ∧
          ∀ E'', eagree ss'.s_next E1 E'' → scs_denot segs base E'' scs := by
        cases hrb : find_readbase ss.s_next scs with
        | none =>
          refine ⟨E, eagree_refl _ _, ?_⟩
          intro E'' Ha''
          have HaE : eagree ss.s_next E E'' := eagree_le Ha'' hle
          obtain ⟨-, -, -, Hkn'', -⟩ := st_okR_parts segs E'' base rom ss ms (HX E'' HaE)
          intro sc hsc
          have hdd : x_dischargeable segs ss ss' (find_readbase ss.s_next scs) sc = true :=
            x_filter_nil segs ss ss' scs sc hfil hsc
          rw [hrb] at hdd
          exact x_discharge_sound segs E E'' base ss ss' none sc Hkn'' HaE hdd
            (fun a n sx h => absurd h (by simp))
        | some p =>
          obtain ⟨a, n, sx⟩ := p
          have hIn : sidecond.SCReadBase a n sx (.EVar ss.s_next) ∈ scs :=
            find_readbase_In ss.s_next scs a n sx hrb
          have hdis : x_dischargeable segs ss ss' (some (a, n, sx))
              (sidecond.SCReadBase a n sx (.EVar ss.s_next)) = true := by
            rw [← hrb]
            exact x_filter_nil segs ss ss' scs _ hfil hIn
          obtain ⟨hlt, -, hn1, hn8, hkr⟩ :=
            x_dischargeable_read_base segs ss ss' a n sx hdis
          obtain ⟨-, bs, Hbs, -⟩ :=
            kn_readable_sound segs E base (facts_of ss.s_know) ss.s_know base a.a_base a.a_off n
              (facts_of_ok segs E base ss.s_know Hkn0) Hkn0 hn1 hn8 hkr
          refine ⟨eupd E ss.s_next (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))),
            eagree_upd E ss.s_next _, ?_⟩
          intro E'' Ha''
          have HaE : eagree ss.s_next E E'' :=
            eagree_trans (eagree_upd E ss.s_next _) (eagree_le Ha'' hle)
          obtain ⟨-, -, -, Hkn'', -⟩ := st_okR_parts segs E'' base rom ss ms (HX E'' HaE)
          intro sc hsc
          have hdd : x_dischargeable segs ss ss' (find_readbase ss.s_next scs) sc = true :=
            x_filter_nil segs ss ss' scs sc hfil hsc
          rw [hrb] at hdd
          exact x_discharge_sound segs E E'' base ss ss' (some (a, n, sx)) sc Hkn'' HaE hdd
            (fun a' n' sx' hEq => by
              simp only [Option.some.injEq, Prod.mk.injEq] at hEq
              obtain ⟨rfl, rfl, rfl⟩ := hEq
              exact ⟨bs, Hbs, by rw [← (Ha''.1 ss.s_next hlt), eupd_at]⟩)
      obtain ⟨E1, Ha1, Hscs⟩ := HV
      -- the classic step, under `E1` and under every extension of it
      obtain ⟨msA, Hstep, -⟩ :=
        sym_step_soundR segs E1 base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd hst
          (Hscs E1 (eagree_refl _ _)) (HX E1 Ha1)
      have ALL : ∀ E'', eagree ss'.s_next E1 E'' → st_okR segs E'' base rom ss' msA := by
        intro E'' Ha''
        have HaE : eagree ss.s_next E E'' := eagree_trans Ha1 (eagree_le Ha'' hle)
        obtain ⟨ms2, Hstep2, HR2⟩ :=
          sym_step_soundR segs E'' base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd hst
            (Hscs E'' Ha'') (HX E'' HaE)
        rw [Hstep] at Hstep2
        cases Hstep2
        exact HR2
      obtain ⟨E', Ha', Hle', HX'⟩ := cap_rd_sound segs K i E1 base rom ss' msA ALL
      exact ⟨E', msA, eagree_trans Ha1 (eagree_le Ha' hle), Nat.le_trans hle Hle', Hstep, HX'⟩
    · rw [ite_eq_right hle] at Hs
      exact absurd (show stepres.SStop = stepres.SOk ssx [] scr' from Hs) (by simp)
/-! ### The XSound drivers

    The extension-mode counterpart of `sgo_ok`: the run may EXTEND the
    valuation (this step's fresh reads are named), so the invariant carries
    the extension `E'` and the counter bound as well. -/

/-- Driver invariant in extension mode: clean exit, the counter grew, and
    every run of the machine from a `st_okX` state extends the valuation,
    simulates the steps and lands in `st_okX` at the result. -/
def sgoX_ok (segs : List Segment) (base rom : word → Option byte)
    (ss r : sym_state) : Prop :=
  r.s_resv = none ∧ ss.s_next ≤ r.s_next ∧
    (∀ E ms, st_okX segs E base rom ss ms →
      ∃ E' mr, eagree ss.s_next E E' ∧ CatSim.msteps segs ms mr ∧
        st_okX segs E' base rom r mr)

theorem sgoX_stop_ok (segs : List Segment) (base rom : word → Option byte)
    (ss ck : sym_state) :
    (if s_clean ss then ss else ck) = ck ∨
      sgoX_ok segs base rom ss (if s_clean ss then ss else ck) := by
  by_cases hc : s_clean ss = true
  · rw [ite_eq_left hc]
    right
    refine ⟨(s_clean_None ss).mp hc, Nat.le_refl _, ?_⟩
    intro E ms Hst
    exact ⟨E, ms, eagree_refl _ _, CatSim.msteps.mst_refl ms, Hst⟩
  · rw [ite_eq_right hc]
    left; rfl

theorem sym_execTX_go_sound (segs : List Segment) (base rom : word → Option byte)
    (t : itab) (K : Nat) (Ht : itab_sound segs t) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execTX_go segs t K fuel first stops ss ck = ck ∨
        sgoX_ok segs base rom ss (sym_execTX_go segs t K fuel first stops ss ck) := by
  intro fuel
  induction fuel with
  | zero =>
    intro first stops ss ck
    simp only [sym_execTX_go]
    exact sgoX_stop_ok segs base rom ss ck
  | succ f ih =>
    intro first stops ss ck
    simp only [sym_execTX_go]
    by_cases hstop : (!first && stops.any (· == ss.s_pc)) = true
    · rw [ite_eq_left hstop]; exact sgoX_stop_ok segs base rom ss ck
    · rw [ite_eq_right hstop]
      cases hl : itab_lookup t ss.s_pc with
      | none => simp only []; exact sgoX_stop_ok segs base rom ss ck
      | some i =>
        simp only []
        obtain ⟨w, hf, hef, hd⟩ := itab_entry_parts segs ss.s_pc i (Ht ss.s_pc i hl)
        cases hs : sym_stepX segs K i ss scr_nil with
        | SStop => simp only []; exact sgoX_stop_ok segs base rom ss ck
        | SOk ss2 scs2 scr2 =>
          cases scs2 with
          | nil =>
            simp only []
            have ONE : ∀ E ms, st_okX segs E base rom ss ms →
                ∃ E' msA, eagree ss.s_next E E' ∧ CatSim.msteps segs ms msA ∧
                  st_okX segs E' base rom ss2 msA := by
              intro E ms Hst
              obtain ⟨E', msA, Ha, -, HstepA, HstA⟩ :=
                sym_stepX_sound segs K E base rom ss ms i ss2 scr2 w hf hef hd hs Hst
              refine ⟨E', msA, Ha, CatSim.msteps.mst_step ms msA msA ?_ HstepA
                (CatSim.msteps.mst_refl msA), HstA⟩
              obtain ⟨-, -, -, -, hms⟩ :=
                st_okR_parts segs E base rom ss ms (st_okX_R segs E base rom ss ms Hst)
              rw [hms]
              rfl
            cases hgo : sym_execTX_go segs t K f false stops ss2
                (if s_clean ss2 then ss2 else ck) with
            | mk r =>
              have IH := ih false stops ss2 (if s_clean ss2 then ss2 else ck)
              rw [hgo] at IH
              rcases IH with hck | ⟨Hr, Hle2, Hrun⟩
              · by_cases hc2 : s_clean ss2 = true
                · rw [ite_eq_left hc2] at hck
                  rw [hck]
                  right
                  exact ⟨(s_clean_None ss2).mp hc2,
                    sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs,
                    fun E ms Hst => ONE E ms Hst⟩
                · rw [ite_eq_right hc2] at hck
                  left; exact hck
              · right
                refine ⟨Hr, Nat.le_trans
                  (sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs) Hle2, ?_⟩
                intro E ms Hst
                obtain ⟨E', msA, Ha, HmsA, HstA⟩ := ONE E ms Hst
                obtain ⟨E2, mr, Ha2, Hmr, Hstr⟩ := Hrun E' msA HstA
                exact ⟨E2, mr, eagree_trans Ha (eagree_le Ha2
                    (sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs)),
                  CatSim.msteps_trans segs ms msA mr HmsA Hmr, Hstr⟩
          | cons x l => simp only []; exact sgoX_stop_ok segs base rom ss ck

theorem sym_execTX_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (K : Nat) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state) (Ht : itab_sound segs t)
    (Hst : ∀ E', eagree ss.s_next E E' → st_ok segs E' base rom ss ms) :
    ∃ E' ms', eagree ss.s_next E E' ∧
      ss.s_next ≤ (sym_execTX segs t K fuel first stops ss).s_next ∧
      CatSim.msteps segs ms ms' ∧
      (∀ E'', eagree (sym_execTX segs t K fuel first stops ss).s_next E' E'' →
        st_ok segs E'' base rom (sym_execTX segs t K fuel first stops ss) ms') := by
  unfold sym_execTX
  have HX : st_okX segs E base rom (clr ss) ms := st_okX_clr segs E base rom ss ms Hst
  have H := sym_execTX_go_sound segs base rom t K Ht fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, Hle, Hrun⟩
  · rw [Hck]
    exact ⟨E, ms, eagree_refl _ _, Nat.le_refl _, CatSim.msteps.mst_refl ms,
      fun E'' Ha'' => st_okR_ok segs E'' base rom (clr ss) ms (HX E'' Ha'') rfl⟩
  · obtain ⟨E', mr, Ha, Hmr, HX'⟩ := Hrun E ms HX
    exact ⟨E', mr, Ha, Hle, Hmr,
      fun E'' Ha'' => st_okR_ok segs E'' base rom _ mr (HX' E'' Ha'') Hr⟩

theorem sym_execTX_ex (segs : List Segment) (E : env) (base rom : word → Option byte)
    (t : itab) (K : Nat) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state) (Ht : itab_sound segs t)
    (Hst : ∀ E', eagree ss.s_next E E' → st_ok segs E' base rom ss ms) :
    ∃ E' R, eagree ss.s_next E E' ∧
      ss.s_next ≤ (sym_execTX segs t K fuel first stops ss).s_next ∧
      regs_ok E' (sym_execTX segs t K fuel first stops ss).s_regs R ∧
      log_flat E' (sym_execTX segs t K fuel first stops ss).s_log ∧
      know_ok segs E' base (sym_execTX segs t K fuel first stops ss).s_know ∧
      CatSim.msteps segs ms
        (mkst R (Z_to_bv 64 (sym_execTX segs t K fuel first stops ss).s_pc)
          (mem_denot E' base (sym_execTX segs t K fuel first stops ss).s_log) rom) ∧
      (∀ E'', eagree (sym_execTX segs t K fuel first stops ss).s_next E' E'' →
        st_ok segs E'' base rom (sym_execTX segs t K fuel first stops ss)
          (mkst R (Z_to_bv 64 (sym_execTX segs t K fuel first stops ss).s_pc)
            (mem_denot E' base (sym_execTX segs t K fuel first stops ss).s_log) rom)) := by
  obtain ⟨E', ms', Ha, Hle, Hms, HALL⟩ :=
    sym_execTX_sound segs E base rom t K fuel first stops ss ms Ht Hst
  obtain ⟨R, Heq, Hregs, Hlf, Hkn⟩ := HALL E' (eagree_refl _ _)
  -- `Z_to_bv` is an `abbrev`, so the `mkst` of the statement is only
  -- DEFINITIONALLY the `BitVec.ofInt` spelling of `st_ok`; bridge it once.
  have hEq : mkst R (Z_to_bv 64 (sym_execTX segs t K fuel first stops ss).s_pc)
        (mem_denot E' base (sym_execTX segs t K fuel first stops ss).s_log) rom
      = mkst R (BitVec.ofInt 64 (sym_execTX segs t K fuel first stops ss).s_pc)
        (mem_denot E' base (sym_execTX segs t K fuel first stops ss).s_log) rom := rfl
  refine ⟨E', R, Ha, Hle, Hregs, Hlf, Hkn, ?_, ?_⟩
  · rw [hEq, ← Heq]; exact Hms
  · intro E'' Ha''
    rw [hEq, ← Heq]
    exact HALL E'' Ha''

theorem sym_execTX_resv (segs : List Segment) (t : itab) (K : Nat) (fuel : Nat)
    (first : Bool) (stops : List Int) (ss : sym_state) (Ht : itab_sound segs t) :
    (sym_execTX segs t K fuel first stops ss).s_resv = none := by
  unfold sym_execTX
  have H := sym_execTX_go_sound segs (fun _ => none) (fun _ => none) t K Ht
    fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, -⟩
  · rw [Hck]; rfl
  · exact Hr

theorem sym_execSX_go_sound (segs : List Segment) (base rom : word → Option byte) (K : Nat) :
    ∀ (fuel : Nat) (first : Bool) (stops : List Int) (ss ck : sym_state),
      sym_execSX_go segs K fuel first stops ss ck = ck ∨
        sgoX_ok segs base rom ss (sym_execSX_go segs K fuel first stops ss ck) := by
  intro fuel
  induction fuel with
  | zero =>
    intro first stops ss ck
    simp only [sym_execSX_go]
    exact sgoX_stop_ok segs base rom ss ck
  | succ f ih =>
    intro first stops ss ck
    simp only [sym_execSX_go]
    by_cases hstop : (!first && stops.any (· == ss.s_pc)) = true
    · rw [ite_eq_left hstop]; exact sgoX_stop_ok segs base rom ss ck
    · rw [ite_eq_right hstop]
      cases hf : fetch_word segs (Z_to_bv 64 ss.s_pc) with
      | none => simp only []; exact sgoX_stop_ok segs base rom ss ck
      | some w =>
        simp only []
        by_cases he : is_ecall w = true
        · rw [ite_eq_left he]; exact sgoX_stop_ok segs base rom ss ck
        · rw [ite_eq_right he]
          have hef : is_ecall w = false := by cases h : is_ecall w <;> simp_all
          cases hd : decodeAny w with
          | none => simp only []; exact sgoX_stop_ok segs base rom ss ck
          | some p =>
            obtain ⟨i, sz⟩ := p
            simp only []
            by_cases hsz : (!(sz == 4)) = true
            · rw [ite_eq_left hsz]; exact sgoX_stop_ok segs base rom ss ck
            · rw [ite_eq_right hsz]
              have hsz4 : sz = 4 := sym_exec_sz_eq sz hsz
              rw [hsz4] at hd
              cases hs : sym_stepX segs K i ss scr_nil with
              | SStop => simp only []; exact sgoX_stop_ok segs base rom ss ck
              | SOk ss2 scs2 scr2 =>
                cases scs2 with
                | nil =>
                  simp only []
                  have ONE : ∀ E ms, st_okX segs E base rom ss ms →
                      ∃ E' msA, eagree ss.s_next E E' ∧ CatSim.msteps segs ms msA ∧
                        st_okX segs E' base rom ss2 msA := by
                    intro E ms Hst
                    obtain ⟨E', msA, Ha, -, HstepA, HstA⟩ :=
                      sym_stepX_sound segs K E base rom ss ms i ss2 scr2 w hf hef hd hs Hst
                    refine ⟨E', msA, Ha, CatSim.msteps.mst_step ms msA msA ?_ HstepA
                      (CatSim.msteps.mst_refl msA), HstA⟩
                    obtain ⟨-, -, -, -, hms⟩ :=
                      st_okR_parts segs E base rom ss ms (st_okX_R segs E base rom ss ms Hst)
                    rw [hms]
                    rfl
                  cases hgo : sym_execSX_go segs K f false stops ss2
                      (if s_clean ss2 then ss2 else ck) with
                  | mk r =>
                    have IH := ih false stops ss2 (if s_clean ss2 then ss2 else ck)
                    rw [hgo] at IH
                    rcases IH with hck | ⟨Hr, Hle2, Hrun⟩
                    · by_cases hc2 : s_clean ss2 = true
                      · rw [ite_eq_left hc2] at hck
                        rw [hck]
                        right
                        exact ⟨(s_clean_None ss2).mp hc2,
                          sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs,
                          fun E ms Hst => ONE E ms Hst⟩
                      · rw [ite_eq_right hc2] at hck
                        left; exact hck
                    · right
                      refine ⟨Hr, Nat.le_trans
                        (sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs) Hle2, ?_⟩
                      intro E ms Hst
                      obtain ⟨E', msA, Ha, HmsA, HstA⟩ := ONE E ms Hst
                      obtain ⟨E2, mr, Ha2, Hmr, Hstr⟩ := Hrun E' msA HstA
                      exact ⟨E2, mr, eagree_trans Ha (eagree_le Ha2
                          (sym_stepX_next_ge segs K i ss scr_nil ss2 [] scr2 hs)),
                        CatSim.msteps_trans segs ms msA mr HmsA Hmr, Hstr⟩
                | cons x l => simp only []; exact sgoX_stop_ok segs base rom ss ck

theorem sym_execSX_sound (segs : List Segment) (E : env) (base rom : word → Option byte)
    (K : Nat) (fuel : Nat) (first : Bool) (stops : List Int) (ss : sym_state)
    (ms : machine_state)
    (Hst : ∀ E', eagree ss.s_next E E' → st_ok segs E' base rom ss ms) :
    ∃ E' ms', eagree ss.s_next E E' ∧
      ss.s_next ≤ (sym_execSX segs K fuel first stops ss).s_next ∧
      CatSim.msteps segs ms ms' ∧
      (∀ E'', eagree (sym_execSX segs K fuel first stops ss).s_next E' E'' →
        st_ok segs E'' base rom (sym_execSX segs K fuel first stops ss) ms') := by
  unfold sym_execSX
  have HX : st_okX segs E base rom (clr ss) ms := st_okX_clr segs E base rom ss ms Hst
  have H := sym_execSX_go_sound segs base rom K fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, Hle, Hrun⟩
  · rw [Hck]
    exact ⟨E, ms, eagree_refl _ _, Nat.le_refl _, CatSim.msteps.mst_refl ms,
      fun E'' Ha'' => st_okR_ok segs E'' base rom (clr ss) ms (HX E'' Ha'') rfl⟩
  · obtain ⟨E', mr, Ha, Hmr, HX'⟩ := Hrun E ms HX
    exact ⟨E', mr, Ha, Hle, Hmr,
      fun E'' Ha'' => st_okR_ok segs E'' base rom _ mr (HX' E'' Ha'') Hr⟩

theorem sym_execSX_resv (segs : List Segment) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) :
    (sym_execSX segs K fuel first stops ss).s_resv = none := by
  unfold sym_execSX
  have H := sym_execSX_go_sound segs (fun _ => none) (fun _ => none) K
    fuel first stops (clr ss) (clr ss)
  rcases H with Hck | ⟨Hr, -⟩
  · rw [Hck]; rfl
  · exact Hr


/-! ### The joint END fact

    `end_hi` turns a `KRange (b + k + n) _ ehi` fact — the shape `mmap_null`
    records for a SYMBOLIC length — into an integer upper bound of
    `b+k, +n`.  The only work is the no-wrap arithmetic: the record is only
    taken when `0 ≤ lo1 + k` and `hi1 + k + h1 < 2^64`, so neither the
    `b+k` sum nor the full `b+k+n` sum wraps. -/

/-- **`end_hi_sound`.** -/
theorem end_hi_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b : expr) (k : Int) (n : expr) (lo1 hi1 h1 e : Int)
    (Hkn : know_ok segs E M kn) (Hb : base_range kn b = some (lo1, hi1))
    (Hx : xhi kn n = some h1) (H : end_hi kn b k n lo1 hi1 h1 = some e) :
    estart E (SA b k) + elenZ E n ≤ e := by
  have hu_lit : bv_unsigned (edenot E (.ELit k)) = k % 2 ^ 64 := u_lit64 k
  unfold end_hi at H
  split at H
  · exact absurd H (by simp)
  · split at H
    · split at H
      · rename_i hlt
        split at H
        · rename_i elo ehi hfr
          rw [Option.some.injEq] at H
          rw [← H]
          obtain ⟨A1, B1⟩ := base_range_sound segs E M kn b lo1 hi1 Hkn Hb
          have Xn : bv_unsigned (edenot E n) ≤ h1 := xhi_sound segs E M kn n h1 Hkn Hx
          have hlt' : hi1 + k + h1 < 2 ^ 64 := hlt
          have HB := (find_range_sound segs E M (facts_of kn)
            (mkAlu .ADD (mkAlu .ADD b (.ELit k)) n) elo ehi
            (facts_of_ok segs E M kn Hkn) hfr).2
          simp only [mkAlu_denot] at HB
          rw [SymExec.alu64_add_eq, SymExec.alu64_add_eq, u_add64, u_add64, hu_lit] at HB
          -- keep every bound in the `bv_unsigned` spelling the goal uses
          -- (`u64_range` states it as `↑(w.toNat)`, which `omega` treats as a
          -- DIFFERENT atom — see the header note)
          have hb0 : 0 ≤ bv_unsigned (edenot E b) := (u64_range (edenot E b)).1
          have hb1 : bv_unsigned (edenot E b) < 2 ^ 64 := (u64_range (edenot E b)).2
          have hn0 : 0 ≤ bv_unsigned (edenot E n) := (u64_range (edenot E n)).1
          have hn1 : bv_unsigned (edenot E n) < 2 ^ 64 := (u64_range (edenot E n)).2
          have hk : 0 ≤ bv_unsigned (edenot E b) + k := by omega
          have h1' : bv_unsigned (edenot E b) + k < 2 ^ 64 := by omega
          have h2' : bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n) < 2 ^ 64 := by
            omega
          have hcol : ((bv_unsigned (edenot E b) + k % 2 ^ 64) % 2 ^ 64
                + bv_unsigned (edenot E n)) % 2 ^ 64
              = bv_unsigned (edenot E b) + k + bv_unsigned (edenot E n) := by
            rw [Int.add_emod_emod, Int.emod_eq_of_lt hk h1',
              Int.emod_eq_of_lt (by omega) h2']
          rw [hcol] at HB
          simpa only [estart, elenZ] using HB
        · exact absurd H (by simp)
      · exact absurd H (by simp)
    · exact absurd H (by simp)

/-- `le_end`: the END-fact test only says what it should. -/
theorem le_end_sound (x : Option Int) (y : Int) (H : le_end x y = true) :
    ∃ e, x = some e ∧ e ≤ y := by
  unfold le_end at H
  split at H
  · rename_i e
    exact ⟨e, rfl, of_decide_eq_true H⟩
  · exact absurd H (by simp)

/-- The NUMERIC-bounds arm of `ranges_apart_x`: separate base brackets, or a
    joint END fact on either side. -/
theorem num_apart_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr) (k2 : Int)
    (n2 : expr) (Hkn : know_ok segs E M kn)
    (H : num_apart kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b1 k1) + elenZ E n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + elenZ E n2 ≤ estart E (SA b1 k1) := by
  unfold num_apart at H
  split at H
  · rename_i _o1 _o2 _o3 _o4 lo1 hi1 lo2 hi2 h1 h2 he1 he2 he3 he4
    obtain ⟨A1, B1⟩ := base_range_sound segs E M kn b1 lo1 hi1 Hkn he1
    obtain ⟨A2, B2⟩ := base_range_sound segs E M kn b2 lo2 hi2 Hkn he2
    have X1 : bv_unsigned (edenot E n1) ≤ h1 := xhi_sound segs E M kn n1 h1 Hkn he3
    have X2 : bv_unsigned (edenot E n2) ≤ h2 := xhi_sound segs E M kn n2 h2 Hkn he4
    have N1 : 0 ≤ bv_unsigned (edenot E n1) := (u64_range (edenot E n1)).1
    have N2 : 0 ≤ bv_unsigned (edenot E n2) := (u64_range (edenot E n2)).1
    split at H
    · rename_i hc
      rcases (Bool.or_eq_true ..).mp hc with hc | hc
      · left
        have hle : hi1 + k1 + h1 ≤ lo2 + k2 := of_decide_eq_true hc
        show bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1)
          ≤ bv_unsigned (edenot E b2) + k2
        omega
      · right
        have hle : hi2 + k2 + h2 ≤ lo1 + k1 := of_decide_eq_true hc
        show bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2)
          ≤ bv_unsigned (edenot E b1) + k1
        omega
    · split at H
      · rename_i he
        obtain ⟨e, hx, hle⟩ := le_end_sound _ _ he
        have HE : bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1) ≤ e :=
          end_hi_sound segs E M kn b1 k1 n1 lo1 hi1 h1 e Hkn he1 he3 hx
        left
        show bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1)
          ≤ bv_unsigned (edenot E b2) + k2
        omega
      · obtain ⟨e, hx, hle⟩ := le_end_sound _ _ H
        have HE : bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2) ≤ e :=
          end_hi_sound segs E M kn b2 k2 n2 lo2 hi2 h2 e Hkn he2 he4 hx
        right
        show bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2)
          ≤ bv_unsigned (edenot E b1) + k1
        omega
  · exact absurd H (by simp)

/-- The two side conditions the carry chain needs, PLUS a `KDisj` fact.
    Sums of the two immediate consequences. -/
theorem ranges_apart_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr) (k2 : Int)
    (n2 : expr) (Hkn : know_ok segs E M kn)
    (H : ranges_apart_x kn b1 k1 n1 b2 k2 n2 = true) :
    estart E (SA b1 k1) + elenZ E n1 ≤ estart E (SA b2 k2) ∨
      estart E (SA b2 k2) + elenZ E n2 ≤ estart E (SA b1 k1) := by
  unfold ranges_apart_x at H
  split at H
  · rename_i z1 z2
    have A := ranges_apart_sound segs E M kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2) Hkn H
    have hz1 : zlit64 z1 = z1 % 2 ^ 64 := by rw [zlit64_eq, two64_eq]
    have hz2 : zlit64 z2 = z2 % 2 ^ 64 := by rw [zlit64_eq, two64_eq]
    rw [hz1, hz2] at A
    rw [elenZ_lit, elenZ_lit]
    exact A
  · split at H
    · rename_i hA
      exact num_apart_sound segs E M kn b1 k1 n1 b2 k2 n2 Hkn hA
    · split at H
      · rename_i hB
        exact kdisj_apart_x_sound segs E M kn kn b1 k1 n1 b2 k2 n2 Hkn Hkn hB
      · split at H
        · exact absurd H (by simp)
        · split at H
          · rename_i hD
            have A := lin_ge0_sound segs E M kn [(b2, k2)] [(b1, k1), (n1, 0)] Hkn hD
            simp only [xt_den] at A
            left
            show bv_unsigned (edenot E b1) + k1 + bv_unsigned (edenot E n1)
              ≤ bv_unsigned (edenot E b2) + k2
            omega
          · have A := lin_ge0_sound segs E M kn [(b1, k1)] [(b2, k2), (n2, 0)] Hkn H
            simp only [xt_den] at A
            right
            show bv_unsigned (edenot E b2) + k2 + bv_unsigned (edenot E n2)
              ≤ bv_unsigned (edenot E b1) + k1
            omega


/-! ### `Section CarrySound`, part 1: the store frame

    A knowledge entry whose range the store misses survives it.
    * `subst hka` where `hka : ka = a` joins two LOCAL VARIABLES: Lean
      eliminates the later one (`a`), which is exactly the one the rest of
      the proof wants, and reports `unknown identifier a` afterwards.  And
      `rw [hka] at *` is no good either: `at *` includes `hka` itself, so
      the rule rewrites to `a = a` before reaching the other hypotheses.
      What works is `rw [hka] at Hdis`: the disjointness hypothesis is the
      only place the ranges appear.
    * `flat` is a def, so `omega` cannot see through it: destruct `Hfl`
      into its four conjuncts (`Hk1 … Hk4`) before any arithmetic. -/

/-- A read outside the written range is unchanged. -/
theorem wbytes_out (bs : List byte) (m : word → Option byte) (addr x : word)
    (Hnw : (addr.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hx : (x.toNat : Int) < (addr.toNat : Int) ∨
      (addr.toNat : Int) + (bs.length : Int) ≤ (x.toNat : Int)) :
    wbytes m addr bs x = m x := by
  rcases Hx with H | H
  · exact wbytes_below bs m addr x Hnw H
  · exact wbytes_above bs m addr x H

/-- **`kentry_ok_frame`.**  A knowledge entry survives a store it is disjoint
    from.  The `match` hypothesis says which address/length the entry's
    range has (`ka, kl`), spelled per constructor exactly as in that
    constructor's `kentry_ok` arm. -/
theorem kentry_ok_frame (segs : List Segment) (E : env) (M : word → Option byte)
    (wa : saddr) (w : Nat) (V : word) (K : kentry) (ka : saddr) (kl : expr)
    (Hfw : flat E wa (w : Int)) (HK : kentry_ok segs E M K)
    (Hshape :
      match K with
      | .KWord a w' _ => ka = a ∧ kl = elen w' ∧ w' ≤ 8
      | .KZero a n => ka = a ∧ kl = n
      | .KBlob a n _ => ka = a ∧ kl = n
      | .KImg lo hi => ka = SA (.ELit 0) lo ∧ kl = .ELit (hi - lo) ∧ hi - lo < 2 ^ 64
      | .KAlign _ _ => True
      | .KRange _ _ _ => True
      | .KWr _ _ => True
      | .KDisj _ _ _ _ => True
      | .KFill a n _ => ka = a ∧ kl = n
      | .KUnk a n => ka = a ∧ kl = n)
    (Hdis : estart E wa + (w : Int) ≤ estart E ka ∨
      estart E ka + elenZ E kl ≤ estart E wa) :
    kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K := by
  have Huw : ((adenot E wa).toNat : Int) = estart E wa := flat_u E wa (w : Int) Hfw
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  have hlen : ((word_to_le_bytes w V).length : Nat) = w := length_N_to_le_bytes w V
  have hbnd : ((adenot E wa).toNat : Int) + (((word_to_le_bytes w V).length : Nat) : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlen, Huw, ← two64_eq_natCast, two64_eq]; exact Hw4
  have OUT : ∀ x : word,
      (bv_unsigned x < estart E wa ∨ estart E wa + (w : Int) ≤ bv_unsigned x) →
      wbytes M (adenot E wa) (word_to_le_bytes w V) x = M x := by
    intro x Hx
    exact wbytes_out _ M (adenot E wa) x hbnd (by rw [hlen, Huw]; exact Hx)
  cases K with
  | KWord a w' v =>
    obtain ⟨hka, hkl, hw8⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨HK1, HK2, HK3⟩ := HK
    refine ⟨HK1, HK2, ?_⟩
    rw [elenZ_elen E w' hw8] at Hdis
    have hfk : ((adenot E a).toNat : Int) = estart E a := flat_u E a (w' : Int) HK2
    have hout : ((adenot E a).toNat : Int) + ((w' : Nat) : Int) ≤ ((adenot E wa).toNat : Int) ∨
        ((adenot E wa).toNat : Int) + (((word_to_le_bytes w V).length : Nat) : Int)
          ≤ ((adenot E a).toNat : Int) := by
      rw [hfk, Huw, hlen]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hnw : ((adenot E a).toNat : Int) + ((w' : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
      rw [hfk, ← two64_eq_natCast, two64_eq]; exact HK2.2.2.2
    rw [rdn_wbytes_out segs (word_to_le_bytes w V) M (adenot E wa) (adenot E a) w'
      hout hnw hbnd]
    exact HK3
  | KZero a n =>
    obtain ⟨hka, hkl⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hfl, Hz⟩ := HK
    obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
    refine ⟨⟨Hk1, Hk2, Hk3, Hk4⟩, ?_⟩
    intro i Hi0 Hilen
    have hi0 : 0 ≤ estart E a + i := by omega
    have hilt : estart E a + i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
      u_small ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E a + i)) < estart E wa ∨
        estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
      rw [hx]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [OUT _ hout]
    exact Hz i Hi0 Hilen
  | KBlob a n k =>
    obtain ⟨hka, hkl⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hfl, Hlen, Hb⟩ := HK
    obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
    refine ⟨⟨Hk1, Hk2, Hk3, Hk4⟩, Hlen, ?_⟩
    intro i Hi0 Hilen
    have hi0 : 0 ≤ estart E a + i := by omega
    have hilt : estart E a + i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
      u_small ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E a + i)) < estart E wa ∨
        estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
      rw [hx]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [OUT _ hout]
    exact Hb i Hi0 Hilen
  | KImg lo hi =>
    obtain ⟨hka, hkl, hsz⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hlo, Hhi, Hnone⟩ := HK
    refine ⟨Hlo, Hhi, ?_⟩
    intro i Hi1 Hi2
    have hi0 : 0 ≤ i := by omega
    have hilt : i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 i) = i := u_small ⟨hi0, hilt⟩
    rw [estart_lit0, elenZ_lit] at Hdis
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at Hdis
    have hout : bv_unsigned (Z_to_bv 64 i) < estart E wa ∨
        estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 i) := by
      rw [hx]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [OUT _ hout]
    exact Hnone i Hi1 Hi2
  | KAlign e m => exact HK
  | KRange e lo hi => exact HK
  | KWr a n =>
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hfl, Hso⟩ := HK
    refine ⟨Hfl, ?_⟩
    intro d mm Hd Hm
    exact store_ok_mono segs mm M (wbytes M (adenot E wa) (word_to_le_bytes w V))
      (BitVec.ofInt 64 (estart E a + d)) (wbytes_grows _ M (adenot E wa))
      (Hso d mm Hd Hm)
  | KDisj a1 n1 a2 n2 => exact HK
  | KFill a n c =>
    obtain ⟨hka, hkl⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hfl, Hz⟩ := HK
    obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
    refine ⟨⟨Hk1, Hk2, Hk3, Hk4⟩, ?_⟩
    intro i Hi0 Hilen
    have hi0 : 0 ≤ estart E a + i := by omega
    have hilt : estart E a + i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
      u_small ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E a + i)) < estart E wa ∨
        estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
      rw [hx]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [OUT _ hout]
    exact Hz i Hi0 Hilen
  | KUnk a n =>
    obtain ⟨hka, hkl⟩ := Hshape
    rw [hka] at Hdis; rw [hkl] at Hdis
    simp only [kentry_ok] at HK ⊢
    obtain ⟨Hfl, Hz⟩ := HK
    obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
    refine ⟨⟨Hk1, Hk2, Hk3, Hk4⟩, ?_⟩
    intro i Hi0 Hilen
    have hi0 : 0 ≤ estart E a + i := by omega
    have hilt : estart E a + i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 (estart E a + i)) = estart E a + i :=
      u_small ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E a + i)) < estart E wa ∨
        estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 (estart E a + i)) := by
      rw [hx]
      rcases Hdis with H | H
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    rw [OUT _ hout]
    exact Hz i Hi0 Hilen


/-!  This tree proves the GENERIC form here and keeps
    `kzero_piece` as its `KZero` instance (same two statements, one proof).
    `estart` is a def, so `omega`
    sees `estart E (SA wb kk)` and `bv_unsigned (edenot E wb) + kk` as two
    different atoms.  Restate every flat conjunct in the unfolded spelling
    (`have hk1 : 0 ≤ bv_unsigned (edenot E wb) + kk := Hk1` typechecks by
    defeq) before any arithmetic; `rw` on the `estart` form does not reach
    inside the def `flat`. -/

/-- A piece of a literal-length `zf` entry: bytes `[i0, i0+len)` of the
    entry, rebuilt at `kk + i0` and surviving a store its range misses. -/
theorem zf_piece (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (V : word) (kk l0 i0 len : Int)
    (Hkind : zf_kind segs mk byteof)
    (Hfw : flat E (SA wb wk) (w : Int))
    (HK : kentry_ok segs E M (mk (SA wb kk) (.ELit l0)))
    (Hi0 : 0 ≤ i0) (Hlen : 0 < len) (Hil : i0 + len ≤ l0 % 2 ^ 64)
    (Hdis : kk + i0 + len ≤ wk ∨ wk + (w : Int) ≤ kk + i0) :
    kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
      (mk (SA wb (kk + i0)) (.ELit len)) := by
  obtain ⟨Hfk, Hz⟩ := (Hkind E M (SA wb kk) (.ELit l0)).1 HK
  rw [elenZ_lit] at Hfk Hz
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfk
  have hk1 : 0 ≤ bv_unsigned (edenot E wb) + kk := Hk1
  have hk2 : bv_unsigned (edenot E wb) + kk < 2 ^ 64 := Hk2
  have hk4 : bv_unsigned (edenot E wb) + kk + l0 % 2 ^ 64 ≤ 2 ^ 64 := Hk4
  have Huw : ((adenot E (SA wb wk)).toNat : Int) = estart E (SA wb wk) :=
    flat_u E (SA wb wk) (w : Int) Hfw
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  have hsew : estart E (SA wb wk) = bv_unsigned (edenot E wb) + wk := rfl
  have hlen : ((word_to_le_bytes w V).length : Nat) = w := length_N_to_le_bytes w V
  have hbnd : ((adenot E (SA wb wk)).toNat : Int)
      + (((word_to_le_bytes w V).length : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlen, Huw, ← two64_eq_natCast, two64_eq]; exact Hw4
  have hmod_lt : l0 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (two_pow_pos_int 64)
  have hlen_lt : len < 2 ^ 64 := by omega
  have hlen_mod : len % 2 ^ 64 = len := Int.emod_eq_of_lt (by omega) hlen_lt
  refine (Hkind E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
    (SA wb (kk + i0)) (.ELit len)).2 ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show (0 : Int) ≤ bv_unsigned (edenot E wb) + (kk + i0); omega
    · show bv_unsigned (edenot E wb) + (kk + i0) < 2 ^ 64; omega
    · rw [elenZ_lit, hlen_mod]; omega
    · rw [elenZ_lit, hlen_mod]
      show bv_unsigned (edenot E wb) + (kk + i0) + len ≤ 2 ^ 64
      omega
  · intro i Hi0' Hilen'
    rw [elenZ_lit, hlen_mod] at Hilen'
    show byteof (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V)
      (Z_to_bv 64 (bv_unsigned (edenot E wb) + (kk + i0) + i)))
    have hi : 0 ≤ bv_unsigned (edenot E wb) + (kk + i0) + i := by omega
    have hilt : bv_unsigned (edenot E wb) + (kk + i0) + i < 2 ^ 64 := by omega
    have hx : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E wb) + (kk + i0) + i))
        = bv_unsigned (edenot E wb) + (kk + i0) + i := u_small ⟨hi, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E wb) + (kk + i0) + i))
          < estart E (SA wb wk) ∨
        estart E (SA wb wk) + (w : Int)
          ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E wb) + (kk + i0) + i)) := by
      rw [hx, hsew]
      rcases Hdis with H | H
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [wbytes_out _ M (adenot E (SA wb wk)) _ hbnd (by rw [hlen, Huw]; exact hout)]
    rw [show bv_unsigned (edenot E wb) + (kk + i0) + i
        = bv_unsigned (edenot E wb) + kk + (i0 + i) from by omega]
    exact Hz (i0 + i) (by omega) (by omega)

/-- `kzero_piece`: the `KZero` instance of `zf_piece`. -/
theorem kzero_piece (segs : List Segment) (E : env) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (V : word) (kk l0 i0 len : Int)
    (Hfw : flat E (SA wb wk) (w : Int))
    (HK : kentry_ok segs E M (.KZero (SA wb kk) (.ELit l0)))
    (Hi0 : 0 ≤ i0) (Hlen : 0 < len) (Hil : i0 + len ≤ l0 % 2 ^ 64)
    (Hdis : kk + i0 + len ≤ wk ∨ wk + (w : Int) ≤ kk + i0) :
    kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
      (.KZero (SA wb (kk + i0)) (.ELit len)) :=
  zf_piece segs .KZero (fun x => x = some (Z_to_bv 8 0)) E M wb wk w V kk l0 i0 len
    (zf_kind_zero segs) Hfw HK Hi0 Hlen Hil Hdis

/-- `kimg_piece`: a `KImg` range cut down to a sub-range survives a
    store the sub-range misses. -/
theorem kimg_piece (segs : List Segment) (E : env) (M : word → Option byte) (wa : saddr)
    (w : Nat) (V : word) (lo hi lo' hi' : Int)
    (Hfw : flat E wa (w : Int)) (HK : kentry_ok segs E M (.KImg lo hi))
    (H1 : lo ≤ lo') (H2 : hi' ≤ hi)
    (Hdis : hi' ≤ estart E wa ∨ estart E wa + (w : Int) ≤ lo') :
    kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (.KImg lo' hi') := by
  simp only [kentry_ok] at HK ⊢
  obtain ⟨Hlo, Hhi, Hnone⟩ := HK
  have Huw : ((adenot E wa).toNat : Int) = estart E wa := flat_u E wa (w : Int) Hfw
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  have hlen : ((word_to_le_bytes w V).length : Nat) = w := length_N_to_le_bytes w V
  have hbnd : ((adenot E wa).toNat : Int) + (((word_to_le_bytes w V).length : Nat) : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlen, Huw, ← two64_eq_natCast, two64_eq]; exact Hw4
  refine ⟨by omega, by omega, ?_⟩
  intro i Hi1 Hi2
  have hi0 : 0 ≤ i := by omega
  have hilt : i < 2 ^ 64 := by omega
  have hx : bv_unsigned (Z_to_bv 64 i) = i := u_small ⟨hi0, hilt⟩
  have hout : bv_unsigned (Z_to_bv 64 i) < estart E wa ∨
      estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 i) := by
    rw [hx]
    rcases Hdis with H | H
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [wbytes_out _ M (adenot E wa) _ hbnd (by rw [hlen, Huw]; exact hout)]
  exact Hnone i (by omega) (by omega)

/-! ### `Section CarrySound`, part 3: `kcut`

    `kcut` splits a `KZero`/`KFill`/`KUnk` entry `kb+kk, +len` into the part
    strictly below the store's start and the part from the store's end up;
    the two `lin_ge0` pairs decide whether each part can be provably
    non-empty (`S >= 0` / `S <= len` for the low part, `T >= 0` / `T <= len`
    for the high one, `lin_ge0 pos neg` meaning `pos >= neg`).

    The two pieces are proved by the local
    helpers `kcut_low_piece` / `kcut_high_piece` (the generic `zf_kind`
    argument makes the `KZero`/`KFill`/`KUnk` instances one line each), and
    the assembly is three small generic lemmas about `Bool` `if`-chains:
    `mem_ite_single` (membership in `if c then [x] else []`),
    `lowc_true`/`highc_true` (what a `true` value of the nested tests
    says).
    LAYOUT.  The two PIECE lemmas and their arithmetic helpers come first,
    then the P2/P3 cache equations (part 4), and only then the ASSEMBLY
    `kcut_sound` + its four instances (`kcut_high_bounds`/`kcut_high_len`
    are the arithmetic of the high piece, kept next to their user) — Lean
    checks in file order, and the assembly is the only part that needs the
    `Bool`-`if` machinery.
 `omega` gives up on `q * 2^64`, so the
    this tree squeezes through `eqm_eq_of_range` (a modular equality of two
    values in `[0, 2^64)` is an equality) and `sub_len_eq`; both are
    local and reused by the two pieces.  All bounds are stated in the
    `estart`/`elenZ` spelling the goals use (`omega` sees the unfolded
    `bv_unsigned (edenot E b) + k` as a different atom), and only the
    `lin_ge0_sound` results — which come in the unfolded spelling, with a
    trailing `+ 0` — are rebuilt with `by omega` before being `exact`ed
    into the `estart` statements. -/

/-- A modular equality of two values that both sit in `[0, 2^64)` is an
    equality (this tree's `Z_to_bv`-injectivity replacement). -/
theorem eqm_eq_of_range {a b : Int} (H : eqm a b) (Ha0 : 0 ≤ a) (Ha1 : a < 2 ^ 64)
    (Hb0 : 0 ≤ b) (Hb1 : b < 2 ^ 64) : a = b := by
  obtain ⟨q, hq⟩ := H
  have h1 : a % 2 ^ 64 = b % 2 ^ 64 := by
    rw [hq, Int.add_mul_emod_self_right, Int.emod_eq_of_lt Hb0 Hb1]
  rw [Int.emod_eq_of_lt Ha0 Ha1, Int.emod_eq_of_lt Hb0 Hb1] at h1
  exact h1

theorem kcut_low_piece (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M M' : word → Option byte)
    (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hkind : zf_kind segs mk byteof)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x)
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
  · intro i Hi0 HiS
    rw [HL] at HiS
    have hi0 : 0 ≤ bv_unsigned (edenot E kb) + kk + i := by omega
    have hilt : bv_unsigned (edenot E kb) + kk + i < 2 ^ 64 := by omega
    have hxi : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i))
        = bv_unsigned (edenot E kb) + kk + i := u_small ⟨hi0, hilt⟩
    show byteof (M' (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i)))
    have hout : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i))
          < estart E (SA wb wk) ∨
        estart E (SA wb wk) + elenZ E wn
          ≤ bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E kb) + kk + i)) := by
      rw [hxi]
      left
      show bv_unsigned (edenot E kb) + kk + i < bv_unsigned (edenot E wb) + wk
      omega
    rw [Hout _ hout]
    exact Hz i Hi0 (by omega)

theorem kcut_high_piece (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M M' : word → Option byte)
    (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (ha : saddr) (L : expr)
    (Hkind : zf_kind segs mk byteof)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x)
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
  · intro i Hi0 HiT
    rw [HL] at HiT
    rw [Hst]
    have hi0 : 0 ≤ estart E (SA wb wk) + elenZ E wn + i := by omega
    have hilt : estart E (SA wb wk) + elenZ E wn + i < 2 ^ 64 := by omega
    have hxi : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i))
        = estart E (SA wb wk) + elenZ E wn + i := u_small ⟨hi0, hilt⟩
    have hout : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i))
          < estart E (SA wb wk) ∨
        estart E (SA wb wk) + elenZ E wn
          ≤ bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + elenZ E wn + i)) := by
      rw [hxi]
      exact Or.inr (by omega)
    rw [Hout _ hout]
    have hidx : estart E (SA wb wk) + elenZ E wn + i
        = estart E (SA kb kk)
          + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i) := by
      omega
    rw [hidx]
    exact Hz _ (by omega) (by omega)

/-- `eqm` at an `mkAlu.ADD` (this tree's `u_add_eqm` composed). -/
theorem add_eqm (E : env) (x y : expr) (a b : Int)
    (Hx : eqm (bv_unsigned (edenot E x)) a) (Hy : eqm (bv_unsigned (edenot E y)) b) :
    eqm (bv_unsigned (edenot E (mkAlu .ADD x y))) (a + b) := by
  rw [mkAlu_denot]
  show eqm (bv_unsigned (edenot E x + edenot E y)) (a + b)
  exact eqm_trans (u_add_eqm _ _) (eqm_add Hx Hy)

/-- The length of an `mkAlu .SUB` whose parts are `eqm` to two INT values
    that both sit in `[0, 2^64)` with a difference that does too. -/
theorem sub_len_eq (E : env) (x y : expr) (A B : Int)
    (Hx : eqm (bv_unsigned (edenot E x)) A) (Hy : eqm (bv_unsigned (edenot E y)) B)
    (Hd0 : 0 ≤ A - B) (Hd1 : A - B < 2 ^ 64) :
    elenZ E (mkAlu .SUB x y) = A - B := by
  show bv_unsigned (edenot E (mkAlu .SUB x y)) = A - B
  rw [mkAlu_denot]
  show bv_unsigned (edenot E x - edenot E y) = A - B
  have hneg : eqm (- bv_unsigned (edenot E y)) (- B) := by
    obtain ⟨q, hq⟩ := Hy
    exact ⟨-q, by omega⟩
  exact eqm_eq_of_range (eqm_trans (u_sub_eqm _ _) (eqm_add Hx hneg))
    (u64_range _).1 (u64_range _).2 Hd0 Hd1

theorem mem_ite_single {α : Type} (c : Bool) (x y : α)
    (h : y ∈ (if c then [x] else ([] : List α))) : c = true ∧ y = x := by
  by_cases hc : c = true
  · rw [ite_eq_left hc] at h
    exact ⟨hc, List.mem_singleton.mp h⟩
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)

theorem lowc_true {A B C : Bool}
    (h : (if A then false else if B then C else false) = true) :
    A = false ∧ B = true ∧ C = true := by
  cases A <;> cases B <;> cases C <;> simp_all

theorem highc_true {D E2 G : Bool}
    (h : (if D then (if E2 then G else false) else false) = true) :
    D = true ∧ E2 = true ∧ G = true := by
  cases D <;> cases E2 <;> cases G <;> simp_all

/-! ### `Section CarrySound`, part 4: the prepared / cached prune pass


    `mk_sprep` prepares the store-side tests once per store; `prune1p` /
    `prunep` use them, `prune1pc` / `prunepc` additionally cache the
    ENTRY-side `base_range` lookups.  All five passes must agree with the
    reference ones by THEOREM, and the four equations below say exactly
    that (`in_sides_eq`/`in_sides_x_eq` are the two auxiliary equalities
    that make `ranges_apart_p_eq` go through).

    NOTES.
    * `in_sides_eq` / `in_sides_x_eq`: induction on the knowledge list and
      `cases` on the four `sub_itv` tests, then `simp only [in_sides, …]`
      reduces the list fold; the branch where both list-building tests are
      `false` leaves exactly the induction hypothesis.  (`disj_sides` and
      `kdisj_apart` agree only AFTER the two `sub_itv` tests are known, so
      the goal has to be split on them, not on the list shape.)
    * `ranges_apart_p_eq`: `mk_sprep`'s projections have to be rewritten
      (`rfl` equations on `sp_D` / `sp_Dx` / `sp_rng`) before
      `in_sides_(x_)eq` can fire; `cases n1`/`cases n2` alone is not
      enough, since `(mk_sprep …).sp_D` is not syntactically
      `disj_sides …`.
    * `prune1p_eq` / `ranges_apart_pc_eq` are one `cases K` plus `simp`.
    * `prunepc_eq`: `cases K` FIRST (so that `kbase K` reduces to a literal
      `some`/`none` *definitionally* — a `cases hk : kbase K` would rewrite
      the `match kbase K` hypothesis of `prune1pc_eq` out of shape), then
      the two `br_lookup` shapes, and the induction hypothesis at the cache
      the branch builds. -/

set_option linter.unusedSimpArgs false

theorem in_sides_eq (allkn kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr)
    (k2 n2 : Int) :
    in_sides allkn (disj_sides allkn kn b1 k1 n1) b2 k2 n2
      = kdisj_apart allkn kn b1 k1 n1 b2 k2 n2 := by
  induction kn with
  | nil => rfl
  | cons K rest ih =>
    cases K with
    | KDisj c1 m1 c2 m2 =>
      simp only [disj_sides, kdisj_apart]
      cases hA : sub_itv allkn b1 k1 n1 c1 m1 <;>
        cases hB : sub_itv allkn b1 k1 n1 c2 m2 <;>
        cases hC : sub_itv allkn b2 k2 n2 c1 m1 <;>
        cases hD : sub_itv allkn b2 k2 n2 c2 m2 <;>
        simp only [hA, hB, hC, hD, in_sides, Bool.false_eq_true, ite_false, ite_true] <;>
        exact ih
    | _ => simp only [disj_sides, kdisj_apart]; exact ih

theorem in_sides_x_eq (allkn kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr)
    (k2 : Int) (n2 : expr) :
    in_sides_x allkn (disj_sides_x allkn kn b1 k1 n1) b2 k2 n2
      = kdisj_apart_x allkn kn b1 k1 n1 b2 k2 n2 := by
  induction kn with
  | nil => rfl
  | cons K rest ih =>
    cases K with
    | KDisj c1 m1 c2 m2 =>
      simp only [disj_sides_x, kdisj_apart_x]
      cases hA : sub_itv_x allkn b1 k1 n1 c1 m1 <;>
        cases hB : sub_itv_x allkn b1 k1 n1 c2 m2 <;>
        cases hC : sub_itv_x allkn b2 k2 n2 c1 m1 <;>
        cases hD : sub_itv_x allkn b2 k2 n2 c2 m2 <;>
        simp only [hA, hB, hC, hD, in_sides_x, Bool.false_eq_true, ite_false, ite_true] <;>
        exact ih
    | _ => simp only [disj_sides_x, kdisj_apart_x]; exact ih

theorem num_apart_p_eq (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr)
    (k2 : Int) (n2 : expr) :
    num_apart_p kn (mk_sprep kn b1 k1 n1) b1 k1 n1 b2 k2 n2
      = num_apart kn b1 k1 n1 b2 k2 n2 := by
  unfold num_apart_p num_apart mk_sprep
  rfl

theorem ranges_apart_p_eq (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) (b2 : expr)
    (k2 : Int) (n2 : expr) :
    ranges_apart_p kn (mk_sprep kn b1 k1 n1) b1 k1 n1 b2 k2 n2
      = ranges_apart_x kn b1 k1 n1 b2 k2 n2 := by
  unfold ranges_apart_p ranges_apart_x
  have hDx : (mk_sprep kn b1 k1 n1).sp_Dx = disj_sides_x kn kn b1 k1 n1 := rfl
  cases n1 with
  | ELit z1 =>
    cases n2 with
    | ELit z2 =>
      unfold ranges_apart
      dsimp only
      have hD : (mk_sprep kn b1 k1 (.ELit z1)).sp_D = disj_sides kn kn b1 k1 (zlit64 z1) := rfl
      have hRng : (mk_sprep kn b1 k1 (.ELit z1)).sp_rng = base_range kn b1 := rfl
      rw [hD, in_sides_eq, hRng]
    | _ =>
      dsimp only
      rw [num_apart_p_eq, hDx, in_sides_x_eq]
  | _ =>
    dsimp only
    rw [num_apart_p_eq, hDx, in_sides_x_eq]

theorem prune1p_eq (allkn : List kentry) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) :
    prune1p allkn (mk_sprep allkn wa.a_base wa.a_off (elen w)) wa w wv K hints
      = prune1 allkn wa w wv K hints := by
  cases K <;> simp only [prune1p, prune1, prune_zf, ranges_apart_p_eq]

theorem prunep_eq (allkn : List kentry) (wa : saddr) (w : Nat) (wv : expr) :
    ∀ (kn : List kentry) (hints : List Bool),
      prunep allkn (mk_sprep allkn wa.a_base wa.a_off (elen w)) wa w wv kn hints
        = prune allkn wa w wv kn hints := by
  intro kn
  induction kn with
  | nil => intro hints; rfl
  | cons K rest ih =>
    intro hints
    simp only [prunep, prune, prune1p_eq]
    generalize h : prune1 allkn wa w wv K hints = p
    obtain ⟨kept, scs1, hs1⟩ := p
    dsimp only
    rw [ih hs1]

theorem ranges_apart_pc_eq (kn : List kentry) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) :
    ranges_apart_pc kn sp b1 k1 n1 (base_range kn b2) b2 k2 n2
      = ranges_apart_p kn sp b1 k1 n1 b2 k2 n2 := by
  unfold ranges_apart_pc ranges_apart_p num_apart_p
  cases n1 <;> cases n2 <;> rfl

theorem prune1pc_eq (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (K : kentry) (hints : List Bool) (br2 : Option (Int × Int))
    (Hb : match kbase K with | some kb => br2 = base_range allkn kb | none => True) :
    prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints := by
  cases K with
  | KWr a n => simp only [kbase, prune1pc, prune1p] at Hb ⊢
  | KAlign e m => simp only [kbase, prune1pc, prune1p] at Hb ⊢
  | KRange e lo hi => simp only [kbase, prune1pc, prune1p] at Hb ⊢
  | KDisj a1 n1 a2 n2 => simp only [kbase, prune1pc, prune1p] at Hb ⊢
  | KImg lo hi => simp only [kbase, prune1pc, prune1p] at Hb ⊢
  | KWord a w' v =>
    simp only [kbase] at Hb
    rw [Hb]
    by_cases hb : expr_eqb a.a_base wa.a_base = true
    · simp only [prune1pc, prune1p, ite_eq_left hb]
    · simp only [prune1pc, prune1p, ite_eq_right hb, ranges_apart_pc_eq]
  | KBlob a n k =>
    simp only [kbase] at Hb
    rw [Hb]
    by_cases hb : expr_eqb a.a_base wa.a_base = true
    · simp only [prune1pc, prune1p, ite_eq_left hb]
    · simp only [prune1pc, prune1p, ite_eq_right hb, ranges_apart_pc_eq]
  | KZero kb len =>
    simp only [kbase] at Hb
    rw [Hb]
    by_cases hb : expr_eqb kb.a_base wa.a_base = true
    · simp only [prune1pc, prune1p, prune_zf, ite_eq_left hb]
    · simp only [prune1pc, prune1p, prune_zf, kzero_cut, ite_eq_right hb, ranges_apart_pc_eq]
  | KFill kb len c =>
    simp only [kbase] at Hb
    rw [Hb]
    by_cases hb : expr_eqb kb.a_base wa.a_base = true
    · simp only [prune1pc, prune1p, prune_zf, ite_eq_left hb]
    · simp only [prune1pc, prune1p, prune_zf, kfill_cut, ite_eq_right hb, ranges_apart_pc_eq]
  | KUnk kb len =>
    simp only [kbase] at Hb
    rw [Hb]
    by_cases hb : expr_eqb kb.a_base wa.a_base = true
    · simp only [prune1pc, prune1p, prune_zf, ite_eq_left hb]
    · simp only [prune1pc, prune1p, prune_zf, kunk_cut, ite_eq_right hb, ranges_apart_pc_eq]

theorem prunepc_eq (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) :
    ∀ (kn : List kentry) (hints : List Bool) (cache : List (expr × Option (Int × Int))),
      br_cache_ok allkn cache →
      prunepc allkn sp wa w wv kn hints cache = prunep allkn sp wa w wv kn hints := by
  intro kn
  induction kn with
  | nil => intro hints cache Hc; rfl
  | cons K rest ih =>
    intro hints cache Hc
    cases K with
    | KAlign e m =>
      simp only [prunepc, prunep, kbase]
      try dsimp only
      rw [prune1pc_eq allkn sp wa w wv (.KAlign e m) hints none (by trivial)]
      try dsimp only
      rw [ih _ cache Hc]
    | KRange e lo hi =>
      simp only [prunepc, prunep, kbase]
      try dsimp only
      rw [prune1pc_eq allkn sp wa w wv (.KRange e lo hi) hints none (by trivial)]
      try dsimp only
      rw [ih _ cache Hc]
    | KWr a n =>
      simp only [prunepc, prunep, kbase]
      try dsimp only
      rw [prune1pc_eq allkn sp wa w wv (.KWr a n) hints none (by trivial)]
      try dsimp only
      rw [ih _ cache Hc]
    | KDisj a1 n1 a2 n2 =>
      simp only [prunepc, prunep, kbase]
      try dsimp only
      rw [prune1pc_eq allkn sp wa w wv (.KDisj a1 n1 a2 n2) hints none (by trivial)]
      try dsimp only
      rw [ih _ cache Hc]
    | KImg lo hi =>
      simp only [prunepc, prunep, kbase]
      try dsimp only
      rw [prune1pc_eq allkn sp wa w wv (.KImg lo hi) hints none (by trivial)]
      try dsimp only
      rw [ih _ cache Hc]
    | KWord a w' v =>
      simp only [prunepc, prunep, kbase]
      cases hl : br_lookup cache a.a_base with
      | none =>
        try dsimp only
        rw [prune1pc_eq allkn sp wa w wv (.KWord a w' v) hints (base_range allkn a.a_base) (by trivial)]
        try dsimp only
        rw [ih _ ((a.a_base, base_range allkn a.a_base) :: cache) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · rfl
          · exact Hc p hp')]
      | some r =>
        try dsimp only
        have hr : r = base_range allkn a.a_base := br_lookup_ok allkn cache a.a_base r Hc hl
        rw [prune1pc_eq allkn sp wa w wv (.KWord a w' v) hints r (by trivial)]
        try dsimp only
        rw [ih _ cache Hc]
    | KBlob a n k =>
      simp only [prunepc, prunep, kbase]
      cases hl : br_lookup cache a.a_base with
      | none =>
        try dsimp only
        rw [prune1pc_eq allkn sp wa w wv (.KBlob a n k) hints (base_range allkn a.a_base) (by trivial)]
        try dsimp only
        rw [ih _ ((a.a_base, base_range allkn a.a_base) :: cache) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · rfl
          · exact Hc p hp')]
      | some r =>
        try dsimp only
        have hr : r = base_range allkn a.a_base := br_lookup_ok allkn cache a.a_base r Hc hl
        rw [prune1pc_eq allkn sp wa w wv (.KBlob a n k) hints r (by trivial)]
        try dsimp only
        rw [ih _ cache Hc]
    | KZero kb len =>
      simp only [prunepc, prunep, kbase]
      cases hl : br_lookup cache kb.a_base with
      | none =>
        try dsimp only
        rw [prune1pc_eq allkn sp wa w wv (.KZero kb len) hints (base_range allkn kb.a_base) (by trivial)]
        try dsimp only
        rw [ih _ ((kb.a_base, base_range allkn kb.a_base) :: cache) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · rfl
          · exact Hc p hp')]
      | some r =>
        try dsimp only
        have hr : r = base_range allkn kb.a_base := br_lookup_ok allkn cache kb.a_base r Hc hl
        rw [prune1pc_eq allkn sp wa w wv (.KZero kb len) hints r (by trivial)]
        try dsimp only
        rw [ih _ cache Hc]
    | KFill kb len c =>
      simp only [prunepc, prunep, kbase]
      cases hl : br_lookup cache kb.a_base with
      | none =>
        try dsimp only
        rw [prune1pc_eq allkn sp wa w wv (.KFill kb len c) hints (base_range allkn kb.a_base) (by trivial)]
        try dsimp only
        rw [ih _ ((kb.a_base, base_range allkn kb.a_base) :: cache) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · rfl
          · exact Hc p hp')]
      | some r =>
        try dsimp only
        have hr : r = base_range allkn kb.a_base := br_lookup_ok allkn cache kb.a_base r Hc hl
        rw [prune1pc_eq allkn sp wa w wv (.KFill kb len c) hints r (by trivial)]
        try dsimp only
        rw [ih _ cache Hc]
    | KUnk kb len =>
      simp only [prunepc, prunep, kbase]
      cases hl : br_lookup cache kb.a_base with
      | none =>
        try dsimp only
        rw [prune1pc_eq allkn sp wa w wv (.KUnk kb len) hints (base_range allkn kb.a_base) (by trivial)]
        try dsimp only
        rw [ih _ ((kb.a_base, base_range allkn kb.a_base) :: cache) (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp'
          · rfl
          · exact Hc p hp')]
      | some r =>
        try dsimp only
        have hr : r = base_range allkn kb.a_base := br_lookup_ok allkn cache kb.a_base r Hc hl
        rw [prune1pc_eq allkn sp wa w wv (.KUnk kb len) hints r (by trivial)]
        try dsimp only
        rw [ih _ cache Hc]

/-- **`kcut_sound`**: both pieces of a literal-length `zf` entry survive a
    store the entry's own range covers the write legally (see `kcut`). -/
theorem kcut_high_bounds (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M0 M : word → Option byte)
    (allkn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr)
    (Hkind : zf_kind segs mk byteof) (Hall : know_ok segs E M0 allkn)
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

/-- The length of `kcut`'s HIGH piece. -/
theorem kcut_high_len (E : env) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr)
    (Hm0 : 0 ≤ estart E (SA wb wk) + elenZ E wn)
    (Hm1 : estart E (SA wb wk) + elenZ E wn ≤ estart E (SA kb kk) + elenZ E len)
    (Hm2 : estart E (SA kb kk) + elenZ E len ≤ 2 ^ 64 - 1) :
    elenZ E (mkAlu .SUB (mkAlu .ADD (mkAlu .ADD kb (.ELit kk)) len)
        (mkAlu .ADD (mkAlu .ADD wb (.ELit wk)) wn))
      = estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn) := by
  have hX : eqm (bv_unsigned (edenot E (mkAlu .ADD (mkAlu .ADD kb (.ELit kk)) len)))
      (bv_unsigned (edenot E kb) + kk + bv_unsigned (edenot E len)) :=
    add_eqm E _ _ _ _ (add_eqm E _ _ _ _ (eqm_refl _) (eqm_u_lit kk)) (eqm_refl _)
  have hY : eqm (bv_unsigned (edenot E (mkAlu .ADD (mkAlu .ADD wb (.ELit wk)) wn)))
      (bv_unsigned (edenot E wb) + wk + bv_unsigned (edenot E wn)) :=
    add_eqm E _ _ _ _ (add_eqm E _ _ _ _ (eqm_refl _) (eqm_u_lit wk)) (eqm_refl _)
  exact sub_len_eq E _ _ _ _ hX hY (by omega) (by omega)

theorem kcut_sound (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M0 : word → Option byte)
    (M M' : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hkind : zf_kind segs mk byteof) (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x) :
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
    exact kcut_low_piece segs mk byteof E M M' wb wk wn kb kk len Hkind HK Hout hA hB
  have HIGH : ∀ (h1 : lin_ge0 allkn [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)] = true)
      (h2 : lin_ge0 allkn [(wb, wk), (wn, 0)] [(kb, kk)] = true)
      (h3 : lin_ge0 allkn [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)] = true)
      (ha : saddr) (L : expr),
      estart E ha = estart E (SA wb wk) + elenZ E wn →
      elenZ E L = estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn) →
      kentry_ok segs E M' (mk ha L) := by
    intro h1 h2 h3 ha L hst hl
    obtain ⟨W0, W1, A1, B1, C1⟩ :=
      kcut_high_bounds segs mk byteof E M0 M allkn wb wk wn kb kk len Hkind Hall HK h1 h2 h3
    exact kcut_high_piece segs mk byteof E M M' wb wk wn kb kk len ha L Hkind HK Hout
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
      kcut_high_bounds segs mk byteof E M0 M allkn wb wk wn kb kk len Hkind Hall HK h1 h2 h3
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

/-- `kcut` at `KZero`. -/
theorem kzero_cut_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (M M' : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (.KZero (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x) :
    ∀ K ∈ kzero_cut allkn wb wk wn kb kk len, kentry_ok segs E M' K :=
  kcut_sound segs .KZero (fun x => x = some (Z_to_bv 8 0)) E M0 M M' allkn wb wk wn kb kk len
    (zf_kind_zero segs) Hall HK Hout

/-- `kcut` at `KFill c`. -/
theorem kfill_cut_sound (segs : List Segment) (c : Int) (E : env) (M0 : word → Option byte)
    (M M' : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (.KFill (SA kb kk) len c))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x) :
    ∀ K ∈ kfill_cut c allkn wb wk wn kb kk len, kentry_ok segs E M' K :=
  kcut_sound segs (fun a n => .KFill a n c) (fun x => x = some (Z_to_bv 8 c)) E M0 M M' allkn
    wb wk wn kb kk len (zf_kind_fill segs c) Hall HK Hout

/-- `kcut` at `KUnk`. -/
theorem kunk_cut_sound (segs : List Segment) (E : env) (M0 : word → Option byte)
    (M M' : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr)
    (Hall : know_ok segs E M0 allkn)
    (HK : kentry_ok segs E M (.KUnk (SA kb kk) len))
    (Hout : ∀ x : word, (bv_unsigned x < estart E (SA wb wk) ∨
      estart E (SA wb wk) + elenZ E wn ≤ bv_unsigned x) → M' x = M x) :
    ∀ K ∈ kunk_cut allkn wb wk wn kb kk len, kentry_ok segs E M' K :=
  kcut_sound segs .KUnk (fun x => x ≠ none) E M0 M M' allkn wb wk wn kb kk len
    (zf_kind_unk segs) Hall HK Hout

/-- `kcut` for a store of `w` bytes at `wa`. -/
theorem kcut_store (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M0 M : word → Option byte)
    (allkn : List kentry) (wa : saddr) (w : Nat) (V : word) (kb : expr) (kk : Int)
    (len : expr)
    (Hkind : zf_kind segs mk byteof) (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8)
    (Hfw : flat E wa (w : Int)) (HK : kentry_ok segs E M (mk (SA kb kk) len)) :
    ∀ K ∈ kcut mk allkn wa.a_base wa.a_off (elen w) kb kk len,
      kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K := by
  refine kcut_sound segs mk byteof E M0 M (wbytes M (adenot E wa) (word_to_le_bytes w V))
    allkn wa.a_base wa.a_off (elen w) kb kk len Hkind Hall HK ?_
  have Huw : ((adenot E wa).toNat : Int) = estart E wa := flat_u E wa (w : Int) Hfw
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  have hlen : ((word_to_le_bytes w V).length : Nat) = w := length_N_to_le_bytes w V
  have hbnd : ((adenot E wa).toNat : Int) + (((word_to_le_bytes w V).length : Nat) : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlen, Huw, ← two64_eq_natCast, two64_eq]; exact Hw4
  intro x Hx
  rw [elenZ_elen E w Hw8] at Hx
  exact wbytes_out _ M (adenot E wa) x hbnd (by rw [hlen, Huw]; exact Hx)

/-- `kcut_store` at `KZero`. -/
theorem kzero_cut_store (segs : List Segment) (E : env) (M0 M : word → Option byte)
    (allkn : List kentry) (wa : saddr) (w : Nat) (V : word) (kb : expr) (kk : Int)
    (len : expr)
    (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8) (Hfw : flat E wa (w : Int))
    (HK : kentry_ok segs E M (.KZero (SA kb kk) len)) :
    ∀ K ∈ kzero_cut allkn wa.a_base wa.a_off (elen w) kb kk len,
      kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) K :=
  kcut_store segs .KZero (fun x => x = some (Z_to_bv 8 0)) E M0 M allkn wa w V kb kk len
    (zf_kind_zero segs) Hall Hw8 Hfw HK


/-! ### `Section CarrySound`, part 5: `ktrim` and `prune_zf`

    Three lemmas, all instances of `zf_piece` / `kentry_ok_frame`-style
    reasoning at the generic `zf_kind`:

    * `zf_frame` — an entry the store misses survives it (`kentry_ok_frame`
      at an abstract `mk`, i.e. without the per-constructor case bash);
    * `ktrim_sound` — both literal-length pieces of `ktrim` are pieces of
      the entry (`zf_piece` with `i0 = 0` and `i0 = lo2 - kk`);
    * `prune_zf_sound` — the shared `KZero`/`KFill`/`KUnk` case of
      `prune1`/`prune1p`: same base → `ktrim` (literal length) or
      keep/`kcut`, different base → apart (`zf_frame`) or `kcut`
      (`kcut_store`), and the caller's `diffbase` thunk if the cut is
      empty.

    In `prune_zf_sound` the `match len with` branch is entered
    with `cases len`, which SUBSTITUTES the length expression — so the
    non-literal arms cannot name `len` for `kcut_store`/`zf_frame`.  Pass
    `_` for that argument instead: the expected type already contains the
    substituted expression, so unification recovers it.  The same-base
    branch needs `kb = wb` (`expr_eqb_eq`) rewritten into `Hp`/`HK` by
    `rw [hkbeq]`; `subst` cannot be used because both are plain parameters
    and Lean eliminates the WRONG one (see the note in part 1).
    `mem_ite_single_prop` is the `Prop`-condition twin of `mem_ite_single`
    (`ktrim`'s pieces are guarded by `if kk < hi1 then …`, an `ite` on a
    `Prop`, not on a `Bool`). -/
theorem mem_ite_single_prop {α : Type} (c : Prop) [Decidable c] (x y : α)
    (h : y ∈ (if c then [x] else ([] : List α))) : c ∧ y = x := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact ⟨hc, List.mem_singleton.mp h⟩
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)

theorem zf_frame (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M : word → Option byte)
    (wa : saddr) (w : Nat) (V : word) (kb : expr) (kk : Int) (len : expr)
    (Hkind : zf_kind segs mk byteof) (Hfw : flat E wa (w : Int))
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hdis : estart E wa + (w : Int) ≤ estart E (SA kb kk) ∨
      estart E (SA kb kk) + elenZ E len ≤ estart E wa) :
    kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (mk (SA kb kk) len) := by
  obtain ⟨Hfl, Hz⟩ := (Hkind E M (SA kb kk) len).1 HK
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
  have Huw : ((adenot E wa).toNat : Int) = estart E wa := flat_u E wa (w : Int) Hfw
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  have hlen : ((word_to_le_bytes w V).length : Nat) = w := length_N_to_le_bytes w V
  have hbnd : ((adenot E wa).toNat : Int) + (((word_to_le_bytes w V).length : Nat) : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlen, Huw, ← two64_eq_natCast, two64_eq]; exact Hw4
  refine (Hkind E (wbytes M (adenot E wa) (word_to_le_bytes w V)) (SA kb kk) len).2
    ⟨⟨Hk1, Hk2, Hk3, Hk4⟩, ?_⟩
  intro i Hi0 Hilen
  have hi0 : 0 ≤ estart E (SA kb kk) + i := by omega
  have hilt : estart E (SA kb kk) + i < 2 ^ 64 := by omega
  have hx : bv_unsigned (Z_to_bv 64 (estart E (SA kb kk) + i)) = estart E (SA kb kk) + i :=
    u_small ⟨hi0, hilt⟩
  have hout : bv_unsigned (Z_to_bv 64 (estart E (SA kb kk) + i)) < estart E wa ∨
      estart E wa + (w : Int) ≤ bv_unsigned (Z_to_bv 64 (estart E (SA kb kk) + i)) := by
    rw [hx]
    rcases Hdis with H | H
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  rw [wbytes_out _ M (adenot E wa) _ hbnd (by rw [hlen, Huw]; exact hout)]
  exact Hz i Hi0 Hilen

theorem ktrim_sound (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (V : word) (kk l0 : Int)
    (Hkind : zf_kind segs mk byteof) (Hfw : flat E (SA wb wk) (w : Int))
    (HK : kentry_ok segs E M (mk (SA wb kk) (.ELit l0))) :
    ∀ K ∈ ktrim mk wb kk l0 wk w,
      kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V)) K := by
  obtain ⟨Hfl, -⟩ := (Hkind E M (SA wb kk) (.ELit l0)).1 HK
  rw [elenZ_lit] at Hfl
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfl
  unfold ktrim
  dsimp only
  rw [two64_eq]
  intro K hK
  rcases List.mem_append.mp hK with hK | hK
  · obtain ⟨hc, hK⟩ := mem_ite_single_prop _ _ K hK
    rw [hK]
    have h := zf_piece segs mk byteof E M wb wk w V kk l0 0 (min wk (kk + l0 % 2 ^ 64) - kk)
      Hkind Hfw HK (by omega) (by omega) (by omega) (by left; omega)
    rwa [show kk + 0 = kk from by omega] at h
  · obtain ⟨hc, hK⟩ := mem_ite_single_prop _ _ K hK
    rw [hK]
    have h := zf_piece segs mk byteof E M wb wk w V kk l0
      (max kk (wk + (w : Int)) - kk) (kk + l0 % 2 ^ 64 - max kk (wk + (w : Int)))
      Hkind Hfw HK (by omega) (by omega) (by omega) (by right; omega)
    rwa [show kk + (max kk (wk + ↑w) - kk) = max kk (wk + ↑w) from by omega] at h

theorem prune_zf_sound (segs : List Segment) (mk : saddr → expr → kentry)
    (byteof : Option byte → Prop) (E : env) (anybase M0 : word → Option byte)
    (M : word → Option byte) (allkn : List kentry) (wb : expr) (wk : Int) (w : Nat)
    (V : word) (kb : expr) (kk : Int) (len : expr) (apart : Unit → Bool) (hints : List Bool)
    (diffbase : Unit → List kentry × List sidecond × List Bool)
    (kept : List kentry) (scs : List sidecond) (hs' : List Bool)
    (Hkind : zf_kind segs mk byteof)
    (Hp : prune_zf mk allkn wb wk w (mk (SA kb kk) len) kb kk len apart hints diffbase
      = (kept, scs, hs'))
    (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8) (Hfw : flat E (SA wb wk) (w : Int))
    (HK : kentry_ok segs E M (mk (SA kb kk) len))
    (Hapart : apart () = true →
      (estart E (SA wb wk) + (w : Int) ≤ estart E (SA kb kk) ∨
        estart E (SA kb kk) + elenZ E len ≤ estart E (SA wb wk)))
    (Hdb : diffbase () = (kept, scs, hs') → scs_denot segs anybase E scs →
      ∀ K ∈ kept, kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V)) K)
    (Hscs : scs_denot segs anybase E scs) :
    ∀ K ∈ kept, kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V)) K := by
  unfold prune_zf at Hp
  by_cases hb : expr_eqb kb wb = true
  · rw [ite_eq_left hb] at Hp
    have hkbeq : kb = wb := expr_eqb_eq kb wb hb
    rw [hkbeq] at Hp HK
    cases len with
    | ELit l0 =>
      obtain ⟨rfl, rfl, rfl⟩ := Hp
      exact ktrim_sound segs mk byteof E M wb wk w V kk l0 Hkind Hfw HK
    | _ =>
      by_cases hle : wk + (w : Int) ≤ kk
      · rw [ite_eq_left hle] at Hp
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        refine Forall_one _ _ ?_
        refine zf_frame segs mk byteof E M (SA wb wk) w V wb kk _ Hkind Hfw HK (Or.inl ?_)
        show bv_unsigned (edenot E wb) + wk + (w : Int) ≤ bv_unsigned (edenot E wb) + kk
        omega
      · rw [ite_eq_right hle] at Hp
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        exact kcut_store segs mk byteof E M0 M allkn (SA wb wk) w V wb kk _ Hkind Hall Hw8 Hfw HK
  · rw [ite_eq_right hb] at Hp
    by_cases ha : apart () = true
    · rw [ite_eq_left ha] at Hp
      obtain ⟨rfl, rfl, rfl⟩ := Hp
      refine Forall_one _ _ ?_
      exact zf_frame segs mk byteof E M (SA wb wk) w V kb kk _ Hkind Hfw HK (Hapart ha)
    · rw [ite_eq_right ha] at Hp
      generalize hcut : kcut mk allkn wb wk (elen w) kb kk len = c at Hp
      cases c with
      | nil => exact Hdb Hp Hscs
      | cons c0 cut =>
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        rw [← hcut]
        exact kcut_store segs mk byteof E M0 M allkn (SA wb wk) w V kb kk _ Hkind Hall Hw8 Hfw HK


/-!  Lean core has neither `Int` bit
    extensionality nor `Int.emod_ediv`, but every value in play here is
    NON-NEGATIVE (`word_to_le_bytes` reads `v.toNat`), so the same fact is
    proved at `Nat` arguments by induction on `n`: the low byte with
    `Nat.mod_mod_of_dvd`, the shifted tail with the `Nat` division identity
    `(m % (A * 256)) / 256 = (m / 256) % A` (`div_256_mod` below). -/

/-- The low byte of a `Nat`, as `Z_to_le_bytes` encodes it. -/
theorem toNat_ofInt_8_nat (m : Nat) : (BitVec.ofInt 8 (m : Int)).toNat = m % 256 := by
  rw [BitVec.toNat_ofInt]
  rw [Int.toNat_emod (Int.natCast_nonneg m) (by decide)]
  rw [show ((2 ^ 8 : Nat) : Int) = (256 : Int) by decide]
  simp

/-- `(m : Int) >>> 8` at a `Nat` argument is the `Nat` quotient `m / 256`. -/
theorem int_shiftRight_8_natCast (m : Nat) :
    ((m : Int) >>> 8) = ((m / 256 : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.ofNat_ediv_ofNat]

/-- The little-endian shift of a byte modulus: taking the low `A * 256` bits
    and then dropping the low byte is the quotient by `256`, reduced mod
    `A`. -/
theorem div_256_mod (m A : Nat) (hA : 0 < A) :
    m % (A * 256) / 256 = m / 256 % A := by
  have h256 : 0 < 256 := by decide
  have hlt : m % (A * 256) / 256 < A := by
    rw [Nat.div_lt_iff_lt_mul h256]
    exact Nat.mod_lt _ (by omega)
  have hassoc : (A * 256) * (m / (A * 256)) = (A * (m / (A * 256))) * 256 := by
    rw [Nat.mul_assoc, Nat.mul_comm 256 (m / (A * 256)), ← Nat.mul_assoc]
  have hsum : (A * (m / (A * 256))) * 256 + m % (A * 256) = m := by
    rw [← hassoc]; exact Nat.div_add_mod m (A * 256)
  have key : ((A * (m / (A * 256))) * 256 + m % (A * 256)) / 256
      = m % (A * 256) / 256 + A * (m / (A * 256)) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h256]
  have hstep : m / 256 = m % (A * 256) / 256 + A * (m / (A * 256)) := by
    calc m / 256 = ((A * (m / (A * 256))) * 256 + m % (A * 256)) / 256 := by rw [hsum]
      _ = m % (A * 256) / 256 + A * (m / (A * 256)) := key
  rw [hstep, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `Z_to_le_bytes` only reads the low `8n` bits, at a `Nat` argument.
 -/
theorem Z_to_le_bytes_mod_nat (n m : Nat) :
    Z_to_le_bytes n ((m % 2 ^ (8 * n) : Nat) : Int) = Z_to_le_bytes n (m : Int) := by
  induction n generalizing m with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  | succ n ih =>
    have hpow : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by
      rw [show 8 * (n + 1) = 8 * n + 8 from by omega, Nat.pow_add,
        show (2 : Nat) ^ 8 = 256 from by decide]
    rw [show Z_to_le_bytes (n + 1) ((m % 2 ^ (8 * (n + 1)) : Nat) : Int)
        = BitVec.ofInt 8 ((m % 2 ^ (8 * (n + 1)) : Nat) : Int)
          :: Z_to_le_bytes n (((m % 2 ^ (8 * (n + 1)) : Nat) : Int) >>> 8) from rfl,
      show Z_to_le_bytes (n + 1) (m : Int)
        = BitVec.ofInt 8 (m : Int) :: Z_to_le_bytes n ((m : Int) >>> 8) from rfl]
    have hhead : BitVec.ofInt 8 ((m % 2 ^ (8 * (n + 1)) : Nat) : Int)
        = BitVec.ofInt 8 ((m : Int)) := by
      refine BitVec.eq_of_toNat_eq ?_
      rw [toNat_ofInt_8_nat, toNat_ofInt_8_nat]
      exact Nat.mod_mod_of_dvd m ⟨2 ^ (8 * n), by rw [hpow, Nat.mul_comm]⟩
    have htail : Z_to_le_bytes n (((m % 2 ^ (8 * (n + 1)) : Nat) : Int) >>> 8)
        = Z_to_le_bytes n ((m : Int) >>> 8) := by
      rw [int_shiftRight_8_natCast, int_shiftRight_8_natCast, hpow,
        div_256_mod m (2 ^ (8 * n)) (Nat.two_pow_pos _)]
      exact ih (m / 256)
    rw [hhead, htail]

/-- The kept byte slices of a partially overwritten literal word.
 -/
theorem word_slice_bytes (w' d n : Nat) (V : word) (Hdn : d + n ≤ w') (Hw8 : w' ≤ 8) :
    word_to_le_bytes n (ext_val false d n V)
      = ((word_to_le_bytes w' V).drop d).take n := by
  have hn8 : n ≤ 8 := by omega
  have hbvN : bv_unsigned V = ((V.toNat : Nat) : Int) := rfl
  have hpowd : (2 : Int) ^ (8 * d) = ((2 ^ (8 * d) : Nat) : Int) :=
    (Int.natCast_pow 2 (8 * d)).symm
  have hpown : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) :=
    (Int.natCast_pow 2 (8 * n)).symm
  have hL : word_to_le_bytes n (ext_val false d n V)
      = Z_to_le_bytes n (bv_unsigned V / ((2 ^ (8 * d) : Nat) : Int)) := by
    have hu := ext_Z_range d n (bv_unsigned V) hn8
    have hult : (ext_Z false d n (bv_unsigned V)).toNat < 2 ^ 64 := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg hu.1]; exact hu.2
    have hbv : (Z_to_bv 64 (ext_Z false d n (bv_unsigned V))).toNat
        = (ext_Z false d n (bv_unsigned V)).toNat := by
      show (BitVec.ofInt 64 (ext_Z false d n (bv_unsigned V))).toNat = _
      rw [BitVec.toNat_ofInt, Int.toNat_emod hu.1 (Int.natCast_nonneg (2 ^ 64)),
        Int.toNat_natCast, Nat.mod_eq_of_lt hult]
    have hm : bv_unsigned V / ((2 ^ (8 * d) : Nat) : Int)
        = ((V.toNat / 2 ^ (8 * d) : Nat) : Int) := by
      rw [hbvN, ← Int.natCast_ediv]
    have hmod : bv_unsigned V / ((2 ^ (8 * d) : Nat) : Int) % ((2 ^ (8 * n) : Nat) : Int)
        = ((V.toNat / 2 ^ (8 * d) % 2 ^ (8 * n) : Nat) : Int) := by
      rw [hm, ← Int.natCast_emod]
    unfold word_to_le_bytes ext_val
    rw [hbv, Int.toNat_of_nonneg hu.1]
    show Z_to_le_bytes n (bv_unsigned V / (2 : Int) ^ (8 * d) % (2 : Int) ^ (8 * n)) = _
    rw [hpowd, hpown, hmod, hm]
    exact Z_to_le_bytes_mod_nat n (V.toNat / 2 ^ (8 * d))
  have hR : ((word_to_le_bytes w' V).drop d).take n
      = Z_to_le_bytes n (bv_unsigned V / ((2 ^ (8 * d) : Nat) : Int)) := by
    unfold word_to_le_bytes
    rw [skipn_Z_to_le_bytes w' d (V.toNat : Int) (by omega),
      firstn_Z_to_le_bytes (w' - d) n _ (by omega), hpowd, hbvN]
  rw [hL, hR]

/-! ### `kword_cut_sound`

    The literal bytes of a `KWord` that survive a PARTIAL overwrite of the
    same base: those below the store start (`d = 0`) and those above it.
    Both are one `KWord` at a byte-slice of the entry (`PIECE`), a
    `word_slice_bytes` instance. -/

theorem kword_cut_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (V : word) (kk : Int) (w' : Nat) (v : expr)
    (Hfw : flat E (SA wb wk) (w : Int))
    (HK : kentry_ok segs E M (.KWord (SA wb kk) w' v))
    (Hov1 : wk < kk + (w' : Int)) (Hov2 : kk < wk + (w : Int)) :
    ∀ K ∈ kword_cut wb kk w' v wk w,
      kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V)) K := by
  obtain ⟨Hkw8, Hfk0, Hrd⟩ := HK
  obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := Hfw
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hfk0
  have Hfw : flat E (SA wb wk) (w : Int) := ⟨Hw1, Hw2, Hw3, Hw4⟩
  have Hfk : flat E (SA wb kk) (w' : Int) := ⟨Hk1, Hk2, Hk3, Hk4⟩
  have hw1' : (0 : Int) ≤ bv_unsigned (edenot E wb) + wk := Hw1
  have hw2' : bv_unsigned (edenot E wb) + wk < 2 ^ 64 := Hw2
  have hw3' : (0 : Int) ≤ (w : Int) := Hw3
  have hk1' : (0 : Int) ≤ bv_unsigned (edenot E wb) + kk := Hk1
  have hk3' : (0 : Int) ≤ (w' : Int) := Hk3
  have hw4' : bv_unsigned (edenot E wb) + wk + (w : Int) ≤ 2 ^ 64 := Hw4
  have hk2' : bv_unsigned (edenot E wb) + kk < 2 ^ 64 := Hk2
  have hk4' : bv_unsigned (edenot E wb) + kk + (w' : Int) ≤ 2 ^ 64 := Hk4
  have Huw : ((adenot E (SA wb wk)).toNat : Int) = bv_unsigned (edenot E wb) + wk :=
    flat_u E _ _ Hfw
  cases v with
  | ELit z =>
    have PIECE : ∀ (d : Int) (n : Nat), 0 ≤ d → 1 ≤ n → d.toNat + n ≤ w' →
        (kk + d + (n : Int) ≤ wk ∨ wk + (w : Int) ≤ kk + d) →
        kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w V))
          (.KWord (SA wb (kk + d)) n (mkExt false d.toNat n (.ELit z))) := by
      intro d n Hd Hn1 Hdn Hdis
      have hdnI : d + (n : Int) ≤ (w' : Int) := by
        have h1 : ((d.toNat : Int)) = d := Int.toNat_of_nonneg Hd
        have h2 : ((d.toNat + n : Nat) : Int) ≤ (w' : Int) := by
          rw [Int.natCast_add]; exact Int.ofNat_le.mpr Hdn
        omega
      have hfp : flat E (SA wb (kk + d)) (n : Int) := by
        refine ⟨?_, ?_, by omega, ?_⟩
        · show (0 : Int) ≤ bv_unsigned (edenot E wb) + (kk + d); omega
        · show bv_unsigned (edenot E wb) + (kk + d) < 2 ^ 64
          omega
        · show bv_unsigned (edenot E wb) + (kk + d) + (n : Int) ≤ 2 ^ 64
          omega
      have hup : ((adenot E (SA wb (kk + d))).toNat : Int)
          = bv_unsigned (edenot E wb) + (kk + d) := flat_u E _ _ hfp
      refine ⟨by omega, hfp, ?_⟩
      have hout : ((adenot E (SA wb (kk + d))).toNat : Int) + (n : Int)
            ≤ ((adenot E (SA wb wk)).toNat : Int) ∨
          ((adenot E (SA wb wk)).toNat : Int) + ((word_to_le_bytes w V).length : Int)
            ≤ ((adenot E (SA wb (kk + d))).toNat : Int) := by
        rw [hup, Huw, length_N_to_le_bytes]
        rcases Hdis with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hnw : ((adenot E (SA wb (kk + d))).toNat : Int) + (n : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hup, ← two64_eq_natCast, two64_eq]; omega
      have hnw' : ((adenot E (SA wb wk)).toNat : Int) + ((word_to_le_bytes w V).length : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [Huw, length_N_to_le_bytes, ← two64_eq_natCast, two64_eq]; omega
      rw [rdn_wbytes_out segs (word_to_le_bytes w V) M (adenot E (SA wb wk))
        (adenot E (SA wb (kk + d))) n hout hnw hnw']
      have hshift : adenot E (SA wb (kk + d)) = adenot E (SA wb kk) + nat_to_word d.toNat :=
        adenot_shift E (SA wb kk) (SA wb (kk + d)) (w' : Int) (n : Int) d Hfk hfp
          (by show bv_unsigned (edenot E wb) + (kk + d) = bv_unsigned (edenot E wb) + kk + d
              omega)
          Hd
      rw [hshift]
      rw [rdn_slice segs M w' (adenot E (SA wb kk))
        (word_to_le_bytes w' (edenot E (.ELit z))) d.toNat n Hrd Hdn]
      rw [mkExt_denot E false d.toNat n (.ELit z) (by omega) (Or.inl rfl)]
      rw [word_slice_bytes w' d.toNat n (edenot E (.ELit z)) Hdn (by omega)]
    unfold kword_cut
    dsimp only
    intro K hK
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨hc, rfl⟩ := mem_ite_single_prop _ _ K hK
      have h := PIECE 0 (wk - kk).toNat (by omega) (by omega) (by omega) (Or.inl (by omega))
      rw [show kk + (0 : Int) = kk from by omega, show ((0 : Int)).toNat = 0 from rfl] at h
      exact h
    · obtain ⟨hc, rfl⟩ := mem_ite_single_prop _ _ K hK
      exact PIECE (wk + (w : Int) - kk) (w' - (wk + (w : Int) - kk).toNat)
        (by omega) (by omega) (by omega) (Or.inr (by omega))
  | _ => simp [kword_cut]



/-- The hint-list fallback table of `prune1`, as a standalone function: the
    store range is `apart` from the entry, or the caller's hint decides.
     -/
def prune1_dbfun (K : kentry) (allkn : List kentry) (wb : expr) (wk : Int) (w : Nat)
    (ka : saddr) (kl : expr) (hints : List Bool) :
    Unit → List kentry × List sidecond × List Bool :=
  fun _ =>
    if ranges_apart_x allkn wb wk (elen w) ka.a_base ka.a_off kl then
      ([K], ([] : List sidecond), hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj (SA wb wk) (elen w) ka kl], hs)
      | false :: hs => ([], [], hs)
      | [] => ([], [], [])

/-!  Here they are separate lemmas so the ten
    `kentry` constructors share them.  The split matters: the "shape" fact
    that `kentry_ok_frame` takes is a `match` on the entry, so it must be
    elaborated in a context where the entry and its `kentry_ok` are the only
    things depending on it — hence `prune1_keep_piece` takes the shape and
    the disjunction ONLY, and the membership plumbing lives in
    `prune1_diffbase_mem` (which needs no shape). -/

/-- One kept entry, at a range provably apart from the store.   -/
theorem prune1_keep_piece (segs : List Segment) (E : env) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (wv : expr) (K : kentry) (ka : saddr) (kl : expr)
    (Hfw : flat E (SA wb wk) (w : Int)) (HK : kentry_ok segs E M K)
    (Hshape : match K with
      | .KWord a w' _ => ka = a ∧ kl = elen w' ∧ w' ≤ 8
      | .KZero a n => ka = a ∧ kl = n
      | .KBlob a n _ => ka = a ∧ kl = n
      | .KImg lo hi => ka = SA (.ELit 0) lo ∧ kl = .ELit (hi - lo) ∧ hi - lo < 2 ^ 64
      | .KAlign _ _ => True
      | .KRange _ _ _ => True
      | .KWr _ _ => True
      | .KDisj _ _ _ _ => True
      | .KFill a n _ => ka = a ∧ kl = n
      | .KUnk a n => ka = a ∧ kl = n)
    (Hdis : estart E (SA wb wk) + (w : Int) ≤ estart E ka ∨
      estart E ka + elenZ E kl ≤ estart E (SA wb wk)) :
    kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv))) K :=
  kentry_ok_frame segs E M (SA wb wk) w (edenot E wv) K ka kl Hfw HK Hshape Hdis

/-- The membership plumbing of `prune1`'s hint-fallback arms.  Generic in the
    property of the entry, so the caller supplies the two "keep" cases. -/
theorem prune1_diffbase_mem {P : kentry → Prop} (K : kentry) (allkn : List kentry)
    (wb : expr) (wk : Int) (w : Nat) (ka : saddr) (kl : expr)
    (hints : List Bool) (kept : List kentry) (scs : List sidecond) (hs' : List Bool)
    (segs : List Segment) (anybase : word → Option byte) (E : env) (Hw8 : w ≤ 8)
    (Hm : prune1_dbfun K allkn wb wk w ka kl hints () = (kept, scs, hs'))
    (Hscs : scs_denot segs anybase E scs)
    (Hapart : ranges_apart_x allkn wb wk (elen w) ka.a_base ka.a_off kl = true → P K)
    (Hhint : (estart E (SA wb wk) + (w : Int) ≤ estart E ka ∨
      estart E ka + elenZ E kl ≤ estart E (SA wb wk)) → P K) :
    ∀ K' ∈ kept, P K' := by
  dsimp only [prune1_dbfun] at Hm
  by_cases hap : ranges_apart_x allkn wb wk (elen w) ka.a_base ka.a_off kl = true
  · rw [ite_eq_left hap] at Hm
    obtain ⟨rfl, rfl, rfl⟩ := Hm
    exact Forall_one _ _ (Hapart hap)
  · rw [ite_eq_right hap] at Hm
    cases hints with
    | nil =>
      obtain ⟨rfl, rfl, rfl⟩ := Hm
      intro K' hK'
      exact absurd hK' (by simp)
    | cons b hs =>
      cases b with
      | false =>
        obtain ⟨rfl, rfl, rfl⟩ := Hm
        intro K' hK'
        exact absurd hK' (by simp)
      | true =>
        obtain ⟨rfl, rfl, rfl⟩ := Hm
        refine Forall_one _ _ ?_
        have hsc := Hscs (.SCDisj (SA wb wk) (elen w) ka kl) (by simp)
        obtain ⟨-, -, hdis⟩ := hsc
        rw [elenZ_elen E w Hw8] at hdis
        exact Hhint hdis

/-- The `KZero`/`KFill`/`KUnk` arm: `prune1` hands off to `prune_zf`.
     -/
theorem prune1_zf_sound (segs : List Segment) (E : env) (anybase M0 : word → Option byte)
    (allkn : List kentry) (M : word → Option byte)
    (wb : expr) (wk : Int) (w : Nat) (wv : expr) (K : kentry)
    (mk : saddr → expr → kentry) (byteof : Option byte → Prop)
    (kb : expr) (kk : Int) (len : expr) (hints : List Bool)
    (kept : List kentry) (scs : List sidecond) (hs' : List Bool)
    (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8) (Hfw : flat E (SA wb wk) (w : Int))
    (Hkind : zf_kind segs mk byteof)
    (HKm : kentry_ok segs E M (mk (SA kb kk) len))
    (Hp : prune_zf mk allkn wb wk w (mk (SA kb kk) len) kb kk len
        (fun _ => ranges_apart_x allkn wb wk (elen w) kb kk len) hints
        (prune1_dbfun K allkn wb wk w (SA kb kk) len hints) = (kept, scs, hs'))
    (Hapart : ranges_apart_x allkn wb wk (elen w) kb kk len = true →
      (estart E (SA wb wk) + (w : Int) ≤ estart E (SA kb kk) ∨
        estart E (SA kb kk) + elenZ E len ≤ estart E (SA wb wk)))
    (Hdb : prune1_dbfun K allkn wb wk w (SA kb kk) len hints () = (kept, scs, hs') →
      scs_denot segs anybase E scs →
      ∀ K' ∈ kept,
        kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv))) K')
    (Hscs : scs_denot segs anybase E scs) :
    ∀ K' ∈ kept,
      kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv))) K' :=
  prune_zf_sound segs mk byteof E anybase M0 M allkn wb wk w (edenot E wv) kb kk len
    (fun _ => ranges_apart_x allkn wb wk (elen w) kb kk len) hints
    (prune1_dbfun K allkn wb wk w (SA kb kk) len hints)
    kept scs hs' Hkind Hp Hall Hw8 Hfw HKm Hapart Hdb Hscs

/-- The benign alias of `prune1`'s `KWord` arm: a ONE-byte store of the same
    value leaves a one-byte `KWord` intact — either the read hits the store
    (`rdn_wbytes_hit`) or it misses it (`rdn_wbytes_out`). -/
theorem kword1_same_write (segs : List Segment) (E : env) (M : word → Option byte)
    (wa : saddr) (wv : expr) (kb : expr) (kk : Int) (v : expr)
    (Hfw : flat E wa (1 : Int)) (HK : kentry_ok segs E M (.KWord (SA kb kk) 1 v))
    (hwv : wv = v) :
    kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes 1 (edenot E wv)))
      (.KWord (SA kb kk) 1 v) := by
  rw [hwv]
  obtain ⟨h8, hfk, hrd⟩ := HK
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hfk
  obtain ⟨hw1, hw2, hw3, hw4⟩ := Hfw
  have Hfw' : flat E wa (1 : Int) := ⟨hw1, hw2, hw3, hw4⟩
  have Hfk' : flat E (SA kb kk) (1 : Int) := ⟨hk1, hk2, hk3, hk4⟩
  refine ⟨h8, Hfk', ?_⟩
  have Huw : ((adenot E wa).toNat : Int) = estart E wa := flat_u E _ _ Hfw'
  have Huk : ((adenot E (SA kb kk)).toNat : Int) = estart E (SA kb kk) := flat_u E _ _ Hfk'
  have hk4' : ((adenot E (SA kb kk)).toNat : Int) + (1 : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [Huk, ← two64_eq_natCast, two64_eq]; exact hk4
  have hw4' : ((adenot E wa).toNat : Int) + ((word_to_le_bytes 1 (edenot E v)).length : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [Huw, length_N_to_le_bytes, ← two64_eq_natCast, two64_eq]; exact hw4
  by_cases heq : bv_unsigned (adenot E (SA kb kk)) = bv_unsigned (adenot E wa)
  · have ea : adenot E (SA kb kk) = adenot E wa := by
      apply BitVec.eq_of_toNat_eq
      have h := heq
      simp only [bv_unsigned] at h
      omega
    rw [ea]
    have hhit := SeqExec.rdn_wbytes_hit segs (word_to_le_bytes 1 (edenot E v)) M (adenot E wa) hw4'
    rwa [show (word_to_le_bytes 1 (edenot E v)).length = 1 from length_N_to_le_bytes 1 _] at hhit
  · have hout : ((adenot E (SA kb kk)).toNat : Int) + (1 : Int)
          ≤ ((adenot E wa).toNat : Int) ∨
        ((adenot E wa).toNat : Int) + ((word_to_le_bytes 1 (edenot E v)).length : Int)
          ≤ ((adenot E (SA kb kk)).toNat : Int) := by
      rw [length_N_to_le_bytes]
      have h := heq
      simp only [bv_unsigned] at h
      omega
    rw [rdn_wbytes_out segs (word_to_le_bytes 1 (edenot E v)) M (adenot E wa)
      (adenot E (SA kb kk)) 1 hout hk4' hw4']
    exact hrd

/-- **`prune1_sound`** : one knowledge entry survives the
    store `wa, +w`, either kept whole (its range is apart from the store or
    the caller's hint says so) or split into the bytes the store does not
    cover. -/
theorem prune1_sound (segs : List Segment) (E : env) (anybase M0 : word → Option byte)
    (allkn : List kentry) (M : word → Option byte)
    (wa : saddr) (w : Nat) (wv : expr) (K : kentry) (hints : List Bool)
    (kept : List kentry) (scs : List sidecond) (hs' : List Bool)
    (Hp : prune1 allkn wa w wv K hints = (kept, scs, hs'))
    (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8) (Hfw : flat E wa (w : Int))
    (HK : kentry_ok segs E M K)
    (Hscs : scs_denot segs anybase E scs) :
    ∀ K' ∈ kept,
      kentry_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w (edenot E wv))) K' := by
  obtain ⟨wb, wk⟩ := wa
  have Hfw' : flat E (SA wb wk) (w : Int) := Hfw
  unfold prune1 at Hp
  cases K with
  | KAlign e m =>
    dsimp only at Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp
    exact Forall_one _ _ HK
  | KRange e lo hi =>
    dsimp only at Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp
    exact Forall_one _ _ HK
  | KWr a n =>
    dsimp only at Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp
    refine Forall_one _ _ ?_
    obtain ⟨hf0, hs0⟩ := HK
    refine ⟨hf0, ?_⟩
    intro d m' Hd Hm'
    exact store_ok_mono segs m' M
      (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv)))
      (Z_to_bv 64 (estart E a + d))
      (wbytes_grows (word_to_le_bytes w (edenot E wv)) M (adenot E (SA wb wk)))
      (hs0 d m' Hd Hm')
  | KDisj a1 n1 a2 n2 =>
    dsimp only at Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp
    exact Forall_one _ _ HK
  | KImg lo hi =>
    dsimp only at Hp
    have hws : estart E (SA (.ELit 0) wk) = wk := by
      show bv_unsigned (Z_to_bv 64 0) + wk = wk
      rw [u_lit64a]; simp
    have hfb : (if hi - lo < 2 ^ 64 then
                  prune1_dbfun (.KImg lo hi) allkn wb wk w (SA (.ELit 0) lo) (.ELit (hi - lo)) hints ()
                else ([], [], hints)) = (kept, scs, hs') →
        ∀ K' ∈ kept,
          kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv))) K' := by
      intro Hq
      by_cases hlt : hi - lo < 2 ^ 64
      · rw [ite_eq_left hlt] at Hq
        refine prune1_diffbase_mem (.KImg lo hi) allkn wb wk w (SA (.ELit 0) lo)
          (.ELit (hi - lo)) hints kept scs hs' segs anybase E Hw8 Hq Hscs ?_ ?_
        · intro hap
          exact prune1_keep_piece segs E M wb wk w wv (.KImg lo hi) (SA (.ELit 0) lo)
            (.ELit (hi - lo)) Hfw' HK ⟨rfl, rfl, hlt⟩ (by
              have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) (.ELit 0) lo
                (.ELit (hi - lo)) Hall hap
              rwa [elenZ_elen E w Hw8] at h)
        · intro hdis
          exact prune1_keep_piece segs E M wb wk w wv (.KImg lo hi) (SA (.ELit 0) lo)
            (.ELit (hi - lo)) Hfw' HK ⟨rfl, rfl, hlt⟩ hdis
      · rw [ite_eq_right hlt] at Hq
        obtain ⟨rfl, rfl, rfl⟩ := Hq
        intro K' hK'
        exact absurd hK' (by simp)
    cases wb with
    | ELit z =>
      cases z with
      | ofNat nz =>
        cases nz with
        | zero =>
          try dsimp only at Hp
          obtain ⟨rfl, rfl, rfl⟩ := Hp
          refine Forall_app_intro _ _ _ ?_ ?_
          · by_cases h1 : lo < min wk hi
            · rw [ite_eq_left h1]
              refine Forall_one _ _ ?_
              exact kimg_piece segs E M (SA (.ELit 0) wk) w (edenot E wv) lo hi lo (min wk hi)
                Hfw' HK (by omega) (by omega) (by rw [hws]; omega)
            · rw [ite_eq_right h1]
              intro K' hK'
              exact absurd hK' (by simp)
          · by_cases h2 : max lo (wk + (w : Int)) < hi
            · rw [ite_eq_left h2]
              refine Forall_one _ _ ?_
              exact kimg_piece segs E M (SA (.ELit 0) wk) w (edenot E wv) lo hi
                (max lo (wk + (w : Int))) hi Hfw' HK (by omega) (by omega) (by rw [hws]; omega)
            · rw [ite_eq_right h2]
              intro K' hK'
              exact absurd hK' (by simp)
        | succ mz =>
          try dsimp only at Hp
          exact hfb Hp
      | negSucc mz =>
        try dsimp only at Hp
        exact hfb Hp
    | EVar n =>
      try dsimp only at Hp
      exact hfb Hp
    | EAlu op a b =>
      try dsimp only at Hp
      exact hfb Hp
    | EAluw op a b =>
      try dsimp only at Hp
      exact hfb Hp
    | EMd op a b =>
      try dsimp only at Hp
      exact hfb Hp
    | EMdw op a b =>
      try dsimp only at Hp
      exact hfb Hp
    | EExt sx lo' n' e =>
      try dsimp only at Hp
      exact hfb Hp
    | EBlob sx k i n' =>
      try dsimp only at Hp
      exact hfb Hp
  | KZero a n =>
    obtain ⟨kb, kk⟩ := a
    dsimp only at Hp
    refine prune1_zf_sound segs E anybase M0 allkn M wb wk w wv (.KZero (SA kb kk) n) .KZero
      (fun x => x = some (BitVec.ofInt 8 0)) kb kk n hints kept scs hs' Hall Hw8 Hfw'
      (zf_kind_zero segs) HK Hp ?_ ?_ Hscs
    · intro Hap
      have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall Hap
      rwa [elenZ_elen E w Hw8] at h
    · intro Hm Hsc
      refine prune1_diffbase_mem (.KZero (SA kb kk) n) allkn wb wk w (SA kb kk) n hints
        kept scs hs' segs anybase E Hw8 Hm Hsc ?_ ?_
      · intro hap
        refine prune1_keep_piece segs E M wb wk w wv (.KZero (SA kb kk) n) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ ?_
        have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall hap
        rwa [elenZ_elen E w Hw8] at h
      · intro hdis
        exact prune1_keep_piece segs E M wb wk w wv (.KZero (SA kb kk) n) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ hdis
  | KFill a n c =>
    obtain ⟨kb, kk⟩ := a
    dsimp only at Hp
    refine prune1_zf_sound segs E anybase M0 allkn M wb wk w wv (.KFill (SA kb kk) n c)
      (fun a n => .KFill a n c) (fun x => x = some (BitVec.ofInt 8 c)) kb kk n hints kept scs hs'
      Hall Hw8 Hfw' (zf_kind_fill segs c) HK Hp ?_ ?_ Hscs
    · intro Hap
      have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall Hap
      rwa [elenZ_elen E w Hw8] at h
    · intro Hm Hsc
      refine prune1_diffbase_mem (.KFill (SA kb kk) n c) allkn wb wk w (SA kb kk) n hints
        kept scs hs' segs anybase E Hw8 Hm Hsc ?_ ?_
      · intro hap
        refine prune1_keep_piece segs E M wb wk w wv (.KFill (SA kb kk) n c) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ ?_
        have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall hap
        rwa [elenZ_elen E w Hw8] at h
      · intro hdis
        exact prune1_keep_piece segs E M wb wk w wv (.KFill (SA kb kk) n c) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ hdis
  | KUnk a n =>
    obtain ⟨kb, kk⟩ := a
    dsimp only at Hp
    refine prune1_zf_sound segs E anybase M0 allkn M wb wk w wv (.KUnk (SA kb kk) n) .KUnk
      (fun x => x ≠ none) kb kk n hints kept scs hs' Hall Hw8 Hfw'
      (zf_kind_unk segs) HK Hp ?_ ?_ Hscs
    · intro Hap
      have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall Hap
      rwa [elenZ_elen E w Hw8] at h
    · intro Hm Hsc
      refine prune1_diffbase_mem (.KUnk (SA kb kk) n) allkn wb wk w (SA kb kk) n hints
        kept scs hs' segs anybase E Hw8 Hm Hsc ?_ ?_
      · intro hap
        refine prune1_keep_piece segs E M wb wk w wv (.KUnk (SA kb kk) n) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ ?_
        have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall hap
        rwa [elenZ_elen E w Hw8] at h
      · intro hdis
        exact prune1_keep_piece segs E M wb wk w wv (.KUnk (SA kb kk) n) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ hdis
  | KWord a w' v =>
    obtain ⟨kb, kk⟩ := a
    dsimp only at Hp
    have hw8' : w' ≤ 8 := HK.1
    by_cases hb : expr_eqb kb wb = true
    · rw [ite_eq_left hb] at Hp
      have hkbeq : kb = wb := expr_eqb_eq kb wb hb
      rw [hkbeq] at Hp HK
      by_cases hov : kk + (w' : Int) ≤ wk ∨ wk + (w : Int) ≤ kk
      · have hb1 : (kk + (w' : Int) ≤ wk || wk + (w : Int) ≤ kk) = true := by
          rcases hov with h | h <;> simp [h]
        rw [ite_eq_left hb1] at Hp
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        refine Forall_one _ _ ?_
        refine prune1_keep_piece segs E M wb wk w wv (.KWord (SA wb kk) w' v) (SA wb kk)
          (elen w') Hfw' HK ⟨rfl, rfl, hw8'⟩ ?_
        rw [elenZ_elen E w' hw8']
        rcases hov with h | h
        · exact Or.inr (by
            show bv_unsigned (edenot E wb) + kk + (w' : Int) ≤ bv_unsigned (edenot E wb) + wk
            omega)
        · exact Or.inl (by
            show bv_unsigned (edenot E wb) + wk + (w : Int) ≤ bv_unsigned (edenot E wb) + kk
            omega)
      · have hb0 : (kk + (w' : Int) ≤ wk || wk + (w : Int) ≤ kk) = false := by
          rcases not_or.mp hov with ⟨h1, h2⟩
          simp [h1, h2]
        rw [ite_eq_right (by rw [hb0]; simp)] at Hp
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        exact kword_cut_sound segs E M wb wk w (edenot E wv) kk w' v Hfw' HK (by omega) (by omega)
    · rw [ite_eq_right hb] at Hp
      by_cases hap : ranges_apart_x allkn wb wk (elen w) kb kk (elen w') = true
      · rw [ite_eq_left hap] at Hp
        obtain ⟨rfl, rfl, rfl⟩ := Hp
        refine Forall_one _ _ ?_
        refine prune1_keep_piece segs E M wb wk w wv (.KWord (SA kb kk) w' v) (SA kb kk)
          (elen w') Hfw' HK ⟨rfl, rfl, hw8'⟩ ?_
        have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk (elen w') Hall hap
        rwa [elenZ_elen E w Hw8] at h
      · rw [ite_eq_right hap] at Hp
        by_cases hben : (w == 1 && w' == 1 && expr_eqb wv v) = true
        · rw [ite_eq_left hben] at Hp
          obtain ⟨rfl, rfl, rfl⟩ := Hp
          refine Forall_one _ _ ?_
          rw [Bool.and_eq_true] at hben
          obtain ⟨hben1, hvv⟩ := hben
          rw [Bool.and_eq_true] at hben1
          obtain ⟨hw1, hw1'⟩ := hben1
          rw [beq_iff_eq] at hw1 hw1'
          have hwvv : wv = v := expr_eqb_eq wv v hvv
          rw [hw1] at Hfw' ⊢
          rw [hw1'] at HK hw8' ⊢
          exact kword1_same_write segs E M (SA wb wk) wv kb kk v Hfw' HK hwvv
        · rw [ite_eq_right hben] at Hp
          refine prune1_diffbase_mem (.KWord (SA kb kk) w' v) allkn wb wk w (SA kb kk)
            (elen w') hints kept scs hs' segs anybase E Hw8 Hp Hscs ?_ ?_
          · intro hapd
            refine prune1_keep_piece segs E M wb wk w wv (.KWord (SA kb kk) w' v) (SA kb kk)
              (elen w') Hfw' HK ⟨rfl, rfl, hw8'⟩ ?_
            have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk (elen w')
              Hall hapd
            rwa [elenZ_elen E w Hw8] at h
          · intro hdis
            exact prune1_keep_piece segs E M wb wk w wv (.KWord (SA kb kk) w' v) (SA kb kk)
              (elen w') Hfw' HK ⟨rfl, rfl, hw8'⟩ hdis
  | KBlob a n bk =>
    obtain ⟨kb, kk⟩ := a
    dsimp only at Hp
    by_cases hb : expr_eqb kb wb = true
    · rw [ite_eq_left hb] at Hp
      have hkbeq : kb = wb := expr_eqb_eq kb wb hb
      rw [hkbeq] at Hp HK
      have NOK : ∀ (nn : expr), kentry_ok segs E M (.KBlob (SA wb kk) nn bk) →
          (if wk + (w : Int) ≤ kk then
              ([.KBlob (SA wb kk) nn bk], ([] : List sidecond), hints)
           else ([], [], hints)) = (kept, scs, hs') →
          ∀ K' ∈ kept,
            kentry_ok segs E (wbytes M (adenot E (SA wb wk)) (word_to_le_bytes w (edenot E wv))) K' := by
        intro nn HKn Hm
        by_cases hle : wk + (w : Int) ≤ kk
        · rw [ite_eq_left hle] at Hm
          obtain ⟨rfl, rfl, rfl⟩ := Hm
          refine Forall_one _ _ ?_
          exact prune1_keep_piece segs E M wb wk w wv (.KBlob (SA wb kk) nn bk) (SA wb kk) nn
            Hfw' HKn ⟨rfl, rfl⟩ (Or.inl (by
              show bv_unsigned (edenot E wb) + wk + (w : Int) ≤ bv_unsigned (edenot E wb) + kk
              omega))
        · rw [ite_eq_right hle] at Hm
          obtain ⟨rfl, rfl, rfl⟩ := Hm
          intro K' hK'
          exact absurd hK' (by simp)
      cases n with
      | ELit l0 =>
        dsimp only at Hp
        by_cases hc : kk + l0 % two64 ≤ wk ∨ wk + (w : Int) ≤ kk
        · have hb1 : (kk + l0 % two64 ≤ wk || wk + (w : Int) ≤ kk) = true := by
            rcases hc with h | h <;> simp [h]
          rw [ite_eq_left hb1] at Hp
          obtain ⟨rfl, rfl, rfl⟩ := Hp
          refine Forall_one _ _ ?_
          refine prune1_keep_piece segs E M wb wk w wv (.KBlob (SA wb kk) (.ELit l0) bk)
            (SA wb kk) (.ELit l0) Hfw' HK ⟨rfl, rfl⟩ ?_
          rw [elenZ_lit]
          rw [two64_eq] at hc
          rcases hc with h | h
          · exact Or.inr (by
              show bv_unsigned (edenot E wb) + kk + l0 % 2 ^ 64
                ≤ bv_unsigned (edenot E wb) + wk
              omega)
          · exact Or.inl (by
              show bv_unsigned (edenot E wb) + wk + (w : Int) ≤ bv_unsigned (edenot E wb) + kk
              omega)
        · have hb0 : (kk + l0 % two64 ≤ wk || wk + (w : Int) ≤ kk) = false := by
            rcases not_or.mp hc with ⟨h1, h2⟩
            simp [h1, h2]
          rw [ite_eq_right (by rw [hb0]; simp)] at Hp
          obtain ⟨rfl, rfl, rfl⟩ := Hp
          intro K' hK'
          exact absurd hK' (by simp)
      | EVar m => dsimp only at Hp; exact NOK _ HK Hp
      | EAlu op a1 b1 => dsimp only at Hp; exact NOK _ HK Hp
      | EAluw op a1 b1 => dsimp only at Hp; exact NOK _ HK Hp
      | EMd op a1 b1 => dsimp only at Hp; exact NOK _ HK Hp
      | EMdw op a1 b1 => dsimp only at Hp; exact NOK _ HK Hp
      | EExt sx lo' n' e => dsimp only at Hp; exact NOK _ HK Hp
      | EBlob sx k i n' => dsimp only at Hp; exact NOK _ HK Hp
    · rw [ite_eq_right hb] at Hp
      refine prune1_diffbase_mem (.KBlob (SA kb kk) n bk) allkn wb wk w (SA kb kk) n hints
        kept scs hs' segs anybase E Hw8 Hp Hscs ?_ ?_
      · intro hapd
        refine prune1_keep_piece segs E M wb wk w wv (.KBlob (SA kb kk) n bk) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ ?_
        have h := ranges_apart_x_sound segs E M0 allkn wb wk (elen w) kb kk n Hall hapd
        rwa [elenZ_elen E w Hw8] at h
      · intro hdis
        exact prune1_keep_piece segs E M wb wk w wv (.KBlob (SA kb kk) n bk) (SA kb kk) n
          Hfw' HK ⟨rfl, rfl⟩ hdis

/-- **`prune_sound`** : pruning the whole knowledge list keeps
    every entry sound. -/
theorem prune_sound (segs : List Segment) (E : env) (anybase M0 : word → Option byte)
    (allkn : List kentry) (M : word → Option byte) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) (hints : List Bool) (kn' : List kentry) (scs : List sidecond)
    (hs' : List Bool)
    (Hp : prune allkn wa w wv kn hints = (kn', scs, hs'))
    (Hall : know_ok segs E M0 allkn) (Hw8 : w ≤ 8) (Hfw : flat E wa (w : Int))
    (Hkn : know_ok segs E M kn) (Hscs : scs_denot segs anybase E scs) :
    know_ok segs E (wbytes M (adenot E wa) (word_to_le_bytes w (edenot E wv))) kn' := by
  revert Hp Hkn Hscs
  revert hints kn' scs hs'
  induction kn with
  | nil =>
    intro hints kn' scs hs' Hp Hkn Hscs
    dsimp only [prune] at Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp
    intro K hK
    exact absurd hK (by simp)
  | cons K rest ih =>
    intro hints kn' scs hs' Hp Hkn Hscs
    have hK : kentry_ok segs E M K := Hkn K (List.mem_cons_self ..)
    have hrest : know_ok segs E M rest := fun x hx => Hkn x (List.mem_cons_of_mem _ hx)
    dsimp only [prune] at Hp
    obtain ⟨k1, scs1, hs1, hp1⟩ :
        ∃ a b c, prune1 allkn wa w wv K hints = (a, b, c) := ⟨_, _, _, rfl⟩
    rw [hp1] at Hp
    dsimp only at Hp
    obtain ⟨k2, scs2, hs2, hp2⟩ :
        ∃ a b c, prune allkn wa w wv rest hs1 = (a, b, c) := ⟨_, _, _, rfl⟩
    rw [hp2] at Hp
    dsimp only at Hp
    have h1 : k1 ++ k2 = kn' := congrArg Prod.fst Hp
    have h2 : scs1 ++ scs2 = scs := congrArg (fun p => p.2.1) Hp
    rw [← h1]
    rw [← h2] at Hscs
    have hs1d : scs_denot segs anybase E scs1 := (scs_denot_app segs anybase E scs1 scs2).mp Hscs |>.1
    have hs2d : scs_denot segs anybase E scs2 := (scs_denot_app segs anybase E scs1 scs2).mp Hscs |>.2
    intro K' hK'
    rcases List.mem_append.mp hK' with h | h
    · exact prune1_sound segs E anybase M0 allkn M wa w wv K hints k1 scs1 hs1 hp1 Hall Hw8
        Hfw hK hs1d K' h
    · exact ih hs1 k2 scs2 hs2 hp2 hrest hs2d K' h

/-- **`carry_sound`** : the knowledge carried across a block
    for the store log `log` is sound for `mem_denot E base log`.  This is
    the theorem `AxSymRun3.carry_after` consumes. -/
theorem carry_sound (segs : List Segment) (E : env) (anybase : word → Option byte)
    (base : word → Option byte) (log : List sentry) (kn : List kentry) (hints : List Bool)
    (kn' : List kentry) (scs : List sidecond) (hs' : List Bool)
    (Hc : carry log kn hints = (kn', scs, hs'))
    (Hlf : log_flat E log) (Hkn : know_ok segs E base kn)
    (Hscs : scs_denot segs anybase E scs) :
    know_ok segs E (mem_denot E base log) kn' := by
  revert Hc Hlf Hkn Hscs
  revert kn hints kn' scs hs'
  induction log with
  | nil =>
    intro kn hints kn' scs hs' Hc Hlf Hkn Hscs
    dsimp only [carry] at Hc
    obtain ⟨rfl, rfl, rfl⟩ := Hc
    exact Hkn
  | cons hd older ih =>
    obtain ⟨a, w, v⟩ := hd
    intro kn hints kn' scs hs' Hc Hlf Hkn Hscs
    dsimp only [carry, log_flat] at Hc Hlf
    obtain ⟨hw8, hfa, hlf⟩ := Hlf
    obtain ⟨c1, hc1⟩ : ∃ c1, carry older kn hints = c1 := ⟨_, rfl⟩
    rw [hc1] at Hc
    obtain ⟨kn1, scs1, hs1⟩ := c1
    dsimp only at Hc
    rw [prunepc_eq (facts_of kn1) (mk_sprep (facts_of kn1) a.a_base a.a_off (elen w)) a w v kn1
      hs1 [] (by intro p hp; exact absurd hp (by simp))] at Hc
    rw [prunep_eq (facts_of kn1) a w v kn1 hs1] at Hc
    obtain ⟨c2, hc2⟩ : ∃ c2, prune (facts_of kn1) a w v kn1 hs1 = c2 := ⟨_, rfl⟩
    rw [hc2] at Hc
    obtain ⟨kn2, scs2, hs2⟩ := c2
    dsimp only at Hc
    have h1 : .KWord a w v :: kn2 = kn' := congrArg Prod.fst Hc
    have h2 : scs1 ++ scs2 = scs := congrArg (fun p => p.2.1) Hc
    rw [← h1]
    rw [← h2] at Hscs
    dsimp only [mem_denot]
    have hs1d : scs_denot segs anybase E scs1 := (scs_denot_app segs anybase E scs1 scs2).mp Hscs |>.1
    have hs2d : scs_denot segs anybase E scs2 := (scs_denot_app segs anybase E scs1 scs2).mp Hscs |>.2
    have hkn1 : know_ok segs E (mem_denot E base older) kn1 :=
      ih kn hints kn1 scs1 hs1 hc1 hlf Hkn hs1d
    intro K' hK'
    rcases List.mem_cons.mp hK' with rfl | hK'
    · refine ⟨hw8, hfa, ?_⟩
      have hbnd : ((adenot E a).toNat : Int)
          + ((word_to_le_bytes w (edenot E v)).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
        have hu : ((adenot E a).toNat : Int) = estart E a := flat_u E a (w : Int) hfa
        rw [length_N_to_le_bytes, hu, ← two64_eq_natCast, two64_eq]
        exact hfa.2.2.2
      have hhit := SeqExec.rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v))
        (mem_denot E base older) (adenot E a) hbnd
      rwa [show (word_to_le_bytes w (edenot E v)).length = w from length_N_to_le_bytes w _] at hhit
    · exact prune_sound segs E anybase (mem_denot E base older) (facts_of kn1)
        (mem_denot E base older) a w v kn1 hs1 kn2 scs2 hs2 hc2
        (facts_of_ok segs E (mem_denot E base older) kn1 hkn1) hw8 hfa hkn1 hs2d K' hK'
