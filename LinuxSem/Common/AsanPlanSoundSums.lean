/-
  * `x_stmt` soundness for the byte-routine summaries (Module APSX)
  module `APSX`.
    Covers `summary_copy` with the HAVOC-SOURCE branch + `after_call2` fresh
    destination words, and the byte fallback of `copy_facts`.

    Image-independent.  Same Section variables / hypotheses as
    [`AsanPlanSound.APS`] (Section [`Sound`]) plus ONE hypothesis per
    summarized routine, of the shapes [`fill_spec`] / [`copy_spec`] /
    [`miz_spec`] below (a routine summary restated over [`SEGS`] and a `Z`
    entry pc), and ONE extra image fact [`segs_wr_ok SEGS`] (every writable
    segment is readable; needed by the havoc-source copy, which derives
    readability of the source from its KWr-writability).
    Pattern (`AsanPlanSound.run_block_sound`): the summary's [`msteps`] fact
    is instantiated with the RESTRICTED memory [`Mr E cs model FULL`] (the
    memory the knowledge talks about), lifted to `realizes` on the full
    memory / real model with `AsanAcctShape.srz_msteps_restricted_T`, and
    [`cs_ok`] of the node's post-state is re-established for every
    materialized successor model under an extended valuation [`E'`]
    ([`call_core`]; [`call_node_sound`] for [`after_call`]: E' =
    [`ext_call E nx regs'`] = the 16 caller-saved values; [`call_node_sound2`]
    for [`after_call2 .. extra`]: E' = [`ext_call2 E nx regs' vals`] = those +
    [`extra`] more values [`vals`], for the havoc-source copy the destination
    words read back from the post-copy memory).  Adding a further fact shape
    for the havoc'd destination (a [`KUnk dst n`]) = one more conjunct in the
    [`GEN`] step of [`summary_copy_sound`] (the bytes exist:
    [`wbytes_defined`]).
    USAGE (assembly).  [`APS.check_sound`] has the hypothesis
    [`node_x_sound : forall x, APS.x_stmt SEGS A nx0 LIMIT SINV argH FS0 x`].
    Discharge it by [`destruct x`]; the five summary cases are the theorems of
    part 6 of this file,

      APSX.node_x_sound_XIMemset   : ... -> APSX.fill_spec SEGS (x_imemset A) 256    -> APS.x_stmt SEGS A nx0 LIMIT SINV argH FS0 XIMemset
      APSX.node_x_sound_XMemset    : ... -> APSX.fill_spec SEGS (x_memset A) two64   -> APS.x_stmt ... XMemset
      APSX.node_x_sound_XIMemcpy   : ... -> APSX.segs_wr_ok SEGS -> APSX.copy_spec SEGS (x_imemcpy A) -> APS.x_stmt ... XIMemcpy
      APSX.node_x_sound_XMemcpy    : ... -> APSX.segs_wr_ok SEGS -> APSX.copy_spec SEGS (x_memcpy A)  -> APS.x_stmt ... XMemcpy
      APSX.node_x_sound_XMemIsZero : ... -> APSX.miz_spec SEGS (x_memiszero A)       -> APS.x_stmt ... XMemIsZero
    where [...] = SEGS A nx0 LIMIT, SEGS_wx, SEGS_in_hull, hull_ok (stated as
    [`hull_okP A`], convertible to [`hull_ok A`] and to the bare conjunction),
    SINV argH, argH_high, argH_agree, SINV_frame, SINV_agree, FS0 — APS's own
    Section variables / hypotheses; so inside any context holding them,
    [`eapply APSX.node_x_sound_XIMemcpy; try eassumption`] leaves
    [`segs_wr_ok SEGS`] and the summary fact.
  * `Z` is `Int`, `nat` is `Nat`, `Z.of_nat` is `(· : Int)`, `Z.leb` /
    `Z.ltb` / `Z.eqb` become `≤` / `<` / `==`, `negb` is `!`,
    `existsb` / `forallb` are `List.any` / `List.all`, `Z.to_nat` is
    `Int.toNat`, `repeat` is `List.replicate`, `nth` is `List.getD`,
    `2 ^ k` on `Int` is `zpow 2 k` (`AsanPlanCore`).
  * `bitvec` bit-blasting lemmas: `Z.land` / `Z.lor` / `Z.shiftl` /
    `Z.shiftr` and `Z.bits_inj'` are absent, so the two little-endian
    round-trip lemmas (`Z_to_le_bytes_of_bytes`, `word_to_le_bytes_of_bytes`)
    are re-done on this tree's `Z_to_le_bytes` recursion with `Nat`/`Int`
    `%`-arithmetic instead of `Z.bits_inj'`.
  * Word hygiene: this file contains no proof hole and no extra postulate.
  : the WHOLE of parts 1–2 is present — every
  definition of the file (`kept_ok`, `fill_spec`, `copy_spec`, `miz_spec`,
  `SEALED_BYTES`, `istrncpy_spec`, `ext_call`, `ext_call2`, `piece_ok`,
  `res_len_okP`, `hull_okP`, `segs_wr_ok`) — together with the complete
  generic register algebra of part 2, the memory/byte kit the summaries rest
  on (several lemmas are thin wrappers over this tree's core:
  `RefMemcpyLib.Z_to_le_bytes_lez`, `StoreOk.store_ok_sub`,
  `MemsetLib.nth_repeat_lt`, `SeqExec.rdn_nth`,
  `AsanPlanSound.nth_sr_vars_lt`, `AxSymExec3Sound.Z_to_bv8_mod`), all six
  knowledge tests of part 3 (`kwritable_sound`,
  `kwritable_x_sound`, `kzero_x_sound`, `kimg_cut_sound`, `lookup_piece`,
  `kread8e_piece`), the READ side of the knowledge
  (`kreadZ1_byte`, `kread_bytes_sound`, `zbytes_of_small`), the copy-fact
  enumeration (`copy_facts_sound`) and `k0_sound`, the complete `w_*`
  wrapper block, the readability kit
  (`find_segment_In`, `wview_rd1`, `store_ok_rdn`), the call-node helpers
  (`sr_vars_lt_fresh`, `ret_lit_sound`, `split_lit_vars`,
  `wbytes_fill_at`), the three `call_*` lifting lemmas of part 4
  (`call_core`, `call_node_sound`, `call_node_sound2` — the hypotheses
  `node_x_sound` reaches `check_sound` through), `popfree_facts_sound`,
  and the `SEALED_BYTES` / list bookkeeping
  (`SEALED_W_bytes`, `SEALED_BYTES_nth_hi`, `img_cov_sound`,
  `firstn_skipn_map_nth`), and — from part 5–6 — ALL FIVE routine-summary
  proofs `summary_fill_sound`, `summary_miz_sound`,
  `summary_istrncpy_sound`, `summary_popfree_sound`,
  `summary_copy_sound` with all seven interface theorems
  `node_x_sound_XIMemset`, `node_x_sound_XMemset`,
  `node_x_sound_XMemIsZero`, `node_x_sound_XIStrncpy`,
  `node_x_sound_XPopFree`, `node_x_sound_XIMemcpy`,
  `node_x_sound_XMemcpy`.  That is 90 of the 92 declarations, and
  the file is silent under `lake env lean`.  spelling bridges were
  needed for part 5 and sit next to `Z_to_bv5_ten`: `Z_to_bv64_bv_unsigned`
  (the `bv_unsigned` spelling of `BvBase.ofInt_toNat`), `Z_to_bv5_one`,
  `Z_to_bv5_eleven`/`_twelve`/`_fourteen`/`_fifteen` (the `↑n` spellings the
  `w_reg_lit_sound` / `reg_of_ridx` conclusions use) and `wbytes_nth` (the
  `bv_unsigned`/`getD` restatement of the landed `wbytes_getD`); none of them
  carries mathematical content.  A summary proof is a *node* proof: it peels
  the node's guard out of the `after_call` equation, reads the register /
  bounds facts off `HC`, and closes through `call_node_sound`
  (`summary_popfree_sound` instead uses `call_core` + a pointwise `regs_ok`,
  which is why this file's `popfree_spec` states the kept registers
  pointwise).
 INTEGRATION NOTE: `check_sound`
  passes `node_x_sound` as a hypothesis, so `segs_wr_ok SEGS` must be in
  scope at that assembly site.  The only other facts the copy proof
  uses are the `↑10` spelling bridge `Z_to_bv5_ten_up` and
  `RefMemcpyLib.at_nat` (see the note next to `Z_to_bv5_ten`); everything else
  it rests on was already landed.  The two bitwise lemmas at the end of this
  file are a DEVIATION, not missing work.
  TACTIC TRAPS measured while proving the four summaries (each of them cost a
  round; they are the ones that recur in this file's shape):
  * `split at Hn` is NOT usable to peel a `Bool` guard built from `==` on
    `Int` (it descends into `Int.beq`'s inner `match`).  The uniform recipe is
    `cases hg : <the Bool expression>` + `rw [hg] at Hn` +
    `simp only [Bool.false_eq_true, ite_false] at Hn` (false side) /
    `simp only [ite_true] at Hn` (true side).  `split at Hn` IS the right tool
    for a genuine outer `match` — e.g. the 4-way `match xlo …, xhi …, xhi …,
    xhi …` of `summary_copy`: it splits the patterns and leaves the arm's
    equations as `heq` hypotheses (rename them with `rename_i`).
  * `simp only [] at Hn` ERRORS ("simp made no progress") when nothing
    iota-reduces; `simp at Hn` does the same iota reduction but also closes
    the goal outright when the equation becomes `none = some cs'`.  When the
    underlying `match` is *stuck* (see the `args` bullet below) neither of
    them helps.
  * `cases`/`simp` never close `Hn : none = some cs'` — that needs
    `exact absurd Hn (by simp)`.
  * `++` on `List` associates to the LEFT (`a ++ b ++ c = (a ++ b) ++ c`), so
    `List.mem_append.mp` splits off the LAST chunk first; and a 3-way
    `rcases h with h | h | h` DESTRUCTS the third hypothesis — if that one is
    `Ke ∈ kn_havoc …` (a `List.Mem` over the non-variable list
    `(k.map …).flatten`) the elimination dies.  Split with
    `List.mem_append.mp` into `have`s instead, so the third proof is only
    bound, and use `have h : Ke = <entry> := by simpa using hKe` rather than
    `rw [List.mem_singleton]` / `subst`.
  * `match args with | [.ELit K], … | _, … => none` is stuck on the inner
    `expr` discriminator, not on the list shape: `cases ha : a` must precede
    `cases hr : rest`.
  * `two64` is an OPAQUE atom to `omega`; re-spell the hypothesis
    (`have h' : … < (2 : Int) ^ 64 := h`) or `rw [← two64_eq_natCast, two64_eq]`
    on the goal.  `↑(4 * k)` and `4 * ↑k` are different terms.
  * there is no `norm_num` / `ring` in this project (core Lean only).
  * `xnode.XIMemcpy`-style qualification is mandatory (a bare `XIMemcpy` is
    not in scope at a use site); `w_know_ok_havoc`'s `k` argument is the
    HAVOC'D base list, not `kn cs`.
  TACTIC TRAPS measured while proving `summary_copy_sound` (the fifth, and by
  far the largest):
  * `split at Hn` peels ONE level per call in this file's shape — the outer
    `match` first, then the `if` inside the arm, then the `match copy_facts`
    inside *that*.  It does NOT descend into the `ite`s sitting in *argument*
    position (`after_call2 … (if 0 < nlo then … else …) …`), which is what
    makes `exact HSRC Hn` work after the peel.  `rename_i z heqz` names an
    arm's pattern variables (`z` first, the discriminant equation `heqz`
    last); `next` does not accept the saddr pattern variable of
    `some (.KBlob _ (.ELit n0) j)`, so case that one with
    `rename_i a0 n0 j heq` + `cases a0`.
  * `Bool.and_eq_true` is a PROP EQUALITY, not an `↔`: use
    `rw [Bool.and_eq_true] at h`.  And `⟨h1, h2, h3, h4⟩` on the
    left-nested `((A ∧ B) ∧ C) ∧ D` that `a && b && c && d` produces is
    silently the WRONG shape — write `⟨⟨⟨h1, h2⟩, _⟩, _⟩` (measured: a 3-arg
    anonymous constructor matched `(A∧B)∧C` against `A∧B`).
  * `decide_eq_true_eq` must NOT sit in a `simp only` set over a
    `decide (nhi ≤ 256) = true` conjunct: Lean hard-errors with "Dependent
    elimination failed … at case `Int.NonNeg.mk`".  Leave those conjuncts
    opaque (`Bool.and_eq_true` + `beq_iff_eq` only).
  * `List.mem_map.mp` yields `i ∈ List.range W`, NOT `i < W`: `omega` cannot
    see the bound, so add `List.mem_range.mp` first (cost: one `omega`
    counterexample round).  Likewise `Nat.cast_le` does not exist in this
    toolchain — the Nat→Int comparison is `Int.ofNat_le.mp`.
  * `first | t1 | t2` is NOT a backtracking filter when a branch contains a
    TERM elaboration that fails: `exact absurd Hn (by simp)` reports
    "unsolved goals" as a hard error, so any `first` list must put that
    alternative LAST.
  * `kentry_ok` is a `match`, so a `refine ⟨?_, ?_⟩` needs a `show` of the
    unfolded triple first; and the same-named `kzero_x_sound` of
    `AsanNodesMmB` has the tuple `⟨bounds, pointwise⟩` while THIS file's has
    `⟨pointwise, bounds, bounds⟩` — read the premise shape, not the name.
  * `Z_to_bv 64 B = beg` gives `bv_unsigned beg = B` only for `B < 2 ^ 64`:
    every consumer here has `0 < n`, which with `estart + n ≤ 2 ^ 64` gives
    `B < 2 ^ 64` by `omega`, so the corner never needs the disjunction that
    `summary_miz_sound` carries (`HuB`).
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.AsanPopFree
import LinuxSem.Common.Hoare
import LinuxSem.Common.SeqExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.MemsetLib
import LinuxSem.Common.RefMemcpyLib
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanPlanSoundSums

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
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StoreOk
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanAcct
open LinuxSem.Common.AsanPlacement
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.Hoare
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.AsanAcctShape

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- The entry FP state. -/
local instance asanplansums_fx : PropExec.FPState := PropExec.fx0

/-! ## 1. Shapes of the routine summaries (hypotheses of the node proofs) -/

/-- registers a summarized routine keeps: everything outside `caller_saved`
    (x0 aside) -/
def kept_ok (regs regs' : BvMap word) : Prop :=
  ∀ r : reg, r ≠ 0 → ¬ ridx r ∈ caller_saved → getr regs' r = getr regs r

/-! ### `Section Specs` -/

/-- memset-like routine at `entry`: fills `s, s+n` with the low byte of `c`
    (for `c < cmax`; internal_memset: cmax = 256, musl memset: cmax = 2^64),
    returns to `ra` with a0 = s -/
def fill_spec (SEGS : List Segment) (entry cmax : Int) : Prop :=
  ∀ (mem0 : word → Option byte) (s c : word) (n : Int) (regs : BvMap word) (ret : word),
    0 ≤ n → (s.toNat : Int) + n < 2 ^ 64 →
    store_ok SEGS mem0 s n.toNat = true →
    (c.toNat : Int) < cmax →
    ret_ok ret → getr regs 1 = ret →
    getr regs 10 = s → getr regs 11 = c → getr regs 12 = Z_to_bv 64 n →
    ∃ regs', msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                (mkst regs' ret
                  (wbytes mem0 s (List.replicate n.toNat (Z_to_bv 8 (c.toNat))))
                  (seg_rom SEGS))
      ∧ kept_ok regs regs' ∧ getr regs' 10 = s

/-- memcpy-like routine at `entry`: copies the readable, disjoint source
    `src, src+n` over the writable `dst, dst+n`, returns with a0 = dst -/
def copy_spec (SEGS : List Segment) (entry : Int) : Prop :=
  ∀ (mem0 : word → Option byte) (dst src : word) (n : Int) (bs : List byte)
      (regs : BvMap word) (ret : word),
    0 ≤ n → bs.length = n.toNat →
    rdn SEGS mem0 src bs.length = some bs →
    store_ok SEGS mem0 dst bs.length = true →
    ((dst.toNat : Int) + n ≤ (src.toNat : Int) ∨ (src.toNat : Int) + n ≤ (dst.toNat : Int)) →
    (src.toNat : Int) + n < 2 ^ 64 → (dst.toNat : Int) + n < 2 ^ 64 →
    ret_ok ret → getr regs 1 = ret →
    getr regs 10 = dst → getr regs 11 = src → getr regs 12 = Z_to_bv 64 n →
    ∃ regs', msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      ∧ kept_ok regs regs' ∧ getr regs' 10 = dst

/-- mem_is_zero at `entry`, one-sided: all bytes of `beg, beg+N` read 0 ==>
    returns a0 = 1; writes only the saved ra at sp-8 -/
def miz_spec (SEGS : List Segment) (entry : Int) : Prop :=
  ∀ (mem : word → Option byte) (beg sp : word) (N : Int) (regs : BvMap word) (ret : word),
    0 ≤ N → N ≤ 2 ^ 40 → (beg.toNat : Int) + N + 8 ≤ 2 ^ 64 → 16 ≤ (sp.toNat : Int) →
    store_ok SEGS mem (Z_to_bv 64 ((sp.toNat : Int) - 8)) 8 = true →
    ((beg.toNat : Int) + N ≤ (sp.toNat : Int) - 8 ∨ (sp.toNat : Int) ≤ (beg.toNat : Int)) →
    (∀ a : word, (beg.toNat : Int) ≤ (a.toNat : Int) →
       (a.toNat : Int) < (beg.toNat : Int) + N → rdn SEGS mem a 1 = some [Z_to_bv 8 0]) →
    ret_ok ret → getr regs 1 = ret → getr regs 2 = sp →
    getr regs 10 = beg → getr regs 11 = Z_to_bv 64 N →
    ∃ regs', msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                (mkst regs' ret
                  (wbytes mem (Z_to_bv 64 ((sp.toNat : Int) - 8))
                    (word_to_le_bytes 8 ret))
                  (seg_rom SEGS))
      ∧ kept_ok regs regs' ∧ getr regs' 10 = Z_to_bv 64 1

/-- `"<sealed>"` ++ 4087 zero bytes: what `internal_strncpy(dst, "<sealed>", 4095)`
    leaves in dst -/
def SEALED_BYTES : List byte :=
  [Z_to_bv 8 0x3c, Z_to_bv 8 0x73, Z_to_bv 8 0x65, Z_to_bv 8 0x61, Z_to_bv 8 0x6c,
   Z_to_bv 8 0x65, Z_to_bv 8 0x64, Z_to_bv 8 0x3e]
  ++ List.replicate 4087 (Z_to_bv 8 0)

/-- sanitizer `internal_strncpy` at `entry`, for its only use
    `strncpy(dst, src = the image string "<sealed>\0" at src, 4095)`: the 9
    source bytes are pristine image bytes (overlay undefined), dst writable and
    apart; returns to ra with a0 = dst, dst := SEALED_BYTES -/
def istrncpy_spec (SEGS : List Segment) (entry src : Int) : Prop :=
  ∀ (mem0 : word → Option byte) (dst : word) (regs : BvMap word) (ret : word),
    (∀ i, src ≤ i → i < src + 9 → mem0 (Z_to_bv 64 i) = none) →
    store_ok SEGS mem0 dst 4095 = true →
    (dst.toNat : Int) + 4095 < 2 ^ 64 →
    ((dst.toNat : Int) + 4095 ≤ src ∨ src + 9 ≤ (dst.toNat : Int)) →
    ret_ok ret → getr regs 1 = ret →
    getr regs 10 = dst → getr regs 11 = Z_to_bv 64 src → getr regs 12 = Z_to_bv 64 4095 →
    ∃ regs', msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                (mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
      ∧ kept_ok regs regs' ∧ getr regs' 10 = dst

/-! ## 2. Generic facts: registers after a call, memory algebra -/

/-! ### Registers -/

theorem reg_of_ridx (r : reg) (n : Nat) (H : ridx r = n) : r = Z_to_bv 5 (n : Int) := by
  rw [← H]
  exact (ridx_roundtrip r).symm

theorem regs_ok_pointwise (E : env) (sr : List expr) (R : BvMap word)
    (H : ∀ r : reg, r ≠ 0 → getr R r = edenot E (sr.getD (ridx r) (.ELit 0))) :
    regs_ok E sr R := by
  intro r
  unfold sr_get
  by_cases hr : bv_eqb r 0 = true
  · have h0 : r = 0 := (bv_eqb_eq r 0).mp hr
    subst h0
    rw [ite_eq_left hr]
    rw [SeqExec.getr_zero]
    rfl
  · rw [ite_eq_right hr]
    exact H r (fun h0 => hr ((bv_eqb_eq r 0).mpr h0))

theorem caller_saved_nodup : caller_saved.Nodup := by decide

theorem nth_sr_fresh_out (cs0 : List Nat) (nx : Nat) (sr : List expr) (i : Nat)
    (Hn : ¬ i ∈ cs0) :
    (sr_fresh sr cs0 nx).getD i (.ELit 0) = sr.getD i (.ELit 0) := by
  induction cs0 generalizing sr nx with
  | nil => rfl
  | cons c t ih =>
      have hic : i ≠ c := fun h => Hn (by rw [h]; exact List.mem_cons_self)
      have hnt : ¬ i ∈ t := fun h => Hn (List.mem_cons_of_mem c h)
      simp only [sr_fresh]
      rw [ih (sr := sr_upd sr c (.EVar nx)) (nx := nx + 1) hnt, nth_sr_upd, ite_eq_right hic]

theorem nth_sr_fresh_in (cs0 : List Nat) (nx : Nat) (sr : List expr) (j : Nat)
    (Hnd : cs0.Nodup) (Hj : j < cs0.length) :
    (sr_fresh sr cs0 nx).getD (cs0.getD j 0) (.ELit 0) = .EVar (nx + j) := by
  induction cs0 generalizing sr nx j with
  | nil => simp at Hj
  | cons c t ih =>
      have hnd : t.Nodup := (List.nodup_cons.mp Hnd).2
      have hnc : c ∉ t := (List.nodup_cons.mp Hnd).1
      cases j with
      | zero =>
          rw [List.getD_cons_zero]
          simp only [sr_fresh]
          rw [nth_sr_fresh_out t (nx + 1) (sr_upd sr c (.EVar nx)) c hnc, nth_sr_upd, ite_eq_left rfl]
          rfl
      | succ j' =>
          have hlt : j' < t.length := by simpa using Hj
          rw [List.getD_cons_succ]
          simp only [sr_fresh]
          rw [ih (sr := sr_upd sr c (.EVar nx)) (nx := nx + 1) j' hnd hlt]
          congr 1
          omega

def ext_call (E : env) (nx : Nat) (R' : BvMap word) : env :=
  ⟨fun n => if nx ≤ n && n < nx + NCS then
      getr R' (Z_to_bv 5 ((caller_saved.getD (n - nx) 0 : Nat) : Int))
    else E.ev n, E.eb⟩

theorem ext_call_agree (E : env) (nx : Nat) (R' : BvMap word) :
    env_agree nx E (ext_call E nx R') := by
  refine ⟨fun n hn => ?_, rfl⟩
  show E.ev n = (if nx ≤ n && n < nx + NCS then _ else E.ev n)
  rw [ite_eq_right]
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro h
  omega

theorem ext_call_var (E : env) (nx : Nat) (R' : BvMap word) (j : Nat) (Hj : j < NCS) :
    (ext_call E nx R').ev (nx + j)
      = getr R' (Z_to_bv 5 ((caller_saved.getD j 0 : Nat) : Int)) := by
  show (if nx ≤ nx + j && nx + j < nx + NCS then
      getr R' (Z_to_bv 5 ((caller_saved.getD (nx + j - nx) 0 : Nat) : Int))
    else E.ev (nx + j)) = _
  rw [ite_eq_left]
  · congr 2
    have h : nx + j - nx = j := by omega
    rw [h]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega

/-- Any member of a list is reachable at its index (with `getD`). -/
theorem mem_iff_getD {α : Type} {a d : α} {l : List α} :
    a ∈ l ↔ ∃ i, i < l.length ∧ l.getD i d = a := by
  induction l with
  | nil => simp
  | cons x t ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · subst h; exact ⟨0, by simp, rfl⟩
        · obtain ⟨i, hi, hg⟩ := ih.mp h
          exact ⟨i + 1, by simp [hi], by rw [List.getD_cons_succ]; exact hg⟩
      · rintro ⟨i, hi, hg⟩
        cases i with
        | zero => exact by rw [List.getD_cons_zero] at hg; subst hg; exact List.mem_cons_self
        | succ i' =>
            rw [List.getD_cons_succ] at hg
            exact List.mem_cons_of_mem x (ih.mpr ⟨i', by simpa using hi, hg⟩)

theorem regs_after_call (E : env) (sr : List expr) (R R' : BvMap word) (nx : Nat)
    (rv : Option expr) (HR : regs_ok E sr R) (Hsv : AsanPlanCore.sr_vars_lt nx sr = true)
    (Hkept : kept_ok R R')
    (Hrv : match rv with
           | some e => AsanPlanCore.expr_vars_lt nx e = true ∧ getr R' 10 = edenot E e
           | none => True) :
    regs_ok (ext_call E nx R')
      (match rv with
       | some e => sr_upd (sr_fresh sr caller_saved nx) 10 e
       | none => sr_fresh sr caller_saved nx)
      R' := by
  have Hag := ext_call_agree E nx R'
  have hnodup := caller_saved_nodup
  have HOLD : ∀ i, i < 32 →
      edenot (ext_call E nx R') (sr.getD i (.ELit 0)) = edenot E (sr.getD i (.ELit 0)) := by
    intro i hi
    symm
    exact edenot_agree' nx E (ext_call E nx R') _ Hag (nth_sr_vars_lt nx sr i Hsv hi)
  have GEN : ∀ r : reg, r ≠ 0 → getr R' r =
      edenot (ext_call E nx R')
        ((sr_fresh sr caller_saved nx).getD (ridx r) (.ELit 0)) := by
    intro r hr0
    by_cases hcs : ridx r ∈ caller_saved
    · obtain ⟨j, hj, hjn⟩ := mem_iff_getD.mp hcs
      rw [← hjn, nth_sr_fresh_in caller_saved nx sr j hnodup hj]
      simp only [edenot]
      rw [ext_call_var E nx R' j hj, hjn, ← reg_of_ridx r _ rfl]
    · have h1 : getr R r = edenot E (sr.getD (ridx r) (.ELit 0)) := by
        rw [HR r]
        simp only [sr_get]
        rw [ite_eq_right (by intro hb; exact hr0 ((bv_eqb_eq r 0).mp hb))]
      rw [nth_sr_fresh_out caller_saved nx sr (ridx r) hcs, Hkept r hr0 hcs,
        HOLD (ridx r) (ridx_range r)]
      exact h1
  cases rv with
  | none => exact regs_ok_pointwise _ _ _ GEN
  | some e =>
      obtain ⟨Hev, Ha0⟩ := Hrv
      refine regs_ok_pointwise _ _ _ (fun r hr0 => ?_)
      rw [nth_sr_upd]
      by_cases h10 : ridx r = 10
      · rw [ite_eq_left h10]
        have hr10 : r = 10 := ridx_inj (by rw [h10]; decide)
        rw [hr10, Ha0]
        exact edenot_agree' nx E (ext_call E nx R') e Hag Hev
      · rw [ite_eq_right h10]
        exact GEN r hr0

/-! ### Memory algebra -/

/-! `2 ^ 64` as a numeral: `omega` treats the POWER as an opaque atom (both in
    `Nat` and, through the cast, in `Int`), so every bound below is first
    rewritten to the numeral.  -/
theorem two64_nat : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

theorem two64_int : (((2 : Nat) ^ 64 : Nat) : Int) = 18446744073709551616 := by decide

theorem toNat_add_one' (a : word) (h : a.toNat + 1 < 2 ^ 64) : (a + 1).toNat = a.toNat + 1 := by
  rw [two64_nat] at h
  exact CatExec.toNat_add_one a h

theorem Z_to_bv_add_nat (a : word) (j : Nat) :
    Z_to_bv 64 ((a.toNat : Int) + (j : Int)) = a + nat_to_word j := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofInt 64 ((a.toNat : Int) + (j : Int))).toNat = (a + nat_to_word j).toNat
  rw [BitVec.toNat_ofInt, BitVec.toNat_add]
  show ((a.toNat : Int) + (j : Int)).toNat % 2 ^ 64 = (a.toNat + j % 2 ^ 64) % 2 ^ 64
  omega

theorem nat_to_word_succ (j : Nat) : nat_to_word (j + 1) = nat_to_word j + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [nat_to_word, BitVec.toNat_add, BitVec.toNat_ofNat]
  show (j + 1) % 2 ^ 64 = (j % 2 ^ 64 + 1) % 2 ^ 64
  omega

theorem rdn1_overlay (segs : List Segment) (m : word → Option byte) (a : word) (b : byte)
    (H : m a = some b) : rdn segs m a 1 = some [b] :=
  rdn_one segs m a b (by unfold SeqExec.rdn_byte; rw [H])

theorem rdn_nth (segs : List Segment) (m : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (j : Nat)
    (Hnw : ((a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)))
    (H : rdn segs m a n = some bs) (Hj : j < n) :
    rdn segs m (Z_to_bv 64 ((a.toNat : Int) + (j : Int))) 1
      = some [bs.getD j (Z_to_bv 8 0)] := by
  rw [Z_to_bv_add_nat, SeqExec.rdn_nth segs m n a bs j H Hj, List.getD_eq_getElem?_getD]

theorem rdn_overlay_all (segs : List Segment) (m : word → Option byte) (n : Nat)
    (a : word) (b : byte)
    (Hnw : ((a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)))
    (Hall : ∀ i, 0 ≤ i → i < (n : Int) → m (Z_to_bv 64 ((a.toNat : Int) + i)) = some b) :
    rdn segs m a n = some (List.replicate n b) := by
  refine rdn_pointwise segs m n a (List.replicate n b) (by simp) Hnw (fun j hj => ?_)
  have hd : (List.replicate n b).getD j (Z_to_bv 8 0) = b :=
    MemsetLib.nth_repeat_lt b (Z_to_bv 8 0) n j hj
  rw [hd]
  exact Hall (j : Int) (Int.natCast_nonneg _) (by omega)

theorem adenot_SA (E : env) (b : expr) (off : Int) :
    adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)) := rfl

theorem nth_sr_vars_lt' (b : Nat) (sr : List expr) (r : Nat)
    (H : AsanPlanCore.sr_vars_lt b sr = true) (Hr : r < 32) :
    AsanPlanCore.expr_vars_lt b (sr.getD r (.ELit 0)) = true :=
  nth_sr_vars_lt b sr r H Hr

theorem nth_repeat_lt {T : Type} (a d : T) (m j : Nat) (h : j < m) :
    (List.replicate m a).getD j d = a :=
  MemsetLib.nth_repeat_lt a d m j h

theorem Z_to_bv8_mod (c : Int) : Z_to_bv 8 (c % 256) = Z_to_bv 8 c :=
  AxSymExec3Sound.Z_to_bv8_mod c

theorem nth_map_seq {T : Type} (f : Nat → T) (W i : Nat) (d : T) (Hi : i < W) :
    ((List.range W).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range Hi]
  rfl

theorem Z_to_le_bytes_of_bytes (bs : List byte) :
    Z_to_le_bytes bs.length (bytes_le_to_Z bs) = bs :=
  RefMemcpyLib.Z_to_le_bytes_lez bs

theorem word_to_le_bytes_of_bytes (bs : List byte) (Hlen : bs.length ≤ 8) :
    word_to_le_bytes bs.length (Z_to_bv 64 (bytes_le_to_Z bs)) = bs := by
  have hb := PropExec.bytes_le_to_Z_bound bs
  have h8 : 8 * bs.length ≤ 64 := by omega
  have hpow : (2 : Nat) ^ (8 * bs.length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h8
  have hz0 := PropExec.bytes_le_to_Z_nonneg bs
  have hlt : bytes_le_to_Z bs < ((2 ^ 64 : Nat) : Int) := by
    have h1 : bytes_le_to_Z bs < ((2 ^ (8 * bs.length) : Nat) : Int) := hb
    have h2 : ((2 ^ (8 * bs.length) : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
      exact Int.ofNat_le.mpr hpow
    omega
  unfold word_to_le_bytes
  rw [AgentLib.u64_lit (bytes_le_to_Z bs) ⟨hz0, hlt⟩]
  exact Z_to_le_bytes_of_bytes bs

theorem word_to_le_bytes_of_bytes_n (n : Nat) (bs : List byte) (hlen : bs.length = n)
    (hn : n ≤ 8) : word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs := by
  subst hlen
  exact word_to_le_bytes_of_bytes bs hn


/-! ### The `Section Sound` context pieces that are DEFINITIONS -/

/-- Per-image fact (vm_compute per image): the reserved intervals fit in the
    hull. -/
def res_len_okP (SEGS : List Segment) (A : atable) : Prop :=
  (segments_reserved SEGS).length = A.n_res

/-- The two numeric image facts of `hull_ok`, wrapped so that `omega` does not
    make every lemma of the Section depend on them. -/
def hull_okP (A : atable) : Prop :=
  0 ≤ A.img_lo ∧ A.img_lo % 4096 = 0 ∧ A.img_hi % 4096 = 0 ∧ A.img_hi ≤ KHI

/-- Image fact needed by the havoc-source copy: a byte the machine may STORE to
    is also one it can LOAD from, i.e. every writable segment is readable. -/
def segs_wr_ok (SEGS : List Segment) : Prop :=
  ∀ seg, seg ∈ SEGS → seg_writable seg = true → seg_readable seg = true

/-- A successful `w`-byte lookup: the bytes exist and spell the expression. -/
def piece_ok (SEGS : List Segment) (E : env) (M : word → Option byte) (b : expr) (off : Int)
    (w : Nat) (v : expr) : Prop :=
  ∃ bs, rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) w = some bs ∧ bs.length = w
        ∧ word_to_le_bytes w (edenot E v) = bs

/-- Sub-range of a storable range.   -/
theorem store_ok_sub (SEGS : List Segment) (M : word → Option byte) (a : word) (n : Nat)
    (b : word) (m : Nat)
    (Hnw : ((a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)))
    (Hst : store_ok SEGS M a n = true)
    (Hlo : (a.toNat : Int) ≤ (b.toNat : Int))
    (Hhi : (b.toNat : Int) + (m : Int) ≤ (a.toNat : Int) + (n : Int)) :
    store_ok SEGS M b m = true :=
  StoreOk.store_ok_sub SEGS M a b n m Hnw Hst Hlo Hhi

/-! ### `after_call2`: extra fresh variables -/

/-- `after_call2`: `extra` more fresh variables with values `vals`; the caller
    proves the knowledge under the EXTENDED valuation
    `E2 := ext_list (ext_call E nx regs') (nx + NCS) vals`. -/
def ext_call2 (E : env) (nx : Nat) (R' : BvMap word) (vals : List word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals

/-- `ext_call2` still agrees with `E` below `nx`. -/
theorem ext_call2_agree (E : env) (nx : Nat) (R' : BvMap word) (vals : List word) :
    env_agree nx E (ext_call2 E nx R' vals) := by
  have h1 := ext_call_agree E nx R'
  have h3 := ext_list_agree (ext_call E nx R') (nx + NCS) vals
  refine ⟨fun n hn => ?_, by rw [h1.2]; exact h3.2⟩
  rw [h1.1 n hn]
  exact h3.1 n (by omega)

/-- `ext_call` and `ext_call2` agree below `nx + NCS`. -/
theorem ext_call2_agree16 (E : env) (nx : Nat) (R' : BvMap word) (vals : List word) :
    env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals) := by
  unfold ext_call2
  exact ext_list_agree _ _ _

/-- The value `ext_call2` gives variable `nx + NCS + i`. -/
theorem ext_call2_at (E : env) (nx : Nat) (R' : BvMap word) (vals : List word) (i : Nat)
    (Hi : i < vals.length) :
    (ext_call2 E nx R' vals).ev (nx + NCS + i) = vals.getD i (Z_to_bv 64 0) := by
  unfold ext_call2
  exact ext_list_at _ _ _ _ Hi

/-! ### `SEALED_BYTES` bookkeeping (the cheap half of  block) -/

/-- `"<sealed>"` plus 4087 zeros is 4095 bytes. -/
theorem SEALED_BYTES_length : SEALED_BYTES.length = 4095 := by
  unfold SEALED_BYTES
  rw [List.length_append, List.length_replicate]
  rfl

/-- Sanity check: the seal starts with `<`. -/
theorem SEALED_BYTES_head : (SEALED_BYTES.getD 0 (Z_to_bv 8 0)) = Z_to_bv 8 0x3c := by
  decide

/-- Sanity check: the last sealed byte is zero. -/
theorem SEALED_BYTES_last : (SEALED_BYTES.getD 4094 (Z_to_bv 8 0)) = Z_to_bv 8 0 := by
  decide

/-- Every byte of `SEALED_BYTES` from offset 8 on is zero . -/
theorem SEALED_BYTES_nth_hi (j : Nat) (h1 : 8 ≤ j) (h2 : j < 4095) :
    SEALED_BYTES.getD j (Z_to_bv 8 0) = Z_to_bv 8 0 := by
  unfold SEALED_BYTES
  rw [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  rw [ite_eq_right (by simp; omega), ite_eq_left (by simp; omega)]
  rfl


theorem map_range_succ {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun j => f (j + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- A successful one-byte read pins the combined (overlay-then-image) byte. -/
theorem rdn_byte_of_rdn_one (segs : List Segment) (m : word → Option byte) (a : word) (b : byte)
    (h : rdn segs m a 1 = some [b]) : SeqExec.rdn_byte segs m a = some b := by
  cases hm : m a with
  | some c =>
    have h1 : rdn segs m a 1 = some [c] := by simp only [rdn, hm]
    rw [h1] at h
    simp only [SeqExec.rdn_byte, hm]
    exact congrArg (some) (List.cons.inj (Option.some.inj h) |>.1)
  | none =>
    cases hs : seg_rom segs a with
    | none => exact absurd h (by simp only [rdn, hm, hs]; simp)
    | some c =>
      have h1 : rdn segs m a 1 = some [c] := by simp only [rdn, hm, hs]
      rw [h1] at h
      simp only [SeqExec.rdn_byte, hm, hs]
      exact congrArg (some) (List.cons.inj (Option.some.inj h) |>.1)

theorem wbytes_getD (bs : List byte) :
    ∀ (m : word → Option byte) (a : word) (j : Nat),
      (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      j < bs.length →
      wbytes m a bs (Z_to_bv 64 ((a.toNat : Int) + (j : Int)))
        = some (bs.getD j (Z_to_bv 8 0)) := by
  induction bs with
  | nil => intro m a j _ hj; rw [List.length_nil] at hj; omega
  | cons b rest ih =>
    intro m a j Hnw hj
    cases rest with
    | nil =>
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have hx : Z_to_bv 64 ((a.toNat : Int) + ((0 : Nat) : Int)) = a := by
        rw [Int.natCast_zero, Int.add_zero]; exact Z_to_bv_unsigned a
      simp only [wbytes, hx, List.getD_cons_zero]
      rw [ite_eq_left (bv_eqb_refl a)]
    | cons b' rest' =>
      have hlen : ((b :: b' :: rest').length : Int) = ((b' :: rest').length : Int) + 1 := by simp
      have hpos : (1 : Int) ≤ ((b' :: rest').length : Int) := by
        have h : 1 ≤ (b' :: rest').length := by simp
        exact Int.ofNat_le.mpr h
      have hstep : wbytes m a (b :: b' :: rest')
          = wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) (b' :: rest') := rfl
      have hu1 : (a + 1).toNat = a.toNat + 1 := by
        apply toNat_add_one
        omega
      have hb2 : (((a + 1).toNat : Int) + ((b' :: rest').length : Int))
          ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hu1]; omega
      cases j with
      | zero =>
        have hx : Z_to_bv 64 ((a.toNat : Int) + ((0 : Nat) : Int)) = a := by
          rw [Int.natCast_zero, Int.add_zero]; exact Z_to_bv_unsigned a
        rw [hstep, wbytes_below (b' :: rest') _ (a + 1) (Z_to_bv 64 ((a.toNat : Int) + ((0:Nat):Int)))]
        · rw [hx]
          rw [ite_eq_left (bv_eqb_refl a)]
          rfl
        · exact hb2
        · rw [hx, hu1]; omega
      | succ j' =>
        have hxj : Z_to_bv 64 ((a.toNat : Int) + ((j' + 1 : Nat) : Int))
            = Z_to_bv 64 (((a + 1).toNat : Int) + (j' : Int)) := by
          rw [hu1]; congr 1; push_cast; omega
        rw [hstep, hxj, ih (fun x => if bv_eqb x a then some b else m x) (a + 1) j' hb2 (by omega),
          List.getD_cons_succ]

/-- `wbytes_nth`: the `j`-th byte of a `wbytes` walk, stated in the
    `bv_unsigned` / `getD` spelling (a two-line restatement of `wbytes_getD`). -/
theorem wbytes_nth (bs : List byte) (m : word → Option byte) (a : word) (j : Nat)
    (Hnw : bv_unsigned a + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (hj : j < bs.length) :
    wbytes m a bs (Z_to_bv 64 (bv_unsigned a + (j : Int)))
      = some (bs.getD j (Z_to_bv 8 0)) :=
  wbytes_getD bs m a j Hnw hj

theorem wbytes_same (bs : List byte) (m : word → Option byte) (a : word)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hall : ∀ j, j < bs.length →
      m (Z_to_bv 64 ((a.toNat : Int) + (j : Int))) = some (bs.getD j (Z_to_bv 8 0))) :
    wbytes m a bs = m := by
  funext x
  by_cases hlt : x.toNat < a.toNat
  · exact wbytes_below bs m a x Hnw (by omega)
  by_cases hin : x.toNat < a.toNat + bs.length
  · have hge : a.toNat ≤ x.toNat := by omega
    have hjlt : x.toNat - a.toNat < bs.length := by omega
    have hxj : x = Z_to_bv 64 ((a.toNat : Int) + ((x.toNat - a.toNat : Nat) : Int)) := by
      rw [show ((a.toNat : Int) + ((x.toNat - a.toNat : Nat) : Int)) = (x.toNat : Int) by
        push_cast; omega]
      exact (Z_to_bv_unsigned x).symm
    rw [hxj, wbytes_getD bs m a (x.toNat - a.toNat) Hnw hjlt]
    exact (Hall (x.toNat - a.toNat) hjlt).symm
  · exact wbytes_above bs m a x (by omega)

theorem wbytes_defined (bs : List byte) (m : word → Option byte) (a : word) (j : Nat)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (hj : j < bs.length) :
    wbytes m a bs (Z_to_bv 64 ((a.toNat : Int) + (j : Int))) ≠ none := by
  rw [wbytes_getD bs m a j Hnw hj]
  simp

theorem rdn_of_nth (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word) (f : Nat → byte),
      (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (∀ j, j < n → rdn segs m (Z_to_bv 64 ((a.toNat : Int) + (j : Int))) 1 = some [f j]) →
      rdn segs m a n = some ((List.range n).map f) := by
  intro n
  induction n with
  | zero => intro a f _ _; rfl
  | succ n ih =>
    intro a f Hnw Hall
    have hx0 : Z_to_bv 64 ((a.toNat : Int) + ((0 : Nat) : Int)) = a := by
      rw [Int.natCast_zero, Int.add_zero]; exact Z_to_bv_unsigned a
    have hb : SeqExec.rdn_byte segs m a = some (f 0) := by
      have h := Hall 0 (by omega)
      rw [hx0] at h
      exact rdn_byte_of_rdn_one segs m a (f 0) h
    rw [SeqExec.rdn_succ_byte segs m a n (f 0) hb]
    cases n with
    | zero =>
      show (some []).bind (fun rest => some (f 0 :: rest)) = some ((List.range 1).map f)
      show some [f 0] = some [f 0]
      rfl
    | succ n' =>
      have hlen : ((n' + 1 + 1 : Nat) : Int) = ((n' + 1 : Nat) : Int) + 1 := by push_cast; omega
      have hpos : (1 : Int) ≤ ((n' + 1 : Nat) : Int) := by push_cast; omega
      have hu1 : (a + 1).toNat = a.toNat + 1 := by
        apply toNat_add_one
        omega
      have hbnd : (((a+1).toNat : Int) + ((n' + 1 : Nat) : Int)) ≤ ((2 ^ 64 : Nat) : Int) := by
        rw [hu1]; omega
      have hHall' : ∀ j, j < n' + 1 →
          rdn segs m (Z_to_bv 64 (((a+1).toNat : Int) + (j : Int))) 1
            = some [(fun j => f (j + 1)) j] := by
        intro j hj
        rw [hu1]
        have h := Hall (j + 1) (by omega)
        show rdn segs m (Z_to_bv 64 ((a.toNat : Int) + 1 + (j : Int))) 1 = some [f (j + 1)]
        rw [show ((a.toNat : Int) + 1 + (j : Int)) = ((a.toNat : Int) + ((j + 1 : Nat) : Int)) by
          push_cast; omega]
        exact h
      rw [ih (a + 1) (fun j => f (j + 1)) hbnd hHall']
      show some (f 0 :: (List.range (n' + 1)).map (fun j => f (j + 1)))
        = some ((List.range (n' + 1 + 1)).map f)
      rw [map_range_succ f (n' + 1)]

/-! ### The `w_*` wrappers around the `AsanPlanSound` lemmas -/

theorem w_reg_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (n : Nat) (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hn : 0 < n ∧ n < 32) :
    getr R (Z_to_bv 5 (n : Int)) = edenot E (AsanPlanCore.reg cs n) :=
  AsanPlanSound.reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model n HC Hn

theorem w_reg_lit_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (n : Nat) (z : Int) (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hn : 0 < n ∧ n < 32) (H : AsanPlanCore.reg_lit cs n = some z) :
    getr R (Z_to_bv 5 (n : Int)) = Z_to_bv 64 z ∧ 0 ≤ z ∧ z < two64 :=
  AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model n z HC Hn H

theorem w_split_lit_denot (E : env) (e b : expr) (k : Int)
    (H : split_lit e = (b, k)) :
    edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k) :=
  AsanPlanSound.split_lit_denot E e b k H

theorem w_know_ok_havoc (SEGS : List Segment) (E : env) (M M' : word → Option byte)
    (k : List kentry) (b n : expr) (o : Int)
    (HK : know_ok SEGS E M k)
    (Hout : ∀ x : word, bv_unsigned x < estart E (SA b o) ∨
      estart E (SA b o) + elenZ E n ≤ bv_unsigned x → M' x = M x)
    (Hg : StoreOk.mem_grows M M') :
    know_ok SEGS E M' (kn_havoc k b o n) :=
  AsanPlanSound.know_ok_havoc SEGS E M M' k b n o HK Hout Hg

theorem w_flat_x_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b : expr) (off : Int) (n : expr)
    (HK : know_ok SEGS E M k) (H : flat_x k b off n = true) :
    0 ≤ estart E (SA b off) ∧ estart E (SA b off) + bv_unsigned (edenot E n) ≤ 2 ^ 64 ∧
      0 < bv_unsigned (edenot E n) :=
  AsanPlanSound.flat_x_sound SEGS E M k b off n HK H

theorem w_env_agree_le (b b' : Nat) (E E' : env) (H : env_agree b' E E') (Hle : b ≤ b') :
    env_agree b E E' :=
  AsanPlanSound.env_agree_le b b' E E' H Hle

theorem w_cs_ok_agree (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (FS0 : Fs.Fs) (E E' : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte)
    (model : Model) (Hag : env_agree (nxt cs) E E') (Hf : fresh_ok nx0 cs = true)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok SEGS A LIMIT SINV argH FS0 E' cs R FULL model :=
  AsanPlanSound.cs_ok_agree SEGS A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E E' cs R FULL
    model Hag Hf HC

theorem w_hid_agree (A : atable) (nx0 : Nat) (argH : env → word → Bool)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (b : Nat) (E E' : env) (cs : acs) (model : Model) (Hag : env_agree b E E')
    (Hle : nx0 ≤ b) (H : pairs_vars_lt b (cs.a_vis ++ cs.a_ghost) = true) :
    hid A argH E' cs model = hid A argH E cs model :=
  AsanPlanSound.hid_agree A nx0 argH argH_agree b E E' cs model Hag Hle H

theorem w_cs_ok_frame (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (ss' : sym_state) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hs : same_but_materialized model model')
    (Hinv : MInv (allowA A E cs) model')
    (HR : regs_ok E ss'.s_regs R') (HL : ss'.s_log = [])
    (HK : know_ok SEGS E (Mr A argH E cs model FULL') ss'.s_know)
    (Hhid : ∀ a, hid A argH E cs model a = true → FULL' a = FULL a) :
    cs_ok SEGS A LIMIT SINV argH FS0 E (with_ss cs ss') R' FULL' model' :=
  AsanPlanSound.cs_ok_frame SEGS A LIMIT SINV argH FS0 SINV_frame E cs R FULL model ss' R' FULL'
    model' HC Hs Hinv HR HL HK Hhid

theorem w_lazy_cover_cs (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (HULL_ok : hull_okP A) (E : env) (cs : acs) (R : BvMap word)
    (FULL : word → Option byte) (model : Model)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model) :
    lazy_cover (hid A argH E cs model) (m_vm_lazy model) (allowA A E cs) :=
  AsanPlanSound.lazy_cover_cs SEGS A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC

theorem w_A_wf_allowA (A : atable) (E : env) (cs : acs) : A_wf (allowA A E cs) :=
  AsanPlanSound.A_wf_allowA A E cs

theorem w_H_off_segments_cs (SEGS : List Segment) (A : atable) (nx0 : Nat)
    (argH : env → word → Bool) (E : env) (cs : acs) (model : Model)
    (HULL_ok : hull_okP A)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a) :
    H_off_segments SEGS (hid A argH E cs model) :=
  AsanPlanSound.H_off_segments_cs SEGS A argH E cs model HULL_ok SEGS_in_hull argH_high

theorem w_fresh_ok_parts (nx0 : Nat) (cs : acs) (H : fresh_ok nx0 cs = true) :
    AsanPlanCore.sr_vars_lt (nxt cs) cs.a_ss.s_regs = true ∧
    AsanPlanCore.kn_vars_lt (nxt cs) (kn cs) = true ∧
    maps_vars_lt (nxt cs) cs.a_maps = true ∧
    pairs_vars_lt (nxt cs) (cs.a_vis ++ cs.a_ghost) = true ∧
    AsanPlanCore.expr_vars_lt (nxt cs) cs.a_brk = true ∧
    fd_vars_lt (nxt cs) cs.a_fd = true ∧ nx0 ≤ nxt cs :=
  AsanPlanSound.fresh_ok_parts nx0 cs H

/-! ### Readability of a storable range -/

/-- The one-byte read of a segment's static bytes. -/
theorem segment_read_bytes_one (bytes : List String) (off : Nat) (b : byte)
    (H : segment_byte_at bytes off = some b) : segment_read_bytes bytes off 1 = some [b] := by
  simp only [segment_read_bytes, H]

theorem wview_rd1 (SEGS : List Segment) (HSEGS : segs_wr_ok SEGS) :
    ∀ (M : word → Option byte) (a : word) (b : byte), wview SEGS M a = some b →
      (match M a with | some b0 => some b0 | none => seg_rom SEGS a) = some b := by
  intro M a b H
  unfold wview at H
  cases hm : M a with
  | some b0 => simpa only [hm] using H
  | none =>
    simp only [hm] at H
    have hex : ∀ sg : Segment, find_segment SEGS (a.toNat : Int) 1 = some sg →
        seg_writable sg = true ∧
          segment_byte_at sg.seg_bytes (a.toNat - sg.seg_base) = some b := by
      intro sg hsg
      simp only [hsg] at H
      by_cases hw : seg_writable sg = true
      · refine ⟨hw, ?_⟩
        rw [ite_eq_left hw] at H
        exact H
      · rw [ite_eq_right hw] at H
        exact absurd H (by simp)
    unfold seg_rom
    simp only [hm]
    cases hf : find_segment SEGS (a.toNat : Int) 1 with
    | none => rw [hf] at H; exact absurd H (by simp)
    | some seg =>
      obtain ⟨hw, hbyte⟩ := hex seg hf
      have hrd : seg_readable seg = true := HSEGS seg (find_segment_In SEGS _ _ seg hf) hw
      have hf' : find_segment SEGS (a.toNat : Int) ((1 : Nat) : Int) = some seg := hf
      have hmr : memory_read SEGS a 1 = some [b] := by
        unfold memory_read
        rw [hf']
        simp only []
        rw [hrd, ite_eq_left rfl]
        simpa only [] using segment_read_bytes_one seg.seg_bytes (a.toNat - seg.seg_base) b hbyte
      rw [hmr]

theorem store_ok_rdn (SEGS : List Segment) (HSEGS : segs_wr_ok SEGS) :
    ∀ (n : Nat) (M : word → Option byte) (a : word),
      (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      store_ok SEGS M a n = true →
      ∃ bs, rdn SEGS M a n = some bs ∧ bs.length = n := by
  intro n
  induction n with
  | zero => intro M a _ _; exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro M a Hnw Hst
    unfold store_ok at Hst
    cases hv : wview SEGS M a with
    | none => rw [hv] at Hst; exact absurd Hst (by simp)
    | some b =>
      have hb : SeqExec.rdn_byte SEGS M a = some b := wview_rd1 SEGS HSEGS M a b hv
      cases n with
      | zero =>
          refine ⟨[b], ?_, rfl⟩
          show rdn SEGS M a 1 = some [b]
          rw [SeqExec.rdn_succ_byte SEGS M a 0 b hb]
          rfl
      | succ n' =>
          have hu1 : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := u_add1 a (by omega)
          have Hst' : store_ok SEGS M (a + 1) (n' + 1) = true := by simpa only [hv] using Hst
          obtain ⟨bs, hrd, hlen⟩ := ih M (a + 1) (by omega) Hst'
          refine ⟨b :: bs, ?_, by simp only [List.length_cons]; omega⟩
          show rdn SEGS M a ((n' + 1) + 1) = some (b :: bs)
          rw [SeqExec.rdn_succ_byte SEGS M a (n' + 1) b hb, hrd]
          rfl

/-! ### The generic call node, helpers -/

theorem sr_vars_lt_fresh (rs : List Nat) (sr : List expr) (nx b : Nat)
    (Hsr : AsanPlanCore.sr_vars_lt b sr = true) (Hb : nx + rs.length ≤ b) :
    AsanPlanCore.sr_vars_lt b (sr_fresh sr rs nx) = true := by
  induction rs generalizing sr nx with
  | nil => simpa only [sr_fresh] using Hsr
  | cons r rest ih =>
      have hstep : sr_fresh sr (r :: rest) nx = sr_fresh (sr_upd sr r (.EVar nx)) rest (nx + 1) := rfl
      rw [hstep]
      apply ih
      · refine sr_vars_lt_upd b sr r (.EVar nx) Hsr ?_
        simp only [AsanPlanCore.expr_vars_lt]
        exact decide_eq_true (by simp only [List.length_cons] at Hb; omega)
      · simp only [List.length_cons] at Hb ⊢; omega

theorem split_lit_vars (e b : expr) (k : Int) (m : Nat)
    (H : split_lit e = (b, k)) (Hv : AsanPlanCore.expr_vars_lt m e = true) :
    AsanPlanCore.expr_vars_lt m b = true := by
  unfold split_lit at H
  cases e with
  | ELit z =>
      simp only [Prod.mk.injEq] at H
      obtain ⟨hb, _⟩ := H
      subst hb
      rfl
  | EAlu op x y =>
      split at H
      · rw [← (Prod.mk.inj H).1]
        rfl
      · rename_i heq
        injection heq with _ hx _
        rw [← (Prod.mk.inj H).1, ← hx]
        simp only [AsanPlanCore.expr_vars_lt, Bool.and_eq_true] at Hv
        exact Hv.1
      · rw [← (Prod.mk.inj H).1]
        exact Hv
  | EVar n => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv
  | EAluw a b' c => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv
  | EMd a b' c => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv
  | EMdw a b' c => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv
  | EExt a b' => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv
  | EBlob a => simp only [Prod.mk.injEq] at H; obtain ⟨hb, _⟩ := H; rw [← hb]; exact Hv

theorem ret_lit_sound (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (r : Int) (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (H : ret_lit cs = some r) :
    getr R (Z_to_bv 5 ((1 : Nat) : Int)) = Z_to_bv 64 r ∧ ret_ok (Z_to_bv 64 r) ∧
      0 ≤ r ∧ r < two64 := by
  unfold ret_lit at H
  cases hr : AsanPlanCore.reg cs 1 with
  | ELit z =>
      simp only [hr] at H
      by_cases hc : (z % 2 == 0 && z < two64 && 0 ≤ z) = true
      · rw [ite_eq_left hc] at H
        injection H with hEq
        subst hEq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hz1, hz2⟩, hz0⟩ := hc
        have h1 : getr R (Z_to_bv 5 ((1 : Nat) : Int)) = Z_to_bv 64 z := by
          rw [w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 1 HC (by omega)]
          show edenot E (AsanPlanCore.reg cs 1) = Z_to_bv 64 z
          rw [hr]
          rfl
        have hz1' : z % 2 = 0 := by simpa using hz1
        have hlt : z < 2 ^ 64 := by unfold two64 at hz2; exact hz2
        refine ⟨h1, ?_, hz0, hlt⟩
        apply ret_ok_even
        rw [u64_lit z ⟨hz0, hlt⟩]
        exact hz1'
      · rw [ite_eq_right hc] at H
        exact absurd H (by simp)
  | _ => simp only [hr] at H; exact absurd H (by simp)

theorem wbytes_fill_at (M : word → Option byte) (s : word) (b : byte) (n i : Int)
    (Hnw : (s.toNat : Int) + n ≤ ((2 ^ 64 : Nat) : Int)) (Hi : 0 ≤ i ∧ i < n) :
    wbytes M s (List.replicate n.toNat b) (Z_to_bv 64 ((s.toNat : Int) + i)) = some b := by
  have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg (by omega)
  have hi : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg Hi.1
  have hbnd : (s.toNat : Int) + ((List.replicate n.toNat b).length : Int)
      ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [List.length_replicate, hn]; exact Hnw
  have hjlt : i.toNat < (List.replicate n.toNat b).length := by
    rw [List.length_replicate]; omega
  rw [show ((s.toNat : Int) + i) = ((s.toNat : Int) + (i.toNat : Int)) by rw [hi]]
  rw [wbytes_getD _ M s i.toNat hbnd hjlt]
  congr 1
  exact nth_repeat_lt b (Z_to_bv 8 0) n.toNat i.toNat (by rw [List.length_replicate] at hjlt; exact hjlt)

theorem img_cov_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (a b : Int) (HK : know_ok SEGS E M k) (H : img_cov k a b = true) :
    ∀ i, a ≤ i → i < b → M (Z_to_bv 64 i) = none := by
  intro i Hi1 Hi2
  unfold img_cov at H
  rw [List.any_eq_true] at H
  obtain ⟨K, hmem, hK⟩ := H
  cases K with
  | KImg lo hi =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hK
      obtain ⟨h1, h2⟩ := hK
      have hk := HK _ hmem
      simp only [kentry_ok] at hk
      exact hk.2.2 i (by omega) (by omega)
  | KWord a' w v => simp at hK
  | KZero a' n => simp at hK
  | KBlob a' n kk => simp at hK
  | KAlign e m => simp at hK
  | KRange e lo hi => simp at hK
  | KWr a' n => simp at hK
  | KDisj a1 n1 a2 n2 => simp at hK
  | KFill a' n c => simp at hK
  | KUnk a' n => simp at hK

theorem SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = SEALED_BYTES.take 8 := by
  have h : bytes_le_to_Z (SEALED_BYTES.take 8) = SEALED_W := by decide
  rw [← h]
  exact word_to_le_bytes_of_bytes_n 8 (SEALED_BYTES.take 8) (by decide) (by omega)

/-! ### Knowledge tests -/

/-- A `Bool` `if` that yields `true` on the left branch or whose else-branch
    holds. -/
theorem ite_true_or {c a b : Bool} (h : (if c then a else b) = true) : c = true ∨ b = true := by
  cases c <;> simp_all

/-- A `match` on an `Option` that yields `true`. -/
theorem match_some_true {o : Option Int} {f : Int → Bool}
    (h : (match o with | some wl => f wl | none => false) = true) :
    ∃ wl, o = some wl ∧ f wl = true := by
  cases o with
  | none => simp at h
  | some wl => exact ⟨wl, rfl, h⟩

theorem kwritable_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) :
    ∀ (k : List kentry) (b : expr) (off n : Int),
      know_ok segs E M allkn → know_ok segs E M k → kwritable allkn k b off n = true →
      0 ≤ n →
      store_ok segs M (Z_to_bv 64 (estart E (SA b off))) n.toNat = true ∧
        0 ≤ estart E (SA b off) ∧ estart E (SA b off) + n ≤ 2 ^ 64 := by
  intro k
  induction k with
  | nil =>
      intro b off n _ _ H _
      simp only [kwritable] at H
      exact absurd H (by simp)
  | cons K rest ih =>
      intro b off n Hall HK H Hn
      have HKK : kentry_ok segs E M K := HK K (List.mem_cons_self ..)
      have Hrest : know_ok segs E M rest := fun K' h => HK K' (List.mem_cons_of_mem K h)
      cases K with
      | KWr wa wn =>
          obtain ⟨wb, wk⟩ := wa
          simp only [kwritable] at H
          obtain ⟨hfl, hstore⟩ := HKK
          obtain ⟨G1, G2, G3, G4⟩ := hfl
          rcases ite_true_or H with hc0 | helse
          · rcases ite_true_or hc0 with hp | hfalse
            · obtain ⟨hb', hwk⟩ := (by
                have h := hp
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                exact h)
              have hbwe : b = wb := expr_eqb_eq b wb hb'
              rw [ite_eq_left hp] at hc0
              obtain ⟨wl, hxlo, hle⟩ := match_some_true hc0
              simp only [decide_eq_true_eq] at hle
              have hwl : wl ≤ elenZ E wn := xlo_sound segs E M allkn wn wl Hall hxlo
              subst b
              have F1' : 0 ≤ bv_unsigned (edenot E wb) + wk := G1
              have F4' : bv_unsigned (edenot E wb) + wk + elenZ E wn ≤ 2 ^ 64 := G4
              refine ⟨?_, ?_, ?_⟩
              · have hd : (0 : Int) ≤ off - wk := by omega
                have hstep := hstore (off - wk) n.toNat hd (by
                  have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg Hn
                  have : ((n.toNat : Nat) : Int) ≤ elenZ E wn := by omega
                  omega)
                have haddr : Z_to_bv 64 (estart E (SA wb off))
                    = BitVec.ofInt 64 (estart E (SA wb wk) + (off - wk)) := by
                  show BitVec.ofInt 64 (estart E (SA wb off))
                    = BitVec.ofInt 64 (estart E (SA wb wk) + (off - wk))
                  congr 1
                  unfold estart
                  dsimp only
                  omega
                rw [haddr]
                exact hstep
              · show 0 ≤ bv_unsigned (edenot E wb) + off
                omega
              · show bv_unsigned (edenot E wb) + off + n ≤ 2 ^ 64
                omega
            · exact absurd hfalse (by simp)
          · rcases ite_true_or helse with hc1 | hrest
            · obtain ⟨⟨hn0, hnlt⟩, hxin⟩ := (by
                have h := hc1
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                exact h)
              obtain ⟨hA, hB⟩ :=
                xinside_sound segs E M allkn b off (.ELit n) wb wk wn Hall hxin
              have G1' : 0 ≤ estart E (SA wb wk) := G1
              have G4' : estart E (SA wb wk) + elenZ E wn ≤ 2 ^ 64 := G4
              have hlen : elenZ E (.ELit n) = n := by
                show ((BitVec.ofInt 64 n).toNat : Int) = n
                exact u64_lit n ⟨hn0, by unfold two64 at hnlt; exact hnlt⟩
              have hB' : estart E (SA b off) + n ≤ estart E (SA wb wk) + elenZ E wn := by
                rw [← hlen]
                exact hB
              refine ⟨?_, ?_, ?_⟩
              · have hd : 0 ≤ estart E (SA b off) - estart E (SA wb wk) := by omega
                have hstep := hstore (estart E (SA b off) - estart E (SA wb wk)) n.toNat hd (by
                  have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg Hn
                  omega)
                have haddr : Z_to_bv 64 (estart E (SA b off))
                    = BitVec.ofInt 64 (estart E (SA wb wk)
                        + (estart E (SA b off) - estart E (SA wb wk))) := by
                  show BitVec.ofInt 64 (estart E (SA b off)) = BitVec.ofInt 64 _
                  congr 1
                  omega
                rw [haddr]
                exact hstep
              · omega
              · omega
            · exact ih b off n Hall Hrest hrest Hn
      | KWord a' w v => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KZero a' n' => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KBlob a' n' k' => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KImg lo hi => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KAlign e m => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KRange e lo hi => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KDisj a1 n1 a2 n2 => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KFill a' n' c => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn
      | KUnk a' n' => exact ih b off n Hall Hrest (by simpa only [kwritable] using H) Hn

/-- A two-`Option` `match` that yields `true`. -/
theorem match_pair_true {o1 o2 : Option Int} {f : Int → Int → Bool}
    (h : (match o1, o2 with | some a, some b => f a b | _, _ => false) = true) :
    ∃ a b, o1 = some a ∧ o2 = some b ∧ f a b = true := by
  cases o1 with
  | none => cases o2 <;> simp at h
  | some a =>
      cases o2 with
      | none => simp at h
      | some b => exact ⟨a, b, rfl, rfl, h⟩

theorem kwritable_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) :
    ∀ (k : List kentry) (b : expr) (off : Int) (n : expr),
      know_ok segs E M allkn → know_ok segs E M k → kwritable_x allkn k b off n = true →
      (∀ m : Nat, (m : Int) ≤ elenZ E n →
          store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true) ∧
        0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 := by
  intro k
  induction k with
  | nil =>
      intro b off n _ _ H
      simp only [kwritable_x] at H
      exact absurd H (by simp)
  | cons K rest ih =>
      intro b off n Hall HK H
      have HKK : kentry_ok segs E M K := HK K (List.mem_cons_self ..)
      have Hrest : know_ok segs E M rest := fun K' h => HK K' (List.mem_cons_of_mem K h)
      cases K with
      | KWr wa wn =>
          obtain ⟨wb, wk⟩ := wa
          simp only [kwritable_x] at H
          obtain ⟨hfl, hstore⟩ := HKK
          obtain ⟨G1, G2, G3, G4⟩ := hfl
          rcases ite_true_or H with hc0 | helse
          · rcases ite_true_or hc0 with hp | hfalse
            · obtain ⟨hb', hwk⟩ := (by
                have h := hp
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                exact h)
              have hbwe : b = wb := expr_eqb_eq b wb hb'
              rw [ite_eq_left hp] at hc0
              obtain ⟨nh, wl, hxhi, hxlo, hle⟩ := match_pair_true hc0
              simp only [decide_eq_true_eq] at hle
              have hnh : elenZ E n ≤ nh := xhi_sound segs E M allkn n nh Hall hxhi
              have hwl : wl ≤ elenZ E wn := xlo_sound segs E M allkn wn wl Hall hxlo
              subst b
              have F1' : 0 ≤ bv_unsigned (edenot E wb) + wk := G1
              have F4' : bv_unsigned (edenot E wb) + wk + elenZ E wn ≤ 2 ^ 64 := G4
              have G2' : 0 ≤ elenZ E wn := G3
              refine ⟨?_, ?_, ?_⟩
              · intro m hm
                have hd : (0 : Int) ≤ off - wk := by omega
                have hstep := hstore (off - wk) m hd (by omega)
                have haddr : Z_to_bv 64 (estart E (SA wb off))
                    = BitVec.ofInt 64 (estart E (SA wb wk) + (off - wk)) := by
                  show BitVec.ofInt 64 (estart E (SA wb off))
                    = BitVec.ofInt 64 (estart E (SA wb wk) + (off - wk))
                  congr 1
                  unfold estart
                  dsimp only
                  omega
                rw [haddr]
                exact hstep
              · show 0 ≤ bv_unsigned (edenot E wb) + off
                omega
              · show bv_unsigned (edenot E wb) + off + elenZ E n ≤ 2 ^ 64
                omega
            · exact absurd hfalse (by simp)
          · rcases ite_true_or helse with hc1 | hrest
            · obtain ⟨hA, hB⟩ :=
                xinside_sound segs E M allkn b off n wb wk wn Hall hc1
              have G1' : 0 ≤ estart E (SA wb wk) := G1
              have G4' : estart E (SA wb wk) + elenZ E wn ≤ 2 ^ 64 := G4
              refine ⟨?_, ?_, ?_⟩
              · intro m hm
                have hd : 0 ≤ estart E (SA b off) - estart E (SA wb wk) := by omega
                have hstep := hstore (estart E (SA b off) - estart E (SA wb wk)) m hd (by omega)
                have haddr : Z_to_bv 64 (estart E (SA b off))
                    = BitVec.ofInt 64 (estart E (SA wb wk)
                        + (estart E (SA b off) - estart E (SA wb wk))) := by
                  show BitVec.ofInt 64 (estart E (SA b off)) = BitVec.ofInt 64 _
                  congr 1
                  omega
                rw [haddr]
                exact hstep
              · omega
              · omega
            · exact ih b off n Hall Hrest hrest
      | KWord a' w v => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KZero a' n' => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KBlob a' n' k' => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KImg lo hi => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KAlign e m => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KRange e lo hi => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KDisj a1 n1 a2 n2 => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KFill a' n' c => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)
      | KUnk a' n' => exact ih b off n Hall Hrest (by simpa only [kwritable_x] using H)

theorem kzero_x_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (allkn : List kentry) :
    ∀ (k : List kentry) (b : expr) (off : Int) (n : expr),
      know_ok segs E M allkn → know_ok segs E M k → kzero_x allkn k b off n = true →
      (∀ i : Int, 0 ≤ i → i < elenZ E n →
          M (Z_to_bv 64 (estart E (SA b off) + i)) = some (Z_to_bv 8 0)) ∧
        0 ≤ estart E (SA b off) ∧ estart E (SA b off) + elenZ E n ≤ 2 ^ 64 := by
  intro k
  induction k with
  | nil =>
      intro b off n _ _ H
      simp only [kzero_x] at H
      exact absurd H (by simp)
  | cons K rest ih =>
      intro b off n Hall HK H
      have HKK : kentry_ok segs E M K := HK K (List.mem_cons_self ..)
      have Hrest : know_ok segs E M rest := fun K' h => HK K' (List.mem_cons_of_mem K h)
      cases K with
      | KZero za zn =>
          obtain ⟨zb, zk⟩ := za
          simp only [kzero_x] at H
          obtain ⟨hfl, hzero⟩ := HKK
          obtain ⟨G1, G2, G3, G4⟩ := hfl
          rcases ite_true_or H with hc0 | helse
          · rcases ite_true_or hc0 with hp | hfalse
            · obtain ⟨hb', hzk⟩ := (by
                have h := hp
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                exact h)
              have hbwe : b = zb := expr_eqb_eq b zb hb'
              rw [ite_eq_left hp] at hc0
              obtain ⟨nh, zl, hxhi, hxlo, hle⟩ := match_pair_true hc0
              simp only [decide_eq_true_eq] at hle
              have hnh : elenZ E n ≤ nh := xhi_sound segs E M allkn n nh Hall hxhi
              have hzl : zl ≤ elenZ E zn := xlo_sound segs E M allkn zn zl Hall hxlo
              subst b
              have F1' : 0 ≤ bv_unsigned (edenot E zb) + zk := G1
              have F4' : bv_unsigned (edenot E zb) + zk + elenZ E zn ≤ 2 ^ 64 := G4
              refine ⟨?_, ?_, ?_⟩
              · intro i hi0 hilt
                have hd : 0 ≤ off - zk := by omega
                have hlt : off - zk + i < elenZ E zn := by omega
                have hstep := hzero (off - zk + i) (by omega) hlt
                have haddr : Z_to_bv 64 (estart E (SA zb off) + i)
                    = BitVec.ofInt 64 (estart E (SA zb zk) + (off - zk + i)) := by
                  show BitVec.ofInt 64 (estart E (SA zb off) + i) = BitVec.ofInt 64 _
                  congr 1
                  unfold estart
                  dsimp only
                  omega
                rw [haddr]
                exact hstep
              · show 0 ≤ bv_unsigned (edenot E zb) + off
                omega
              · show bv_unsigned (edenot E zb) + off + elenZ E n ≤ 2 ^ 64
                omega
            · exact absurd hfalse (by simp)
          · rcases ite_true_or helse with hc1 | hrest
            · obtain ⟨hA, hB⟩ :=
                xinside_sound segs E M allkn b off n zb zk zn Hall hc1
              have G1' : 0 ≤ estart E (SA zb zk) := G1
              have G4' : estart E (SA zb zk) + elenZ E zn ≤ 2 ^ 64 := G4
              refine ⟨?_, ?_, ?_⟩
              · intro i hi0 hilt
                have hd : 0 ≤ estart E (SA b off) - estart E (SA zb zk) := by omega
                have hlt : estart E (SA b off) - estart E (SA zb zk) + i < elenZ E zn := by omega
                have hstep := hzero (estart E (SA b off) - estart E (SA zb zk) + i) (by omega) hlt
                have haddr : Z_to_bv 64 (estart E (SA b off) + i)
                    = BitVec.ofInt 64 (estart E (SA zb zk)
                        + (estart E (SA b off) - estart E (SA zb zk) + i)) := by
                  show BitVec.ofInt 64 (estart E (SA b off) + i) = BitVec.ofInt 64 _
                  congr 1
                  omega
                rw [haddr]
                exact hstep
              · omega
              · omega
            · exact ih b off n Hall Hrest hrest
      | KWord a' w v => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KBlob a' n' k' => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KImg lo hi => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KAlign e m => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KRange e lo hi => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KWr a' n' => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KDisj a1 n1 a2 n2 => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KFill a' n' c => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)
      | KUnk a' n' => exact ih b off n Hall Hrest (by simpa only [kzero_x] using H)

theorem lookup_piece (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b : expr) (off : Int) (w : Nat) (v : expr) (hs : List Bool)
    (HK : know_ok segs E M k) (Hw : 1 ≤ w ∧ w ≤ 8)
    (HL : know_lookup segs k b off w false [] [] = .LHit v [] hs)
    (Hfl : flat E (SA b off) (w : Int)) :
    piece_ok segs E M b off w v := by
  have X := know_lookup_sound segs E k M b off w false [] [] HK Hw.1 Hw.2
  rw [HL] at X
  obtain ⟨bs, Hrd, Hlen, Hv⟩ := X (fun s hs => absurd hs (by simp)) Hfl
  refine ⟨bs, ?_, Hlen, ?_⟩
  · rw [← adenot_SA]
    exact Hrd
  · simp only [extz, Bool.false_eq_true, ite_false] at Hv
    rw [← Hv, ← Hlen]
    exact word_to_le_bytes_of_bytes bs (by omega)

theorem kread8e_piece (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b : expr) (off : Int) (v : expr)
    (HK : know_ok segs E M k) (H : kread8e segs k b off = some v)
    (Hfl : flat E (SA b off) 8) :
    piece_ok segs E M b off 8 v := by
  unfold kread8e at H
  cases hl : know_lookup segs k b off 8 false [] [] with
  | LHit v' scs hs =>
      cases scs with
      | nil =>
          simp only [hl] at H
          obtain rfl : v' = v := by simpa using H
          exact lookup_piece segs E M k b off 8 v' hs HK ⟨by omega, by omega⟩ hl Hfl
      | cons s rest => simp only [hl] at H; exact absurd H (by simp)
  | LMiss scs hs => simp only [hl] at H; exact absurd H (by simp)
  | LStuck => simp only [hl] at H; exact absurd H (by simp)

theorem firstn_skipn_map_nth {α : Type} (d : α) (k : Nat) (l : List α) (m : Nat)
    (hm : m + k ≤ l.length) :
    (l.drop m).take k = (List.range k).map (fun q => l.getD (m + q) d) := by
  induction l generalizing m k with
  | nil =>
      have hk : k = 0 := by simp at hm; omega
      subst hk
      rfl
  | cons a t ih =>
      cases m with
      | zero =>
          cases k with
          | zero => rfl
          | succ k' =>
              rw [List.drop_zero, List.take_succ_cons, List.range_succ_eq_map,
                List.map_cons, List.map_map]
              rw [show (0 + 0 : Nat) = 0 from rfl, List.getD_cons_zero]
              have hmap : List.map ((fun q => (a :: t).getD (0 + q) d) ∘ Nat.succ) (List.range k')
                  = List.map (fun q => t.getD (0 + q) d) (List.range k') := by
                apply List.map_congr_left
                intro q _
                show (a :: t).getD (0 + (q + 1)) d = t.getD (0 + q) d
                rw [show 0 + (q + 1) = (0 + q) + 1 from by omega, List.getD_cons_succ]
              rw [hmap]
              exact congrArg (List.cons a) (ih (k := k') (m := 0) (by simpa using hm))
      | succ m' =>
          rw [List.drop_succ_cons]
          have hstep : ∀ q : Nat, (a :: t).getD (m' + 1 + q) d = t.getD (m' + q) d := by
            intro q
            rw [show m' + 1 + q = (m' + q) + 1 from by omega, List.getD_cons_succ]
          simp only [hstep]
          exact ih (k := k) (m := m') (by simp only [List.length_cons] at hm; omega)

/-! -/

theorem kreadZ1_byte (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (b : expr) (off z : Int)
    (HK : know_ok segs E M k) (H : kreadZ segs k b off 1 = some z)
    (Hfl : flat E (SA b off) 1) :
    rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = some [Z_to_bv 8 z] ∧ 0 ≤ z ∧ z < 256 := by
  unfold kreadZ at H
  cases hl : know_lookup segs k b off 1 false [] [] with
  | LHit v scs hs =>
      cases scs with
      | cons s rest => simp only [hl] at H; exact absurd H (by simp)
      | nil =>
          cases v with
          | ELit z0 =>
              simp only [hl] at H
              obtain rfl : z0 % two64 = z := by simpa using H
              have X := know_lookup_sound segs E k M b off 1 false [] [] HK (by omega) (by omega)
              rw [hl] at X
              obtain ⟨bs, Hrd, Hlen, Hv⟩ := X (fun s hs => absurd hs (by simp)) Hfl
              simp only [extz, Bool.false_eq_true, ite_false, edenot] at Hv
              show rdn segs M (adenot E (SA b off)) 1 = some [Z_to_bv 8 (z0 % two64)] ∧
                0 ≤ z0 % two64 ∧ z0 % two64 < 256
              cases bs with
              | nil => simp at Hlen
              | cons b0 bs' =>
                  cases bs' with
                  | nil =>
                      rw [bytes_le_single] at Hv
                      have hvu : bv_unsigned b0 = z0 % two64 := by
                        have h := congrArg bv_unsigned Hv
                        simp only [u_lit64] at h
                        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
                          have := b0.isLt
                          show (b0.toNat : Int) < two64
                          unfold two64
                          omega)] at h
                        exact h
                      have hz : z0 % two64 = (b0.toNat : Int) := hvu.symm
                      have hz8 : Z_to_bv 8 (z0 % two64) = b0 := by
                        rw [hz, Z_to_bv8_unsigned]
                      rw [hz8, hz]
                      refine ⟨Hrd, ?_, ?_⟩
                      · exact Int.natCast_nonneg _
                      · have h8 : (2 : Nat) ^ 8 = 256 := by decide
                        have hlt := b0.isLt
                        omega
                  | cons _ _ => simp at Hlen
          | EVar n => simp only [hl] at H; exact absurd H (by simp)
          | EAlu o a1 a2 => simp only [hl] at H; exact absurd H (by simp)
          | EAluw o a1 a2 => simp only [hl] at H; exact absurd H (by simp)
          | EMd o a1 a2 => simp only [hl] at H; exact absurd H (by simp)
          | EMdw o a1 a2 => simp only [hl] at H; exact absurd H (by simp)
          | EExt sx lo n e => simp only [hl] at H; exact absurd H (by simp)
          | EBlob sx kk i n => simp only [hl] at H; exact absurd H (by simp)
  | LMiss scs hs => simp only [hl] at H; exact absurd H (by simp)
  | LStuck => simp only [hl] at H; exact absurd H (by simp)

theorem Z_to_bv_add_int (y : Int) (j : Nat) :
    Z_to_bv 64 (y + (j : Int)) = Z_to_bv 64 y + nat_to_word j := by
  simp only [Z_to_bv, nat_to_word]
  bv_omega

theorem map_Z_to_bv8_bv_unsigned (zs : List Int) (H : ∀ z ∈ zs, 0 ≤ z ∧ z < 256) :
    (zs.map (fun z => Z_to_bv 8 z)).map (fun b => bv_unsigned b) = zs := by
  induction zs with
  | nil => rfl
  | cons z rest ih =>
      have hz := H z (List.mem_cons_self)
      have hrest : ∀ w ∈ rest, 0 ≤ w ∧ w < 256 :=
        fun w hw => H w (List.mem_cons_of_mem z hw)
      simp only [List.map_cons]
      rw [ih hrest, u8_lit, Int.emod_eq_of_lt hz.1 hz.2]

theorem zbytes_of_small (zs : List Int) (H : ∀ z ∈ zs, 0 ≤ z ∧ z < 256) :
    zbytes_le_to_Z zs = bytes_le_to_Z (zs.map (fun z => Z_to_bv 8 z)) % two64 := by
  conv => lhs; rw [← map_Z_to_bv8_bv_unsigned zs H]
  exact zbytes_map (zs.map (fun z => Z_to_bv 8 z))

theorem kread_bytes_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) :
    ∀ (len : Nat) (b : expr) (off : Int) (zs : List Int),
      know_ok segs E M k → kread_bytes segs len k b off = some zs →
      0 ≤ estart E (SA b off) → estart E (SA b off) + (len : Int) ≤ 2 ^ 64 →
      rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = some (zs.map (fun z => Z_to_bv 8 z))
        ∧ zs.length = len ∧ ∀ z ∈ zs, 0 ≤ z ∧ z < 256 := by
  intro len
  induction len with
  | zero =>
      intro b off zs HK H _ _
      simp only [kread_bytes] at H
      obtain rfl : [] = zs := by simpa using H
      exact ⟨rfl, rfl, by simp⟩
  | succ n ih =>
      intro b off zs HK H Hlo Hhi
      simp only [kread_bytes] at H
      cases hz : kreadZ segs k b off 1 with
      | none => rw [hz] at H; exact absurd H (by simp)
      | some z =>
          cases hr : kread_bytes segs n k b (off + 1) with
          | none => rw [hz, hr] at H; exact absurd H (by simp)
          | some rest =>
              rw [hz, hr] at H
              obtain rfl : z :: rest = zs := by simpa using H
              have Hfl : flat E (SA b off) 1 := by
                refine ⟨Hlo, ?_, by omega, ?_⟩ <;> simp only [estart, SA] at Hhi ⊢ <;> omega
              obtain ⟨Hrd, Hz0, Hz1⟩ := kreadZ1_byte segs E M k b off z HK hz Hfl
              have Hlo1 : 0 ≤ estart E (SA b (off + 1)) := by
                simp only [estart, SA] at Hlo ⊢; omega
              have Hhi1 : estart E (SA b (off + 1)) + (n : Int) ≤ 2 ^ 64 := by
                simp only [estart, SA] at Hhi ⊢; omega
              obtain ⟨Hrd2, Hlen, Hall⟩ := ih b (off + 1) rest HK hr Hlo1 Hhi1
              have haddr : Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1
                  = Z_to_bv 64 (estart E (SA b (off + 1))) := by
                rw [← Z_to_bv_add_int]
                congr 1
                simp only [estart, SA]
                omega
              refine ⟨?_, by simp [Hlen], ?_⟩
              · have hstep := rdn_app segs M 1 n (Z_to_bv 64 (estart E (SA b off)))
                  [Z_to_bv 8 z] (rest.map (fun z => Z_to_bv 8 z)) Hrd (by rwa [haddr])
                rw [show 1 + n = n + 1 from by omega] at hstep
                simpa using hstep
              · intro w hw
                rcases List.mem_cons.mp hw with h | h
                · subst h; exact ⟨Hz0, Hz1⟩
                · exact Hall w h


example (n : Int) (w : Nat) (H2 : (w:Int) ≤ n) :
    (n - (w:Int)).toNat = n.toNat - w := by
  rw [Int.toNat_sub'' (by omega) (by omega)]
  simp

/-! ### `copy_facts` list glue -/

theorem take_append_of_length_eq {α : Type} (l1 l2 : List α) (w : Nat) (h : l1.length = w) :
    (l1 ++ l2).take w = l1 := by
  rw [← h, List.take_left]

theorem drop_append_of_length_eq {α : Type} (l1 l2 : List α) (w : Nat) (h : l1.length = w) :
    (l1 ++ l2).drop w = l2 := by
  rw [← h, List.drop_left]

theorem copy_facts_sound (segs : List Segment) (E : env) (M : word → Option byte)
    (k : List kentry) (sb db : expr) :
    ∀ (fuel : Nat) (sk dk n : Int) (kc : List kentry),
      know_ok segs E M k → copy_facts segs fuel k sb sk db dk n = some kc →
      0 ≤ n → n.toNat ≤ fuel →
      0 ≤ estart E (SA sb sk) → estart E (SA sb sk) + n ≤ 2 ^ 64 →
      0 ≤ estart E (SA db dk) → estart E (SA db dk) + n ≤ 2 ^ 64 →
      ∃ bs, bs.length = n.toNat ∧
        rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) n.toNat = some bs ∧
        (∀ M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) n.toNat = some bs →
          know_ok segs E M' kc) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi
      simp only [copy_facts] at H
      obtain rfl : [] = kc := by simpa using H
      have hn0 : n = 0 := by omega
      subst hn0
      exact ⟨[], rfl, rfl, fun M' _ => by simp [know_ok]⟩
  | succ f ih =>
      intro sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi
      simp only [copy_facts] at H
      have haddr : ∀ (b : expr) (o : Int) (w : Nat),
          Z_to_bv 64 (estart E (SA b o)) + nat_to_word w
            = Z_to_bv 64 (estart E (SA b (o + (w : Int)))) := by
        intro b o w
        rw [← Z_to_bv_add_int]
        congr 1
        simp only [estart, SA]
        omega
      have STEP : ∀ (w : Nat) (v : expr) (kr : List kentry),
          1 ≤ w → w ≤ 8 → (w : Int) ≤ n →
          piece_ok segs E M sb sk w v →
          copy_facts segs f k sb (sk + (w : Int)) db (dk + (w : Int)) (n - (w : Int)) = some kr →
          kc = .KWord (SA db dk) w v :: kr →
          ∃ bs, bs.length = n.toNat ∧
            rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) n.toNat = some bs ∧
            (∀ M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) n.toNat = some bs →
              know_ok segs E M' kc) := by
        intro w v kr Hw1 Hw8 Hwn hpiece Hr Hkc
        subst Hkc
        obtain ⟨bsP, HrdP, HlenP, HvP⟩ := hpiece
        have hsub : (n - (w : Int)).toNat = n.toNat - w := by
          rw [Int.toNat_sub'' (by omega) (by omega)]
          simp
        have ES : estart E (SA sb (sk + (w : Int))) = estart E (SA sb sk) + (w : Int) := by
          simp only [estart, SA]; omega
        have ED : estart E (SA db (dk + (w : Int))) = estart E (SA db dk) + (w : Int) := by
          simp only [estart, SA]; omega
        obtain ⟨bsR, HlenR, HrdR, HKR⟩ :=
          ih (sk + (w : Int)) (dk + (w : Int)) (n - (w : Int)) kr HK Hr
            (by omega) (by omega) (by rw [ES]; omega) (by rw [ES]; omega)
            (by rw [ED]; omega) (by rw [ED]; omega)
        refine ⟨bsP ++ bsR, ?_, ?_, ?_⟩
        · rw [List.length_append, HlenP, HlenR, hsub]
          omega
        · have H2 : rdn segs M (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)
              (n.toNat - w) = some bsR := by
            rw [haddr sb sk w, ← hsub]
            exact HrdR
          have hstep := rdn_app segs M w (n.toNat - w)
            (Z_to_bv 64 (estart E (SA sb sk))) bsP bsR HrdP H2
          rw [show w + (n.toNat - w) = n.toNat from by omega] at hstep
          exact hstep
        · intro M' HM'
          have hK : kentry_ok segs E M' (.KWord (SA db dk) w v) := by
            refine ⟨Hw8, ⟨Dlo, ?_, by omega, ?_⟩, ?_⟩
            · omega
            · omega
            · rw [adenot_SA]
              have htake := rdn_firstn segs M' n.toNat
                (Z_to_bv 64 (estart E (SA db dk))) (bsP ++ bsR) w HM' (by omega)
              rw [htake, take_append_of_length_eq bsP bsR w HlenP, HvP]
          intro K hK'
          rcases List.mem_cons.mp hK' with h | h
          · subst h; exact hK
          · exact HKR M' (by
              have hdrop := SeqExec.rdn_skipn segs M' n.toNat
                (Z_to_bv 64 (estart E (SA db dk))) (bsP ++ bsR) w HM' (by omega)
              rw [haddr db dk w, drop_append_of_length_eq bsP bsR w HlenP, ← hsub] at hdrop
              exact hdrop) K h

      cases h8e : kread8e segs k sb sk with
      | some v =>
          rw [h8e] at H
          simp only [Bool.and_true] at H
          split at H
          · rename_i h8
            have h8n : 8 ≤ n := by simpa using h8
            cases hr : copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8) with
            | none => rw [hr] at H; exact absurd H (by simp)
            | some rest =>
                rw [hr] at H
                obtain rfl : .KWord (SA db dk) 8 v :: rest = kc := by simpa using H
                have hfl8 : flat E (SA sb sk) 8 := ⟨Slo, by omega, by omega, by omega⟩
                exact STEP 8 v rest (by omega) (by omega) (by omega)
                  (kread8e_piece segs E M k sb sk v HK h8e hfl8) hr rfl
          · rename_i h8f
            split at H
            · rename_i h1
              have h1n : 1 ≤ n := by simpa using h1
              cases hl : know_lookup segs k sb sk 1 false [] [] with
              | LHit v scs hs =>
                  cases scs with
                  | nil =>
                      cases hr : copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1) with
                      | none => rw [hl, hr] at H; exact absurd H (by simp)
                      | some rest =>
                          rw [hl, hr] at H
                          obtain rfl : .KWord (SA db dk) 1 v :: rest = kc := by simpa using H
                          have hfl1 : flat E (SA sb sk) 1 := ⟨Slo, by omega, by omega, by omega⟩
                          exact STEP 1 v rest (by omega) (by omega) (by omega)
                            (lookup_piece segs E M k sb sk 1 v hs HK ⟨by omega, by omega⟩ hl hfl1)
                            hr rfl
                  | cons s rest => rw [hl] at H; exact absurd H (by simp)
              | LMiss scs hs => rw [hl] at H; exact absurd H (by simp)
              | LStuck => rw [hl] at H; exact absurd H (by simp)
            · rename_i h1f
              obtain rfl : [] = kc := by simpa using H
              have hn0 : n = 0 := by omega
              subst hn0
              exact ⟨[], rfl, rfl, fun M' _ => by simp [know_ok]⟩
      | none =>
          cases h8b : kread_bytes segs 8 k sb sk with
          | none =>
              rw [h8e, h8b] at H
              simp only [Bool.and_false, Bool.false_eq_true, ite_false, ite_false,
                decide_false] at H

              split at H
              · rename_i h1
                have h1n : 1 ≤ n := by simpa using h1
                cases hl : know_lookup segs k sb sk 1 false [] [] with
                | LHit v scs hs =>
                    cases scs with
                    | nil =>
                        cases hr : copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1) with
                        | none => rw [hl, hr] at H; exact absurd H (by simp)
                        | some rest =>
                            rw [hl, hr] at H
                            obtain rfl : .KWord (SA db dk) 1 v :: rest = kc := by simpa using H
                            have hfl1 : flat E (SA sb sk) 1 := ⟨Slo, by omega, by omega, by omega⟩
                            exact STEP 1 v rest (by omega) (by omega) (by omega)
                              (lookup_piece segs E M k sb sk 1 v hs HK ⟨by omega, by omega⟩ hl hfl1)
                              hr rfl
                    | cons s rest => rw [hl] at H; exact absurd H (by simp)
                | LMiss scs hs => rw [hl] at H; exact absurd H (by simp)
                | LStuck => rw [hl] at H; exact absurd H (by simp)
              · rename_i h1f
                obtain rfl : [] = kc := by simpa using H
                have hn0 : n = 0 := by omega
                subst hn0
                exact ⟨[], rfl, rfl, fun M' _ => by simp [know_ok]⟩
          | some zs =>
              rw [h8e, h8b] at H
              simp only [Bool.and_true] at H
              split at H
              · rename_i h8
                have h8n : 8 ≤ n := by simpa using h8
                obtain ⟨Hrd, Hlen, Hall⟩ :=
                  kread_bytes_sound segs E M k 8 sb sk zs HK h8b Slo (by omega)
                have hlen8 : (zs.map (fun z => Z_to_bv 8 z)).length = 8 := by
                  rw [List.length_map]; exact Hlen
                have hpiece : piece_ok segs E M sb sk 8 (.ELit (zbytes_le_to_Z zs)) := by
                  refine ⟨zs.map (fun z => Z_to_bv 8 z), Hrd, hlen8, ?_⟩
                  show word_to_le_bytes 8 (Z_to_bv 64 (zbytes_le_to_Z zs)) = _
                  rw [zbytes_of_small zs Hall, two64_eq, Z_to_bv_emod64]
                  exact word_to_le_bytes_of_bytes_n 8 (zs.map (fun z => Z_to_bv 8 z)) hlen8 (by omega)
                cases hr : copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8) with
                | none => rw [hr] at H; exact absurd H (by simp)
                | some rest =>
                    rw [hr] at H
                    obtain rfl : .KWord (SA db dk) 8 (.ELit (zbytes_le_to_Z zs)) :: rest = kc := by
                      simpa using H
                    exact STEP 8 (.ELit (zbytes_le_to_Z zs)) rest (by omega) (by omega) (by omega)
                      hpiece hr rfl
              · rename_i h8f
                split at H
                · rename_i h1
                  have h1n : 1 ≤ n := by simpa using h1
                  cases hl : know_lookup segs k sb sk 1 false [] [] with
                  | LHit v scs hs =>
                      cases scs with
                      | nil =>
                          cases hr : copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1) with
                          | none => rw [hl, hr] at H; exact absurd H (by simp)
                          | some rest =>
                              rw [hl, hr] at H
                              obtain rfl : .KWord (SA db dk) 1 v :: rest = kc := by simpa using H
                              have hfl1 : flat E (SA sb sk) 1 := ⟨Slo, by omega, by omega, by omega⟩
                              exact STEP 1 v rest (by omega) (by omega) (by omega)
                                (lookup_piece segs E M k sb sk 1 v hs HK ⟨by omega, by omega⟩ hl hfl1)
                                hr rfl
                      | cons s rest => rw [hl] at H; exact absurd H (by simp)
                  | LMiss scs hs => rw [hl] at H; exact absurd H (by simp)
                  | LStuck => rw [hl] at H; exact absurd H (by simp)
                · rename_i h1f
                  obtain rfl : [] = kc := by simpa using H
                  have hn0 : n = 0 := by omega
                  subst hn0
                  exact ⟨[], rfl, rfl, fun M' _ => by simp [know_ok]⟩

/-! ## 4. The generic summarized-call node (`call_core`, `call_node_sound*`) -/

theorem k0_sound (SEGS : List Segment) (A : atable) (E : env) (M : word → Option byte)
    (k : List kentry) (db : expr) (dk : Int) (ne dst : expr) (k0 : List kentry)
    (HK : know_ok SEGS E M k)
    (H : (if off_image_x A k db dk ne then some k
          else match dst, ne with
               | .ELit d, .ELit n => some (kimg_cut k (d % two64) n)
               | _, _ => none) = some k0) :
    know_ok SEGS E M k0 := by
  split at H
  · rename_i h
    obtain rfl : k = k0 := by simpa using H
    exact HK
  · rename_i h
    cases dst with
    | ELit d =>
        cases ne with
        | ELit n =>
            obtain rfl : kimg_cut k (d % two64) n = k0 := by simpa using H
            exact kimg_cut_sound SEGS E M k (d % two64) n HK
        | EVar a => simp at H
        | EAlu o a b => simp at H
        | EAluw o a b => simp at H
        | EMd o a b => simp at H
        | EMdw o a b => simp at H
        | EExt sx l nn e => simp at H
        | EBlob sx kk i nn => simp at H
    | EVar a => simp at H
    | EAlu o a b => simp at H
    | EAluw o a b => simp at H
    | EMd o a b => simp at H
    | EMdw o a b => simp at H
    | EExt sx l nn e => simp at H
    | EBlob sx kk i nn => simp at H

theorem call_core (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (cs : acs) (E E' : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (T : TSet) (ret : Int) (sr2 : List expr) (k' : List kentry) (nx2 : Nat)
    (regs' : BvMap word) (MR' : word → Option byte)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hfresh : fresh_ok nx0 cs = true)
    (Hag : env_agree (nxt cs) E E')
    (Hms : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (Mr A argH E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
    (HR' : regs_ok E' sr2 regs')
    (HK' : know_ok SEGS E' MR' k')
    (Hk : ∀ (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      cs_ok SEGS A LIMIT SINV argH FS0 E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' ret FULL' model') T) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
  obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := w_fresh_ok_parts nx0 cs Hfresh
  have HH : hid A argH E' cs model = hid A argH E cs model :=
    w_hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow
  have HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E' cs R FULL model :=
    w_cs_ok_agree SEGS A LIMIT nx0 SINV SINV_agree argH argH_agree FS0 E E' cs R FULL model
      Hag Hfresh HC
  refine AsanAcctShape.srz_msteps_restricted_T SEGS (hid A argH E cs model)
    (w_H_off_segments_cs SEGS A nx0 argH E cs model HULL_ok SEGS_in_hull argH_high) SEGS_wx
    (allowA A E cs) (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))
    (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
    (w_lazy_cover_cs SEGS A LIMIT nx0 SINV argH FS0 HULL_ok E cs R FULL model HC)
    (w_A_wf_allowA A E cs) HC.co_minv HC.co_halt ?_ ?_
  · rw [restrict_mkst]
    exact Hms
  · intro model' Hinv' Hsame Hclean
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfsm, -, -, -, -, -⟩ :=
      same_but_materialized_frame model model' Hsame
    let FULL' : word → Option byte := munrestrict (hid A argH E cs model) FULL MR'
    have Hmr' : Mr A argH E' cs model FULL' = MR' := by
      show mrestrict (hid A argH E' cs model) FULL' = MR'
      rw [HH]
      exact mrestrict_munrestrict_clean (hid A argH E cs model) FULL MR'
        (fun a Ha => Hclean a Ha)
    refine Hk regs' FULL' model' ?_ hfsm
    refine w_cs_ok_frame SEGS A LIMIT nx0 SINV argH FS0 SINV_frame E' cs R FULL model
      (mk_ss ret sr2 k' nx2) regs' FULL' model' HC1 Hsame ?_ HR' rfl ?_ ?_
    · rw [allowA_agree A (nxt cs) E E' cs Hag Fallow]
      exact Hinv'
    · show know_ok SEGS E' (Mr A argH E' cs model FULL') k'
      rw [Hmr']
      exact HK'
    · intro a Ha
      show (if hid A argH E cs model a then FULL a else MR' a) = FULL a
      rw [HH] at Ha
      rw [Ha]
      rfl
/-- `Z_to_bv 64` round-trips `bv_unsigned`, in the `bv_unsigned` spelling of
    `BvBase.ofInt_toNat` (spelling bridge). -/
theorem Z_to_bv64_bv_unsigned (w : word) : Z_to_bv 64 (bv_unsigned w) = w :=
  ofInt_toNat w

/-- `Z_to_bv 5 1 = 1` as a register index (`Z_to_bv 5 10 = 10` is
    `Z_to_bv5_ten` below; the `w_reg_*` lemmas state their index as
    `Z_to_bv 5 (n : Int)`, the `fill_spec`-style statements as the numeral). -/
theorem Z_to_bv5_one : Z_to_bv 5 ((1 : Nat) : Int) = (1 : reg) := by decide

theorem Z_to_bv5_ten : Z_to_bv 5 (10 : Int) = (10 : reg) := by decide

/-- `Z_to_bv 5 10 = 10` in the OTHER spelling.  `Z_to_bv5_ten` above is the
    `(10 : Int)` literal, which `rw` does not match against the
    `((10 : Nat) : Int)` that `w_reg_sound`'s conclusion carries (they are
    definitionally equal, but `rw`'s keyed matching does not unfold
    `Int.ofNat`); `summary_copy_sound` needs both directions. -/
theorem Z_to_bv5_ten_up : Z_to_bv 5 ((10 : Nat) : Int) = (10 : reg) := by decide

/-- `A1` as a register index, in the `w_reg_*` lemma's spelling. -/
theorem Z_to_bv5_eleven : Z_to_bv 5 ((11 : Nat) : Int) = (11 : reg) := by decide

/-- `A2` as a register index. -/
theorem Z_to_bv5_twelve : Z_to_bv 5 ((12 : Nat) : Int) = (12 : reg) := by decide

/-- `a4` as a register index. -/
theorem Z_to_bv5_fourteen : Z_to_bv 5 ((14 : Nat) : Int) = (14 : reg) := by decide

/-- `a5` as a register index. -/
theorem Z_to_bv5_fifteen : Z_to_bv 5 ((15 : Nat) : Int) = (15 : reg) := by decide

/-! ### Unpacking the two `after_call` guards (glue) -/

theorem after_call_unpack (nx0 : Nat) (cs : acs) (ret : Int) (rv : Option expr)
    (k' : List kentry) (cs' : acs) (H : after_call nx0 cs ret rv k' = some cs') :
    fresh_ok nx0 cs = true ∧ AsanPlanCore.kn_vars_lt (nxt cs) k' = true ∧
    cs' = with_ss cs (mk_ss ret (match rv with
      | some e => sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e
      | none => sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) k' (nxt cs + NCS)) ∧
    (∀ e, rv = some e → AsanPlanCore.expr_vars_lt (nxt cs) e = true) := by
  unfold after_call at H
  dsimp only at H
  cases rv with
  | none =>
      simp only [] at H
      split at H
      · rename_i hc
        obtain rfl : cs' = with_ss cs
            (mk_ss ret (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) k'
              (nxt cs + NCS)) := (Option.some.inj H).symm
        refine ⟨?_, ?_, rfl, fun e he => absurd he (by simp)⟩
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.1
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.2
      · rename_i hc
        simp at H
  | some e =>
      simp only [] at H
      split at H
      · rename_i hc
        obtain rfl : cs' = with_ss cs
            (mk_ss ret (sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e) k'
              (nxt cs + NCS)) := (Option.some.inj H).symm
        refine ⟨?_, ?_, rfl, ?_⟩
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.1
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.2
        · intro e' he'
          rw [Option.some.injEq] at he'
          subst he'
          have h := hc; simp only [Bool.and_eq_true] at h
          exact h.2
      · rename_i hc
        simp at H

theorem call_node_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (cs cs' : acs) (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (T : TSet) (ret : Int) (rv : Option expr) (k' : List kentry)
    (regs' : BvMap word) (MR' : word → Option byte)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hac : after_call nx0 cs ret rv k' = some cs')
    (Hms : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (Mr A argH E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
    (Hkept : kept_ok R regs')
    (Hrv : match rv with
           | some e => getr regs' (Z_to_bv 5 10) = edenot E e
           | none => True)
    (HK' : know_ok SEGS E MR' k')
    (Hk : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' → env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') T) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
  have GO : ∀ (sr2 : List expr), cs' = with_ss cs (mk_ss ret sr2 k' (nxt cs + NCS)) →
      fresh_ok nx0 cs = true → AsanPlanCore.kn_vars_lt (nxt cs) k' = true →
      regs_ok (ext_call E (nxt cs) regs') sr2 regs' →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
    intro sr2 hcs' hf hk Hregs
    have Hk' := Hk
    rw [hcs'] at Hk'
    obtain ⟨Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle⟩ := w_fresh_ok_parts nx0 cs hf
    let E' : env := ext_call E (nxt cs) regs'
    have HagE : env_agree (nxt cs) E E' := ext_call_agree E (nxt cs) regs'
    refine call_core SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
      argH_agree argH_high SEGS_in_hull cs E E' R FULL model T ret sr2 k' (nxt cs + NCS)
      regs' MR' HC hf HagE Hms Hregs ?_ ?_
    · exact know_ok_agree' SEGS (nxt cs) E E' MR' k' HagE hk HK'
    · intro R' FULL' model' HC' Hfs
      exact Hk' E' R' FULL' model' (w_env_agree_le nx0 (nxt cs) E E' HagE Fle) HagE HC' Hfs
  cases rv with
  | none =>
      obtain ⟨hf, hk, hcs', hev⟩ := after_call_unpack _ _ _ _ _ _ Hac
      obtain ⟨Fsr, -, -, -, -, -, -⟩ := w_fresh_ok_parts nx0 cs hf
      refine GO (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) hcs' hf hk ?_
      exact regs_after_call E _ R regs' (nxt cs) none HC.co_regs Fsr Hkept trivial
  | some e =>
      obtain ⟨hf, hk, hcs', hev⟩ := after_call_unpack _ _ _ _ _ _ Hac
      obtain ⟨Fsr, -, -, -, -, -, -⟩ := w_fresh_ok_parts nx0 cs hf
      refine GO (sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e) hcs' hf hk ?_
      exact regs_after_call E _ R regs' (nxt cs) (some e) HC.co_regs Fsr Hkept
        ⟨hev e rfl, by rw [Z_to_bv5_ten] at Hrv; exact Hrv⟩
theorem after_call2_unpack (nx0 : Nat) (cs : acs) (ret : Int) (rv : Option expr)
    (k' : List kentry) (extra : Nat) (cs' : acs)
    (H : after_call2 nx0 cs ret rv k' extra = some cs') :
    fresh_ok nx0 cs = true ∧ AsanPlanCore.kn_vars_lt (nxt cs + NCS + extra) k' = true ∧
    cs' = with_ss cs (mk_ss ret (match rv with
      | some e => sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e
      | none => sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) k' (nxt cs + NCS + extra)) ∧
    (∀ e, rv = some e → AsanPlanCore.expr_vars_lt (nxt cs) e = true) := by
  unfold after_call2 at H
  dsimp only at H
  cases rv with
  | none =>
      simp only [] at H
      split at H
      · rename_i hc
        obtain rfl : cs' = with_ss cs
            (mk_ss ret (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) k'
              (nxt cs + NCS + extra)) := (Option.some.inj H).symm
        refine ⟨?_, ?_, rfl, fun e he => absurd he (by simp)⟩
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.1
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.2
      · rename_i hc
        simp at H
  | some e =>
      simp only [] at H
      split at H
      · rename_i hc
        obtain rfl : cs' = with_ss cs
            (mk_ss ret (sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e) k'
              (nxt cs + NCS + extra)) := (Option.some.inj H).symm
        refine ⟨?_, ?_, rfl, ?_⟩
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.1
        · have h := hc; simp only [Bool.and_eq_true] at h; exact h.1.2
        · intro e' he'
          rw [Option.some.injEq] at he'
          subst he'
          have h := hc; simp only [Bool.and_eq_true] at h
          exact h.2
      · rename_i hc
        simp at H

theorem caller_saved_len : caller_saved.length ≤ NCS := by decide

theorem call_node_sound2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (cs cs' : acs) (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (T : TSet) (ret : Int) (rv : Option expr) (k' : List kentry) (extra : Nat)
    (vals : List word) (regs' : BvMap word) (MR' : word → Option byte)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hac : after_call2 nx0 cs ret rv k' extra = some cs')
    (Hms : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (Mr A argH E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
    (Hkept : kept_ok R regs')
    (Hrv : match rv with
           | some e => getr regs' (Z_to_bv 5 10) = edenot E e
           | none => True)
    (HK' : know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k')
    (Hk : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' → env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') T) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
  have GO : ∀ (sr2 : List expr), cs' = with_ss cs (mk_ss ret sr2 k' (nxt cs + NCS + extra)) →
      fresh_ok nx0 cs = true → AsanPlanCore.kn_vars_lt (nxt cs + NCS + extra) k' = true →
      regs_ok (ext_call2 E (nxt cs) regs' vals) sr2 regs' →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
    intro sr2 hcs' hf hk Hregs
    have Hk' := Hk
    rw [hcs'] at Hk'
    obtain ⟨-, Fkn, -, Fallow, Fbrk, Ffd, Fle⟩ := w_fresh_ok_parts nx0 cs hf
    let E' : env := ext_call2 E (nxt cs) regs' vals
    have HagE : env_agree (nxt cs) E E' := ext_call2_agree E (nxt cs) regs' vals
    refine call_core SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
      argH_agree argH_high SEGS_in_hull cs E E' R FULL model T ret sr2 k'
      (nxt cs + NCS + extra) regs' MR' HC hf HagE Hms Hregs HK' ?_
    intro R' FULL' model' HC' Hfs
    exact Hk' E' R' FULL' model' (w_env_agree_le nx0 (nxt cs) E E' HagE Fle) HagE HC' Hfs
  cases rv with
  | none =>
      obtain ⟨hf, hk, hcs', hev⟩ := after_call2_unpack _ _ _ _ _ _ _ Hac
      obtain ⟨Fsr, -, -, -, -, -, -⟩ := w_fresh_ok_parts nx0 cs hf
      have Hsf : AsanPlanCore.sr_vars_lt (nxt cs + NCS)
          (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) = true :=
        sr_vars_lt_fresh caller_saved cs.a_ss.s_regs (nxt cs) (nxt cs + NCS)
          (sr_vars_lt_mono (nxt cs) (nxt cs + NCS) cs.a_ss.s_regs Fsr (by omega))
          (by have := caller_saved_len; omega)
      have hregs : regs_ok (ext_call E (nxt cs) regs')
          (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) regs' :=
        regs_after_call E _ R regs' (nxt cs) none HC.co_regs Fsr Hkept trivial
      exact GO _ hcs' hf hk (regs_ok_agree' (nxt cs + NCS) _ _ _ regs'
        (ext_call2_agree16 E (nxt cs) regs' vals) Hsf hregs)
  | some e =>
      obtain ⟨hf, hk, hcs', hev⟩ := after_call2_unpack _ _ _ _ _ _ _ Hac
      obtain ⟨Fsr, -, -, -, -, -, -⟩ := w_fresh_ok_parts nx0 cs hf
      have Hsf : AsanPlanCore.sr_vars_lt (nxt cs + NCS)
          (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) = true :=
        sr_vars_lt_fresh caller_saved cs.a_ss.s_regs (nxt cs) (nxt cs + NCS)
          (sr_vars_lt_mono (nxt cs) (nxt cs + NCS) cs.a_ss.s_regs Fsr (by omega))
          (by have := caller_saved_len; omega)
      have Hsf' : AsanPlanCore.sr_vars_lt (nxt cs + NCS)
          (sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e) = true :=
        sr_vars_lt_upd (nxt cs + NCS) (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e Hsf
          (expr_vars_lt_mono (nxt cs) (nxt cs + NCS) e (hev e rfl) (by omega))
      have hregs : regs_ok (ext_call E (nxt cs) regs')
          (sr_upd (sr_fresh cs.a_ss.s_regs caller_saved (nxt cs)) 10 e) regs' :=
        regs_after_call E _ R regs' (nxt cs) (some e) HC.co_regs Fsr Hkept
          ⟨hev e rfl, by rw [Z_to_bv5_ten] at Hrv; exact Hrv⟩
      exact GO _ hcs' hf hk (regs_ok_agree' (nxt cs + NCS) _ _ _ regs'
        (ext_call2_agree16 E (nxt cs) regs' vals) Hsf' hregs)
/-! ## `popfree_facts` is a fact about the freshly filled cell range -/

theorem popfree_facts_sound (SEGS : List Segment) (E : env) (M : word → Option byte)
    (lb : expr) (lk cnt c s : Int) (K : Nat) (base : word)
    (Hbase : bv_unsigned base = estart E (SA lb lk))
    (HK : K ≤ cnt.toNat) (Hcnt : 0 < cnt)
    (Hhi : estart E (SA lb lk) + 4 * cnt ≤ 2 ^ 64) (Hlo : 0 ≤ estart E (SA lb lk)) :
    know_ok SEGS E (wbytes M base (AsanPopFree.pf_bytes c s cnt.toNat))
      (popfree_facts lb lk cnt c s K) := by
  intro Kx Hin
  unfold popfree_facts at Hin
  rw [List.mem_map] at Hin
  obtain ⟨t, ht, rfl⟩ := Hin
  rw [List.mem_range] at ht
  have hcnt : ((cnt.toNat : Nat) : Int) = cnt := Int.toNat_of_nonneg (by omega)
  have htK : (t : Int) < cnt := by
    have h1 : ((t : Int)) < ((cnt.toNat : Nat) : Int) := by omega
    rwa [hcnt] at h1
  have hj0 : 0 ≤ cnt - 1 - (t : Int) := by omega
  have hjc : cnt - 1 - (t : Int) < cnt := by omega
  have hj1 : (cnt - 1 - (t : Int)) + 1 ≤ cnt := by omega
  have HDj : estart E (SA lb (lk + 4 * (cnt - 1 - (t : Int))))
      = estart E (SA lb lk) + 4 * (cnt - 1 - (t : Int)) := by
    simp only [estart, SA]; omega
  have Hlen : (AsanPopFree.pf_bytes c s cnt.toNat).length = 4 * cnt.toNat := AsanPopFree.pf_bytes_length c s cnt.toNat
  have h4j : ((4 * (cnt - 1 - (t : Int))).toNat : Int) = 4 * (cnt - 1 - (t : Int)) :=
    Int.toNat_of_nonneg (by omega)
  have Hu : ((Z_to_bv 64 (estart E (SA lb lk) + 4 * (cnt - 1 - (t : Int)))).toNat : Int)
      = estart E (SA lb lk) + 4 * (cnt - 1 - (t : Int)) :=
    AgentLib.u64_lit _ ⟨by omega, by omega⟩
  have Hbs : ((base.toNat : Int)) = estart E (SA lb lk) := Hbase
  refine ⟨by omega, ?_, ?_⟩
  · refine ⟨?_, ?_, by omega, ?_⟩ <;> rw [HDj] <;> omega
  · rw [adenot_SA, HDj]
    simp only [edenot]
    rw [AsanPopFree.word_to_le_bytes4_Z]
    have hjv : ((cnt.toNat : Int) - 1 - (cnt - 1 - (t : Int))) = (t : Int) := by
      rw [hcnt]; omega
    rw [show (c + (t : Int) * s) / 16
          = (c + ((cnt.toNat : Int) - 1 - (cnt - 1 - (t : Int))) * s) / 16 from by rw [hjv]]
    rw [← AsanPopFree.pf_bytes_cell c s cnt.toNat (cnt - 1 - (t : Int)) hj0 (by rw [hcnt]; exact hjc)]
    have hmk : (4 * (cnt - 1 - (t : Int))).toNat + 4 ≤ (AsanPopFree.pf_bytes c s cnt.toNat).length := by
      rw [Hlen]; omega
    rw [firstn_skipn_map_nth (Z_to_bv 8 0) 4 (AsanPopFree.pf_bytes c s cnt.toNat)
      (4 * (cnt - 1 - (t : Int))).toNat hmk]
    apply rdn_of_nth
    · rw [Hu]
      have htc : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := two64_eq_natCast
      rw [htc] at Hhi
      omega
    · intro q hq
      refine rdn1_overlay SEGS (wbytes M base (AsanPopFree.pf_bytes c s cnt.toNat)) _ _ ?_
      have Haddr : Z_to_bv 64 (((Z_to_bv 64 (estart E (SA lb lk)
            + 4 * (cnt - 1 - (t : Int)))).toNat : Int) + (q : Int))
          = Z_to_bv 64 ((base.toNat : Int) + (((4 * (cnt - 1 - (t : Int))).toNat + q : Nat) : Int)) := by
        rw [Hu, ← Hbs]
        congr 1
        push_cast
        omega
      rw [Haddr]
      exact wbytes_getD (AsanPopFree.pf_bytes c s cnt.toNat) M base
        ((4 * (cnt - 1 - (t : Int))).toNat + q)
        (by
          have htc : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := two64_eq_natCast
          rw [htc] at Hhi
          rw [Hbs, Hlen, Int.natCast_mul, hcnt]
          omega)
        (by rw [Hlen]; omega)

theorem summary_fill_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (entry cmax : Int) (SUM : fill_spec SEGS entry cmax) :
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always
      (fun cs => summary_fill A nx0 cs entry cmax) := by
  intro cs cs' E R FULL model T HC Hpre Hn Hk
  let M : word → Option byte := Mr A argH E cs model FULL
  have HKN : know_ok SEGS E M (kn cs) := HC.co_know
  dsimp only at Hn
  rw [summary_fill_eq A nx0 cs entry cmax] at Hn
  unfold summary_fill_ref at Hn
  dsimp only at Hn
  cases hpc0 : (pc cs == entry) with
  | false =>
    rw [hpc0] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hpc : pc cs = entry := beq_iff_eq.mp hpc0
  rw [hpc0] at Hn
  simp only [Bool.not_true, ite_false] at Hn
  cases hret : ret_lit cs with
  | none =>
    rw [hret] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some ret =>
  cases h11 : reg_lit cs 11 with
  | none =>
    rw [hret, h11] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some c =>
  rw [hret, h11] at Hn
  simp only [] at Hn
  cases hcmd : decide (c < cmax) with
  | false =>
    rw [hcmd] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hcm : c < cmax := of_decide_eq_true hcmd
  rw [hcmd] at Hn
  simp only [Bool.not_true, ite_false] at Hn
  cases hspl : split_lit (AsanPlanCore.reg cs 10) with
  | mk db dk =>
  rw [hspl] at Hn
  simp only [] at Hn
  cases hnlo : xlo (kn cs) (AsanPlanCore.reg cs 12) with
  | none =>
    rw [hnlo] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some nlo =>
  cases hnhi : xhi (kn cs) (AsanPlanCore.reg cs 12) with
  | none =>
    rw [hnlo, hnhi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some nhi =>
  cases hdhi : xhi (kn cs) (AsanPlanCore.reg cs 10) with
  | none =>
    rw [hnlo, hnhi, hdhi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some dhi =>
  rw [hnlo, hnhi, hdhi] at Hn
  simp only [] at Hn
  cases hbnd : (decide (0 ≤ nlo) && decide (nhi ≤ zpow 2 40) && decide (dhi + nhi < two64)) with
  | false =>
    rw [hbnd] at Hn
    simp only [Bool.false_eq_true, ite_false] at Hn
    exact absurd Hn (by simp)
  | true =>
  rw [hbnd] at Hn
  simp only [ite_true] at Hn
  obtain ⟨⟨hb1, hb2⟩, hb3⟩ : (0 ≤ nlo ∧ nhi ≤ zpow 2 40) ∧ dhi + nhi < two64 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hbnd
  have hb3' : dhi + nhi < 2 ^ 64 := hb3
  obtain ⟨R1, Hrok, hret0, hret1⟩ :=
    ret_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ret HC hret
  obtain ⟨R11, hc0, hc1⟩ :=
    w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 c HC (by omega) h11
  have R10 : getr R (Z_to_bv 5 (10 : Int)) = edenot E (AsanPlanCore.reg cs 10) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC (by omega)
  have R12 : getr R (Z_to_bv 5 (12 : Int)) = edenot E (AsanPlanCore.reg cs 12) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 HC (by omega)
  have hnlo' : nlo ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
    xlo_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 12) nlo HKN hnlo
  have hnhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ nhi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 12) nhi HKN hnhi
  have hdhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ≤ dhi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 10) dhi HKN hdhi
  have hsd : edenot E (AsanPlanCore.reg cs 10) = Z_to_bv 64 (estart E (SA db dk)) := by
    rw [w_split_lit_denot E (AsanPlanCore.reg cs 10) db dk hspl, estart_SA]
  have hc8e : Z_to_bv 8 (↑(Z_to_bv 64 c).toNat) = Z_to_bv 8 c := by
    rw [u64_lit c ⟨hc0, hc1⟩]
  have hc1' : c < 2 ^ 64 := hc1
  have htoNat : ((bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat : Int)
      = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
    Int.toNat_of_nonneg (by have h := u64_range (edenot E (AsanPlanCore.reg cs 12)); omega)
  have hbs : (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
      (Z_to_bv 8 c)).length
      = (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat := List.length_replicate
  have hnw2 : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
      + ((List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
          (Z_to_bv 8 c)).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hbs, htoNat]
    show bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
      + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ ((2 ^ 64 : Nat) : Int)
    have htc : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := two64_eq_natCast
    rw [← htc]
    omega
  have hnw3 : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
      + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ ((2 ^ 64 : Nat) : Int) := by
    have h := hnw2
    rw [hbs, htoNat] at h
    exact h
  have FIN : ∀ (k' : List kentry),
      store_ok SEGS M (edenot E (AsanPlanCore.reg cs 10))
        (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = true →
      know_ok SEGS E (wbytes M (edenot E (AsanPlanCore.reg cs 10))
        (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
          (Z_to_bv 8 c))) k' →
      after_call nx0 cs ret (some (AsanPlanCore.reg cs 10)) k' = some cs' →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
    intro k' hst hk' hac
    obtain ⟨regs', hms, hkept, ha0⟩ :=
      SUM M (edenot E (AsanPlanCore.reg cs 10)) (Z_to_bv 64 c)
        (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))) R (Z_to_bv 64 ret)
        (by have h := u64_range (edenot E (AsanPlanCore.reg cs 12)); exact h.1)
        (by have h3 := hdhi'; have h2 := hnhi'; have h4 := hnlo'
            show bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
              + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64
            omega)
        hst
        (by rw [u64_lit c ⟨hc0, hc1'⟩]; exact hcm)
        Hrok
        (by rw [Z_to_bv5_one] at R1; exact R1)
        R10
        R11
        (by rw [Z_to_bv64_bv_unsigned]; exact R12)
    have hms' : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
        (mkst regs' (Z_to_bv 64 ret) (wbytes M (edenot E (AsanPlanCore.reg cs 10))
          (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
            (Z_to_bv 8 c))) (seg_rom SEGS)) := by
      have hms1 := hms
      rw [hc8e] at hms1
      rw [hpc]
      exact hms1
    refine call_node_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
      argH_agree argH_high SEGS_in_hull cs cs' E R FULL model T ret
      (some (AsanPlanCore.reg cs 10)) k' regs' _ HC hac hms' hkept ?_ hk' ?_
    · show getr regs' (Z_to_bv 5 10) = edenot E (AsanPlanCore.reg cs 10)
      rw [Z_to_bv5_ten]
      exact ha0
    · intro E' R' FULL' model' h1 h2 hc hfs
      exact Hk E' R' FULL' model' ⟨h1, h2⟩ hc hfs
  cases hnz : (nhi == 0) with
  | true =>
    rw [hnz] at Hn
    simp only [ite_true] at Hn
    have hnhi0 : nhi = 0 := by simpa using hnz
    have hzn : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = 0 := by omega
    refine FIN (kn cs) ?_ ?_ Hn
    · rw [show (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = 0 from by rw [hzn]; rfl]
      rfl
    · rw [show (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = 0 from by
          rw [hzn]; rfl]
      exact HKN
  | false =>
  rw [hnz] at Hn
  simp only [Bool.false_eq_true, ite_false] at Hn
  cases hzb : (c % 256 == 0 && kzero_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) &&
      kwritable_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12)) with
  | true =>
    rw [hzb] at Hn
    simp only [ite_true] at Hn
    by_cases hnz0 : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = 0
    · refine FIN (kn cs) ?_ ?_ Hn
      · rw [show (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = 0 from by
            rw [hnz0]; rfl]
        rfl
      · rw [show (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = 0 from by
            rw [hnz0]; rfl]
        exact HKN
    · have hnpos : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by omega
      obtain ⟨⟨hc80, hkz⟩, hwr⟩ : ((c % 256 == 0) = true ∧
          kzero_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) = true) ∧
          kwritable_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) = true := by
        simpa only [Bool.and_eq_true] using hzb
      obtain ⟨Wst, Wlo, Whi⟩ :=
        kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) HKN HKN hwr
      obtain ⟨Zb, -, -⟩ :=
        kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) HKN HKN hkz
      have hlen : elenZ E (AsanPlanCore.reg cs 12)
          = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := rfl
      have Whi' : estart E (SA db dk) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
          ≤ 2 ^ 64 := by
        have h := Whi; rwa [hlen] at h
      have Hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) = estart E (SA db dk) := by
        rw [hsd]
        exact u64_lit _ ⟨Wlo, by omega⟩
      have hc80' : c % 256 = 0 := beq_iff_eq.mp hc80
      have hzero : Z_to_bv 8 c = Z_to_bv 8 0 := by rw [← Z_to_bv8_mod c, hc80']
      refine FIN (kn cs) ?_ ?_ Hn
      · have h := Wst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat (by
          rw [hlen]; omega)
        rw [← hsd] at h
        exact h
      · rw [show wbytes M (edenot E (AsanPlanCore.reg cs 10))
            (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
              (Z_to_bv 8 c)) = M from ?_]
        exact HKN
        apply wbytes_same
        · exact hnw2
        · intro j hj
          rw [List.length_replicate] at hj
          rw [nth_repeat_lt (Z_to_bv 8 c) (Z_to_bv 8 0) _ j hj]
          have hj' : (j : Int) < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by omega
          have h := Zb (j : Int) (by omega) (by rw [hlen]; exact hj')
          have haddr : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) + (j : Int)
              = estart E (SA db dk) + (j : Int) :=
            congrArg (fun z => z + (j : Int)) Hus
          rw [haddr, h, hzero]
  | false =>
    rw [hzb] at Hn
    simp only [Bool.false_eq_true, ite_false] at Hn
    split at Hn
    · exact absurd Hn (by simp)
    · rename_i k0 hofk0
      cases hwr : kwritable_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) with
      | false =>
        rw [hwr] at Hn
        simp only [Bool.false_eq_true, ite_false] at Hn
        exact absurd Hn (by simp)
      | true =>
        rw [hwr] at Hn
        simp only [ite_true] at Hn
        have HK0 : know_ok SEGS E M k0 :=
          k0_sound SEGS A E M (kn cs) db dk (AsanPlanCore.reg cs 12) (AsanPlanCore.reg cs 10)
            k0 HKN hofk0
        obtain ⟨Wst, Wlo, Whi⟩ :=
          kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) HKN HKN hwr
        have hlen : elenZ E (AsanPlanCore.reg cs 12)
            = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := rfl
        have Whi' : estart E (SA db dk) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
            ≤ 2 ^ 64 := by
          have h := Whi; rwa [hlen] at h
        have HusOf : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) →
            bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) = estart E (SA db dk) := by
          intro hp
          rw [hsd]
          exact u64_lit _ ⟨Wlo, by omega⟩
        have HAV : know_ok SEGS E (wbytes M (edenot E (AsanPlanCore.reg cs 10))
            (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
              (Z_to_bv 8 c)))
            (kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) := by
          refine w_know_ok_havoc SEGS E M _ k0 db (AsanPlanCore.reg cs 12) dk HK0 ?_
            (wbytes_grows _ M _)
          intro x hx
          by_cases hx0 : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = 0
          · rw [show List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (Z_to_bv 8 c) = [] from by rw [hx0]; rfl]
            rfl
          · have hp : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by omega
            have hD := HusOf hp
            rcases hx with hx | hx
            · rw [← hD] at hx
              exact wbytes_out _ M _ x hnw2 (Or.inl (by omega))
            · rw [hlen, ← hD] at hx
              exact wbytes_out _ M _ x hnw2 (Or.inr (by rw [hbs, htoNat]; omega))
        by_cases hpos : 0 < nlo
        · rw [ite_eq_left hpos] at Hn
          have hnpos' : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by omega
          have Hus := HusOf hnpos'
          cases hc8 : (c % 256 == 0) with
          | true =>
            rw [hc8] at Hn
            simp only [ite_true] at Hn
            have hc80' : c % 256 = 0 := beq_iff_eq.mp hc8
            have hzero : Z_to_bv 8 c = Z_to_bv 8 0 := by rw [← Z_to_bv8_mod c, hc80']
            refine FIN (kentry.KZero (SA db dk) (AsanPlanCore.reg cs 12)
              :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) ?_ ?_ Hn
            · have hw := Wst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (by rw [hlen, htoNat]; omega)
              rw [← hsd] at hw
              exact hw
            · intro K hK
              rw [List.mem_cons] at hK
              rcases hK with rfl | hK
              · refine ⟨?_, ?_⟩
                · show 0 ≤ estart E (SA db dk) ∧ estart E (SA db dk) < 2 ^ 64
                    ∧ 0 ≤ elenZ E (AsanPlanCore.reg cs 12)
                    ∧ estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                  rw [hlen]
                  exact ⟨Wlo, by omega, by omega, Whi'⟩
                · intro i hi1 hi2
                  rw [hlen] at hi2
                  show wbytes M (edenot E (AsanPlanCore.reg cs 10))
                    (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                      (Z_to_bv 8 c))
                    (Z_to_bv 64 (estart E (SA db dk) + i)) = some (Z_to_bv 8 0)
                  rw [← Hus]
                  rw [wbytes_fill_at M _ (Z_to_bv 8 c) _ i hnw3 ⟨hi1, hi2⟩, hzero]
              · exact HAV K hK
          | false =>
            rw [hc8] at Hn
            simp only [Bool.false_eq_true, ite_false] at Hn
            refine FIN (kentry.KFill (SA db dk) (AsanPlanCore.reg cs 12) (c % 256)
              :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) ?_ ?_ Hn
            · have hw := Wst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (by rw [hlen, htoNat]; omega)
              rw [← hsd] at hw
              exact hw
            · intro K hK
              rw [List.mem_cons] at hK
              rcases hK with rfl | hK
              · refine ⟨?_, ?_⟩
                · show 0 ≤ estart E (SA db dk) ∧ estart E (SA db dk) < 2 ^ 64
                    ∧ 0 ≤ elenZ E (AsanPlanCore.reg cs 12)
                    ∧ estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                  rw [hlen]
                  exact ⟨Wlo, by omega, by omega, Whi'⟩
                · intro i hi1 hi2
                  rw [hlen] at hi2
                  show wbytes M (edenot E (AsanPlanCore.reg cs 10))
                    (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                      (Z_to_bv 8 c))
                    (Z_to_bv 64 (estart E (SA db dk) + i)) = some (Z_to_bv 8 (c % 256))
                  rw [← Hus]
                  rw [wbytes_fill_at M _ (Z_to_bv 8 c) _ i hnw3 ⟨hi1, hi2⟩, Z_to_bv8_mod]
              · exact HAV K hK
        · rw [ite_eq_right hpos] at Hn
          refine FIN (kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) ?_ HAV Hn
          have hw := Wst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
            (by rw [hlen, htoNat]; omega)
          rw [← hsd] at hw
          exact hw


/-! ## 6a. The `fill_spec` interface theorems (`check_sound`'s `node_x_sound`) -/

/-- `check_sound`'s `node_x_sound` at `XIMemset`: one `intro args` away from
    `summary_fill_sound` . -/
theorem node_x_sound_XIMemset (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : fill_spec SEGS A.x_imemset 256) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XIMemset := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XIMemset args
      = fun cs => summary_fill A nx0 cs A.x_imemset 256 :=
    funext (fun cs => node_x_imemset SEGS A nx0 args cs)
  rw [hx]
  exact summary_fill_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull A.x_imemset 256 SUM

/-- `check_sound`'s `node_x_sound` at `XMemset` (musl `memset`: `cmax = 2^64`). -/
theorem node_x_sound_XMemset (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : fill_spec SEGS A.x_memset two64) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XMemset := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XMemset args
      = fun cs => summary_fill A nx0 cs A.x_memset two64 :=
    funext (fun cs => rfl)
  rw [hx]
  exact summary_fill_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull A.x_memset two64 SUM

/-! ## 5b. `summary_miz_sound` (`XMemIsZero`) -/

/-- `:1148` (`bzero`/`internal_memzero`): no store at all when `N = 0`,
    a `KZero` overlay when the target is already zero, otherwise havoc + a
    precise re-description.  The stack slot at `sp - 16` is live (`kwritable`)
    so the callee may use it, and the range is `sp`-apart from it. -/
theorem summary_miz_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : miz_spec SEGS (A.x_memiszero)) :
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always
      (fun cs => summary_miz A nx0 cs) := by
  intro cs cs' E R FULL model T HC Hpre Hn Hk
  let M : word → Option byte := Mr A argH E cs model FULL
  have HKN : know_ok SEGS E M (kn cs) := HC.co_know
  dsimp only at Hn
  rw [summary_miz_eq A nx0 cs] at Hn
  unfold summary_miz_ref at Hn
  dsimp only at Hn
  cases hpc0 : (pc cs == A.x_memiszero) with
  | false =>
    rw [hpc0] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hpc : pc cs = A.x_memiszero := beq_iff_eq.mp hpc0
  rw [hpc0] at Hn
  simp only [Bool.not_true, ite_false] at Hn
  cases hret : ret_lit cs with
  | none =>
    rw [hret] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some ret =>
  rw [hret] at Hn
  simp only [] at Hn
  cases hb : split_lit (AsanPlanCore.reg cs 10) with
  | mk bb bk =>
  rw [hb] at Hn
  simp only [] at Hn
  cases hq : split_lit (eaddz (AsanPlanCore.reg cs 2) (-16)) with
  | mk qb qk =>
  rw [hq] at Hn
  simp only [] at Hn
  cases hnlo : xlo (kn cs) (AsanPlanCore.reg cs 11) with
  | none =>
    rw [hnlo] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some nlo =>
  cases hnhi : xhi (kn cs) (AsanPlanCore.reg cs 11) with
  | none =>
    rw [hnlo, hnhi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some nhi =>
  cases hbhi : xhi (kn cs) (AsanPlanCore.reg cs 10) with
  | none =>
    rw [hnlo, hnhi, hbhi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some bhi =>
  cases hsplo : xlo (kn cs) (AsanPlanCore.reg cs 2) with
  | none =>
    rw [hnlo, hnhi, hbhi, hsplo] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some splo =>
  cases hsphi : xhi (kn cs) (AsanPlanCore.reg cs 2) with
  | none =>
    rw [hnlo, hnhi, hbhi, hsplo, hsphi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some sphi =>
  rw [hnlo, hnhi, hbhi, hsplo, hsphi] at Hn
  simp only [] at Hn
  cases hcond : (decide (0 ≤ nlo) && decide (nhi ≤ zpow 2 40) &&
      decide (bhi + nhi + 8 ≤ two64) && decide (16 ≤ splo) && decide (sphi < two64) &&
      kwritable (kn cs) (kn cs) qb qk 16 &&
      ranges_apart_x (kn cs) qb qk (.ELit 16) bb bk (AsanPlanCore.reg cs 11) &&
      kzero_x (kn cs) (kn cs) bb bk (AsanPlanCore.reg cs 11)) with
  | false =>
    rw [hcond] at Hn
    simp only [Bool.false_eq_true, ite_false] at Hn
    exact absurd Hn (by simp)
  | true =>
  rw [hcond] at Hn
  simp only [ite_true] at Hn
  have hcd := hcond
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcd
  obtain ⟨⟨⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hwr⟩, hap⟩, hkz⟩ := hcd
  have hb3' : bhi + nhi + 8 ≤ 2 ^ 64 := hb3
  have hb5' : sphi < 2 ^ 64 := hb5
  -- registers
  obtain ⟨R1, Hrok, hret0, hret1⟩ :=
    ret_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ret HC hret
  have R2 : getr R (Z_to_bv 5 (2 : Int)) = edenot E (AsanPlanCore.reg cs 2) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 2 HC (by omega)
  have R10 : getr R (Z_to_bv 5 (10 : Int)) = edenot E (AsanPlanCore.reg cs 10) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC (by omega)
  have R11 : getr R (Z_to_bv 5 (11 : Int)) = edenot E (AsanPlanCore.reg cs 11) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 HC (by omega)
  have hnlo' : nlo ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) :=
    xlo_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 11) nlo HKN hnlo
  have hnhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) ≤ nhi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 11) nhi HKN hnhi
  have hbhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ≤ bhi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 10) bhi HKN hbhi
  have hsplo' : splo ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) :=
    xlo_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 2) splo HKN hsplo
  have hsphi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) ≤ sphi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 2) sphi HKN hsphi
  -- the two spec bounds, materialised
  have hn0 : 0 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) :=
    (u64_range (edenot E (AsanPlanCore.reg cs 11))).1
  have hnw : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) < 2 ^ 64 :=
    (u64_range (edenot E (AsanPlanCore.reg cs 11))).2
  have hs0 : 0 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) :=
    (u64_range (edenot E (AsanPlanCore.reg cs 2))).1
  -- kwritable / kzero / ranges_apart
  obtain ⟨Qst, Qlo, Qhi⟩ :=
    kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN hwr (by decide)
  obtain ⟨Zb, Blo, Bhi⟩ :=
    kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (AsanPlanCore.reg cs 11) HKN HKN hkz
  have hapv :=
    ranges_apart_x_sound SEGS E M (kn cs) qb qk (.ELit 16) bb bk
      (AsanPlanCore.reg cs 11) HKN hap
  have hlen : elenZ E (AsanPlanCore.reg cs 11)
      = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) := rfl
  have hl16 : elenZ E (.ELit 16) = 16 := AsanPlanSound.elenZ_lit E 16 ⟨by decide, by decide⟩
  have hQhi' : estart E (SA qb qk) < 2 ^ 64 := by omega
  -- `bv_unsigned` of the frame-slot address
  have hQe : bv_unsigned (edenot E (eaddz (AsanPlanCore.reg cs 2) (-16)))
      = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 16 := by
    show bv_unsigned (edenot E (mkAlu .ADD (AsanPlanCore.reg cs 2) (.ELit (-16)))) = _
    rw [mkAlu_denot]
    show bv_unsigned (edenot E (AsanPlanCore.reg cs 2) + Z_to_bv 64 (-16)) = _
    rw [u_add64, u_lit64]
    simp only [two64]
    have hneg : (-16 : Int) % 2 ^ 64 = 2 ^ 64 - 16 := by decide
    rw [Int.add_comm, emod_add_mod]
    rw [show (-16 : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 2))
        = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 16 from by omega]
    have e1 : 0 ≤ (-16 : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) := by
      have h1 : (16 : Int) ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) :=
        Int.le_trans hb4 hsplo'
      omega
    have e2 : (-16 : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 2))
        < ((2 ^ 64 : Nat) : Int) := by
      have h8 : bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) < ((2 ^ 64 : Nat) : Int) :=
        (u64_range (edenot E (AsanPlanCore.reg cs 2))).2
      have h9 : (-16 : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 2))
          ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) := by omega
      exact Int.lt_of_le_of_lt h9 h8
    exact Int.emod_eq_of_lt e1 e2
  have hQsp : bv_unsigned (edenot E (eaddz (AsanPlanCore.reg cs 2) (-16)))
      = estart E (SA qb qk) :=
    u_of_split E (eaddz (AsanPlanCore.reg cs 2) (-16)) qb qk hq ⟨Qlo, hQhi'⟩
  have hQ : estart E (SA qb qk) = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 16 := by
    rw [← hQsp]
    exact hQe
  -- the source range address
  -- `beg` versus the start `B` of the zero range.  The only corner is
  -- `B = 2 ^ 64` (i.e. `N = 0`), which `Z_to_bv` wraps to `0`; this tree carries
  -- it as a disjunction (`HuB`) and so does this proof.
  have HBden : edenot E (AsanPlanCore.reg cs 10) = Z_to_bv 64 (estart E (SA bb bk)) :=
    w_split_lit_denot E (AsanPlanCore.reg cs 10) bb bk hb
  have HuB : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) = estart E (SA bb bk)
      ∨ (estart E (SA bb bk) = 2 ^ 64 ∧ bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) = 0) := by
    by_cases hB : estart E (SA bb bk) = 2 ^ 64
    · right
      refine ⟨hB, ?_⟩
      rw [HBden, hB, u_lit64]
      show (2 : Int) ^ 64 % two64 = 0
      simp only [two64]
      exact Int.emod_self
    · left
      rw [HBden, u_lit64]
      exact u_small_id _ ⟨Blo, by omega⟩
  -- in that corner `N` is forced to `0`
  have hN0c : estart E (SA bb bk) = 2 ^ 64 →
      bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) = 0 := by
    intro hB
    rw [← hlen]
    omega
  -- the frame slot is a store of its own
  have hQhiNat : estart E (SA qb qk) + 16 ≤ ((2 ^ 64 : Nat) : Int) := by
    have htc : (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) := two64_eq_natCast
    rw [← htc]
    exact Qhi
  have hspwlt : bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) < 2 ^ 64 :=
    (u64_range (edenot E (AsanPlanCore.reg cs 2))).2
  have hstk : store_ok SEGS M
      (Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8))) 8 = true := by
    have hQval : ((Z_to_bv 64 (estart E (SA qb qk))).toNat : Int) = estart E (SA qb qk) :=
      u64_lit _ ⟨Qlo, hQhi'⟩
    have hbval : ((Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8))).toNat : Int)
        = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8 :=
      u64_lit _ ⟨by omega, by omega⟩
    have hQ16 : estart E (SA qb qk) + 16 = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) := by
      omega
    refine store_ok_sub SEGS M (Z_to_bv 64 (estart E (SA qb qk))) 16
      (Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8))) 8 ?_ Qst ?_ ?_
    · omega
    · rw [hbval, hQval]; omega
    · rw [hbval, hQval]; omega
  -- the zero-byte range
  have hz : ∀ a : word, (bv_unsigned (edenot E (AsanPlanCore.reg cs 10))) ≤ (a.toNat : Int) →
      (a.toNat : Int) < bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
        + bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) →
      rdn SEGS M a 1 = some [Z_to_bv 8 0] := by
    intro a h1 h2
    apply rdn1_overlay
    rcases HuB with h | ⟨hB, h0⟩
    · have h1' : estart E (SA bb bk) ≤ (a.toNat : Int) := by rw [← h]; exact h1
      have h2' : (a.toNat : Int) < estart E (SA bb bk)
          + bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) := by rw [← h]; exact h2
      have hstep : Z_to_bv 64 (estart E (SA bb bk)
          + ((a.toNat : Int) - estart E (SA bb bk))) = a := by
        rw [show estart E (SA bb bk) + ((a.toNat : Int) - estart E (SA bb bk)) = (a.toNat : Int)
          from by omega]
        exact Z_to_bv_unsigned a
      rw [← hstep]
      apply Zb
      · omega
      · rw [hlen]; omega
    · have hN0 := hN0c hB
      omega
  -- the read/write disjointness
  have hdisj : (bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
        + bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
          ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8 ∨
      bv_unsigned (edenot E (AsanPlanCore.reg cs 2))
        ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 10))) := by
    have h := hapv
    rw [hl16] at h
    rcases HuB with hb' | ⟨hB, h0⟩
    · rcases h with h | h
      · right; omega
      · left; rw [hlen] at h; omega
    · have hN0 := hN0c hB
      left
      rw [h0, hN0]
      omega
  -- the routine run
  obtain ⟨regs', hms, hkept, ha0⟩ :=
    SUM M (edenot E (AsanPlanCore.reg cs 10)) (edenot E (AsanPlanCore.reg cs 2))
      (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) R (Z_to_bv 64 ret)
      (by have h := u64_range (edenot E (AsanPlanCore.reg cs 11)); exact h.1)
      (by have h2 := hnhi'; have h2' : nhi ≤ 2 ^ 40 := hb2; omega)
      (by show bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
            + bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) + 8 ≤ 2 ^ 64
          have h3 := hbhi'; have h2 := hnhi'; omega)
      (by show 16 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 2))
          have h4 := hsplo'; omega)
      hstk
      hdisj
      hz
      Hrok
      (by rw [Z_to_bv5_one] at R1; exact R1)
      R2
      R10
      (by rw [← Z_to_bv5_eleven, Z_to_bv64_bv_unsigned]; exact R11)
  have HK' : know_ok SEGS E
      (wbytes M (Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8)))
        (word_to_le_bytes 8 (Z_to_bv 64 ret)))
      (kn_havoc (kn cs) qb qk (.ELit 16)) := by
    refine w_know_ok_havoc SEGS E M _ (kn cs) qb (.ELit 16) qk HKN ?_
      (wbytes_grows _ M _)
    intro x hx
    rw [hl16] at hx
    rw [show estart E (SA qb qk) = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 16
        from hQ] at hx
    have hub2 : ((Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8))).toNat : Int)
        = bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8 :=
      u64_lit _ ⟨by omega, by omega⟩
    have hlen2 : (word_to_le_bytes 8 (Z_to_bv 64 ret)).length = 8 :=
      CatExec.length_N_to_le_bytes 8 _
    refine wbytes_out _ M _ x ?_ ?_
    · show ((Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8))).toNat : Int)
          + ((word_to_le_bytes 8 (Z_to_bv 64 ret)).length : Int) ≤ ((2 ^ 64 : Nat) : Int)
      rw [hlen2, hub2, two64_eq_natCast.symm]
      omega
    · rw [hub2, hlen2]
      rcases hx with hx | hx
      · left
        show bv_unsigned x < bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8
        omega
      · right
        show bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8 + 8 ≤ bv_unsigned x
        omega
  have hms' : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
      (mkst regs' (Z_to_bv 64 ret)
        (wbytes M (Z_to_bv 64 ((bv_unsigned (edenot E (AsanPlanCore.reg cs 2)) - 8)))
          (word_to_le_bytes 8 (Z_to_bv 64 ret))) (seg_rom SEGS)) := by
    rw [hpc]
    exact hms
  refine call_node_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
    argH_agree argH_high SEGS_in_hull cs cs' E R FULL model T ret
    (some (.ELit 1)) (kn_havoc (kn cs) qb qk (.ELit 16)) regs' _ HC Hn hms' hkept ?_ HK' ?_
  · show getr regs' (Z_to_bv 5 10) = edenot E (.ELit 1)
    rw [Z_to_bv5_ten]
    show getr regs' 10 = Z_to_bv 64 1
    exact ha0
  · intro E' R' FULL' model' h1 h2 hc hfs
    exact Hk E' R' FULL' model' ⟨h1, h2⟩ hc hfs

/-- `check_sound`'s `node_x_sound` at `XMemIsZero`: one `intro args` away from
    `summary_miz_sound`. -/
theorem node_x_sound_XMemIsZero (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : miz_spec SEGS A.x_memiszero) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XMemIsZero := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XMemIsZero args
      = fun cs => summary_miz A nx0 cs := funext (fun cs => rfl)
  rw [hx]
  exact summary_miz_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull SUM

/-! ## 5c. `summary_istrncpy_sound` (`XIStrncpy`) -/

/-- `:1504` (`strncpy(dst, "<sealed>", 4095)`): the destination gets a
    `KWord dst 8 "<sealed>"` head, a 4087-byte `KZero` tail (the NUL padding)
    and the frame havoc'd; the source range is covered by an image fact so the
    copy reads the pristine image bytes. -/
theorem summary_istrncpy_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : istrncpy_spec SEGS A.x_istrncpy A.x_sealed) :
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always
      (fun cs => summary_istrncpy A nx0 cs) := by
  intro cs cs' E R FULL model T HC Hpre Hn Hk
  let M : word → Option byte := Mr A argH E cs model FULL
  have HKN : know_ok SEGS E M (kn cs) := HC.co_know
  dsimp only at Hn
  rw [summary_istrncpy_eq A nx0 cs] at Hn
  unfold summary_istrncpy_ref at Hn
  dsimp only at Hn
  cases hpc0 : (pc cs == A.x_istrncpy) with
  | false =>
    rw [hpc0] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hpc : pc cs = A.x_istrncpy := beq_iff_eq.mp hpc0
  rw [hpc0] at Hn
  simp only [Bool.not_true, ite_false] at Hn
  cases hret : ret_lit cs with
  | none =>
    rw [hret] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some ret =>
  cases h11 : reg_lit cs 11 with
  | none =>
    rw [hret, h11] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some src =>
  cases h12 : reg_lit cs 12 with
  | none =>
    rw [hret, h11, h12] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some nn =>
  rw [hret, h11, h12] at Hn
  simp only [] at Hn
  cases hsn : (src == A.x_sealed && nn == 4095) with
  | false =>
    rw [hsn] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  rw [hsn] at Hn
  simp only [Bool.not_true, ite_false] at Hn
  have hsn' := hsn
  simp only [Bool.and_eq_true] at hsn'
  obtain ⟨hse, h4⟩ := hsn'
  have hsrc : src = A.x_sealed := beq_iff_eq.mp hse
  have hn4095 : nn = 4095 := beq_iff_eq.mp h4
  subst hsrc
  subst hn4095
  cases hspl : split_lit (AsanPlanCore.reg cs 10) with
  | mk db dk =>
  rw [hspl] at Hn
  simp only [] at Hn
  cases hdhi : xhi (kn cs) (AsanPlanCore.reg cs 10) with
  | none =>
    rw [hdhi] at Hn
    simp only [] at Hn
    exact absurd Hn (by simp)
  | some dhi =>
  rw [hdhi] at Hn
  simp only [] at Hn
  have h4095 : elenZ E (.ELit 4095) = 4095 := AsanPlanSound.elenZ_lit E 4095 ⟨by decide, by decide⟩
  have h4087 : elenZ E (.ELit 4087) = 4087 := AsanPlanSound.elenZ_lit E 4087 ⟨by decide, by decide⟩
  have h9 : elenZ E (.ELit 9) = 9 := AsanPlanSound.elenZ_lit E 9 ⟨by decide, by decide⟩
  obtain ⟨R1, Hrok, hret0, hret1⟩ :=
    ret_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ret HC hret
  obtain ⟨R11, -, -⟩ :=
    w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 A.x_sealed HC (by omega) h11
  obtain ⟨R12, -, -⟩ :=
    w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 4095 HC (by omega) h12
  have R10 : getr R (Z_to_bv 5 (10 : Int)) = edenot E (AsanPlanCore.reg cs 10) :=
    w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC (by omega)
  have hdhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ≤ dhi :=
    xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 10) dhi HKN hdhi
  have hse : Z_to_bv 64 (estart E (SA db dk)) = edenot E (AsanPlanCore.reg cs 10) :=
    (w_split_lit_denot E (AsanPlanCore.reg cs 10) db dk hspl).symm
  have hx0 : estart E (SA (.ELit 0) A.x_sealed) = A.x_sealed := by
    show bv_unsigned (edenot E (.ELit 0)) + A.x_sealed = A.x_sealed
    rw [edenot_lit, u_lit0]
    omega
  -- how every branch ends: the guard, with `k0` still a parameter
  have FIN : ∀ (k0 : List kentry), know_ok SEGS E M k0 →
      (if (dhi + 4095 < two64 && 0 ≤ A.x_sealed && A.x_sealed + 9 < two64
           && kwritable_x (kn cs) (kn cs) db dk (.ELit 4095)
           && img_cov k0 A.x_sealed (A.x_sealed + 9)
           && ranges_apart_x (kn cs) db dk (.ELit 4095) (.ELit 0) A.x_sealed (.ELit 9))
        then after_call nx0 cs ret (some (AsanPlanCore.reg cs 10))
          (.KWord (SA db dk) 8 (.ELit SEALED_W) :: .KZero (SA db (dk + 8)) (.ELit 4087)
            :: kn_havoc k0 db dk (.ELit 4095)) else none) = some cs' →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
    intro k0 HK0 Hn
    cases hcond : (dhi + 4095 < two64 && 0 ≤ A.x_sealed && A.x_sealed + 9 < two64
        && kwritable_x (kn cs) (kn cs) db dk (.ELit 4095)
        && img_cov k0 A.x_sealed (A.x_sealed + 9)
        && ranges_apart_x (kn cs) db dk (.ELit 4095) (.ELit 0) A.x_sealed (.ELit 9)) with
    | false =>
      rw [hcond] at Hn
      simp only [Bool.false_eq_true, ite_false] at Hn
      exact absurd Hn (by simp)
    | true =>
    rw [hcond] at Hn
    simp only [ite_true] at Hn
    have hcd := hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcd
    obtain ⟨⟨⟨⟨⟨hb, hs0'⟩, hs9⟩, hwr⟩, hcov⟩, hap⟩ := hcd
    have hb' : dhi + 4095 < (2 : Int) ^ 64 := hb
    have hs9' : A.x_sealed + 9 < (2 : Int) ^ 64 := hs9
    have hlen4095 : (SEALED_BYTES.length : Int) = 4095 := by rw [SEALED_BYTES_length]; rfl
    have hbw : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + 4095 < (2 : Int) ^ 64 := by
      omega
    have hB : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (SEALED_BYTES.length : Int)
        ≤ ((2 ^ 64 : Nat) : Int) := by
      rw [hlen4095, ← two64_eq_natCast, two64_eq]
      omega
    obtain ⟨Wst, Wlo, Whi⟩ :=
      kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (.ELit 4095) HKN HKN hwr
    have hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) = estart E (SA db dk) := by
      rw [← hse]
      exact u64_lit _ ⟨Wlo, by omega⟩
    have hapart :=
      ranges_apart_x_sound SEGS E M (kn cs) db dk (.ELit 4095) (.ELit 0) A.x_sealed (.ELit 9)
        HKN hap
    have hnone := img_cov_sound SEGS E M k0 A.x_sealed (A.x_sealed + 9) HK0 hcov
    obtain ⟨regs', hms, hkept, ha0⟩ :=
      SUM M (edenot E (AsanPlanCore.reg cs 10)) R (Z_to_bv 64 ret)
        hnone
        (by rw [← hse]; exact Wst 4095 (by rw [h4095]; omega))
        (by have hdt : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                = bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) := rfl
            rw [hdt]; omega)
        (by have hdt : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                = bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) := rfl
            rw [hdt]
            have h := hapart
            rw [h4095, h9, hx0] at h
            rw [← hus] at h
            exact h)
        Hrok
        (by rw [← Z_to_bv5_one]; exact R1)
        (by rw [← Z_to_bv5_ten]; exact R10)
        (by rw [← Z_to_bv5_eleven]; exact R11)
        (by rw [← Z_to_bv5_twelve]; exact R12)
    have hms' : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
        (mkst regs' (Z_to_bv 64 ret)
          (wbytes M (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES) (seg_rom SEGS)) := by
      rw [hpc]
      exact hms
    have hus' : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) = estart E (SA db dk) := hus
    have hBY : ∀ j : Nat, j < 4095 →
        wbytes M (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES
          (Z_to_bv 64 (estart E (SA db dk) + (j : Int)))
          = some (SEALED_BYTES.getD j (Z_to_bv 8 0)) := by
      intro j hj
      have h := wbytes_nth SEALED_BYTES M (edenot E (AsanPlanCore.reg cs 10)) j hB
        (by rw [SEALED_BYTES_length]; exact hj)
      rw [← hus]
      exact h
    have hD8 : estart E (SA db (dk + 8)) = estart E (SA db dk) + 8 := by
      show bv_unsigned (edenot E db) + (dk + 8) = bv_unsigned (edenot E db) + dk + 8
      omega
    refine call_node_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
      argH_agree argH_high SEGS_in_hull cs cs' E R FULL model T ret
      (some (AsanPlanCore.reg cs 10))
      (.KWord (SA db dk) 8 (.ELit SEALED_W) :: .KZero (SA db (dk + 8)) (.ELit 4087)
        :: kn_havoc k0 db dk (.ELit 4095)) regs' _ HC Hn hms' hkept ?_ ?_ ?_
    · show getr regs' (Z_to_bv 5 10) = edenot E (AsanPlanCore.reg cs 10)
      rw [Z_to_bv5_ten]
      show getr regs' 10 = edenot E (AsanPlanCore.reg cs 10)
      exact ha0
    · intro K hK
      rw [List.mem_cons] at hK
      rcases hK with rfl | hK
      · refine ⟨?_, ?_, ?_⟩
        · show (8 : Nat) ≤ 8
          omega
        · show 0 ≤ estart E (SA db dk) ∧ estart E (SA db dk) < 2 ^ 64 ∧ 0 ≤ (8 : Int)
            ∧ estart E (SA db dk) + 8 ≤ 2 ^ 64
          omega
        · show rdn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES)
              (adenot E (SA db dk)) 8
            = some (word_to_le_bytes 8 (edenot E (.ELit SEALED_W)))
          rw [adenot_SA, hse, edenot_lit, SEALED_W_bytes]
          show rdn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES)
              (edenot E (AsanPlanCore.reg cs 10)) 8 = some (SEALED_BYTES.take 8)
          have hhit := rdn_wbytes_hit SEGS SEALED_BYTES M
            (edenot E (AsanPlanCore.reg cs 10)) hB
          exact rdn_firstn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES)
            SEALED_BYTES.length (edenot E (AsanPlanCore.reg cs 10)) SEALED_BYTES 8 hhit
            (by rw [SEALED_BYTES_length]; omega)
      · rw [List.mem_cons] at hK
        rcases hK with rfl | hK
        · refine ⟨?_, ?_⟩
          · show 0 ≤ estart E (SA db (dk + 8)) ∧ estart E (SA db (dk + 8)) < 2 ^ 64
              ∧ 0 ≤ elenZ E (.ELit 4087)
              ∧ estart E (SA db (dk + 8)) + elenZ E (.ELit 4087) ≤ 2 ^ 64
            rw [h4087, hD8]
            omega
          · intro i hi1 hi2
            rw [h4087] at hi2
            have h8i : (((8 + i).toNat : Nat) : Int) = 8 + i :=
              Int.toNat_of_nonneg (by omega)
            rw [hD8]
            have hstep : estart E (SA db dk) + 8 + i
                = estart E (SA db dk) + (((8 + i).toNat : Nat) : Int) := by omega
            rw [hstep, hBY (8 + i).toNat (by omega)]
            congr 1
            exact SEALED_BYTES_nth_hi _ (by omega) (by omega)
        · refine w_know_ok_havoc SEGS E M _ k0 db (.ELit 4095) dk HK0 ?_
            (wbytes_grows _ M _) K hK
          intro x hx
          rw [h4095] at hx
          have hdt : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
              = estart E (SA db dk) := hus
          refine wbytes_out SEALED_BYTES M (edenot E (AsanPlanCore.reg cs 10)) x ?_ ?_
          · rwa [hdt, SEALED_BYTES_length]
          · have hxb : bv_unsigned x = (x.toNat : Int) := rfl
            rw [hxb, ← hus] at hx
            rcases hx with h | h
            · exact Or.inl h
            · exact Or.inr (by rw [SEALED_BYTES_length]; exact h)
    · intro E' R' FULL' model' h1 h2 hc hfs
      exact Hk E' R' FULL' model' ⟨h1, h2⟩ hc hfs
  -- the destination must be a literal for `kimg_cut`, and the image test is
  -- decidable, so `k0` is one of two knowledge lists
  cases hoff : off_image_x A (kn cs) db dk (.ELit 4095) with
  | true =>
    rw [hoff] at Hn
    simp only [ite_true] at Hn
    exact FIN (kn cs) HKN Hn
  | false =>
    rw [hoff] at Hn
    simp only [Bool.false_eq_true, ite_false] at Hn
    cases hdst : AsanPlanCore.reg cs 10 with
    | ELit d =>
      rw [hdst] at Hn
      simp only [] at Hn
      rw [← hdst] at Hn
      exact FIN (kimg_cut (kn cs) (d % two64) 4095)
        (kimg_cut_sound SEGS E M (kn cs) (d % two64) 4095 HKN) Hn
    | EVar n => rw [hdst] at Hn; simp at Hn
    | EAlu op a b => rw [hdst] at Hn; simp at Hn
    | EAluw op a b => rw [hdst] at Hn; simp at Hn
    | EMd op a b => rw [hdst] at Hn; simp at Hn
    | EMdw op a b => rw [hdst] at Hn; simp at Hn
    | EExt sx lo n e => rw [hdst] at Hn; simp at Hn
    | EBlob sx k i n => rw [hdst] at Hn; simp at Hn

/-- `check_sound`'s `node_x_sound` at `XIStrncpy`: one `intro args` away from
    `summary_istrncpy_sound`. -/
theorem node_x_sound_XIStrncpy (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : istrncpy_spec SEGS A.x_istrncpy A.x_sealed) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XIStrncpy := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XIStrncpy args
      = fun cs => summary_istrncpy A nx0 cs := funext (fun cs => rfl)
  rw [hx]
  exact summary_istrncpy_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull SUM

/-! ## 5d. `summary_popfree_sound` (`XPopFree`) -/

/-- `:1616` (the `free()`-side pointer walk of the class): the frame
    slot `sp - 4n` is written with `pf_bytes c s (n - i)` cells, the knowledge
    gets the `popfree_facts` cells (plus a `KUnk` for the un-written tail),
    and `a0/a2/a4/a5` are updated by the routine. -/
theorem summary_popfree_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : AsanPopFree.popfree_spec SEGS A.x_popfree) :
    ∀ args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always
      (fun cs => summary_popfree A nx0 cs args) := by
  intro args cs cs' E R FULL model T HC Hpre Hn Hk
  let M : word → Option byte := Mr A argH E cs model FULL
  have HKN : know_ok SEGS E M (kn cs) := HC.co_know
  dsimp only at Hn
  unfold summary_popfree at Hn
  dsimp only at Hn
  cases hpc0 : (pc cs == A.x_popfree) with
  | false =>
    rw [hpc0] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hpc : pc cs = A.x_popfree := beq_iff_eq.mp hpc0
  rw [hpc0] at Hn
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hn
  cases hargs : args with
  | nil => rw [hargs] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
  | cons a rest =>
      cases ha : a with
      | ELit K =>
        cases hr : rest with
        | cons b rest2 => rw [hargs, ha, hr] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
        | nil =>
        rw [hargs, ha, hr] at Hn
        cases h10 : reg_lit cs 10 with
        | none => rw [h10] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
        | some i =>
        cases h12 : reg_lit cs 12 with
        | none => rw [h10, h12] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
        | some c =>
        cases h21 : reg_lit cs 21 with
        | none => rw [h10, h12, h21] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
        | some s =>
        cases h19 : reg_lit cs 19 with
        | none => rw [h10, h12, h21, h19] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
        | some nn =>
        rw [h10, h12, h21, h19] at Hn
        simp only [] at Hn
        cases hspl : split_lit (eaddz (AsanPlanCore.reg cs 11) (- (4 * nn))) with
        | mk lb lk =>
        rw [hspl] at Hn
        simp only [] at Hn
        cases hel : xlo (kn cs) (AsanPlanCore.reg cs 11) with
        | none => rw [hel] at Hn; simp at Hn
        | some el =>
        cases heh : xhi (kn cs) (AsanPlanCore.reg cs 11) with
        | none => rw [heh] at Hn; simp at Hn
        | some eh =>
        rw [hel, heh] at Hn
        simp only [] at Hn
        cases hcond : (decide (0 ≤ i) && decide (i < nn) && decide (4 * nn ≤ el) && decide (eh < two64)
            && decide (0 ≤ c) && decide (0 ≤ s) && decide (c + (nn - i) * s < two64)
            && decide (0 ≤ K) && decide (K ≤ nn - i) && decide (pc cs + 32 < two64)
            && fresh_ok nx0 cs && kwritable_x (kn cs) (kn cs) lb lk (.ELit (4 * (nn - i)))
            && off_image_x A (kn cs) lb lk (.ELit (4 * (nn - i)))) with
        | false =>
          rw [hcond] at Hn
          simp only [Bool.false_eq_true, ite_false] at Hn
          exact absurd Hn (by simp)
        | true =>
        rw [hcond] at Hn
        simp only [ite_true] at Hn
        have hcond' := hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond'
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi0, hin⟩, h4n⟩, heh64⟩, hc0⟩, hs0⟩, hcs⟩, hK0⟩, hKcnt⟩,
          hpc32⟩, hfresh⟩, hwr⟩, hoff⟩ := hcond'
        rw [Option.some.injEq] at Hn
        subst Hn
        obtain ⟨R10, -, -⟩ :=
          w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 i HC (by omega) h10
        obtain ⟨R12, -, -⟩ :=
          w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 c HC (by omega) h12
        obtain ⟨R21, -, -⟩ :=
          w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 21 s HC (by omega) h21
        obtain ⟨R19, -, -⟩ :=
          w_reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 19 nn HC (by omega) h19
        have R11 : getr R (Z_to_bv 5 (11 : Int)) = edenot E (AsanPlanCore.reg cs 11) :=
          w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 HC (by omega)
        have hel' : el ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) :=
          xlo_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 11) el HKN hel
        have heh' : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) ≤ eh :=
          xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 11) eh HKN heh
        -- the low address `e - 4n`
        have heh64' : eh < (2 : Int) ^ 64 := heh64
        have hcs' : c + (nn - i) * s < (2 : Int) ^ 64 := hcs
        have h4n0 : 0 ≤ 4 * nn := by omega
        have h4n64 : 4 * nn < 2 ^ 64 := by
          have h := heh'
          omega
        have hLoval : bv_unsigned (edenot E (eaddz (AsanPlanCore.reg cs 11) (- (4 * nn))))
            = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn := by
          show bv_unsigned (edenot E (mkAlu .ADD (AsanPlanCore.reg cs 11) (.ELit (- (4 * nn))))) = _
          rw [mkAlu_denot]
          show bv_unsigned (edenot E (AsanPlanCore.reg cs 11) + Z_to_bv 64 (- (4 * nn))) = _
          rw [u_add64, u_lit64]
          simp only [two64]
          rw [Int.add_comm, emod_add_mod]
          rw [show (- (4 * nn) : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
              = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn from by omega]
          have e1 : 0 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn := by omega
          have e2 : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn
              < ((2 ^ 64 : Nat) : Int) := by
            have h8 : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) < ((2 ^ 64 : Nat) : Int) :=
              (u64_range (edenot E (AsanPlanCore.reg cs 11))).2
            omega
          exact Int.emod_eq_of_lt e1 e2
        have HloD : edenot E (eaddz (AsanPlanCore.reg cs 11) (- (4 * nn)))
            = Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn) := by
          rw [← hLoval]
          exact (Z_to_bv_unsigned _).symm
        -- the split of the frame slot
        obtain ⟨Wst, Wlo, Whi⟩ :=
          kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (.ELit (4 * (nn - i))) HKN HKN hwr
        have hlen4 : elenZ E (.ELit (4 * (nn - i))) = 4 * (nn - i) :=
          AsanPlanSound.elenZ_lit E _ ⟨by omega, by omega⟩
        have HD : estart E (SA lb lk) = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn := by
          have hsd := w_split_lit_denot E (eaddz (AsanPlanCore.reg cs 11) (- (4 * nn))) lb lk hspl
          have HDdef : estart E (SA lb lk) = bv_unsigned (edenot E lb) + lk := rfl
          rw [HloD, ← HDdef] at hsd
          have hb := congrArg bv_unsigned hsd
          have h1 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn))
              = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn := by
            rw [u_lit64]
            exact u_small_id _ ⟨by omega, by omega⟩
          have h2 : bv_unsigned (Z_to_bv 64 (estart E (SA lb lk)))
              = estart E (SA lb lk) := by
            rw [u_lit64]
            refine u_small_id _ ⟨Wlo, ?_⟩
            have h := Whi
            rw [hlen4] at h
            omega
          rw [h1, h2] at hb
          omega
        have Hbase : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn))
            = estart E (SA lb lk) := by
          have h := HD
          have h1 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn))
              = bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn := by
            rw [u_lit64]
            exact u_small_id _ ⟨by omega, by omega⟩
          rw [h1]; omega
        obtain ⟨regs', Hms, G10, G12, G14, G15, Gkeep⟩ :=
          SUM R M i (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) c s nn
            R10
            (by rw [← Z_to_bv5_eleven, Z_to_bv64_bv_unsigned]; exact R11)
            R12 R21 R19
            ⟨hi0, hin⟩
            ⟨by omega, by omega⟩
            hc0 hs0
            (by have h := hcs'; omega)
            (by
              have h : store_ok SEGS M (Z_to_bv 64 (estart E (SA lb lk))) (4 * (nn - i)).toNat = true :=
                Wst (4 * (nn - i)).toNat (by rw [hlen4]; omega)
              rwa [HD] at h)
        refine call_core SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
          argH_agree argH_high SEGS_in_hull cs E E R FULL model T (pc cs + 32)
          (sr_upd (sr_upd (sr_upd (sr_upd cs.a_ss.s_regs 10 (.ELit nn))
              12 (.ELit (c + (nn - i) * s))) 14 (.ELit ((c + (nn - i - 1) * s) / 16)))
            15 (eaddz (AsanPlanCore.reg cs 11) (- (4 * nn))))
          (popfree_facts lb lk (nn - i) c s K.toNat
            ++ (if K < nn - i then [.KUnk (SA lb lk) (.ELit (4 * ((nn - i) - K)))] else [])
            ++ kn_havoc (kn cs) lb lk (.ELit (4 * (nn - i))))
          (nxt cs) regs'
          (wbytes M (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn))
            (AsanPopFree.pf_bytes c s (nn - i).toNat))
          HC hfresh (env_agree_refl (nxt cs) E)
          ?_ ?_ ?_ ?_
        · -- the run
          rw [hpc]
          exact Hms
        · -- the registers
          refine regs_ok_pointwise E _ regs' ?_
          intro r hr0
          rw [nth_sr_upd, nth_sr_upd, nth_sr_upd, nth_sr_upd]
          have HR := HC.co_regs r
          unfold sr_get at HR
          have hrz : bv_eqb r 0 = false := bv_eqb_neq r 0 hr0
          rw [hrz] at HR
          simp only [Bool.false_eq_true, ite_false] at HR
          by_cases h15 : ridx r = 15
          · rw [ite_eq_left h15]
            rw [reg_of_ridx r 15 h15, Z_to_bv5_fifteen, HloD]
            exact G15
          · rw [ite_eq_right h15]
            by_cases h14 : ridx r = 14
            · rw [ite_eq_left h14]
              rw [reg_of_ridx r 14 h14, Z_to_bv5_fourteen]
              refine Eq.trans G14 ?_
              rw [edenot_lit]
            · rw [ite_eq_right h14]
              by_cases h12 : ridx r = 12
              · rw [ite_eq_left h12]
                rw [reg_of_ridx r 12 h12, Z_to_bv5_twelve]
                refine Eq.trans G12 ?_
                rw [edenot_lit]
              · rw [ite_eq_right h12]
                by_cases h10 : ridx r = 10
                · rw [ite_eq_left h10]
                  rw [reg_of_ridx r 10 h10]
                  show getr regs' (Z_to_bv 5 (10 : Int)) = edenot E (.ELit nn)
                  rw [Z_to_bv5_ten]
                  refine Eq.trans G10 ?_
                  rw [edenot_lit]
                · rw [ite_eq_right h10]
                  rw [Gkeep r (by intro h; exact h10 (by rw [h]; decide))
                    (by intro h; exact h12 (by rw [h]; decide))
                    (by intro h; exact h14 (by rw [h]; decide))
                    (by intro h; exact h15 (by rw [h]; decide))]
                  exact HR
        · -- the knowledge
          intro Ke hKe
          have hsp1 : Ke ∈ (popfree_facts lb lk (nn - i) c s K.toNat
              ++ (if K < nn - i then [.KUnk (SA lb lk) (.ELit (4 * ((nn - i) - K)))] else []))
              ∨ Ke ∈ kn_havoc (kn cs) lb lk (.ELit (4 * (nn - i))) :=
            List.mem_append.mp hKe
          rcases hsp1 with hKe | hKe
          · have hsp2 : Ke ∈ popfree_facts lb lk (nn - i) c s K.toNat
                ∨ Ke ∈ (if K < nn - i then [.KUnk (SA lb lk) (.ELit (4 * ((nn - i) - K)))] else []) :=
              List.mem_append.mp hKe
            rcases hsp2 with hKe | hKe
            · exact popfree_facts_sound SEGS E M lb lk (nn - i) c s K.toNat
                (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn))
                Hbase (by omega) (by omega) (by rw [HD]; omega) (by rw [HD]; omega) Ke hKe
            · by_cases hKlt : K < nn - i
              · rw [ite_eq_left hKlt] at hKe
                have hKe' : Ke = .KUnk (SA lb lk) (.ELit (4 * ((nn - i) - K))) := by
                  simpa using hKe
                rw [hKe']
                refine ⟨?_, ?_⟩
                · rw [AsanPlanSound.elenZ_lit E _ ⟨by omega, by omega⟩]
                  show 0 ≤ estart E (SA lb lk) ∧ estart E (SA lb lk) < 2 ^ 64
                    ∧ 0 ≤ 4 * ((nn - i) - K) ∧ estart E (SA lb lk) + 4 * ((nn - i) - K) ≤ 2 ^ 64
                  rw [HD]
                  have h := Whi
                  rw [hlen4] at h
                  omega
                · intro q hq1 hq2
                  rw [AsanPlanSound.elenZ_lit E _ ⟨by omega, by omega⟩] at hq2
                  have hlen : (AsanPopFree.pf_bytes c s (nn - i).toNat).length = 4 * (nn - i).toNat :=
                    AsanPopFree.pf_bytes_length c s (nn - i).toNat
                  have hw : ((Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn)).toNat : Int)
                      = estart E (SA lb lk) := Hbase
                  have hnj : ((q.toNat : Nat) : Int) = q := Int.toNat_of_nonneg hq1
                  have hstep : estart E (SA lb lk) + q
                      = ((Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn)).toNat : Int)
                        + ((q.toNat : Nat) : Int) := by rw [hw, hnj]
                  rw [hstep]
                  refine wbytes_defined _ _ _ _ ?_ ?_
                  · rw [hlen]
                    have h := Whi
                    rw [hlen4] at h
                    have h64 : ((4 * ((nn - i)).toNat : Nat) : Int) = 4 * (nn - i) := by
                      rw [Int.natCast_mul, Int.toNat_of_nonneg (by omega)]
                      simp
                    rw [h64, ← two64_eq_natCast, two64_eq]
                    omega
                  · rw [hlen]
                    have h64 : ((4 * ((nn - i)).toNat : Nat) : Int) = 4 * (nn - i) := by
                      rw [Int.natCast_mul, Int.toNat_of_nonneg (by omega)]
                      simp
                    have hq3 : (q.toNat : Int) < 4 * (nn - i) := by
                      have : q < 4 * ((nn - i) - K) := hq2
                      omega
                    omega
              · rw [ite_eq_right hKlt] at hKe
                exact absurd hKe (by simp)
          · refine w_know_ok_havoc SEGS E M _ (kn cs) lb (.ELit (4 * (nn - i))) lk HKN ?_
              (wbytes_grows _ M _) Ke hKe
            intro x hx
            rw [hlen4] at hx
            have hlen : (AsanPopFree.pf_bytes c s (nn - i).toNat).length = 4 * (nn - i).toNat :=
              AsanPopFree.pf_bytes_length c s (nn - i).toNat
            have hw : ((Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn)).toNat : Int)
                = estart E (SA lb lk) := Hbase
            have h64 : ((4 * ((nn - i)).toNat : Nat) : Int) = 4 * (nn - i) := by
              rw [Int.natCast_mul, Int.toNat_of_nonneg (by omega)]
              simp
            have hxb : bv_unsigned x = (x.toNat : Int) := rfl
            refine wbytes_out (AsanPopFree.pf_bytes c s (nn - i).toNat) M
              (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) - 4 * nn)) x ?_ ?_
            · rw [hw, hlen, h64, ← two64_eq_natCast, two64_eq]
              have h := Whi
              rw [hlen4] at h
              omega
            · rw [hw, hlen, h64]
              rw [hxb] at hx
              exact hx
        · -- the continuation
          intro R' FULL' model' HC' Hfs
          exact Hk E R' FULL' model' ⟨env_agree_refl nx0 E, env_agree_refl (nxt cs) E⟩ HC' Hfs
      | EVar m => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EAlu op a1 a2 => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EAluw op a1 a2 => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EMd op a1 a2 => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EMdw op a1 a2 => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EExt sx lo n e => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
      | EBlob sx k idx n => rw [hargs, ha] at Hn; simp only [] at Hn; exact absurd Hn (by simp)

/-- `check_sound`'s `node_x_sound` at `XPopFree`: one `intro args` away from
    `summary_popfree_sound`. -/
theorem node_x_sound_XPopFree (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : AsanPopFree.popfree_spec SEGS A.x_popfree) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XPopFree := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XPopFree args
      = fun cs => summary_popfree A nx0 cs args := funext (fun cs => rfl)
  rw [hx]
  exact summary_popfree_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull SUM args

/-! ## 5d. `summary_copy_sound` (`XIMemcpy` / `XMemcpy`) -/

/-- `:1290` (`memcpy` / `internal_memcpy`): the heaviest of the five
    summaries, and the only one that

      * concludes through `after_call2` — its HAVOC-SOURCE branch re-describes
        the first `W` destination words by the fresh variables
        `nxt cs + NCS + i`, so it must close through `call_node_sound2`; and
      * consumes the image fact `segs_wr_ok SEGS` — the source's readability
        is derived from its `KWr`-writability through `store_ok_rdn`, which is
        stated against `segs_wr_ok`.
    Four ways out, in the checker's own order: no store at all when `n` is
    provably `0`; a `KZero` overlay when the source is already zero; the
    piecewise copy `copy_facts` describes when `n` is a literal and the
    source's bytes are known; and otherwise havoc, plus the `KUnk` /
    `kn_havoc` re-description of the destination. -/
theorem summary_copy_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HSEGS : segs_wr_ok SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (entry : Int) (SUM : copy_spec SEGS entry) :
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always
      (fun cs => summary_copy A SEGS nx0 cs entry) := by
  intro cs cs' E R FULL model T HC Hpre Hn Hk
  let M : word → Option byte := Mr A argH E cs model FULL
  have HKN : know_ok SEGS E M (kn cs) := HC.co_know
  dsimp only at Hn
  rw [summary_copy_eq A SEGS nx0 cs entry] at Hn
  unfold summary_copy_ref at Hn
  dsimp only at Hn
  cases hpc0 : (pc cs == entry) with
  | false =>
    rw [hpc0] at Hn
    simp only [Bool.not_false, ite_true] at Hn
    exact absurd Hn (by simp)
  | true =>
  have hpc : pc cs = entry := beq_iff_eq.mp hpc0
  rw [hpc0] at Hn
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hn
  cases hret : ret_lit cs with
  | none => rw [hret] at Hn; simp only [] at Hn; exact absurd Hn (by simp)
  | some ret =>
  rw [hret] at Hn
  simp only [] at Hn
  cases hspd : split_lit (AsanPlanCore.reg cs 10) with
  | mk db dk =>
  rw [hspd] at Hn
  simp only [] at Hn
  cases hsps : split_lit (AsanPlanCore.reg cs 11) with
  | mk sb sk =>
  rw [hsps] at Hn
  simp only [] at Hn
  have MAIN : ∀ (nlo nhi dhi shi : Int),
      xlo (kn cs) (AsanPlanCore.reg cs 12) = some nlo →
      xhi (kn cs) (AsanPlanCore.reg cs 12) = some nhi →
      xhi (kn cs) (AsanPlanCore.reg cs 10) = some dhi →
      xhi (kn cs) (AsanPlanCore.reg cs 11) = some shi →
      (if (decide (0 ≤ nlo) && decide (nhi ≤ zpow 2 40) &&
            decide (dhi + nhi < two64) && decide (shi + nhi < two64)) then
          (if (nhi == 0) then after_call nx0 cs ret (some (AsanPlanCore.reg cs 10)) (kn cs)
           else
             match (if off_image_x A (kn cs) db dk (AsanPlanCore.reg cs 12) then some (kn cs)
                    else match AsanPlanCore.reg cs 10, AsanPlanCore.reg cs 12 with
                         | .ELit d, .ELit n => some (kimg_cut (kn cs) (d % two64) n)
                         | _, _ => none) with
             | none => none
             | some k0 =>
                 if (kwritable_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) &&
                     ranges_apart_x (kn cs) db dk (AsanPlanCore.reg cs 12) sb sk (AsanPlanCore.reg cs 12)) then
                   let k1 := kn_havoc k0 db dk (AsanPlanCore.reg cs 12)
                   let nx := nxt cs
                   let words := if (nlo == nhi && nhi % 8 == 0 && decide (nhi ≤ 256) && decide (0 < nhi)) then
                                  (nhi / 8).toNat else 0
                   let kfresh := (List.range words).map (fun i =>
                     .KWord (SA db (dk + 8 * (i : Int))) 8 (.EVar (nx + NCS + i)))
                   let havoc_src := if (kwritable_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12) &&
                                        flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12)) then
                                      after_call2 nx0 cs ret (some (AsanPlanCore.reg cs 10))
                                        (kfresh ++ kblob_prefix (kn cs) sb sk db dk nlo
                                         ++ (if 0 < nlo then .KUnk (SA db dk) (AsanPlanCore.reg cs 12) :: k1 else k1))
                                        words
                                    else none
                   if (decide (0 < nlo) && kzero_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12)) then
                     after_call nx0 cs ret (some (AsanPlanCore.reg cs 10))
                       (.KZero (SA db dk) (AsanPlanCore.reg cs 12) :: k1)
                   else
                     match AsanPlanCore.reg cs 12 with
                     | .ELit z =>
                         if (decide (nhi ≤ 2048) && flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12)) then
                           match copy_facts SEGS nhi.toNat (kn cs) sb sk db dk nhi with
                           | some kc => after_call nx0 cs ret (some (AsanPlanCore.reg cs 10)) (kc ++ k1)
                           | none => havoc_src
                         else havoc_src
                     | _ => havoc_src
                 else none) else none) = some cs' →
      srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
    intro nlo nhi dhi shi hnlo hnhi hdhi hshi Hn
    cases hcond : (decide (0 ≤ nlo) && decide (nhi ≤ zpow 2 40) &&
        decide (dhi + nhi < two64) && decide (shi + nhi < two64)) with
    | false =>
      rw [hcond] at Hn
      simp only [Bool.false_eq_true, ite_false] at Hn
      exact absurd Hn (by simp)
    | true =>
    rw [hcond] at Hn
    simp only [ite_true] at Hn
    have hcond' := hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcond'
    have h3' : dhi + nhi < (2 : Int) ^ 64 := h3
    have h4' : shi + nhi < (2 : Int) ^ 64 := h4
    obtain ⟨R1, Hrok, hret0, hret1⟩ :=
      ret_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ret HC hret
    have R10 : getr R (Z_to_bv 5 (10 : Int)) = edenot E (AsanPlanCore.reg cs 10) :=
      w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 HC (by omega)
    have R11 : getr R (Z_to_bv 5 (11 : Int)) = edenot E (AsanPlanCore.reg cs 11) :=
      w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 11 HC (by omega)
    have R12 : getr R (Z_to_bv 5 (12 : Int)) = edenot E (AsanPlanCore.reg cs 12) :=
      w_reg_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 HC (by omega)
    have hnlo' : nlo ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
      xlo_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 12) nlo HKN hnlo
    have hnhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ nhi :=
      xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 12) nhi HKN hnhi
    have hdhi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ≤ dhi :=
      xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 10) dhi HKN hdhi
    have hshi' : bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) ≤ shi :=
      xhi_sound SEGS E M (kn cs) (AsanPlanCore.reg cs 11) shi HKN hshi
    have hsd : edenot E (AsanPlanCore.reg cs 10) = Z_to_bv 64 (estart E (SA db dk)) := by
      rw [w_split_lit_denot E (AsanPlanCore.reg cs 10) db dk hspd, estart_SA]
    have hss : edenot E (AsanPlanCore.reg cs 11) = Z_to_bv 64 (estart E (SA sb sk)) := by
      rw [w_split_lit_denot E (AsanPlanCore.reg cs 11) sb sk hsps, estart_SA]
    have hstep : ∀ (K : List kentry) (bs : List byte),
        bs.length = (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat →
        rdn SEGS M (edenot E (AsanPlanCore.reg cs 11)) bs.length = some bs →
        store_ok SEGS M (edenot E (AsanPlanCore.reg cs 10)) bs.length = true →
        (((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
            ≤ ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int) ∨
          ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
            ≤ ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)) →
        know_ok SEGS E (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) K →
        after_call nx0 cs ret (some (AsanPlanCore.reg cs 10)) K = some cs' →
        srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
      intro K bs hlen hrd hst hdisj HK' hac
      obtain ⟨regs', hms, hkept, ha0⟩ :=
        SUM M (edenot E (AsanPlanCore.reg cs 10)) (edenot E (AsanPlanCore.reg cs 11))
          (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))) bs R (Z_to_bv 64 ret)
          (by have h := u64_range (edenot E (AsanPlanCore.reg cs 12)); omega)
          hlen hrd hst hdisj
          (by show bv_unsigned (edenot E (AsanPlanCore.reg cs 11)) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64
              have h := hshi'; omega)
          (by show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64
              have h := hdhi'; omega)
          Hrok
          (by rw [← Z_to_bv5_one]; exact R1)
          (by rw [← Z_to_bv5_ten_up]; exact R10)
          (by rw [← Z_to_bv5_eleven]; exact R11)
          (by rw [← Z_to_bv5_twelve, Z_to_bv64_bv_unsigned]; exact R12)
      have hms' : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
          (mkst regs' (Z_to_bv 64 ret)
            (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) (seg_rom SEGS)) := by
        rw [hpc]
        exact hms
      refine call_node_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree SINV_frame
        argH_agree argH_high SEGS_in_hull cs cs' E R FULL model T ret
        (some (AsanPlanCore.reg cs 10)) K regs' _ HC hac hms' hkept ?_ HK' ?_
      · show getr regs' (Z_to_bv 5 10) = edenot E (AsanPlanCore.reg cs 10)
        rw [Z_to_bv5_ten]
        show getr regs' (10 : reg) = edenot E (AsanPlanCore.reg cs 10)
        exact ha0
      · intro E' R' FULL' model' h1 h2 hc hfs
        exact Hk E' R' FULL' model' ⟨h1, h2⟩ hc hfs
    -- branch 1: `n` provably 0
    cases hz0 : (nhi == 0) with
    | true =>
      rw [hz0] at Hn
      simp only [ite_true] at Hn
      have hnhi0 : nhi = 0 := beq_iff_eq.mp hz0
      have hn0 : 0 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
        (u64_range (edenot E (AsanPlanCore.reg cs 12))).1
      have hz : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = 0 := by omega
      refine hstep (kn cs) [] ?_ ?_ ?_ ?_ ?_ Hn
      · show (0 : Nat) = (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
        rw [hz]
        rfl
      · rfl
      · rfl
      · show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
            + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ _
          ∨ ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
            + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) ≤ _
        omega
      · show know_ok SEGS E M (kn cs)
        exact HKN
    | false =>
      rw [hz0] at Hn
      simp only [Bool.false_eq_true, ite_false] at Hn
      have hnhi0 : nhi ≠ 0 := by
        intro hz
        rw [hz] at hz0
        exact absurd hz0 (by simp)
      cases hk0 : (if off_image_x A (kn cs) db dk (AsanPlanCore.reg cs 12) then some (kn cs)
                   else match AsanPlanCore.reg cs 10, AsanPlanCore.reg cs 12 with
                        | .ELit d, .ELit n => some (kimg_cut (kn cs) (d % two64) n)
                        | _, _ => none) with
      | none =>
        rw [hk0] at Hn
        simp only [] at Hn
        exact absurd Hn (by simp)
      | some k0 =>
        rw [hk0] at Hn
        simp only [] at Hn
        have HK0 : know_ok SEGS E M k0 :=
          k0_sound SEGS A E M (kn cs) db dk (AsanPlanCore.reg cs 12)
            (AsanPlanCore.reg cs 10) k0 HKN hk0
        cases hwa : (kwritable_x (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12) &&
            ranges_apart_x (kn cs) db dk (AsanPlanCore.reg cs 12) sb sk
              (AsanPlanCore.reg cs 12)) with
        | false =>
          rw [hwa] at Hn
          simp only [Bool.false_eq_true, ite_false] at Hn
          exact absurd Hn (by simp)
        | true =>
          rw [hwa] at Hn
          simp only [ite_true] at Hn
          have hwa' := hwa
          simp only [Bool.and_eq_true] at hwa'
          obtain ⟨hwr, hap⟩ := hwa'
          obtain ⟨Wst, Wlo, Whi⟩ :=
            kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (AsanPlanCore.reg cs 12)
              HKN HKN hwr
          have hapart :=
            ranges_apart_x_sound SEGS E M (kn cs) db dk (AsanPlanCore.reg cs 12) sb sk
              (AsanPlanCore.reg cs 12) HKN hap
          have hn0 : 0 ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
            (u64_range (edenot E (AsanPlanCore.reg cs 12))).1
          have hnw : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64 :=
            (u64_range (edenot E (AsanPlanCore.reg cs 12))).2
          have hlen12 : elenZ E (AsanPlanCore.reg cs 12)
              = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := rfl
          have VARS : fresh_ok nx0 cs = true →
              AsanPlanCore.kn_vars_lt (nxt cs) (kn cs) = true ∧
                AsanPlanCore.expr_vars_lt (nxt cs) db = true ∧
                  AsanPlanCore.expr_vars_lt (nxt cs) (AsanPlanCore.reg cs 12) = true ∧
                    AsanPlanCore.sr_vars_lt (nxt cs) cs.a_ss.s_regs = true := by
            intro Hfresh
            obtain ⟨Fsr, Fkn, -, -, -, -, -⟩ := w_fresh_ok_parts nx0 cs Hfresh
            refine ⟨Fkn, ?_, ?_, Fsr⟩
            · exact split_lit_vars (AsanPlanCore.reg cs 10) db dk (nxt cs) hspd
                (nth_sr_vars_lt' (nxt cs) cs.a_ss.s_regs 10 Fsr (by decide))
            · exact nth_sr_vars_lt' (nxt cs) cs.a_ss.s_regs 12 Fsr (by decide)
          have HAVOC : ∀ (bs : List byte),
              bs.length = (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat →
              0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) →
              know_ok SEGS E (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                (kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) := by
            intro bs hlbs hpos
            have hlen_bs : (bs.length : Int)
                = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by
              rw [hlbs]
              exact Int.toNat_of_nonneg hn0
            have Hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                = estart E (SA db dk) := by
              have hDlo : 0 ≤ estart E (SA db dk) := Wlo
              have hDhi : estart E (SA db dk) < 2 ^ 64 := by
                have h := Whi
                rw [show elenZ E (AsanPlanCore.reg cs 12)
                      = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) from rfl] at h
                omega
              rw [hsd, u_lit64]
              exact u_small_id _ ⟨hDlo, hDhi⟩
            refine w_know_ok_havoc SEGS E M _ k0 db (AsanPlanCore.reg cs 12) dk HK0 ?_
              (wbytes_grows _ M _)
            intro x hx
            rw [← Hus] at hx
            refine wbytes_out bs M (edenot E (AsanPlanCore.reg cs 10)) x ?_ ?_
            · show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (bs.length : Int)
                ≤ ((2 ^ 64 : Nat) : Int)
              rw [← two64_eq_natCast, hlen_bs, Hus]
              show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
              exact Whi
            · rcases hx with hx | hx
              · left
                exact hx
              · right
                rw [hlen_bs]
                exact hx
          -- ---- the HAVOC-SOURCE result: source writable+flat; destination
          -- havoc'd, for W > 0 its first W words re-described by the fresh
          -- variables `nxt cs + NCS + i` ----
          have GEN : kwritable_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12) = true →
              flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12) = true →
              ∀ (W : Nat), 8 * (W : Int)
                  ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) →
                after_call2 nx0 cs ret (some (AsanPlanCore.reg cs 10))
                  ((List.range W).map (fun (i : Nat) =>
                      kentry.KWord (SA db (dk + 8 * (i : Int))) 8
                        (expr.EVar (nxt cs + NCS + i)))
                   ++ kblob_prefix (kn cs) sb sk db dk nlo
                   ++ (if 0 < nlo then
                         kentry.KUnk (SA db dk) (AsanPlanCore.reg cs 12)
                           :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12)
                       else kn_havoc k0 db dk (AsanPlanCore.reg cs 12))) W = some cs' →
                srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
            intro Hswr Hsfl W HW Hac
            obtain ⟨SWst, Slo, Shi⟩ :=
              kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12)
                HKN HKN Hswr
            obtain ⟨Sflo, Sfhi, Spos⟩ :=
              w_flat_x_sound SEGS E M (kn cs) sb sk (AsanPlanCore.reg cs 12) HKN Hsfl
            have hlen12 : elenZ E (AsanPlanCore.reg cs 12)
                = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := rfl
            -- the source address, in `edenot` spelling
            have Husr : bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
                = estart E (SA sb sk) := by
              have hSlo : 0 ≤ estart E (SA sb sk) := Slo
              have hShi : estart E (SA sb sk) < 2 ^ 64 := by
                have h := Sfhi
                omega
              rw [hss, u_lit64]
              exact u_small_id _ ⟨hSlo, hShi⟩
            -- the destination address, likewise
            have Hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                = estart E (SA db dk) := by
              have hDlo : 0 ≤ estart E (SA db dk) := Wlo
              have hDhi : estart E (SA db dk) < 2 ^ 64 := by
                have h := Whi
                rw [hlen12] at h
                omega
              rw [hsd, u_lit64]
              exact u_small_id _ ⟨hDlo, hDhi⟩
            -- the source is readable (it is writable), so the bytes exist
            have hpre1 : ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                + ((bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat : Int)
                ≤ ((2 ^ 64 : Nat) : Int) := by
              rw [show ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                    = estart E (SA sb sk) from Husr,
                  Int.toNat_of_nonneg hn0,
                  show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64
                    from two64_eq_natCast.symm]
              exact Sfhi
            have hpre2 : store_ok SEGS M (edenot E (AsanPlanCore.reg cs 11))
                (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat = true := by
              have h := SWst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (by rw [Int.toNat_of_nonneg hn0]; exact Int.le_refl _)
              rwa [← hss] at h
            obtain ⟨bs, hrd0, Hlbs⟩ :=
              store_ok_rdn SEGS HSEGS
                (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat M
                (edenot E (AsanPlanCore.reg cs 11)) hpre1 hpre2
            have hlen_bs : (bs.length : Int)
                = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by
              rw [Hlbs, Int.toNat_of_nonneg hn0]
            have hrd : rdn SEGS M (edenot E (AsanPlanCore.reg cs 11)) bs.length = some bs := by
              rw [Hlbs]
              exact hrd0
            have hst : store_ok SEGS M (edenot E (AsanPlanCore.reg cs 10)) bs.length = true := by
              have h := Wst bs.length
                (by rw [Hlbs, Int.toNat_of_nonneg hn0]; exact Int.le_refl _)
              rwa [← hsd] at h
            have hdisj : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                  + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                  ≤ ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int) ∨
                ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                  + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                  ≤ ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) := by
              have hdst : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                  = estart E (SA db dk) := Hus
              have hsrc : ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                  = estart E (SA sb sk) := Husr
              rcases hapart with h | h
              · left
                rw [hdst, hsrc]
                exact h
              · right
                rw [hdst, hsrc]
                exact h
            obtain ⟨regs', hms, hkept, ha0⟩ :=
              SUM M (edenot E (AsanPlanCore.reg cs 10)) (edenot E (AsanPlanCore.reg cs 11))
                (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))) bs R (Z_to_bv 64 ret)
                (by have h := u64_range (edenot E (AsanPlanCore.reg cs 12)); omega)
                Hlbs hrd hst hdisj
                (by show bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
                        + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64
                    have h := hshi'; omega)
                (by show bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                        + bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) < 2 ^ 64
                    have h := hdhi'; omega)
                Hrok
                (by rw [← Z_to_bv5_one]; exact R1)
                (by rw [← Z_to_bv5_ten_up]; exact R10)
                (by rw [← Z_to_bv5_eleven]; exact R11)
                (by rw [← Z_to_bv5_twelve, Z_to_bv64_bv_unsigned]; exact R12)
            have hms' : msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
                (mkst regs' (Z_to_bv 64 ret)
                  (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) (seg_rom SEGS)) := by
              rw [hpc]
              exact hms
            refine call_node_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HULL_ok SINV_agree
              SINV_frame argH_agree argH_high SEGS_in_hull cs cs' E R FULL model T ret
              (some (AsanPlanCore.reg cs 10)) _ W
              ((List.range W).map (fun (i : Nat) =>
                Z_to_bv 64 (bytes_le_to_Z ((bs.drop (8 * i)).take 8)))) regs'
              (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) HC Hac hms' hkept ?_ ?_ ?_
            · show getr regs' (Z_to_bv 5 10) = edenot E (AsanPlanCore.reg cs 10)
              rw [Z_to_bv5_ten]
              show getr regs' (10 : reg) = edenot E (AsanPlanCore.reg cs 10)
              exact ha0
            · -- HK': the knowledge after the copy, under the extended valuation
              let E2 : env := ext_call2 E (nxt cs) regs'
                ((List.range W).map (fun (i : Nat) =>
                  Z_to_bv 64 (bytes_le_to_Z ((bs.drop (8 * i)).take 8))))
              have Hag2 : env_agree (nxt cs) E E2 :=
                ext_call2_agree E (nxt cs) regs' _
              have Hfresh : fresh_ok nx0 cs = true := by
                by_cases h : fresh_ok nx0 cs = true
                · exact h
                · have hf : fresh_ok nx0 cs = false := by
                    cases hv : fresh_ok nx0 cs with
                    | false => rfl
                    | true => exact absurd hv h
                  unfold after_call2 at Hac
                  dsimp only at Hac
                  rw [hf] at Hac
                  simp at Hac
              obtain ⟨Fkn, Fdb, Fne, Fsr⟩ := VARS Hfresh
              -- the destination address, under `E2`
              have Edb : edenot E2 db = edenot E db :=
                (edenot_agree' (nxt cs) E E2 db Hag2 Fdb).symm
              have ED2 : estart E2 (SA db dk) = estart E (SA db dk) := by
                simp only [estart, Edb]
              have Ene : edenot E2 (AsanPlanCore.reg cs 12)
                  = edenot E (AsanPlanCore.reg cs 12) :=
                (edenot_agree' (nxt cs) E E2 (AsanPlanCore.reg cs 12) Hag2 Fne).symm
              have HKN2 : know_ok SEGS E2 M (kn cs) :=
                know_ok_agree' SEGS (nxt cs) E E2 M (kn cs) Hag2 Fkn HKN
              have HK02 : know_ok SEGS E2 M k0 :=
                k0_sound SEGS A E2 M (kn cs) db dk (AsanPlanCore.reg cs 12)
                  (AsanPlanCore.reg cs 10) k0 HKN2 hk0
              change ∀ K ∈ (List.range W).map (fun (i : Nat) =>
                    kentry.KWord (SA db (dk + 8 * (i : Int))) 8
                      (expr.EVar (nxt cs + NCS + i)))
                  ++ kblob_prefix (kn cs) sb sk db dk nlo
                  ++ (if 0 < nlo then
                        kentry.KUnk (SA db dk) (AsanPlanCore.reg cs 12)
                          :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12)
                      else kn_havoc k0 db dk (AsanPlanCore.reg cs 12)),
                kentry_ok SEGS E2 (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) K
              intro K hK
              rcases List.mem_append.mp hK with hK | hK
              · rcases List.mem_append.mp hK with hK | hK
                · -- (a) the fresh destination words
                  obtain ⟨i, hiW, rfl⟩ := List.mem_map.mp hK
                  have hiWlt : i < W := List.mem_range.mp hiW
                  have hi8 : 8 * (i : Int) + 8
                      ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by
                    have h := HW
                    omega
                  have EDi : estart E2 (SA db (dk + 8 * (i : Int)))
                      = estart E (SA db dk) + 8 * (i : Int) := by
                    simp only [estart, Edb]
                    omega
                  show 8 ≤ 8 ∧ flat E2 (SA db (dk + 8 * (i : Int))) (8 : Int) ∧
                    rdn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                      (adenot E2 (SA db (dk + 8 * (i : Int)))) 8
                      = some (word_to_le_bytes 8 (edenot E2 (expr.EVar (nxt cs + NCS + i))))
                  refine ⟨by decide, ?_, ?_⟩
                  · show 0 ≤ estart E2 (SA db (dk + 8 * (i : Int))) ∧
                        estart E2 (SA db (dk + 8 * (i : Int))) < 2 ^ 64 ∧
                        0 ≤ (8 : Int) ∧
                        estart E2 (SA db (dk + 8 * (i : Int))) + 8 ≤ 2 ^ 64
                    rw [EDi]
                    have hD0 : 0 ≤ estart E (SA db dk) := Wlo
                    have hD8 : estart E (SA db dk) + 8 ≤ 2 ^ 64 := by
                      have h := Whi
                      rw [hlen12] at h
                      omega
                    refine ⟨by omega, by omega, by decide, by omega⟩
                  · -- the piece of `bs` that this word describes
                    have hi8n : 8 * i + 8 ≤ bs.length := by
                      have h2 : ((8 * i + 8 : Nat) : Int) ≤ (bs.length : Int) := by
                        rw [Int.natCast_add, Int.natCast_mul, hlen_bs]
                        exact hi8
                      exact Int.ofNat_le.mp h2
                    have Hpiece : ((bs.drop (8 * i)).take 8).length = 8 := by
                      rw [List.length_take, List.length_drop]
                      exact Nat.min_eq_left (by omega)
                    have hat : edenot E (AsanPlanCore.reg cs 10) + nat_to_word (8 * i)
                        = Z_to_bv 64 (estart E (SA db dk) + 8 * (i : Int)) := by
                      rw [RefMemcpyLib.at_nat]
                      show Z_to_bv 64 ((edenot E (AsanPlanCore.reg cs 10)).toNat
                            + ((8 * i : Nat) : Int)) = _
                      rw [show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                            = bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) from rfl,
                          Hus, Int.natCast_mul]
                      rfl
                    have hev : edenot E2 (expr.EVar (nxt cs + NCS + i))
                        = Z_to_bv 64 (bytes_le_to_Z ((bs.drop (8 * i)).take 8)) := by
                      dsimp only [E2, edenot]
                      rw [ext_call2_at E (nxt cs) regs'
                        ((List.range W).map (fun (j : Nat) =>
                          Z_to_bv 64 (bytes_le_to_Z ((bs.drop (8 * j)).take 8))))
                        i (by rw [List.length_map, List.length_range]; exact hiWlt)]
                      exact nth_map_seq (fun (j : Nat) =>
                        Z_to_bv 64 (bytes_le_to_Z ((bs.drop (8 * j)).take 8))) W i (Z_to_bv 64 0) hiWlt
                    have hrdw : rdn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                        (edenot E (AsanPlanCore.reg cs 10)) bs.length = some bs := by
                      refine rdn_wbytes_hit SEGS bs M (edenot E (AsanPlanCore.reg cs 10)) ?_
                      rw [← two64_eq_natCast,
                        show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                          = estart E (SA db dk) from Hus, hlen_bs]
                      show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                      exact Whi
                    have hskip := SeqExec.rdn_skipn SEGS (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                      bs.length (edenot E (AsanPlanCore.reg cs 10)) bs (8 * i) hrdw (by omega)
                    have hfi := SeqExec.rdn_firstn SEGS
                      (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                      (bs.length - 8 * i)
                      (edenot E (AsanPlanCore.reg cs 10) + nat_to_word (8 * i))
                      (bs.drop (8 * i)) 8 hskip (by omega)
                    rw [adenot_SA, EDi, ← hat, hev,
                      word_to_le_bytes_of_bytes_n 8 ((bs.drop (8 * i)).take 8) Hpiece (by decide)]
                    exact hfi
                · -- (b) the transported leading blob
                  have hb : ∃ (n0 : Int) (j : Nat),
                      0 < n0 ∧ n0 ≤ nlo ∧
                        kentry.KBlob (SA sb sk) (.ELit n0) j ∈ kn cs ∧
                        K = kentry.KBlob (SA db dk) (.ELit n0) j := by
                    unfold kblob_prefix at hK
                    split at hK
                    · rename_i a0 n0 j heq
                      cases a0 with
                      | mk bb oo =>
                        have hpred := List.find?_some heq
                        have hmem := List.mem_of_find?_eq_some heq
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
                        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hpred
                        have h1' : bb = sb := expr_eqb_eq bb sb h1
                        have h2' : oo = sk := beq_iff_eq.mp h2
                        simp only [List.mem_singleton] at hK
                        exact ⟨n0, j, h3, h4, by rw [h1', h2'] at hmem; exact hmem, hK⟩
                    · simp at hK
                  obtain ⟨n0, j, hn0pos, hn0le, hmem, hKeq⟩ := hb
                  rw [hKeq]
                  -- the source blob entry, in `kn cs`
                  have hsrc : kentry_ok SEGS E M (.KBlob (SA sb sk) (.ELit n0) j) :=
                    HKN _ hmem
                  obtain ⟨Bflat, Blen, Bbytes⟩ := hsrc
                  -- `n0` is small
                  have hn0lt : n0 < 2 ^ 64 :=
                    Int.lt_of_le_of_lt (Int.le_trans hn0le hnlo') hnw
                  have En0 : elenZ E (.ELit n0) = n0 := by
                    show bv_unsigned (edenot E (.ELit n0)) = n0
                    rw [show edenot E (.ELit n0) = Z_to_bv 64 n0 from rfl, u_lit64]
                    exact u_small_id n0 ⟨Int.le_of_lt hn0pos, hn0lt⟩
                  have En0' : elenZ E2 (.ELit n0) = n0 := by
                    show bv_unsigned (edenot E2 (.ELit n0)) = n0
                    rw [show edenot E2 (.ELit n0) = Z_to_bv 64 n0 from rfl, u_lit64]
                    exact u_small_id n0 ⟨Int.le_of_lt hn0pos, hn0lt⟩
                  show flat E2 (SA db dk) (elenZ E2 (.ELit n0)) ∧
                    ((E2.eb j).length : Int) = elenZ E2 (.ELit n0) ∧
                    ∀ i, 0 ≤ i → i < elenZ E2 (.ELit n0) →
                      wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs
                        (Z_to_bv 64 (estart E2 (SA db dk) + i))
                        = some ((E2.eb j).getD i.toNat (Z_to_bv 8 0))
                  refine ⟨?_, ?_, ?_⟩
                  · show 0 ≤ estart E2 (SA db dk) ∧ estart E2 (SA db dk) < 2 ^ 64 ∧
                        0 ≤ elenZ E2 (.ELit n0) ∧
                        estart E2 (SA db dk) + elenZ E2 (.ELit n0) ≤ 2 ^ 64
                    rw [ED2, En0']
                    have hDn : estart E (SA db dk) + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                        ≤ 2 ^ 64 := by
                      have h := Whi
                      rw [hlen12] at h
                      exact h
                    have hnpos : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
                      Int.lt_of_lt_of_le (Int.lt_of_lt_of_le hn0pos hn0le) hnlo'
                    refine ⟨Wlo, by omega, Int.le_of_lt hn0pos, by omega⟩
                  · rw [En0', show E2.eb = E.eb from Hag2.2.symm, ← En0]
                    exact Blen
                  · intro i hi0 hin
                    rw [En0'] at hin
                    have hnb : ((i.toNat : Nat) : Int) = i := Int.toNat_of_nonneg hi0
                    have hilt : i.toNat < bs.length := by
                      rw [Hlbs]
                      omega
                    have hnbnd : bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                        + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
                      show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (bs.length : Int)
                          ≤ ((2 ^ 64 : Nat) : Int)
                      rw [← two64_eq_natCast, hlen_bs, Hus]
                      show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                      exact Whi
                    have hbsn : wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs
                        (Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                          + (i.toNat : Int)))
                        = some (bs.getD i.toNat (Z_to_bv 8 0)) :=
                      wbytes_nth bs M (edenot E (AsanPlanCore.reg cs 10)) i.toNat hnbnd hilt
                    -- the same byte in the source, through the blob entry
                    have hblob : M (Z_to_bv 64 (estart E (SA sb sk) + i))
                        = some ((E.eb j).getD i.toNat (Z_to_bv 8 0)) :=
                      Bbytes i hi0 (by rw [En0]; exact hin)
                    have hnbnd' : ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                        + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
                      rw [← two64_eq_natCast,
                        show ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                          = estart E (SA sb sk) from Husr, hlen_bs]
                      show estart E (SA sb sk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                      exact Sfhi
                    have hsrcn := rdn_nth SEGS M bs.length (edenot E (AsanPlanCore.reg cs 11))
                      bs i.toNat hnbnd' hrd hilt
                    have hs1 : rdn SEGS M (Z_to_bv 64 (estart E (SA sb sk) + i)) 1
                        = some [bs.getD i.toNat (Z_to_bv 8 0)] := by
                      rw [show Z_to_bv 64 ((edenot E (AsanPlanCore.reg cs 11)).toNat
                            + (i.toNat : Int)) = Z_to_bv 64 (estart E (SA sb sk) + i) from by
                          rw [show ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                              = estart E (SA sb sk) from Husr, hnb]] at hsrcn
                      exact hsrcn
                    have hb1 : rdn SEGS M (Z_to_bv 64 (estart E (SA sb sk) + i)) 1
                        = some [((E.eb j).getD i.toNat (Z_to_bv 8 0))] :=
                      rdn1_overlay SEGS M _ _ hblob
                    rw [hs1] at hb1
                    -- put the two together
                    have hb2 : bs.getD i.toNat (Z_to_bv 8 0)
                        = (E.eb j).getD i.toNat (Z_to_bv 8 0) := by
                      simpa using hb1
                    rw [show E2.eb = E.eb from Hag2.2.symm,
                      show Z_to_bv 64 (estart E2 (SA db dk) + i)
                        = Z_to_bv 64 (bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                            + (i.toNat : Int)) from by rw [ED2, Hus, hnb], hbsn]
                    exact congrArg some hb2
              · -- (c) the havoc'd old knowledge, re-derived under `E2`
                have HAV2 : know_ok SEGS E2
                    (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs)
                    (kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) := by
                  refine w_know_ok_havoc SEGS E2 M _ k0 db (AsanPlanCore.reg cs 12) dk
                    HK02 ?_ (wbytes_grows _ M _)
                  intro x hx
                  rw [ED2, show elenZ E2 (AsanPlanCore.reg cs 12)
                        = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) from by
                      simp only [elenZ, Ene]] at hx
                  rw [← Hus] at hx
                  refine wbytes_out bs M (edenot E (AsanPlanCore.reg cs 10)) x ?_ ?_
                  · show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (bs.length : Int)
                      ≤ ((2 ^ 64 : Nat) : Int)
                    rw [← two64_eq_natCast, hlen_bs, Hus]
                    show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                    exact Whi
                  · rcases hx with hx | hx
                    · left
                      exact hx
                    · right
                      rw [hlen_bs]
                      exact hx
                by_cases hpos : 0 < nlo
                · rw [ite_eq_left hpos] at hK
                  rcases List.mem_cons.mp hK with rfl | hK
                  · -- `KUnk (SA db dk) ne`: the destination bytes are defined after the copy
                    show flat E2 (SA db dk) (elenZ E2 (AsanPlanCore.reg cs 12)) ∧
                      ∀ i, 0 ≤ i → i < elenZ E2 (AsanPlanCore.reg cs 12) →
                        wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs
                          (Z_to_bv 64 (estart E2 (SA db dk) + i)) ≠ none
                    refine ⟨?_, ?_⟩
                    · show 0 ≤ estart E2 (SA db dk) ∧ estart E2 (SA db dk) < 2 ^ 64 ∧
                          0 ≤ elenZ E2 (AsanPlanCore.reg cs 12) ∧
                          estart E2 (SA db dk) + elenZ E2 (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                      rw [ED2, show elenZ E2 (AsanPlanCore.reg cs 12)
                            = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) from by
                          simp only [elenZ, Ene]]
                      have h := Whi
                      rw [hlen12] at h
                      have hpos' : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
                        Int.lt_of_lt_of_le hpos hnlo'
                      refine ⟨Wlo, by omega, by omega, h⟩
                    · intro i hi0 hin
                      rw [show elenZ E2 (AsanPlanCore.reg cs 12)
                            = bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) from by
                          simp only [elenZ, Ene]] at hin
                      have hnb : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
                      have hj : i.toNat < bs.length := by
                        rw [Hlbs]
                        omega
                      have haddr : Z_to_bv 64 (estart E2 (SA db dk) + i)
                          = Z_to_bv 64 (((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                              + (i.toNat : Int)) := by
                        rw [show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                            = estart E (SA db dk) from Hus, hnb, ED2]
                      rw [haddr]
                      refine wbytes_defined bs M (edenot E (AsanPlanCore.reg cs 10)) i.toNat ?_ hj
                      show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (bs.length : Int)
                          ≤ ((2 ^ 64 : Nat) : Int)
                      rw [← two64_eq_natCast, hlen_bs, Hus]
                      show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                      exact Whi
                  · exact HAV2 K hK
                · rw [ite_eq_right hpos] at hK
                  exact HAV2 K hK
            · intro E' R' FULL' model' h1 h2 hc hfs
              exact Hk E' R' FULL' model' ⟨h1, h2⟩ hc hfs
          -- the havoc-source alternative as it occurs (three times) in the checker
          have HSRC :
              (if (kwritable_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12) &&
                  flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12)) then
                after_call2 nx0 cs ret (some (AsanPlanCore.reg cs 10))
                  ((List.range (if (nlo == nhi && nhi % 8 == 0 && nhi ≤ 256 && 0 < nhi)
                      then (nhi / 8).toNat else 0)).map (fun (i : Nat) =>
                        kentry.KWord (SA db (dk + 8 * (i : Int))) 8
                          (expr.EVar (nxt cs + NCS + i)))
                    ++ kblob_prefix (kn cs) sb sk db dk nlo
                    ++ (if 0 < nlo then
                          kentry.KUnk (SA db dk) (AsanPlanCore.reg cs 12)
                            :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12)
                        else kn_havoc k0 db dk (AsanPlanCore.reg cs 12)))
                  (if (nlo == nhi && nhi % 8 == 0 && nhi ≤ 256 && 0 < nhi)
                    then (nhi / 8).toNat else 0)
              else none) = some cs' →
              srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T := by
            intro Hsw
            cases hswg : (kwritable_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12) &&
                flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12)) with
            | false =>
              rw [hswg] at Hsw
              simp only [Bool.false_eq_true, ite_false] at Hsw
              exact absurd Hsw (by simp)
            | true =>
              rw [hswg] at Hsw
              simp only [ite_true] at Hsw
              have hswg' := hswg
              simp only [Bool.and_eq_true] at hswg'
              obtain ⟨Hswr, Hsfl⟩ := hswg'
              cases hW : (nlo == nhi && nhi % 8 == 0 && nhi ≤ 256 && 0 < nhi) with
              | false =>
                rw [hW] at Hsw
                simp only [Bool.false_eq_true, ite_false] at Hsw
                exact GEN Hswr Hsfl 0 (by omega) Hsw
              | true =>
                rw [hW] at Hsw
                simp only [ite_true] at Hsw
                have hW' := hW
                simp only [Bool.and_eq_true, beq_iff_eq] at hW'
                obtain ⟨⟨⟨hWeq, hWmod⟩, _⟩, _⟩ := hW'
                have h8W : 8 * ((nhi / 8).toNat : Int)
                    ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by
                  have hnhi0 : 0 ≤ nhi := by rw [← hWeq]; exact h1
                  have h1' : ((nhi / 8).toNat : Int) = nhi / 8 :=
                    Int.toNat_of_nonneg (Int.ediv_nonneg hnhi0 (by decide))
                  have h2' : 8 * (nhi / 8) = nhi := by
                    have h := Int.mul_ediv_add_emod nhi 8
                    rw [hWmod, Int.add_zero] at h
                    exact h
                  have hn_eq : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = nhi := by
                    have hle : nhi ≤ bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := by
                      rw [← hWeq]
                      exact hnlo'
                    exact Int.le_antisymm hnhi' hle
                  rw [h1', h2', hn_eq]
                  exact Int.le_refl _
                exact GEN Hswr Hsfl ((nhi / 8).toNat) h8W Hsw
          cases hz : (0 < nlo && kzero_x (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12)) with
          | true =>
            -- branch 2: the source is already zero
            rw [hz] at Hn
            simp only [ite_true] at Hn
            have hz' := hz
            simp only [Bool.and_eq_true] at hz'
            obtain ⟨hposD, hkz⟩ := hz'
            have hnlopos : 0 < nlo := of_decide_eq_true hposD
            obtain ⟨Zb, Zlo, Zhi⟩ :=
              kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk (AsanPlanCore.reg cs 12)
                HKN HKN hkz
            have hnpos : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) :=
              Int.lt_of_lt_of_le hnlopos hnlo'
            have hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                = estart E (SA db dk) := by
              have h := Whi
              rw [hlen12] at h
              rw [hsd, u_lit64]
              exact u_small_id _ ⟨Wlo, by omega⟩
            have husr : bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
                = estart E (SA sb sk) := by
              have h := Zhi
              rw [hlen12] at h
              rw [hss, u_lit64]
              exact u_small_id _ ⟨Zlo, by omega⟩
            have hdisj : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                  + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                  ≤ ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int) ∨
                ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                  + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                  ≤ ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) := by
              have hdst : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                  = estart E (SA db dk) := hus
              have hsrc : ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                  = estart E (SA sb sk) := husr
              rcases hapart with h | h
              · left
                rw [hdst, hsrc]
                exact h
              · right
                rw [hdst, hsrc]
                exact h
            refine hstep (kentry.KZero (SA db dk) (AsanPlanCore.reg cs 12)
                :: kn_havoc k0 db dk (AsanPlanCore.reg cs 12))
              (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (Z_to_bv 8 0)) List.length_replicate ?_ ?_ hdisj ?_ Hn
            · show rdn SEGS M (edenot E (AsanPlanCore.reg cs 11))
                  (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                    (Z_to_bv 8 0)).length
                  = some (List.replicate
                      (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat (Z_to_bv 8 0))
              rw [List.length_replicate]
              refine rdn_overlay_all SEGS M
                (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (edenot E (AsanPlanCore.reg cs 11)) (Z_to_bv 8 0) ?_ ?_
              · rw [← two64_eq_natCast,
                  show ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                    = estart E (SA sb sk) from husr, Int.toNat_of_nonneg hn0]
                show estart E (SA sb sk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                exact Zhi
              · intro i hi0 hi
                rw [show ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                      = estart E (SA sb sk) from husr]
                exact Zb i hi0 hi
            · show store_ok SEGS M (edenot E (AsanPlanCore.reg cs 10))
                  (List.replicate (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                    (Z_to_bv 8 0)).length = true
              rw [List.length_replicate]
              have h := Wst (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat
                (by rw [Int.toNat_of_nonneg hn0]; exact Int.le_refl _)
              rwa [← hsd] at h
            · intro K hK
              rcases List.mem_cons.mp hK with rfl | hK
              · show flat E (SA db dk) (elenZ E (AsanPlanCore.reg cs 12)) ∧
                  ∀ i, 0 ≤ i → i < elenZ E (AsanPlanCore.reg cs 12) →
                    wbytes M (edenot E (AsanPlanCore.reg cs 10))
                      (List.replicate
                        (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))).toNat (Z_to_bv 8 0))
                      (Z_to_bv 64 (estart E (SA db dk) + i)) = some (Z_to_bv 8 0)
                refine ⟨?_, ?_⟩
                · show 0 ≤ estart E (SA db dk) ∧ estart E (SA db dk) < 2 ^ 64 ∧
                      0 ≤ elenZ E (AsanPlanCore.reg cs 12) ∧
                      estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                  have h := Whi
                  rw [hlen12] at h
                  exact ⟨Wlo, by omega, hn0, h⟩
                · intro i hi0 hi
                  rw [show Z_to_bv 64 (estart E (SA db dk) + i)
                        = Z_to_bv 64 ((edenot E (AsanPlanCore.reg cs 10)).toNat + i) from by
                      rw [show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                          = estart E (SA db dk) from hus]]
                  refine wbytes_fill_at M (edenot E (AsanPlanCore.reg cs 10)) (Z_to_bv 8 0)
                    (bv_unsigned (edenot E (AsanPlanCore.reg cs 12))) i ?_ ⟨hi0, hi⟩
                  rw [← two64_eq_natCast,
                    show ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                      = estart E (SA db dk) from hus]
                  show estart E (SA db dk) + elenZ E (AsanPlanCore.reg cs 12) ≤ 2 ^ 64
                  exact Whi
              · exact HAVOC _ List.length_replicate hnpos K hK
          | false =>
            rw [hz] at Hn
            simp only [Bool.false_eq_true, ite_false] at Hn
            split at Hn
            · rename_i z heqz
              split at Hn
              · -- `nhi ≤ 2048` and the source is flat: the piecewise copy
                have hg : (decide (nhi ≤ 2048) &&
                    flat_x (kn cs) sb sk (AsanPlanCore.reg cs 12)) = true := by
                  assumption
                rw [Bool.and_eq_true] at hg
                obtain ⟨-, hfl⟩ := hg
                split at Hn
                · -- `copy_facts` described the source
                  rename_i kc Hcf
                  -- the length is the literal's value
                  have Hnn : bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) = nhi := by
                    have h2 : zlit64 z = nhi := by
                      have h := hnhi
                      rw [heqz] at h
                      simp only [xhi] at h
                      exact Option.some.inj h
                    rw [heqz]
                    show bv_unsigned (Z_to_bv 64 z) = nhi
                    rw [u_lit64, ← h2, zlit64_eq]
                  have hnhi0 : 0 ≤ nhi := by
                    exact Int.le_trans h1 (Int.le_trans hnlo' hnhi')
                  obtain ⟨Slo, Sfhi, Spos⟩ :=
                    w_flat_x_sound SEGS E M (kn cs) sb sk (AsanPlanCore.reg cs 12) HKN hfl
                  have hnpos : 0 < bv_unsigned (edenot E (AsanPlanCore.reg cs 12)) := Spos
                  have hWi : estart E (SA db dk) + nhi ≤ 2 ^ 64 := by
                    have h := Whi
                    rw [hlen12, Hnn] at h
                    exact h
                  have hSi : estart E (SA sb sk) + nhi ≤ 2 ^ 64 := by
                    have h := Sfhi
                    rw [Hnn] at h
                    exact h
                  have hus : bv_unsigned (edenot E (AsanPlanCore.reg cs 10))
                      = estart E (SA db dk) := by
                    have h := Whi
                    rw [hlen12] at h
                    rw [hsd, u_lit64]
                    exact u_small_id _ ⟨Wlo, by omega⟩
                  have husr : bv_unsigned (edenot E (AsanPlanCore.reg cs 11))
                      = estart E (SA sb sk) := by
                    have h := Sfhi
                    rw [hss, u_lit64]
                    exact u_small_id _ ⟨Slo, by omega⟩
                  have hd : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                      = estart E (SA db dk) := hus
                  have hs : ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                      = estart E (SA sb sk) := husr
                  have hdisj : ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int)
                        + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                        ≤ ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int) ∨
                      ((edenot E (AsanPlanCore.reg cs 11)).toNat : Int)
                        + bv_unsigned (edenot E (AsanPlanCore.reg cs 12))
                        ≤ ((edenot E (AsanPlanCore.reg cs 10)).toNat : Int) := by
                    rcases hapart with h | h
                    · left
                      rw [hd, hs]
                      exact h
                    · right
                      rw [hd, hs]
                      exact h
                  obtain ⟨bs, Hlbs, Hrd, HKC⟩ :=
                    copy_facts_sound SEGS E M (kn cs) sb db nhi.toNat sk dk nhi kc HKN Hcf
                      hnhi0 (Nat.le_refl _) Slo hSi Wlo hWi
                  have hbslen : (bs.length : Int) = nhi := by
                    rw [Hlbs]
                    exact Int.toNat_of_nonneg hnhi0
                  refine hstep (kc ++ kn_havoc k0 db dk (AsanPlanCore.reg cs 12)) bs
                    ?_ ?_ ?_ hdisj ?_ Hn
                  · rw [Hlbs, Hnn]
                  · rw [hss, Hlbs]
                    exact Hrd
                  · have h := Wst bs.length
                      (by rw [Hlbs, hlen12, Hnn, Int.toNat_of_nonneg hnhi0]; exact Int.le_refl _)
                    rwa [← hsd] at h
                  · intro K hK
                    rcases List.mem_append.mp hK with hK | hK
                    · refine HKC (wbytes M (edenot E (AsanPlanCore.reg cs 10)) bs) ?_ K hK
                      rw [show Z_to_bv 64 (estart E (SA db dk))
                            = edenot E (AsanPlanCore.reg cs 10) from hsd.symm,
                          show nhi.toNat = bs.length from Hlbs.symm]
                      refine rdn_wbytes_hit SEGS bs M (edenot E (AsanPlanCore.reg cs 10)) ?_
                      show bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) + (bs.length : Int)
                          ≤ ((2 ^ 64 : Nat) : Int)
                      rw [← two64_eq_natCast, hus, hbslen]
                      show estart E (SA db dk) + nhi ≤ 2 ^ 64
                      exact hWi
                    · exact HAVOC bs (by rw [Hlbs, Hnn]) hnpos K hK
                · exact HSRC Hn
              · exact HSRC Hn
            · exact HSRC Hn
            all_goals first
              | exact HSRC Hn
              | exact absurd Hn (by simp)

  split at Hn
  all_goals first
    | (rename_i _ _ _ _ nlo nhi dhi shi hnlo hnhi hdhi hshi
       exact MAIN nlo nhi dhi shi hnlo hnhi hdhi hshi Hn)
    | exact absurd Hn (by simp)

/-- `check_sound`'s `node_x_sound` at `XIMemcpy`: one `intro args` away from
    `summary_copy_sound`.

    INTEGRATION: this takes `(HSEGS : segs_wr_ok SEGS)` as a leading
    parameter, right after `SEGS_wx`, because `summary_copy_sound` does.
    `check_sound` passes `node_x_sound` as a hypothesis, so `segs_wr_ok SEGS`
    has to be in scope at that assembly site. -/
theorem node_x_sound_XIMemcpy (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HSEGS : segs_wr_ok SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : copy_spec SEGS (A.x_imemcpy)) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XIMemcpy := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XIMemcpy args
      = fun cs => summary_copy A SEGS nx0 cs (A.x_imemcpy) := funext (fun cs => rfl)
  rw [hx]
  exact summary_copy_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HSEGS HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull (A.x_imemcpy) SUM

/-- `check_sound`'s `node_x_sound` at `XMemcpy`: the same summary at the
    non-internal entry point (`A.x_memcpy`).  Takes `segs_wr_ok SEGS` too. -/
theorem node_x_sound_XMemcpy (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_wx : wx_segs_nowrap SEGS) (HSEGS : segs_wr_ok SEGS) (HULL_ok : hull_okP A)
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte),
      env_agree nx0 E E' → SINV E M → SINV E' M)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (SUM : copy_spec SEGS (A.x_memcpy)) :
    x_stmt SEGS A nx0 LIMIT SINV argH FS0 xnode.XMemcpy := by
  intro args
  have hx : node_x SEGS A nx0 xnode.XMemcpy args
      = fun cs => summary_copy A SEGS nx0 cs (A.x_memcpy) := funext (fun cs => rfl)
  rw [hx]
  exact summary_copy_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_wx HSEGS HULL_ok SINV_agree
    SINV_frame argH_agree argH_high SEGS_in_hull (A.x_memcpy) SUM

/-!
    COUNT.  LANDED here: 90 — all 12 definitions, 66 lemmas,
    all FIVE routine-summary proofs `summary_fill_sound` /
    `summary_miz_sound` / `summary_istrncpy_sound` / `summary_popfree_sound` /
    `summary_copy_sound`, and all SEVEN part-6 interface theorems
    (`node_x_sound_XIMemset`, `node_x_sound_XMemset`,
    `node_x_sound_XMemIsZero`, `node_x_sound_XIStrncpy`,
    `node_x_sound_XPopFree`, `node_x_sound_XIMemcpy`,
    `node_x_sound_XMemcpy`).  The two bitwise lemmas below are a DEVIATION
    rather than missing work: they are not expressible in this toolchain (see
    the note in the middle of this block).
 `check_sound` receives `node_x_sound` as a hypothesis,
    so `segs_wr_ok SEGS` must be in scope at that assembly site.  Also: the
    bare constructor name is NOT in scope at a use site — write
    `xnode.XIMemcpy`, else `autoImplicit` silently binds it as a variable and
    the statement means nothing.
 Every arm
    ends in one of two lifting lemmas, so the proof is a tree of four leaves:
    * `n` provably `0` → `call_node_sound` with the unchanged knowledge;
    * an all-zero source (`kzero_x`) → `call_node_sound` with a `KZero`
      overlay, the bytes supplied by `rdn_overlay_all` + `wbytes_fill_at`;
    * a literal length with the source known piecewise (`copy_facts`) →
      `call_node_sound` with `kc ++ kn_havoc`, the bytes from
      `copy_facts_sound` and the destination hit from `rdn_wbytes_hit`;
    * everything else → `call_node_sound2`, with the k' split into the fresh
      word entries (`ext_call2_at` + `nth_map_seq` + `rdn_skipn`/
      `rdn_firstn` + `word_to_le_bytes_of_bytes_n`), the transported leading
      blob (`kblob_prefix`, whose `List.find?` yields one `KBlob` re-based at
      the destination and re-`rdn`'d through `rdn_nth`), and the havoc'd old
      knowledge (`know_ok_agree'` + `k0_sound` + `w_know_ok_havoc`, plus the
      `KUnk` introduction when `0 < nlo`).
 This tree's stand-in for "bit `q`
    of the little-endian value" is `RefMemcpyLib.zbN`, and the round trip
    they feed (`Z_to_le_bytes_of_bytes`, `word_to_le_bytes_of_bytes`) is
    They are listed here for completeness, flagged as a
    deviation rather than as missing work:
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
-/


