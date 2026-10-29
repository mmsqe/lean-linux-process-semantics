/-
  * AsanNodesMmA — soundness of the plan checker's mmap (NULL-hint / FIXED-free) and
    mprotect nodes on the spec (refused | granted), obligations M1 [node_mmap2_sound] and M3 [node_mprotect2_sound]
    of AsanNodesIface.  Generic material: AsanNodesMmLib

    ** AsanNodesMmA — M1 / M3 of [AsanNodesIface]

       The proofs re-establish cs_ok per arm.  Every arm of
       [Mmap.mmap_spec] / [Mprotect.mprotect_spec] is
       [alt (errno ENOMEM) (grant)], so each node has the two children
       REFUSED ([APC.refuse]: a0 := -12, pc+4, model unchanged) and GRANTED,
       assembled with [SpinAlg.srz_alt2] over the index type
       [errno + grant-witness]; the grant witness (exactness) comes from
       [APC.gap_ok] via [AsanPlacement.free_gap_of_totals] (NULL hint) or is
       the fixed address itself.

  STRUCTURE (section by section):

    - `Section Nodes` opens the standard PARAMETER BLOCK of `AsanNodesIface`
      (quoted in that file's header: `SEGS A nx0 LIMIT SINV argH FS0` plus
      `SEGS_wx`, `SEGS_in_hull`, `RES_len`, `RES_hull`, `HULL_ok`,
      `SHADOW_ok`, `argH_high`, `argH_agree`, `SINV_frame`, `SINV_agree`) and
      adds `PLACEMENT : placement_policy` (the NULL-hint grant nodes of
      `AsanNodesMmLib` take it; see `AsanCeil`).  Then ~120 `Let` aliases
      instantiate the `AsanNodesMmLib` Section-`Nodes` lemmas (part 11 of that
      file) at the block's parameters.
    - §7b  (:177) the NULL-hint node (arms P / A / B0 / B), the spec:
           refused | granted — `mmap_null_sound2`.
    - §11  (:491) mprotect of a slice of a PROT_NONE entry, the spec:
           refused | granted — `node_mprotect_sound2`.
    - §12  (:653-:886) MAP_FIXED wholly inside ONE tracked entry (arms E / F /
           G), the spec: refused-kept | ok | refused-destroyed — `slarm_of`,
           `eu_sub`, `eu_add`, `dest_cases_complete`, `mmap_fixed_in_sound3`,
           `node_mmapin_sound`.
    - §13  (:582-:950) the obligations M1 / M3 as declared by
           `AsanNodesIface`: `mmap_gate_sound`, `node_mmap2_sound`,
           `node_mprotect2_sound`, and the three `_OBL` theorems.
 M2 is
  the three-child MAP_FIXED-inside-one-entry node, so its proofs rest on the
  M1 / M3 material (the `_OBL` shape, `mmap_gate_sound`, the Slice family
  `slice_args` / `slice_cs1_ok` / `dest_cs1_ok` / `slarm_of` / `dest_cases` /
  `eu_sub` / `eu_add` / `dest_cases_complete`) plus `srz_mmap_fixedin_lazy`
  in `AsanNodesLibE`; see §12 below for the three structural devices this tree
  needed (a standalone destroyed-child lemma, `def`s for the per-arm
  `prot` / `flags` literals, and the OK child's `slice_post` built at the
  concrete spec model).
  The seven declarations that need none of part 11: `mmap_gate_sound` is pure
  `Option` / `reg_lit` case analysis; `eu_sub` / `eu_add` are `mkAlu_denot` +
  `u_sub64` / `u_add64` + a `mod 2^64` collapse; `slarm_of` is the three-arm
  `match` on `fixed_in_arm` once the `slarm` type exists; `dest_cases_complete` is
  `lin_ge0_sound` (`AxSymExec3Sound`) read against the `if`-cascade that
  builds `APC.dest_cases`; `node_mmap2_sound` / `node_mmap2_sound_OBL` /
  `node_mprotect2_sound_OBL` are `unfold` + the node's own `_sound` lemma.
  NOTES.
  - SECTION VARIABLES.   - declarations (20): the private state `sanitySt`; the four
    `by decide` checks `gate_sanity_accept`, `gate_sanity_reject_sysno`,
    `gate_sanity_reject_flags`, `dest_cases_sanity_full`; and the seven M2
    devices `fixedInKinds`, `fixedInProt`, `fixedInFlags`, `mmap_destroyed_cont`
    plus the arithmetic plumbing `int_add_congr`, `int_add_le_congr`,
    `int_add_lt_two64_congr`, `one_le_sub`, `zero_le_sub`, `sub_le_two64m1`,
    `sub_lt_two64`, `two64m1_lt`, `sub_eq_zero`, `bv_unsigned_Z_to_bv64`,
    `word_eq_of_bv_unsigned`.  Each declaration is flagged
    at its site.
 A `match` there is generalised over
    every hypothesis whose type mentions the scrutinee (so `H13` came out as
    `reg_lit cs 13 = some (match arm, H12 with …)`), which then fails to unify
    with the arm's own equation; a plain `def` is definitionally the same
    `match` and does not generalise.
  - the arithmetic plumbing lemmas (`int_add_congr` and friends) exist because
    the node's context is large enough that a bare `rw` / `congrArg` on the
    same steps overflows the elaborator's stack; they are
    applied, never re-derived, in the node.
  - `mmap_null_sound2` / `node_mprotect_sound2` (this stretch) are transcribed
    arm by arm from .     * the M1 chain (`mmap_fixed_grant_sound2` / `mmap_fixed_free_sound2` /
      `node_mmap2_sound`) added three more measured devices:
      - the fixed grant's VISIBLE arms go through
        `AsanNodesMmLib.vis_add_slice_ok` — the fixed-hint twin of
        `vis_add_sound` (it takes `FULL'` / `model'` and the four-conjunct
        `NEW`), so the `vis_add_sound'` + `know_ok_unhide'` +
        `hid_cons_sub` / `hid_hull` route is not needed at all.  What it does
        need is `kimg_in_hull A (kn (fixed_cs1 …))`, which is
        `kimg_in_hull_app` of the shadow facts (pure: `kimg_in_hull_pure`
        plus `List.mem_flatMap` into `shadow_facts`, whose two members are
        `KWr` / `KZero`) and `kimg_clip_in_hull`;
      - **`split at Hn` splits the OUTER `match` of `node_mmap2` only**, and
        an `Int`-literal arm split does NOT give the caller an equation for
        `prot` / `flags` unless the split is applied to the *inner* match.  The
        working recipe is `split at Hn` (the gate) → `split at Hn` (the
        `Option`-valued `let g`) → `split at heq` (the `prot, flags` match);
        only the third one substitutes `prot` / `flags` into the hypotheses, so
        `H12` / `H13` become the arm's literals;
      - `GM.2 x hx` (`grant_mem`'s second conjunct, bounds in
        `bv_unsigned (Z_to_bv 64 nZ)`) overflows the stack when unified against
        a `hx` spelled with `nZ = page_round_up_Z …`.  Restate the bound first
        (`have hx' := hx; rw [← Un] at hx'`) and pass `hx'`; note
        `simp only [← Un]` LOOPS (the pattern `nZ` occurs inside
        `Z_to_bv 64 nZ`), so the `rw` form is the one that works.
    * **`omega` can STACK-OVERFLOW in this context** (the whole file aborts):
      with the `% 4096`-style hypotheses of `slice_args` / `mmap_len_sound` in
      scope it aborts deterministically, exactly the poisoning documented in
but as a hard crash rather than a failure.  Every
      arithmetic step in these two proofs is therefore
      `Int.le_trans` / `Int.add_le_add_left` / `Int.lt_of_lt_of_le` by hand.
      `simp only [hbvnZ]`-style rewrites of the `u64_lit` bound are used
      instead of `omega` for the same reason.
  - Word hygiene: this file contains no proof hole and no extra postulate.
-/

import LinuxSem.Common.AsanNodesLibE
import LinuxSem.Common.AsanNodesMmLib
import LinuxSem.Common.AsanNodesIface
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AsanNodesMmA

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
open LinuxSem.Common.RocqSpelling
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
open LinuxSem.Common.AsanNodesIface

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The entry FP state. -/
local instance asannodesmma_fx : PropExec.FPState := PropExec.fx0

/-! ## 13. The obligations M1 / M3 of `AsanNodesIface` — the gate

    The gate is what both node dispatches look at first: it fixes `a7 = 222`,
    `a4 = -1`, `a5 = 0` and reads `(prot, flags, a0 is literal 0?)` out of
    `a1`, `a2`, `a3`.  The proof is the case analysis the two node proofs then
    do once, in the shape the `*_sound` lemmas expect: the *only* surviving
    arm of `APC.mmap_gate`'s `match` is the one whose five `reg_lit`s have the
    required literals. -/

/-- `mmap_gate_sound`: an accepted gate pins all five argument
    registers (and the NULL hint to a literal 0). -/
theorem mmap_gate_sound (cs : acs) (prot flags : Int) (isnull : Bool)
    (Hg : mmap_gate cs = some (prot, flags, isnull)) :
    reg_lit cs 17 = some 222 ∧ reg_lit cs 12 = some prot ∧ reg_lit cs 13 = some flags
      ∧ reg_lit cs 14 = some (two64 - 1) ∧ reg_lit cs 15 = some 0
      ∧ (isnull = true → reg_lit cs 10 = some 0) := by
  -- `APC.mmap_gate` is a five-scrutinee `match`; splitting it in the
  -- hypothesis leaves exactly one live arm (every other one forces
  -- `none = some …`), and that arm's split hypotheses are the six conjuncts.
  unfold mmap_gate at Hg
  repeat' split at Hg
  all_goals try simp_all

/-! ### `by decide` checks on the two checker definitions

    The  file declares no definitions of its own, so it carries no
    sanity goals.  These are added per the repository's "definition of done"
    convention: `mmap_gate_sound` (above) and `dest_cases_complete` (below)
    are the two lemmas that *characterise* `APC.mmap_gate` / `APC.dest_cases`,
    so a silent drift in either checker would otherwise invalidate the whole
    M1 / M2 / M3 node chain with no type error anywhere.

    Both start from the empty checker state and write only the registers
    under test (`set_reg`), so they are readable as "the gate / the case
    generator on a blank state". -/

/-- The empty checker state with registers `0..17` present (all `ELit 0`). -/
private def sanitySt : acs :=
  ACS (mk_ss 0 (List.replicate 18 (.ELit 0)) [] 0) [] 0 0 0 [] [] 0 (.ELit 0) .FdStd false

/-- An accepted gate: `a7 = 222`, `a1 = 3`, `a2 = 34`, `a3 = -1`, `a4 = 0`,
    `a0 = 0` reads back as `(prot, flags, isnull) = (3, 34, true)`. -/
theorem gate_sanity_accept :
    mmap_gate (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg sanitySt 17 (.ELit 222))
        12 (.ELit 3)) 13 (.ELit 34)) 14 (.ELit (two64 - 1))) 15 (.ELit 0)) 10 (.ELit 0))
      = some (3, 34, true) := by decide

/-- The gate is not open on a wrong syscall-number literal (`a7 = 223`). -/
theorem gate_sanity_reject_sysno :
    mmap_gate (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg sanitySt 17 (.ELit 223))
        12 (.ELit 3)) 13 (.ELit 34)) 14 (.ELit (two64 - 1))) 15 (.ELit 0)) 10 (.ELit 0))
      = none := by decide

/-- The gate is not open unless `a3` is the literal `2^64 - 1`. -/
theorem gate_sanity_reject_flags :
    mmap_gate (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg sanitySt 17 (.ELit 222))
        12 (.ELit 3)) 13 (.ELit 34)) 14 (.ELit 0)) 15 (.ELit 0)) 10 (.ELit 0))
      = none := by decide

/-! ## 12. Pure facts for the destroyed children

    The mkdir-like three-resolution node of M2 generates one child state per
    open (left?, right?) case; these are the arithmetic and the completeness
    facts its descendants need.  All three are independent of part 11 of
    `AsanNodesMmLib`, so they are landed here ahead of the node proofs. -/

/-- `eu_sub`: `esub` denotes when the difference does not wrap. -/
theorem eu_sub (E : env) (a b : expr)
    (H : bv_unsigned (edenot E b) ≤ bv_unsigned (edenot E a)) :
    bv_unsigned (edenot E (esub a b)) = bv_unsigned (edenot E a) - bv_unsigned (edenot E b) := by
  unfold esub
  rw [mkAlu_denot]
  show bv_unsigned (edenot E a - edenot E b) = _
  rw [u_sub64, Int.emod_eq_of_lt]
  · simp only [bv_unsigned] at H ⊢
    omega
  · simp only [bv_unsigned] at H ⊢
    have := (edenot E a).isLt
    omega

/-- `eu_add`: `eadd` denotes when the sum does not wrap. -/
theorem eu_add (E : env) (a b : expr)
    (H : bv_unsigned (edenot E a) + bv_unsigned (edenot E b) < 2 ^ 64) :
    bv_unsigned (edenot E (eadd a b)) = bv_unsigned (edenot E a) + bv_unsigned (edenot E b) := by
  unfold eadd
  rw [mkAlu_denot]
  show bv_unsigned (edenot E a + edenot E b) = _
  rw [u_add64, Int.emod_eq_of_lt]
  · simp only [bv_unsigned] at H ⊢
    omega
  · simp only [bv_unsigned] at H ⊢
    omega

/-- `dest_cases_complete`: the semantically true (left?, right?) case
    is among `APC.dest_cases` — the knowledge either decides each of the two
    containment tests or the checker keeps both outcomes, so the pair that the
    model actually satisfies is always generated.
-/
theorem dest_cases_complete (SEGS : List Segment) (E : env) (M : word → Option byte)
    (cs : acs) (ne : expr) (m : amap) (lne rne : Bool)
    (HK : know_ok SEGS E M (kn cs))
    (Hin1 : bv_unsigned (edenot E m.am_base) ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hin2 : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) ≤
      bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))
    (Hl : lne = decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))))
    (Hr : rne = decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
      bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))) :
    (lne, rne) ∈ dest_cases cs ne m := by
  unfold dest_cases
  dsimp only
  rw [List.mem_flatMap]
  refine ⟨lne, ?_, ?_⟩
  · -- `lne ∈ ls`, three arms of the left `if`-cascade
    by_cases h1 : lin_ge0 (kn cs) [(reg cs 10, -1)] [(m.am_base, 0)] = true
    · -- knowledge proves `mb < a`
      rw [ite_eq_left h1]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have X := lin_ge0_sound SEGS E M (kn cs) [(reg cs 10, -1)] [(m.am_base, 0)] HK h1
      simp only [xt_den, AxSymExec3Sound.uE] at X
      rw [Hl]
      simp only [decide_eq_true_eq]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : (expr_eqb (reg cs 10) m.am_base ||
          lin_ge0 (kn cs) [(m.am_base, 0)] [(reg cs 10, 0)]) = true
      · -- knowledge proves `a <= mb` (by literal equality or by `mb - a >= 0`)
        rw [ite_eq_left h2]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rw [Hl]
        rw [Bool.or_eq_true] at h2
        rcases h2 with h2 | h2
        · rw [expr_eqb_eq _ _ h2]
          simp
        · have X := lin_ge0_sound SEGS E M (kn cs) [(m.am_base, 0)] [(reg cs 10, 0)] HK h2
          simp only [xt_den, AxSymExec3Sound.uE] at X
          simp only [decide_eq_false_iff_not]
          omega
      · -- undecided: both outcomes are generated
        rw [ite_eq_right h2]
        cases lne <;> simp
  · -- `rne ∈ rs.map …`, same three arms on the right tests
    rw [List.mem_map]
    refine ⟨rne, ?_, rfl⟩
    by_cases h1 : lin_ge0 (kn cs) [(m.am_base, -1), (m.am_len, 0)]
        [(reg cs 10, 0), (ne, 0)] = true
    · -- knowledge proves `a + ne < mb + ml`
      rw [ite_eq_left h1]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      have X := lin_ge0_sound SEGS E M (kn cs) [(m.am_base, -1), (m.am_len, 0)]
        [(reg cs 10, 0), (ne, 0)] HK h1
      simp only [xt_den, AxSymExec3Sound.uE] at X
      rw [Hr]
      simp only [decide_eq_true_eq]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : lin_ge0 (kn cs) [(reg cs 10, 0), (ne, 0)] [(m.am_base, 0), (m.am_len, 0)] = true
      · -- knowledge proves `mb + ml <= a + ne`
        rw [ite_eq_left h2]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        have X := lin_ge0_sound SEGS E M (kn cs) [(reg cs 10, 0), (ne, 0)]
          [(m.am_base, 0), (m.am_len, 0)] HK h2
        simp only [xt_den, AxSymExec3Sound.uE] at X
        rw [Hr]
        simp only [decide_eq_false_iff_not]
        omega
      · -- undecided: both outcomes are generated
        rw [ite_eq_right h2]
        cases rne <;> simp

/-- Sanity check: on a blank state (no knowledge, `a1`/`a2`/`a3`
    distinct variables) neither containment test is decided, so
    `APC.dest_cases` generates all four (left?, right?) combinations — the
    four child states `mmap_destroyed` then checks. -/
theorem dest_cases_sanity_full :
    dest_cases (ACS (mk_ss 0 [] [] 0) [] 0 0 0 [] [] 0 (.ELit 0) .FdStd false)
        (.EVar 1) ⟨.EVar 2, .EVar 3, .KRW⟩
      = [(true, true), (true, false), (false, true), (false, false)] := by decide

/-! ## 7b / 11 / 12 / 13 — the node proofs and the obligations

    `slarm_of` below is the type-level half of §12; §12's M2 node
    (`mmap_destroyed_cont`, `mmap_fixed_in_sound3`, `node_mmapin_sound` and
    `node_mmapin_sound_OBL` — the last one next to M1's `_OBL`) comes first,
    then the node proofs of §7b, §13's M1 (`mmap_fixed_grant_sound2` /
    `mmap_fixed_free_sound2` / `node_mmap2_sound` / `node_mmap2_sound_OBL`),
    §11 and M3. -/

/-- The slice arm of the three `MAP_FIXED`-inside-one-entry arms. -/
def slarm_of : fixed_in_arm → AsanNodesMmLib.slarm
  | .ArmE => AsanNodesMmLib.slarm.SlE
  | .ArmF => AsanNodesMmLib.slarm.SlF
  | .ArmG => AsanNodesMmLib.slarm.SlG

/-! ## 12. MAP_FIXED wholly inside ONE tracked entry

    The M2 node: the spec is refused-kept | ok | refused-DESTROYED, so the
    node has THREE children and the dispatch is `srz_mmap_fixedin_lazy`
    (`AsanNodesLibE` §6b) rather than `srz_alt2`.

    Three devices made this tree tractable, all structural (the context of the
    node carries ~70 hypotheses and ~40 `page_round_up_Z`-spelled terms):

    * the DESTROYED child is a standalone lemma, `mmap_destroyed_cont`, stated
      at the killed range `[addr, addr+n)` and fusing the `cs_ok`
      re-establishment (`dest_cs1_ok` over the `(lne, rne)` pair that
      `dest_cases_complete` picks out) with the spec continuation `HKC`.
      Proving it outside the node's context costs ~1 s; the same steps
      inside it were unusable;
    * the per-arm `prot` / `flags` literals are `def`s (`fixedInProt` /
      `fixedInFlags`) instead of inline `match`es: a `match` in a
      *statement* is generalised over every hypothesis mentioning the
      scrutinee (`H12`), and the resulting `match arm, H12 with …` stops
      unifying with the arm's own equation;
    * the OK child's `slice_post` is built at the CONCRETE spec model
      (`fixedin_ok_model prot flags addr n model`) — passing the model as a
      metavariable makes the anonymous constructor generalise the `match`
      in `sp_lazy` / `sp_mat` over it. -/

/-- the `find_containing` kind list of each `MAP_FIXED`-inside arm. -/
def fixedInKinds : fixed_in_arm → List mkind
  | .ArmE => [.KRW, .KNONE, .KNONELAZY]
  | .ArmF => [.KRWLAZY]
  | .ArmG => [.KRW, .KNONE, .KNONELAZY]

/-- the `prot` literal of each `MAP_FIXED`-inside arm . -/
def fixedInProt : fixed_in_arm → Int
  | .ArmG => 0
  | _ => 3

/-- the `flags` literal of each `MAP_FIXED`-inside arm. -/
def fixedInFlags : fixed_in_arm → Int
  | .ArmF => 16434
  | _ => 50

/-- substituting an equal `nZ` under an `Int` sum.  Stated
    as a definition because the rewriting happens in the huge local context of
    the node proof, where a bare `rw`/`congrArg` on the same step overflows the
    elaborator's stack. -/
theorem int_add_congr {a b : Int} (c : Int) (h : a = b) : c + a = c + b := by rw [h]

/-- `1 ≤ a - b` from `b + 1 ≤ a`. -/
theorem one_le_sub {a b : Int} (h : b + 1 ≤ a) : 1 ≤ a - b :=
  (Int.add_le_iff_le_sub (a := (1 : Int)) (b := b) (c := a)).mp
    (by rw [Int.add_comm]; exact h)

/-- `0 ≤ a - b` from `b < a`. -/
theorem zero_le_sub {a b : Int} (h : b < a) : 0 ≤ a - b :=
  Int.le_trans (by decide : (0 : Int) ≤ 1) (one_le_sub (Int.lt_iff_add_one_le.mp h))

/-- `a - b ≤ two64 - 1` from `0 ≤ b` and `a ≤ two64 - 1`. -/
theorem sub_le_two64m1 {a b : Int} (hb : 0 ≤ b) (h : a ≤ two64 - 1) : a - b ≤ two64 - 1 :=
  Int.le_trans (Int.sub_le_self a hb) h

/-- `two64 - 1 < 2^64`. -/
theorem two64m1_lt : two64 - 1 < 2 ^ 64 := by unfold two64; decide

/-- `a - b < 2^64` from `0 ≤ b` and `a ≤ two64 - 1`. -/
theorem sub_lt_two64 {a b : Int} (hb : 0 ≤ b) (h : a ≤ two64 - 1) : a - b < 2 ^ 64 :=
  Int.lt_of_le_of_lt (sub_le_two64m1 hb h) two64m1_lt


/-- `a - b = 0` when `a = b`. -/
theorem sub_eq_zero {a b : Int} (h : a = b) : a - b = 0 := by rw [h, Int.sub_self]

/-- `bv_unsigned` of a `Z_to_bv 64` literal. -/
theorem bv_unsigned_Z_to_bv64 (z : Int) (h1 : 0 ≤ z) (h2 : z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := u64_lit z ⟨h1, h2⟩

/-- word extensionality through `bv_unsigned`. -/
theorem word_eq_of_bv_unsigned (x y : word) (h : bv_unsigned x = bv_unsigned y) : x = y :=
  BitVec.eq_of_toNat_eq (Int.ofNat.inj h)

/-- `c + a ≤ d` from `c + b ≤ d` and `a = b`. -/
theorem int_add_le_congr {a b d : Int} (c : Int) (h : a = b) (H : c + b ≤ d) : c + a ≤ d := by
  rw [h]; exact H

/-- `c + a < 2^64` from `c + b < 2^64` and `a = b`. -/
theorem int_add_lt_two64_congr {a b : Int} (c : Int) (h : a = b) (H : c + b < 2 ^ 64) :
    c + a < 2 ^ 64 := by rw [h]; exact H

/-- the destroyed child of the contained `MAP_FIXED` node,
    fused (the `cs_ok` re-establishment `dest_cs1_ok` + the spec continuation
    `HKC`), stated at the killed range `[addr, addr+n)` so that the node proof
    does not carry the three `dest_*` structures through its own context. -/
theorem mmap_destroyed_cont (SEGS : List Segment) (A : atable) (LIMIT : Int) (nx0 : Nat)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (RES_hullH : AsanNodesMmLib.RES_hull_def SEGS A)
    (cs : acs) (b : expr) (off : Int) (ne : expr) (m : amap) (hole : Bool)
    (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model) (TC : TSet)
    (n : word) (nZ : Int)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hm : m ∈ cs.a_maps) (Hnf : is_fog m = false)
    (Hne : edenot E ne = n) (HUn : bv_unsigned n = nZ)
    (HnZpos : 0 < nZ) (HnZal : nZ % 4096 = 0)
    (Hal : bv_unsigned (edenot E (reg cs 10)) % 4096 = 0)
    (Hin1 : bv_unsigned (edenot E m.am_base) ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hin2 : bv_unsigned (edenot E (reg cs 10)) + nZ ≤
      bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))
    (Hsum : bv_unsigned (edenot E (reg cs 10)) + nZ ≤ CEIL)
    (Hest : estart E (SA b off) = bv_unsigned (edenot E (reg cs 10)))
    (HmC : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ CEIL)
    (Hp0 : 0 ≤ pc cs) (Hp4 : pc cs + 4 < 2 ^ 64)
    (HKC : ∀ (csc : acs) (E' : env) (R' : BvMap word) (FULL' : word → Option byte)
        (model' : Model),
      csc ∈ mmap_destroyed A hole cs b off ne m →
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' csc R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc csc) FULL' model') TC) :
    srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (errno_ret ENOMEM))
      (v_addi (Z_to_bv 64 (pc cs)) 4) (unfill (edenot E (reg cs 10)) n FULL) (seg_rom SEGS))
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10)) n model)) TC := by
  have HCEIL : CEIL < 2 ^ 64 := by unfold CEIL; decide
  have HAlt : bv_unsigned (edenot E (reg cs 10)) < 2 ^ 64 :=
    Int.lt_of_le_of_lt (Int.le_trans (Int.le_add_of_nonneg_right (Int.le_of_lt HnZpos)) Hsum) HCEIL
  have HA64 : bv_unsigned (edenot E (reg cs 10)) ≤ two64 - 1 := by
    have h2 : bv_unsigned (edenot E (reg cs 10)) < (two64 - 1) + 1 := by
      rw [Int.sub_add_cancel]
      exact Int.lt_of_le_of_lt (Int.le_trans (Int.le_add_of_nonneg_right (Int.le_of_lt HnZpos)) Hsum) HCEIL
    exact Int.lt_add_one_iff.mp h2
  have HBC64 : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ two64 - 1 := by
    have h2 : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) < (two64 - 1) + 1 := by
      rw [Int.sub_add_cancel]; exact Int.lt_of_le_of_lt HmC HCEIL
    exact Int.lt_add_one_iff.mp h2
  have HA0 : 0 ≤ bv_unsigned (edenot E (reg cs 10)) := Int.natCast_nonneg _
  have HNe0 : 0 ≤ bv_unsigned (edenot E ne) := Int.natCast_nonneg _
  have HB0 : 0 ≤ bv_unsigned (edenot E m.am_base) := Int.natCast_nonneg _
  have HBC0 : 0 ≤ bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
    Int.le_trans HA0 (Int.le_add_of_nonneg_right HNe0)
  have HneZ : bv_unsigned (edenot E ne) = nZ := Eq.trans (congrArg bv_unsigned Hne) HUn
  have HneW : bv_unsigned n = bv_unsigned (edenot E ne) := by rw [Hne]
  have Hbcnd : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) < 2 ^ 64 :=
    int_add_lt_two64_congr _ HneZ (Int.lt_of_le_of_lt Hsum HCEIL)
  have Hcsc : mmap_destroyed_with A hole cs b off ne m
      (decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))))
      (decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)))
      ∈ mmap_destroyed A hole cs b off ne m := by
    unfold mmap_destroyed
    refine List.mem_map.mpr
      ⟨(decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))),
        decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))), ?_, rfl⟩
    exact dest_cases_complete SEGS E (Mr A argH E cs model FULL) cs ne m _ _ HC.co_know
      Hin1 (int_add_le_congr _ HneZ Hin2) rfl rfl
  have DPo : AsanNodesMmLib.dest_post (edenot E (reg cs 10))
      n model
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        n model) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have DM : AsanNodesMmLib.dest_mem (edenot E (reg cs 10))
      n FULL
      (unfill (edenot E (reg cs 10))
        n FULL) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact MmapSim.unfill_out _ _ _ x (by simpa only [HUn] using hx)
    · intro x hx
      exact AsanNodesMmLib.unfill_in _ _ _ x (by simpa only [HUn] using hx)
  have DH : AsanNodesMmLib.dest_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model m
      (edenot E (reg cs 10)) n
      nZ
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        n model)
      (unfill (edenot E (reg cs 10))
        n FULL) :=
    ⟨HC, Hm, Hnf, HUn, HnZpos, HnZal, Hal, Hin1, Hin2, DPo, DM⟩
  have Hregs' : regs_ok E (sr_upd cs.a_ss.s_regs 10 (.ELit ENOMEM_RET))
      (regupd R 10 (errno_ret ENOMEM)) := by
    refine AsanPlanSound.regs_ok_set_n E cs.a_ss.s_regs R 10 (.ELit ENOMEM_RET)
      (errno_ret ENOMEM) HC.co_regs (by decide) ?_
    rw [AsanNodesMmLib.errno_ret_ENOMEM]
    rfl
  have MROUT' : ∀ x : word, bv_unsigned x < estart E (SA b off) ∨
      estart E (SA b off) + elenZ E ne ≤ bv_unsigned x →
      Mr A argH E cs (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        n model)
        (unfill (edenot E (reg cs 10))
          n FULL) x
      = Mr A argH E cs model FULL x := by
    intro x hx
    refine AsanNodesMmLib.d_MR_out SEGS A LIMIT SINV argH FS0 E cs R FULL model m
      (edenot E (reg cs 10)) n
      _ _ _ DH cs x rfl ?_
    rw [Hest] at hx
    simpa only [elenZ, Hne, HUn] using hx
  have hleft : kentry_ok SEGS E (Mr A argH E cs (AsanNodesLibE.fixedin_destroyed_model
      (edenot E (reg cs 10))
      n model)
      (unfill (edenot E (reg cs 10))
        n FULL))
      (dest_lfact (reg cs 10) m.am_base
        (decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))))) := by
    have U : bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) =
        bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (edenot E m.am_base) :=
      eu_sub E (reg cs 10) m.am_base Hin1
    by_cases hlt : bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))
    · have hl : decide (bv_unsigned (edenot E m.am_base) <
          bv_unsigned (edenot E (reg cs 10))) = true := by
        simpa only [decide_eq_true_eq] using hlt
      rw [dest_lfact, ite_eq_left hl]
      show 1 ≤ bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) ∧
        bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) ≤ two64 - 1
      rw [U]
      refine ⟨?_, ?_⟩
      · exact Int.add_le_iff_le_sub.mp
          (by rw [Int.add_comm]; exact Int.lt_iff_add_one_le.mp hlt)
      · exact Int.le_trans (Int.sub_le_self _ HB0) HA64
    · have hl : ¬ (decide (bv_unsigned (edenot E m.am_base) <
          bv_unsigned (edenot E (reg cs 10))) = true) := by
        simpa only [decide_eq_true_eq] using hlt
      have hle : bv_unsigned (edenot E (reg cs 10)) ≤ bv_unsigned (edenot E m.am_base) :=
        Int.not_lt.mp hlt
      have heq : bv_unsigned (edenot E (reg cs 10)) = bv_unsigned (edenot E m.am_base) :=
        Int.le_antisymm hle Hin1
      rw [dest_lfact, ite_eq_right hl]
      show 0 ≤ bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) ∧
        bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) ≤ 0
      rw [U, heq, Int.sub_self]
      exact ⟨Int.le_refl 0, Int.le_refl 0⟩
  have hright : kentry_ok SEGS E (Mr A argH E cs (AsanNodesLibE.fixedin_destroyed_model
      (edenot E (reg cs 10))
      n model)
      (unfill (edenot E (reg cs 10))
        n FULL))
      (dest_rfact (reg cs 10) ne m.am_base m.am_len
        (decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)))) := by
    have U1 : bv_unsigned (edenot E (eadd m.am_base m.am_len)) =
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) :=
      eu_add E m.am_base m.am_len (Int.lt_of_le_of_lt HmC HCEIL)
    have U2 : bv_unsigned (edenot E (eadd (reg cs 10) ne)) =
        bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
      eu_add E (reg cs 10) ne Hbcnd
    have U3 : bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) =
        bv_unsigned (edenot E (eadd m.am_base m.am_len)) -
          bv_unsigned (edenot E (eadd (reg cs 10) ne)) :=
      eu_sub E (eadd m.am_base m.am_len) (eadd (reg cs 10) ne)
        (by rw [U1, U2]; exact int_add_le_congr _ HneZ Hin2)
    by_cases hlt : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
    · have hl : decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)) = true := by
        simpa only [decide_eq_true_eq] using hlt
      rw [dest_rfact, ite_eq_left hl]
      show 1 ≤ bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) ∧
        bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) ≤
          two64 - 1
      rw [U3, U1, U2]
      refine ⟨?_, ?_⟩
      · exact Int.add_le_iff_le_sub.mp
          (by rw [Int.add_comm]; exact Int.lt_iff_add_one_le.mp hlt)
      · exact Int.le_trans (Int.sub_le_self _ HBC0) HBC64
    · have hl : ¬ (decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)) = true) := by
        simpa only [decide_eq_true_eq] using hlt
      have hle : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤
          bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
        Int.not_lt.mp hlt
      have heq : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) =
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) :=
        Int.le_antisymm (int_add_le_congr _ HneZ Hin2) hle
      rw [dest_rfact, ite_eq_right hl]
      show 0 ≤ bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) ∧
        bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) ≤ 0
      rw [U3, U1, U2, heq, Int.sub_self]
      exact ⟨Int.le_refl 0, Int.le_refl 0⟩
  have Hcut : know_ok SEGS E (Mr A argH E cs (AsanNodesLibE.fixedin_destroyed_model
      (edenot E (reg cs 10))
      n model)
      (unfill (edenot E (reg cs 10))
        n FULL))
      (kimg_clip A (kn_cutout (kn cs) b off ne)) :=
    know_ok_filter SEGS E _ _ _ (know_ok_cutout SEGS E (Mr A argH E cs model FULL) _ (kn cs)
      b ne off HC.co_know MROUT')
  have Hk' : know_ok SEGS E (Mr A argH E cs (AsanNodesLibE.fixedin_destroyed_model
      (edenot E (reg cs 10))
      n model)
      (unfill (edenot E (reg cs 10))
        n FULL))
      (dest_lfact (reg cs 10) m.am_base
          (decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10)))) ::
        dest_rfact (reg cs 10) ne m.am_base m.am_len
          (decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
            bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))) ::
        kimg_clip A (kn_cutout (kn cs) b off ne)) := by
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact hleft
    · rcases List.mem_cons.mp hK with rfl | hK
      · exact hright
      · exact Hcut K hK
  have h3 : bv_unsigned (edenot E (reg cs 10)) ≤
      bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
    Int.le_add_of_nonneg_right HNe0
  have hhi : bv_unsigned (edenot E (reg cs 10)) +
      bv_unsigned n =
      bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
    (int_add_congr _ HneW)
  have hword : edenot E (esub (reg cs 10) m.am_base) =
      Z_to_bv 64 (bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (edenot E m.am_base)) := by
    have h1 : bv_unsigned (edenot E (esub (reg cs 10) m.am_base)) =
        bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (edenot E m.am_base) :=
      eu_sub E (reg cs 10) m.am_base Hin1
    have h0 : 0 ≤ bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (edenot E m.am_base) := by
      by_cases hlt : bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))
      · exact zero_le_sub hlt
      · have hle : bv_unsigned (edenot E (reg cs 10)) ≤ bv_unsigned (edenot E m.am_base) :=
          Int.not_lt.mp hlt
        have heq : bv_unsigned (edenot E (reg cs 10)) = bv_unsigned (edenot E m.am_base) :=
          Int.le_antisymm hle Hin1
        rw [← heq, Int.sub_self]; exact Int.le_refl 0
    have h2 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E (reg cs 10)) -
        bv_unsigned (edenot E m.am_base))) =
        bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (edenot E m.am_base) :=
      bv_unsigned_Z_to_bv64 _ h0 (sub_lt_two64 HB0 HA64)
    exact word_eq_of_bv_unsigned _ _ (by rw [h1, h2])
  have hbase : edenot E (eadd (reg cs 10) ne) =
      Z_to_bv 64 (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)) := by
    refine word_eq_of_bv_unsigned _ _ ?_
    rw [eu_add E (reg cs 10) ne Hbcnd]
    exact (bv_unsigned_Z_to_bv64 _ HBC0 Hbcnd).symm
  have hword2 : edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne)) =
      Z_to_bv 64 (bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) -
        (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne))) := by
    have U1 : bv_unsigned (edenot E (eadd m.am_base m.am_len)) =
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) :=
      eu_add E m.am_base m.am_len (Int.lt_of_le_of_lt HmC HCEIL)
    have U2 : bv_unsigned (edenot E (eadd (reg cs 10) ne)) =
        bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
      eu_add E (reg cs 10) ne Hbcnd
    have hin2' : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) ≤
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) :=
      int_add_le_congr _ HneZ Hin2
    have h1 : bv_unsigned (edenot E (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))) =
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) -
          (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)) := by
      rw [eu_sub E (eadd m.am_base m.am_len) (eadd (reg cs 10) ne) (by rw [U1, U2]; exact hin2'),
        U1, U2]
    have h0 : 0 ≤ bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) -
        (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)) := by
      by_cases hlt : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
      · exact zero_le_sub hlt
      · have hle : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤
            bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) :=
          Int.not_lt.mp hlt
        have heq : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) =
            bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) :=
          Int.le_antisymm hin2' hle
        rw [← heq, Int.sub_self]; exact Int.le_refl 0
    have h2 : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E m.am_base) +
        bv_unsigned (edenot E m.am_len) -
        (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)))) =
        bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) -
          (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)) :=
      bv_unsigned_Z_to_bv64 _ h0 (sub_lt_two64 HBC0 HBC64)
    exact word_eq_of_bv_unsigned _ _ (by rw [h1, h2])
  have Hpcs : List.map (amap_den E)
      ((if decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10)))
          then [amap.mk m.am_base (esub (reg cs 10) m.am_base) m.am_kind] else [])
        ++ (if decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
              bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))
            then [amap.mk (eadd (reg cs 10) ne) (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))
              m.am_kind] else []))
      = iv_subtract (edenot E m.am_base) (edenot E m.am_len)
          (bv_unsigned (edenot E (reg cs 10)))
          (bv_unsigned (edenot E (reg cs 10)) +
            bv_unsigned n) := by
    rw [hhi, AsanNodesMmLib.iv_subtract_contained (edenot E m.am_base) (edenot E m.am_len)
      (bv_unsigned (edenot E (reg cs 10)))
      (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)) Hin1
      (int_add_le_congr _ HneZ Hin2) h3]
    rw [List.map_append]
    have hL : List.map (amap_den E)
        (if decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10)))
          then [amap.mk m.am_base (esub (reg cs 10) m.am_base) m.am_kind] else [])
        = (if bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))
            then [(edenot E m.am_base,
              Z_to_bv 64 (bv_unsigned (edenot E (reg cs 10)) -
                bv_unsigned (edenot E m.am_base)))] else []) := by
      by_cases hlt : bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))
      · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hlt), ite_eq_left hlt]
        simp only [List.map_cons, List.map_nil, amap_den, hword]
      · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hlt), ite_eq_right hlt]; rfl
    have hR : List.map (amap_den E)
        (if decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
              bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))
          then [amap.mk (eadd (reg cs 10) ne) (esub (eadd m.am_base m.am_len) (eadd (reg cs 10) ne))
            m.am_kind] else [])
        = (if bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
              bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
            then [(Z_to_bv 64 (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne)),
              Z_to_bv 64 (bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) -
                (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne))))]
            else []) := by
      by_cases hlt : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
      · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hlt), ite_eq_left hlt]
        simp only [List.map_cons, List.map_nil, amap_den, hbase, hword2]
      · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hlt), ite_eq_right hlt]; rfl
    rw [hL, hR]
  have Hhp : AsanNodesMmLib.hole_prefix_ok E (edenot E (reg cs 10))
      nZ
      (if hole then [amap.mk (reg cs 10) ne .KHOLE] else []) := by
    cases hole with
    | false => exact Or.inl rfl
    | true => exact Or.inr ⟨reg cs 10, ne, rfl, rfl, by rw [Hne, HUn]⟩
  have HD : cs_ok SEGS A LIMIT SINV argH FS0 E
      (mmap_destroyed_with A hole cs b off ne m
        (decide (bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))))
        (decide (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len))))
      (regupd R 10 (errno_ret ENOMEM))
      (unfill (edenot E (reg cs 10))
        n FULL)
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        n model) := by
    rw [mmap_destroyed_with_eq]
    unfold mmap_destroyed_with_ref
    refine AsanNodesMmLib.dest_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame RES_hullH
      E cs R FULL model m (edenot E (reg cs 10))
      n
      nZ
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        n model)
      (unfill (edenot E (reg cs 10))
        n FULL)
      DH (sr_upd cs.a_ss.s_regs 10 (.ELit ENOMEM_RET)) (regupd R 10 (errno_ret ENOMEM)) _ (pc cs + 4)
      (cs.a_ss.s_next) _ _ Hregs' Hk' Hpcs ?_ Hhp
    intro pc hpc
    rw [List.mem_append] at hpc
    rcases hpc with hpc | hpc
    · by_cases hlt : bv_unsigned (edenot E m.am_base) < bv_unsigned (edenot E (reg cs 10))
      · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hlt)] at hpc
        rw [List.mem_singleton] at hpc
        rw [hpc]
      · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hlt)] at hpc
        simp at hpc
    · by_cases hlt : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <
          bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len)
      · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hlt)] at hpc
        rw [List.mem_singleton] at hpc
        rw [hpc]
      · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hlt)] at hpc
        simp at hpc
  rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4]
  exact HKC _ E (regupd R 10 (errno_ret ENOMEM))
    (unfill (edenot E (reg cs 10))
      n FULL)
    (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
      n model)
    Hcsc ⟨AsanNodesMmLib.env_agree_refl' _ _, AsanNodesMmLib.env_agree_refl' _ _⟩ HD rfl


theorem mmap_fixed_in_sound3 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (hole : Bool) (cs : acs) (arm : fixed_in_arm) (b : expr) (off : Int) (ne : expr)
    (nlo nhi : Int) (m : amap) (csO : acs) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (TA TB TC : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hec : is_ecall_at SEGS cs = true)
    (H17 : reg_lit cs 17 = some 222)
    (H12 : reg_lit cs 12 = some (fixedInProt arm))
    (H13 : reg_lit cs 13 = some (fixedInFlags arm))
    (H14 : reg_lit cs 14 = some (two64 - 1)) (H15 : reg_lit cs 15 = some 0)
    (HFA : fixed_in_args A cs arm = some (b, off, ne, nlo, nhi, m))
    (Hn : mmap_fixed_in A LIMIT cs arm = some csO)
    (HKA : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA)
    (HKB : ∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' csO R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc csO) FULL' model') TB)
    (HKC : ∀ (csc : acs) (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
      csc ∈ mmap_destroyed A hole cs b off ne m →
      env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' csc R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc csc) FULL' model') TC) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)) := by
  obtain ⟨w, Hf, He, Hp0, Hp4⟩ := AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec
  -- ## the argument analysis
  have HEX : fixed_args A cs CEIL = some (b, off, ne, nlo, nhi) ∧
      find_containing (kn cs) cs.a_maps (fixedInKinds arm) b off ne = some m ∧
      (AsanPlanCore.expr_vars_lt (nxt cs) ne &&
        AsanPlanCore.expr_vars_lt (nxt cs) (reg cs 10)) = true := by
    have h := HFA
    rw [fixed_in_args_eq] at h
    unfold fixed_in_args_ref at h
    dsimp only at h
    split at h
    · rename_i b0 off0 ne0 nlo0 nhi0 HFA0
      split at h
      · rename_i m0 Hfind0
        split at h
        · rename_i Hvars0
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          exact ⟨HFA0, Hfind0, Hvars0⟩
        · cases h
      · cases h
    · cases h
  obtain ⟨HFA0, Hfind0, Hvars0⟩ := HEX
  -- ## the slice facts
  obtain ⟨Hm, ⟨Hkind, Hnf⟩, R10, R11, Hlenpos, Hlen64, Hne, hbvnZ, HnZpos, HnZle,
    HnZal, Hal, Hpos, Himg, Hest, Hin1, Hin2, HmC, Hmc, Hrfres, Hov⟩ :=
    AsanNodesMmLib.slice_args SEGS A LIMIT nx0 SINV argH FS0 RES_hull E cs R FULL model
      b off ne nlo nhi _ m (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) HC HFA0
      Hfind0 rfl
  have Hhalt : m_halted model = none := HC.co_halt
  have Hisp : init_sp_ok (m_vmmaps model) := HC.co_wf.2.2.2
  have HnZ0 : 0 ≤ page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) := Int.le_of_lt HnZpos
  have HCEIL : CEIL < 2 ^ 64 := by unfold CEIL; decide
  have Hsum : bv_unsigned (edenot E (reg cs 10)) +
      page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) ≤ CEIL := Int.le_trans Hin2 HmC
  have Hce : bv_unsigned (edenot E (reg cs 10)) +
      page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) ≤ alloc_ceiling :=
    Int.le_trans Hsum (Int.le_of_eq AsanNodesMmLib.CEIL_eq)
  have Hbnd : bv_unsigned (edenot E (reg cs 10)) +
      bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) < 2 ^ 64 := by
    rw [hbvnZ]
    exact Int.lt_of_le_of_lt Hsum HCEIL
  have HAlt : bv_unsigned (edenot E (reg cs 10)) < 2 ^ 64 := by
    refine Int.lt_of_le_of_lt (Int.le_trans (Int.le_add_of_nonneg_right HnZ0) Hsum) HCEIL
  have HA64 : bv_unsigned (edenot E (reg cs 10)) ≤ two64 - 1 := by
    have h2 : bv_unsigned (edenot E (reg cs 10)) < (two64 - 1) + 1 := by
      rw [Int.sub_add_cancel]; exact HAlt
    exact Int.lt_add_one_iff.mp h2
  have HBC64 : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) ≤ two64 - 1 := by
    have h2 : bv_unsigned (edenot E m.am_base) + bv_unsigned (edenot E m.am_len) < (two64 - 1) + 1 := by
      rw [Int.sub_add_cancel]
      exact Int.lt_of_le_of_lt HmC HCEIL
    exact Int.lt_add_one_iff.mp h2
  -- ## the refused continuation
  have HA : srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (errno_ret ENOMEM))
      (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA :=
    AsanNodesMmLib.refuse_cont SEGS A LIMIT nx0 SINV argH FS0 cs E R FULL model TA HC Hp0 Hp4 HKA
  -- ## the destroyed continuation
  have CONTC : srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (errno_ret ENOMEM))
      (v_addi (Z_to_bv 64 (pc cs)) 4)
      (unfill (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL)
      (seg_rom SEGS))
      (AsanNodesLibE.fixedin_destroyed_model (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)) TC :=
    mmap_destroyed_cont SEGS A LIMIT nx0 SINV argH FS0 argH_high SINV_frame RES_hull cs b off ne
      m hole E R FULL model TC
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
      (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
      HC Hm Hnf Hne hbvnZ HnZpos HnZal Hal Hin1 Hin2 Hsum Hest HmC Hp0 Hp4 HKC
  have R17 : getr R 17 = Z_to_bv 64 222 :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 222
      HC (by decide) H17).1
  have R14 : getr R 14 = Z_to_bv 64 (-1) := by
    have h := (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 14
      (two64 - 1) HC (by decide) H14).1
    rw [AsanNodesMmLib.Z_to_bv64_m1 (two64 - 1) rfl] at h
    exact h
  have R15 : getr R 15 = Z_to_bv 64 0 :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 15 0
      HC (by decide) H15).1
  -- ## the arms
  cases arm with
  | ArmE =>
    have HfindE : find_containing (kn cs) cs.a_maps [mkind.KRW, mkind.KNONE, mkind.KNONELAZY] b off ne = some m := Hfind0
    have R12 : getr R 12 = Z_to_bv 64 3 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 3
        HC (by decide) H12).1
    have R13 : getr R 13 = Z_to_bv 64 50 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 13 50
        HC (by decide) H13).1
    obtain ⟨hbudE, HnE⟩ : budget_ok LIMIT cs nhi = true ∧ vis_add A LIMIT
        (ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
            (kimg_clip A (kn_unfill (kn cs) b off ne)) cs.a_ss.s_next)
          (rekind cs.a_maps m) cs.a_totsz cs.a_ylo (cs.a_eager + nhi) cs.a_vis
          cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
        (reg cs 10) ne
        (.KWr (SA b off) ne :: .KZero (SA b off) ne ::
          kimg_clip A (kn_unfill (kn cs) b off ne)) = some csO := by
      have h := Hn
      rw [mmap_fixed_in_eq] at h
      unfold mmap_fixed_in_ref at h
      unfold fixed_in_args_ref at h
      rw [HFA0] at h
      simp only [] at h
      rw [HfindE] at h
      simp only [] at h
      rw [Hvars0] at h
      simp only [ite_true] at h
      split at h
      · rename_i hb
        exact ⟨hb, h⟩
      · simp at h
    have HbudgetE : cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
      unfold budget_ok at hbudE
      simpa only [decide_eq_true_eq] using hbudE
    have HnotF : m.am_kind ≠ .KRWLAZY := by
      intro hk
      rw [hk] at Hkind
      exact absurd Hkind (by decide)
    have CONTB : ∀ (model' : Model) (FULL' : word → Option byte),
        AsanNodesMmLib.slice_post .SlE (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model model' →
        AsanNodesMmLib.slice_mem .SlE (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL FULL' →
        m_fs model' = m_fs model →
        srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (edenot E (reg cs 10)))
          (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB := by
      intro model' FULL' HSPo HSM Hfs
      have Hsh : AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlE m
          (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' :=
        { sh_C := HC, sh_m := Hm, sh_nf := Hnf, sh_Un := hbvnZ, sh_pos := HnZpos,
          sh_nal := HnZal, sh_al := Hal, sh_in1 := Hin1, sh_in2 := Hin2,
          sh_post := HSPo, sh_mem := HSM,
          sh_F := (fun h => absurd h (by decide)), sh_nF := (fun _ hk => HnotF hk) }
      have Hregs' : regs_ok E cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10))) :=
        AsanNodesMmLib.regs_ok_regupd_same E cs.a_ss.s_regs R 10 (edenot E (reg cs 10))
          HC.co_regs (by decide) R10
      have Hk' : know_ok SEGS E (Mr A argH E cs model' FULL')
          (kimg_clip A (kn_unfill (kn cs) b off ne)) := by
        refine AsanNodesMmLib.kn_unfill_clip_ok SEGS A E _ _ (kn cs) b off ne HC.co_know ?_ ?_
        · rw [Hest]; exact Himg
        · intro x hx
          exact AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlE m
            (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
            _ _ _ Hsh cs x rfl (by rw [Hest] at hx; simpa only [elenZ, Hne, hbvnZ] using hx)
      have HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E
          (ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
              (kimg_clip A (kn_unfill (kn cs) b off ne)) cs.a_ss.s_next)
            (rekind cs.a_maps m) cs.a_totsz cs.a_ylo (cs.a_eager + nhi) cs.a_vis
            cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
          (regupd R 10 (edenot E (reg cs 10))) FULL' model' :=
        AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame E cs R FULL
          model .SlE m (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' Hsh
          cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10)))
          (kimg_clip A (kn_unfill (kn cs) b off ne)) (pc cs + 4) cs.a_ss.s_next nhi
          Hregs' Hk' HnZle (fun _ => HbudgetE)
      have Hlo : 0 ≤ bv_unsigned (edenot E (reg cs 10)) := Int.natCast_nonneg _
      have HC2 : cs_ok SEGS A LIMIT SINV argH FS0 E csO
          (regupd R 10 (edenot E (reg cs 10))) FULL' model' := by
        refine AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT nx0 SINV argH FS0 SEGS_in_hull HULL_ok
          SHADOW_ok argH_high E _ csO (reg cs 10) b off ne
          (regupd R 10 (edenot E (reg cs 10))) FULL' model'
          (bv_unsigned (edenot E (reg cs 10)))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) HC1 HnE ?_ rfl Hest ?_ Hlo HnZpos
          Hsum ?_
        · simpa only [kn, mk_ss, rekind] using (kimg_clip_in_hull A (kn_unfill (kn cs) b off ne))
        · simp only [elenZ, Hne, hbvnZ]
        · intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          refine ⟨?_, ?_, ?_, ?_⟩
          · have hmaps := AsanNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlE m
              (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
              _ _ _ Hsh x ⟨hx1, hx2⟩
            rw [HSPo.sp_maps]
            exact hmaps
          · simpa only [AsanNodesMmLib.sl_nn] using
              (AsanNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlE m
                (edenot E (reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
                _ _ _ Hsh x ⟨hx1, hx2⟩)
          · rcases Bool.eq_false_or_eq_true (argH E x) with h | h
            · exact absurd (Int.lt_of_le_of_lt (argH_high E x h)
                (Int.lt_of_lt_of_le hx2 Hsum)) (Int.lt_irrefl CEIL)
            · exact h
          · have hx2' : bv_unsigned x < bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) := by
              rw [hbvnZ]; exact hx2
            simpa only [AsanNodesMmLib.sl_nn, Bool.false_eq_true, ite_false] using HSM.2 x ⟨hx1, hx2'⟩
      obtain ⟨_nh, _hx, hEcs⟩ :=
        AsanNodesMmLib.vis_add_inv A LIMIT _ (reg cs 10) ne _ csO HnE
      have Hpc : pc csO = pc cs + 4 := by rw [hEcs]; rfl
      rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
      exact HKB E (regupd R 10 (edenot E (reg cs 10))) FULL' model'
        ⟨AsanNodesMmLib.env_agree_refl' _ _, AsanNodesMmLib.env_agree_refl' _ _⟩ HC2 Hfs
    have Hbud : (3 : Int) = 3 → Sys.Mm.Mmap.mmap_fixed_rw_budget_ok (Z_to_bv 64 50) model
        (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true := by
      intro _
      refine BackingAlgebra.mmap_fixed_rw_budget_ok_commit_intro (Z_to_bv 64 50) model
        (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
        AsanNodesMmLib.mmap_noreserve_b_32 HC.co_wf ?_
      have hsl : vm_backing_used model + nhi ≤ (m_vmmaps model).vm_limit :=
        AsanNodesMmLib.budget_slack SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model nhi HC hbudE
      refine Int.le_trans (b := vm_backing_used model + page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) ?_ ?_
      · exact Int.add_le_add_left Hov (vm_backing_used model)
      · exact Int.le_trans (Int.add_le_add_left HnZle (vm_backing_used model)) hsl
    refine AsanNodesLibE.srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
      3 (Z_to_bv 64 50) (edenot E (reg cs 10))
      (bv_unsigned (edenot E (reg cs 11))) TA TB TC Hf He Hhalt R17 (Or.inr rfl)
      (AsanNodesMmLib.mmap_flags_core_32) R10 Hal Hpos R11 Hlenpos Hce Hisp R12 R13 R14 R15
      _ rfl Hrfres Hmc Hbud HA ?_ CONTC
    · rw [ite_eq_right (by decide : ¬ ((3 : Int) = 0))]
      refine CONTB (AsanNodesLibE.fixedin_ok_model 3 (Z_to_bv 64 50) (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)
        (zfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
      · unfold AsanNodesLibE.fixedin_ok_model with_mmap_replacement
        rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_32]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact MmapSim.zfill_out _ _ _ x (by simpa only [hbvnZ] using hx)
        · intro x hx
          simpa only [AsanNodesMmLib.sl_nn, Bool.false_eq_true, ite_false] using
            (AsanNodesMmLib.zfill_in _ _ _ x (by simpa only [hbvnZ] using hx))
  | ArmF =>
    have HfindF : find_containing (kn cs) cs.a_maps [mkind.KRWLAZY] b off ne = some m := Hfind0
    have HkindF : m.am_kind = .KRWLAZY := by
      have h : m.am_kind ∈ [mkind.KRWLAZY] := Hkind
      simpa using h
    have R12 : getr R 12 = Z_to_bv 64 3 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 3
        HC (by decide) H12).1
    have R13 : getr R 13 = Z_to_bv 64 16434 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 13 16434
        HC (by decide) H13).1
    have HnF : csO = ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
          (kimg_clip A (kn_rezero (kn cs) b off ne)) cs.a_ss.s_next)
        cs.a_maps cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
        cs.a_brk cs.a_fd cs.a_tidset := by
      have h := Hn
      rw [mmap_fixed_in_eq] at h
      unfold mmap_fixed_in_ref at h
      unfold fixed_in_args_ref at h
      rw [HFA0] at h
      simp only [] at h
      rw [HfindF] at h
      simp only [] at h
      rw [Hvars0] at h
      simp only [ite_true] at h
      exact (Option.some.inj h).symm
    have CONTB : ∀ (model' : Model) (FULL' : word → Option byte),
        AsanNodesMmLib.slice_post .SlF (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model model' →
        AsanNodesMmLib.slice_mem .SlF (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL FULL' →
        m_fs model' = m_fs model →
        srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (edenot E (reg cs 10)))
          (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB := by
      intro model' FULL' HSPo HSM Hfs
      have Hsh : AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlF m
          (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' :=
        { sh_C := HC, sh_m := Hm, sh_nf := Hnf, sh_Un := hbvnZ, sh_pos := HnZpos,
          sh_nal := HnZal, sh_al := Hal, sh_in1 := Hin1, sh_in2 := Hin2,
          sh_post := HSPo, sh_mem := HSM,
          sh_F := (fun _ => HkindF), sh_nF := (fun h _ => absurd rfl h) }
      have Hregs' : regs_ok E cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10))) :=
        AsanNodesMmLib.regs_ok_regupd_same E cs.a_ss.s_regs R 10 (edenot E (reg cs 10))
          HC.co_regs (by decide) R10
      have Hk' : know_ok SEGS E (Mr A argH E cs model' FULL')
          (kimg_clip A (kn_rezero (kn cs) b off ne)) := by
        refine AsanNodesMmLib.kn_rezero_clip_ok SEGS A E _ _ (kn cs) b off ne HC.co_know ?_ ?_ ?_
        · rw [Hest]; exact Himg
        · intro x hx
          exact AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlF m
            (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
            _ _ _ Hsh cs x rfl (by rw [Hest] at hx; simpa only [elenZ, Hne, hbvnZ] using hx)
        · intro x hx1 hx2 hdef
          have hx : bv_unsigned (edenot E (reg cs 10)) ≤ bv_unsigned x ∧
              bv_unsigned x < bv_unsigned (edenot E (reg cs 10)) +
                page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) := by
            refine ⟨?_, ?_⟩
            · rw [← Hest]; exact hx1
            · have h := hx2
              simp only [elenZ, Hest, Hne, hbvnZ] at h
              exact h
          have hvis := AsanNodesMmLib.sl_vis_in_F SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlF m
            (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
            (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' Hsh rfl cs x rfl hx
          unfold Mr mrestrict hid at hdef ⊢
          dsimp only at hdef ⊢
          simp only [hvis]
          cases harg : argH E x with
          | true =>
            refine absurd ?_ hdef
            simp [harg]
          | false =>
            cases hv : vis A E cs model x with
            | true =>
              have hx' : bv_unsigned (edenot E (reg cs 10)) ≤ bv_unsigned x ∧
                  bv_unsigned x < bv_unsigned (edenot E (reg cs 10)) +
                    bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) := by
                refine ⟨hx.1, ?_⟩
                rw [hbvnZ]; exact hx.2
              simpa only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
                AsanNodesMmLib.sl_nn] using HSM.2 x hx'
            | false =>
              exact absurd (by simp only [harg, hv, Bool.not_false, Bool.false_or, ite_true]) hdef
      have HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E
          (ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
              (kimg_clip A (kn_rezero (kn cs) b off ne)) cs.a_ss.s_next)
            (AsanNodesMmLib.slMaps cs .SlF m) cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis
            cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
          (regupd R 10 (edenot E (reg cs 10))) FULL' model' :=
        AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame E cs R FULL
          model .SlF m (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' Hsh
          cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10)))
          (kimg_clip A (kn_rezero (kn cs) b off ne)) (pc cs + 4) cs.a_ss.s_next nhi
          Hregs' Hk' HnZle (fun HH => absurd HH (by decide))
      have Hpc : pc csO = pc cs + 4 := by rw [HnF]; rfl
      rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
      exact HKB E (regupd R 10 (edenot E (reg cs 10))) FULL' model'
        ⟨AsanNodesMmLib.env_agree_refl' _ _, AsanNodesMmLib.env_agree_refl' _ _⟩
        (by rw [HnF]; exact HC1) Hfs
    have Hbud : (3 : Int) = 3 → Sys.Mm.Mmap.mmap_fixed_rw_budget_ok (Z_to_bv 64 16434) model
        (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true := by
      intro _
      refine BackingAlgebra.mmap_fixed_rw_budget_ok_recommit_intro (Z_to_bv 64 16434) model
        (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
        AsanNodesMmLib.mmap_noreserve_b_4032 HC.co_wf Hal ?_ ?_ ?_ ?_
      · simp only [page_size, hbvnZ]; exact HnZal
      · simpa only [hbvnZ] using HnZpos
      · simpa only [hbvnZ] using Int.le_trans Hsum (Int.le_of_lt HCEIL)
      · exact AsanNodesMmLib.vm_backing_used_limit (allowA A E cs) model HC.co_minv
          (A_wf_allowA A E cs)
    refine AsanNodesLibE.srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
      3 (Z_to_bv 64 16434) (edenot E (reg cs 10))
      (bv_unsigned (edenot E (reg cs 11))) TA TB TC Hf He Hhalt R17 (Or.inr rfl)
      (AsanNodesMmLib.mmap_flags_core_4032) R10 Hal Hpos R11 Hlenpos Hce Hisp R12 R13 R14 R15
      _ rfl Hrfres Hmc Hbud HA ?_ CONTC
    · refine CONTB (AsanNodesLibE.fixedin_ok_model 3 (Z_to_bv 64 16434) (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)
        (zfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
      · unfold AsanNodesLibE.fixedin_ok_model with_mmap_replacement
        rw [AsanNodesMmLib.with_mmap_backing_lazy _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_4032]
        have h1 : 0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) := by
          rw [hbvnZ]; exact HnZpos
        have h2 : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) % 4096 = 0 := by
          rw [hbvnZ]; exact HnZal
        have h3 : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) ≤ 2 ^ 64 := by
          rw [hbvnZ]; exact Int.le_trans Hsum (Int.le_of_lt HCEIL)
        have hli : lazy_interior (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = [(edenot E (reg cs 10), Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))] :=
          AsanNodesMmLib.lazy_interior_fresh (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) Hal h2 h1 h3
        have hglazy : m_vm_lazy (vm_add_lazy (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
            (vm_forget_range (bv_unsigned (edenot E (reg cs 10)))
              (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))))
              (with_vmmaps (AsanNodesLibE.fixedin_ok_vmmaps 3 (edenot E (reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) (m_vmmaps model)) model))) =
            (edenot E (reg cs 10), Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) ::
              maps_subtract (m_vm_lazy model) (bv_unsigned (edenot E (reg cs 10)))
                (bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))) := by
          unfold vm_add_lazy
          rw [BackingAlgebra.m_vm_lazy_with_vm_backing, BackingAlgebra.m_vm_lazy_vm_forget_range, hli]
          rfl
        refine ⟨rfl, rfl, rfl, hglazy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact MmapSim.zfill_out _ _ _ x (by simpa only [hbvnZ] using hx)
        · intro x hx
          simpa only [AsanNodesMmLib.sl_nn, Bool.false_eq_true, ite_false] using
            (AsanNodesMmLib.zfill_in _ _ _ x (by simpa only [hbvnZ] using hx))
  | ArmG =>
    have HfindG : find_containing (kn cs) cs.a_maps [mkind.KRW, mkind.KNONE, mkind.KNONELAZY] b off ne = some m := Hfind0
    have HnotF : m.am_kind ≠ .KRWLAZY := by
      intro hk
      rw [hk] at Hkind
      exact absurd Hkind (by decide)
    have R12 : getr R 12 = Z_to_bv 64 0 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 0
        HC (by decide) H12).1
    have R13 : getr R 13 = Z_to_bv 64 50 :=
      (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 13 50
        HC (by decide) H13).1
    have HnG : csO = ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
          (kimg_clip A (kn_cutout (kn cs) b off ne)) cs.a_ss.s_next)
        (rekind cs.a_maps m) cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis cs.a_ghost cs.a_abytes
        cs.a_brk cs.a_fd cs.a_tidset := by
      have h := Hn
      rw [mmap_fixed_in_eq] at h
      unfold mmap_fixed_in_ref at h
      unfold fixed_in_args_ref at h
      rw [HFA0] at h
      simp only [] at h
      rw [HfindG] at h
      simp only [] at h
      rw [Hvars0] at h
      simp only [ite_true] at h
      exact (Option.some.inj h).symm
    have CONTB : ∀ (model' : Model) (FULL' : word → Option byte),
        AsanNodesMmLib.slice_post .SlG (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model model' →
        AsanNodesMmLib.slice_mem .SlG (edenot E (reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL FULL' →
        m_fs model' = m_fs model →
        srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (edenot E (reg cs 10)))
          (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB := by
      intro model' FULL' HSPo HSM Hfs
      have Hsh : AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlG m
          (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' :=
        { sh_C := HC, sh_m := Hm, sh_nf := Hnf, sh_Un := hbvnZ, sh_pos := HnZpos,
          sh_nal := HnZal, sh_al := Hal, sh_in1 := Hin1, sh_in2 := Hin2,
          sh_post := HSPo, sh_mem := HSM,
          sh_F := (fun h => absurd h (by decide)), sh_nF := (fun _ hk => HnotF hk) }
      have Hregs' : regs_ok E cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10))) :=
        AsanNodesMmLib.regs_ok_regupd_same E cs.a_ss.s_regs R 10 (edenot E (reg cs 10))
          HC.co_regs (by decide) R10
      have Hk' : know_ok SEGS E (Mr A argH E cs model' FULL')
          (kimg_clip A (kn_cutout (kn cs) b off ne)) :=
        know_ok_filter SEGS E (Mr A argH E cs model' FULL') _ (kn_cutout (kn cs) b off ne)
          (know_ok_cutout SEGS E (Mr A argH E cs model FULL)
            (Mr A argH E cs model' FULL') (kn cs) b ne off HC.co_know
            (fun x hx =>
              AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlG m
                (edenot E (reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
                _ _ _ Hsh cs x rfl
                (by rw [Hest] at hx; simpa only [elenZ, Hne, hbvnZ] using hx)))
      have HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E
          (ACS (mk_ss (pc cs + 4) cs.a_ss.s_regs
              (kimg_clip A (kn_cutout (kn cs) b off ne)) cs.a_ss.s_next)
            (AsanNodesMmLib.slMaps cs .SlG m) cs.a_totsz cs.a_ylo cs.a_eager cs.a_vis
            cs.a_ghost cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
          (regupd R 10 (edenot E (reg cs 10))) FULL' model' :=
        AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame E cs R FULL
          model .SlG m (edenot E (reg cs 10))
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) model' FULL' Hsh
          cs.a_ss.s_regs (regupd R 10 (edenot E (reg cs 10)))
          (kimg_clip A (kn_cutout (kn cs) b off ne)) (pc cs + 4) cs.a_ss.s_next nhi
          Hregs' Hk' HnZle (fun HH => absurd HH (by decide))
      have Hpc : pc csO = pc cs + 4 := by rw [HnG]; rfl
      rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
      exact HKB E (regupd R 10 (edenot E (reg cs 10))) FULL' model'
        ⟨AsanNodesMmLib.env_agree_refl' _ _, AsanNodesMmLib.env_agree_refl' _ _⟩
        (by rw [HnG]; exact HC1) Hfs
    have Hbud : (0 : Int) = 3 → Sys.Mm.Mmap.mmap_fixed_rw_budget_ok (Z_to_bv 64 50) model
        (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true := by
      intro h
      exact absurd h (by decide)
    refine AsanNodesLibE.srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
      0 (Z_to_bv 64 50) (edenot E (reg cs 10))
      (bv_unsigned (edenot E (reg cs 11))) TA TB TC Hf He Hhalt R17 (Or.inl rfl)
      (AsanNodesMmLib.mmap_flags_core_32) R10 Hal Hpos R11 Hlenpos Hce Hisp R12 R13 R14 R15
      _ rfl Hrfres Hmc Hbud HA ?_ CONTC
    · refine CONTB (AsanNodesLibE.fixedin_ok_model 0 (Z_to_bv 64 50) (edenot E (reg cs 10))
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)
        (unfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
      · unfold AsanNodesLibE.fixedin_ok_model with_mmap_replacement
        rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_32]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨?_, ?_⟩
        · intro x hx
          exact MmapSim.unfill_out _ _ _ x (by simpa only [hbvnZ] using hx)
        · intro x hx
          simpa only [AsanNodesMmLib.sl_nn, ite_true] using
            (AsanNodesMmLib.unfill_in _ _ _ x (by simpa only [hbvnZ] using hx))

theorem node_mmapin_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (hole : Bool) :
    mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A nx0 LIMIT hole) := by
  intro cs csa csb cscs E R FULL model TA TB TC HC Hec Hn HKA HKB HKC
  unfold node_mmapin at Hn
  dsimp only at Hn
  split at Hn
  · rename_i prot flags Hg
    obtain ⟨H17, H12, H13, H14, H15, -⟩ := mmap_gate_sound cs prot flags false Hg
    split at Hn
    · rename_i arm heq
      have CASES : ∀ (arm : fixed_in_arm),
          reg_lit cs 12 = some (fixedInProt arm) →
          reg_lit cs 13 = some (fixedInFlags arm) →
          (match fixed_in_args A cs arm, mmap_fixed_in A LIMIT cs arm with
           | some (b, off, ne, nlo, nhi, m), some csO =>
               some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
           | _, _ => none) = some (csa, csb, cscs) →
          srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA (t_alt2 TB TC)) := by
        intro arm H12' H13' Hn'
        cases hfi : fixed_in_args A cs arm with
        | none => rw [hfi] at Hn'; simp at Hn'
        | some p =>
          obtain ⟨b, off, ne, nlo, nhi, m⟩ := p
          rw [hfi] at Hn'
          cases hmf : mmap_fixed_in A LIMIT cs arm with
          | none => rw [hmf] at Hn'; simp at Hn'
          | some csO =>
            rw [hmf] at Hn'
            simp only [Option.some.injEq, Prod.mk.injEq] at Hn'
            obtain ⟨rfl, rfl, rfl⟩ := Hn'
            exact mmap_fixed_in_sound3 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len
              RES_hull HULL_ok SHADOW_ok argH_high SINV_frame hole cs arm b off ne nlo nhi m csO
              E R FULL model TA TB TC HC Hec H17 H12' H13' H14 H15 hfi hmf HKA HKB
              (fun csc E' R' FULL' model' hmem hag hcs hfs => HKC csc hmem E' R' FULL' model' hag hcs hfs)
      split at heq
      · have harm : arm = .ArmE := (Option.some.inj heq).symm
        rw [harm] at Hn
        exact CASES .ArmE H12 H13 Hn
      · have harm : arm = .ArmF := (Option.some.inj heq).symm
        rw [harm] at Hn
        exact CASES .ArmF H12 H13 Hn
      · have harm : arm = .ArmG := (Option.some.inj heq).symm
        rw [harm] at Hn
        exact CASES .ArmG H12 H13 Hn
      · simp at heq
    · simp at Hn
  · simp at Hn


/-! ## 7b. The NULL-hint node -/

theorem mmap_null_sound2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (PLACEMENT : placement_policy)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (cs : acs) (kd : mkind) (eager visible : Bool) (cs' : acs) (E : env) (R : BvMap word)
    (FULL : word → Option byte) (model : Model) (TA TB : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hec : is_ecall_at SEGS cs = true)
    (H17 : reg_lit cs 17 = some 222) (H10 : reg_lit cs 10 = some 0)
    (H12 : reg_lit cs 12 = some (if AsanNodesMmLib.kind_none kd then 0 else 3))
    (H13 : reg_lit cs 13 = some (if AsanNodesMmLib.kind_lazy kd then 16418 else 34))
    (H14 : reg_lit cs 14 = some (two64 - 1)) (H15 : reg_lit cs 15 = some 0)
    (Hkind : (AsanNodesMmLib.kind_none kd || AsanNodesMmLib.kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false)
    (Hvisible : visible = !(AsanNodesMmLib.kind_none kd))
    (Hn : mmap_null A nx0 LIMIT cs kd eager visible = some cs')
    (HKA : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA)
    (HK : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') TB) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB) := by
  obtain ⟨w, Hf, He, Hp0, Hp4⟩ := AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec
  unfold mmap_null at Hn
  dsimp only at Hn
  cases hml : mmap_len cs with
  | none => rw [hml] at Hn; simp at Hn
  | some pp =>
    obtain ⟨ne, nlo, nhi⟩ := pp
    rw [hml] at Hn
    dsimp only at Hn
    cases hg : (fresh_ok nx0 cs && AsanPlanCore.expr_vars_lt (nxt cs) ne && gap_ok A cs nhi &&
        (!eager || budget_ok LIMIT cs nhi) && decide (KHI + 2 * nhi ≤ cs.a_ylo) &&
        decide (cs.a_ylo ≤ FLOOR) && no_holes cs.a_maps) with
    | false => rw [hg] at Hn; simp at Hn
    | true =>
      rw [hg] at Hn
      simp only [ite_true] at Hn
      simp only [Bool.and_eq_true, and_assoc] at hg
      obtain ⟨Hfresh, Hnev, Hgap, Hbud, Hylo, Hfloor, Hnoh⟩ := hg
      have Hylo' : KHI + 2 * nhi ≤ cs.a_ylo := by simpa only [decide_eq_true_eq] using Hylo
      have Hfloor' : cs.a_ylo ≤ FLOOR := by simpa only [decide_eq_true_eq] using Hfloor
      have HbudT : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
        intro he
        rw [he] at Hbud
        simp only [Bool.not_true, Bool.false_or] at Hbud
        unfold budget_ok at Hbud
        simpa only [decide_eq_true_eq] using Hbud
      have Hhalt : m_halted model = none := HC.co_halt
      have Hisp : init_sp_ok (m_vmmaps model) := HC.co_wf.2.2.2
      have R17 : getr R 17 = Z_to_bv 64 222 :=
        (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 222
          HC (by decide) H17).1
      have R10 : getr R 10 = Z_to_bv 64 0 :=
        (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 10 0
          HC (by decide) H10).1
      have R12 : getr R 12 = Z_to_bv 64 (if AsanNodesMmLib.kind_none kd then 0 else 3) :=
        (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12
          (if AsanNodesMmLib.kind_none kd then 0 else 3) HC (by decide) H12).1
      have R13 : getr R 13 = Z_to_bv 64 (if AsanNodesMmLib.kind_lazy kd then 16418 else 34) :=
        (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 13
          (if AsanNodesMmLib.kind_lazy kd then 16418 else 34) HC (by decide) H13).1
      have R14 : getr R 14 = Z_to_bv 64 (-1) := by
        have h := (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 14
          (two64 - 1) HC (by decide) H14).1
        rw [AsanNodesMmLib.Z_to_bv64_m1 (two64 - 1) rfl] at h
        exact h
      have R15 : getr R 15 = Z_to_bv 64 0 :=
        (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 15 0
          HC (by decide) H15).1
      obtain ⟨R11, Hlenpos, Hlenlt, Hne, HnloPos, HnloLe, HnhiLe, HnZal, HneE⟩ :=
        AsanNodesMmLib.mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi HC hml
      have HnZ0 : 0 ≤ page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) :=
        Int.le_trans (Int.le_of_lt HnloPos) HnloLe
      obtain ⟨a0, Ha0⟩ := AsanNodesMmLib.gap_ok_sound SEGS A LIMIT nx0 SINV argH FS0 RES_len E cs R
        FULL model nhi (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) HC Hgap
        ⟨HnZ0, HnhiLe⟩
      have CONTA : srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (errno_ret ENOMEM))
          (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA :=
        AsanNodesMmLib.refuse_cont SEGS A LIMIT nx0 SINV argH FS0 cs E R FULL model TA HC Hp0 Hp4 HKA
      have Hpc : pc cs' = pc cs + 4 := by
        cases hv : visible with
        | false =>
          rw [hv] at Hn
          simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at Hn
          rw [← Hn]
          rfl
        | true =>
          rw [hv] at Hn
          simp only [ite_true] at Hn
          obtain ⟨_nh, _hx, hEcs⟩ :=
            AsanNodesMmLib.vis_add_inv A LIMIT _ (escale 4096 (.EVar (nxt cs))) ne _ cs' Hn
          rw [hEcs]
          rfl
      have GRANT : ∀ (a : word) (model' : Model) (FULL' : word → Option byte),
          grant_ok_na (Z_to_bv 64 0) model a
              (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) = true →
          AsanNodesMmLib.grant_post kd a
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model model' →
          AsanNodesMmLib.grant_mem kd a
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL FULL' →
          cs_ok SEGS A LIMIT SINV argH FS0 (AsanNodesMmLib.mmEnv E cs a)
              (AsanNodesMmLib.null_cs1 A cs kd eager ne nlo nhi) (regupd R 10 a) FULL' model' ∧
            edenot (AsanNodesMmLib.mmEnv E cs a) (AsanNodesMmLib.mmBase cs) = a ∧
            edenot (AsanNodesMmLib.mmEnv E cs a) ne =
              Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) ∧
            bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) =
              page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) ∧
            env_agree nx0 E (AsanNodesMmLib.mmEnv E cs a) ∧
            (∀ x : word,
              bv_unsigned a ≤ bv_unsigned x ∧
              bv_unsigned x < bv_unsigned a +
                page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) →
              in_ivs (bv_unsigned x) (m_vmmaps model').vm_maps = true ∧
              in_ivs (bv_unsigned x) (m_vmmaps model).vm_noaccess = false ∧
              argH (AsanNodesMmLib.mmEnv E cs a) x = false) := by
        intro a model' FULL' Hg GPo GM
        obtain ⟨HC1, Hbase, HneE', HUn, Hag0, NEW⟩ :=
          AsanNodesMmLib.mmap_null_cs1 SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model kd eager ne
            nlo nhi a _ model' FULL' HULL_ok argH_high argH_agree SINV_frame SINV_agree HC hml Hfresh
            Hnev HbudT Hylo' Hfloor' Hkind Hkfog Hnoh rfl Hg GPo GM
        exact ⟨HC1, Hbase, HneE', HUn, Hag0,
          fun x hx => ⟨(NEW x hx).1, (NEW x hx).2.1, (NEW x hx).2.2.1⟩⟩
      have Hkimg : kimg_in_hull A (kn (AsanNodesMmLib.null_cs1 A cs kd eager ne nlo nhi)) := by
        have hK0 : kimg_in_hull A
            [kentry.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)] :=
          AsanNodesMmLib.kimg_in_hull_pure A _ (by
            intro K hK
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
            rw [hK]
            simp)
        have hK1 : kimg_in_hull A
            ([kentry.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)] ++
              null_kend (escale 4096 (.EVar (nxt cs))) ne nlo) :=
          kimg_in_hull_app A _ _ hK0
            (AsanNodesMmLib.kimg_in_hull_pure A _ (fun K hK => AsanNodesMmLib.null_kend_pure _ ne nlo K hK))
        have hK2 : kimg_in_hull A
            (([kentry.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)] ++
              null_kend (escale 4096 (.EVar (nxt cs))) ne nlo) ++
              kdisj_new cs.a_maps (escale 4096 (.EVar (nxt cs))) ne) :=
          kimg_in_hull_app A _ _ hK1
            (AsanNodesMmLib.kimg_in_hull_pure A _ (fun K hK => AsanNodesMmLib.kdisj_new_pure _ _ ne K hK))
        have hK3 : kimg_in_hull A
            ((([kentry.KRange (.EVar (nxt cs)) (KHI / 4096 + 1) ((CEIL - nlo) / 4096)] ++
              null_kend (escale 4096 (.EVar (nxt cs))) ne nlo) ++
              kdisj_new cs.a_maps (escale 4096 (.EVar (nxt cs))) ne) ++
              kn_grant_filter A (kn cs) cs.a_maps) :=
          kimg_in_hull_app A _ _ hK2 (kimg_clip_in_hull A _)
        simpa only [AsanNodesMmLib.null_cs1, add_entry, kn, mk_ss, List.singleton_append] using hK3
      cases kd with
      | KFOG =>
        simp only [is_tok_kind] at Hkfog
        exact absurd Hkfog (by decide)
      | KHOLE =>
        simp only [is_tok_kind] at Hkfog
        exact absurd Hkfog (by decide)
      | KRW =>
        simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_false,
          Bool.not_false, Bool.not_true] at Hkind H12 H13 Hvisible
        cases eager with
        | false => simp at Hkind
        | true =>
          simp only [Bool.not_true] at Hbud
          have HbudB : budget_ok LIMIT cs nhi = true := by
            simpa only [Bool.false_or] using Hbud
          rw [Hvisible] at Hn
          simp only [ite_true] at Hn
          have Hkindr : AsanNodesMmLib.kind_none mkind.KRW = false := rfl
          have Hklr : AsanNodesMmLib.kind_lazy mkind.KRW = false := rfl
          refine AsanNodesMmLib.srz_mmap_rw2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
            (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) (Z_to_bv 64 34) TA TB
            Hf He Hhalt Hisp R17 R11 ⟨Hlenpos, Hlenlt⟩ R12 R13
            AsanNodesMmLib.mmap_flags_core_22 R14 R15
            (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) rfl
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) rfl
            PLACEMENT ?_ CONTA ?_
          · refine ⟨a0, ?_, ?_⟩
            · rw [R10]; exact Ha0
            · unfold mmap_noreserve_backed_ok
              rw [AsanNodesMmLib.mmap_noreserve_b_22]
              simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq]
              exact Int.le_trans (Int.add_le_add_left HnhiLe (vm_backing_used model))
                (AsanNodesMmLib.budget_slack SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model nhi HC HbudB)
          · intro a Hg _
            rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_22]
            rw [R10] at Hg
            have Hg' := Hg
            simp only [RefNodes.grant_ok_na, Bool.and_eq_true, and_assoc] at Hg'
            obtain ⟨-, -, Hceil, -, -⟩ := Hg'
            rw [AsanNodesMmLib.CEIL_eq] at Hceil
            simp only [decide_eq_true_eq] at Hceil
            have hb2 : bv_unsigned a + page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) ≤ 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              exact Int.le_of_lt h2
            have hzlt : page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) < 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              have h0 : (0 : Int) ≤ ↑(BitVec.toNat a) := Int.natCast_nonneg _
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              omega
            have hUn' : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                = page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) :=
              u64_lit _ ⟨HnZ0, hzlt⟩
            have GPo : AsanNodesMmLib.grant_post .KRW a
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) := by
              refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              · rw [Hkindr]; rfl
              · rw [Hklr]; rfl
            have GM : AsanNodesMmLib.grant_mem .KRW a
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) := by
              refine ⟨?_, ?_⟩
              · intro x hx
                refine MmapSim.zfill_out _ _ _ _ ?_
                simpa only [hUn'] using hx
              · intro x hx
                have h1 : zfill a
                    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                    FULL x = some (Z_to_bv 8 0) := by
                  refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
                  simpa only [hUn'] using hx
                rw [h1]
                rw [Hkindr]
                rfl
            obtain ⟨HC1, Hbase, HneE', HUn, Hag0, NEW⟩ :=
              GRANT a (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) Hg GPo GM
            rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
            refine HK (AsanNodesMmLib.mmEnv E cs a) (regupd R 10 a) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL)
              (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) ⟨Hag0, ext1_agree E (nxt cs) _⟩ ?_ rfl
            refine AsanNodesMmLib.grant_vis_add SEGS A LIMIT nx0 SINV argH FS0 SEGS_in_hull HULL_ok
              SHADOW_ok argH_high (AsanNodesMmLib.mmEnv E cs a) _ cs' (AsanNodesMmLib.mmBase cs) ne
              (regupd R 10 a) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) _ HC1 Hn
              Hkimg Hbase HneE' HUn HnZ0 hb2 NEW ?_
            intro x hx
            refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
            simpa only [HUn] using hx
      | KRWLAZY =>
        simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
          Bool.not_false, Bool.not_true] at Hkind H12 H13 Hvisible
        cases eager with
        | true => simp at Hkind
        | false =>
          rw [Hvisible] at Hn
          simp only [ite_true] at Hn
          have Hkindr : AsanNodesMmLib.kind_none mkind.KRWLAZY = false := rfl
          have Hklr : AsanNodesMmLib.kind_lazy mkind.KRWLAZY = true := rfl
          refine AsanNodesMmLib.srz_mmap_rw2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
            (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) (Z_to_bv 64 16418) TA TB
            Hf He Hhalt Hisp R17 R11 ⟨Hlenpos, Hlenlt⟩ R12 R13
            AsanNodesMmLib.mmap_flags_core_4022 R14 R15
            (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) rfl PLACEMENT ?_ CONTA ?_
          · refine ⟨a0, ?_, ?_⟩
            · rw [R10]; exact Ha0
            · unfold mmap_noreserve_backed_ok
              rw [AsanNodesMmLib.mmap_noreserve_b_4022]
              simp only [ite_true]
          · intro a Hg _
            rw [AsanNodesMmLib.with_mmap_backing_lazy _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_4022]
            rw [R10] at Hg
            have Hg' := Hg
            simp only [RefNodes.grant_ok_na, Bool.and_eq_true, and_assoc] at Hg'
            obtain ⟨Hal, -, Hceil, -, -⟩ := Hg'
            simp only [decide_eq_true_eq] at Hal
            rw [AsanNodesMmLib.CEIL_eq] at Hceil
            simp only [decide_eq_true_eq] at Hceil
            have hzlt : (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) < 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              have h0 : (0 : Int) ≤ ↑(BitVec.toNat a) := Int.natCast_nonneg _
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              omega
            have hUn' : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) := u64_lit _ ⟨HnZ0, hzlt⟩
            have hUlz : 0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) := by rw [hUn']; exact Int.lt_of_lt_of_le HnloPos HnloLe
            have hb2 : bv_unsigned a + (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) ≤ 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              exact Int.le_of_lt h2
            have hli : lazy_interior a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = [(a, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))))] :=
              AsanNodesMmLib.lazy_interior_fresh a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) Hal (by simpa only [hUn'] using HnZal) hUlz
                (by simpa only [hUn'] using hb2)
            have hglazy : m_vm_lazy (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) =
                (if AsanNodesMmLib.kind_lazy mkind.KRWLAZY = true then [(a, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))))] else []) ++
                  m_vm_lazy model := by
              unfold vm_add_lazy
              rw [m_vm_lazy_with_vm_backing, hli, Hklr]
              simp only [ite_true]
              rfl
            have GPo : AsanNodesMmLib.grant_post .KRWLAZY a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) := by
              refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              · rw [Hkindr]; rfl
              · exact hglazy
            have GM : AsanNodesMmLib.grant_mem .KRWLAZY a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) := by
              refine ⟨?_, ?_⟩
              · intro x hx
                refine MmapSim.zfill_out _ _ _ _ ?_
                simpa only [hUn'] using hx
              · intro x hx
                have h1 : zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL x = some (Z_to_bv 8 0) := by
                  refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
                  simpa only [hUn'] using hx
                rw [h1, Hkindr]
                rfl
            obtain ⟨HC1, Hbase, HneE', HUn, Hag0, NEW⟩ :=
              GRANT a (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) Hg GPo GM
            rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
            refine HK (AsanNodesMmLib.mmEnv E cs a) (regupd R 10 a) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL)
              (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) ⟨Hag0, ext1_agree E (nxt cs) _⟩ ?_ rfl
            refine AsanNodesMmLib.grant_vis_add SEGS A LIMIT nx0 SINV argH FS0 SEGS_in_hull HULL_ok
              SHADOW_ok argH_high (AsanNodesMmLib.mmEnv E cs a) _ cs' (AsanNodesMmLib.mmBase cs) ne
              (regupd R 10 a) (zfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (mmap_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) _ HC1 Hn
              Hkimg Hbase HneE' HUn HnZ0 hb2 NEW ?_
            intro x hx
            refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
            simpa only [HUn] using hx
      | KNONE =>
        simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
          Bool.not_false, Bool.not_true] at Hkind H12 H13 Hvisible
        cases eager with
        | true => simp at Hkind
        | false =>
          rw [Hvisible] at Hn
          simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at Hn
          have Hkindn : AsanNodesMmLib.kind_none mkind.KNONE = true := rfl
          have Hkln : AsanNodesMmLib.kind_lazy mkind.KNONE = false := rfl
          refine AsanNodesMmLib.srz_mmap_none2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
            (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) (Z_to_bv 64 34) TA TB
            Hf He Hhalt Hisp R17 R11 ⟨Hlenpos, Hlenlt⟩ R12 R13
            AsanNodesMmLib.mmap_flags_core_22 R14 R15
            (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) rfl PLACEMENT ?_ CONTA ?_
          · exact ⟨a0, by rw [R10]; exact Ha0⟩
          · intro a Hg
            rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_22]
            rw [R10] at Hg
            have Hg' := Hg
            simp only [RefNodes.grant_ok_na, Bool.and_eq_true, and_assoc] at Hg'
            obtain ⟨-, -, Hceil, -, -⟩ := Hg'
            rw [AsanNodesMmLib.CEIL_eq] at Hceil
            simp only [decide_eq_true_eq] at Hceil
            have hzlt : (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) < 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              have h0 : (0 : Int) ≤ ↑(BitVec.toNat a) := Int.natCast_nonneg _
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              omega
            have hUn' : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) := u64_lit _ ⟨HnZ0, hzlt⟩
            have GPo : AsanNodesMmLib.grant_post .KNONE a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) := by
              refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              · rw [Hkindn]; rfl
              · rw [Hkln]; rfl
            have GM : AsanNodesMmLib.grant_mem .KNONE a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) := by
              refine ⟨?_, ?_⟩
              · intro x hx
                refine MmapSim.unfill_out _ _ _ _ ?_
                simpa only [hUn'] using hx
              · intro x hx
                have h1 : unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL x = none :=
                  AsanNodesMmLib.unfill_in _ _ _ _ (by simpa only [hUn'] using hx)
                rw [h1, Hkindn]
                rfl
            obtain ⟨HC1, Hbase, HneE', HUn, Hag0, NEW⟩ :=
              GRANT a (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) Hg GPo GM
            rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
            refine HK (AsanNodesMmLib.mmEnv E cs a) (regupd R 10 a) (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL)
              (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model) ⟨Hag0, ext1_agree E (nxt cs) _⟩ (Hn ▸ HC1) rfl
      | KNONELAZY =>
        simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
          Bool.not_false, Bool.not_true] at Hkind H12 H13 Hvisible
        cases eager with
        | true => simp at Hkind
        | false =>
          rw [Hvisible] at Hn
          simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at Hn
          have Hkindn : AsanNodesMmLib.kind_none mkind.KNONELAZY = true := rfl
          have Hkln : AsanNodesMmLib.kind_lazy mkind.KNONELAZY = true := rfl
          refine AsanNodesMmLib.srz_mmap_none2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
            (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) (Z_to_bv 64 16418) TA TB
            Hf He Hhalt Hisp R17 R11 ⟨Hlenpos, Hlenlt⟩ R12 R13
            AsanNodesMmLib.mmap_flags_core_4022 R14 R15
            (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) rfl PLACEMENT ?_ CONTA ?_
          · exact ⟨a0, by rw [R10]; exact Ha0⟩
          · intro a Hg
            rw [AsanNodesMmLib.with_mmap_backing_lazy _ _ _ _ AsanNodesMmLib.mmap_noreserve_b_4022]
            rw [R10] at Hg
            have Hg' := Hg
            simp only [RefNodes.grant_ok_na, Bool.and_eq_true, and_assoc] at Hg'
            obtain ⟨Hal, -, Hceil, -, -⟩ := Hg'
            simp only [decide_eq_true_eq] at Hal
            rw [AsanNodesMmLib.CEIL_eq] at Hceil
            simp only [decide_eq_true_eq] at Hceil
            have hzlt : (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) < 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              have h0 : (0 : Int) ≤ ↑(BitVec.toNat a) := Int.natCast_nonneg _
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              omega
            have hUn' : bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) := u64_lit _ ⟨HnZ0, hzlt⟩
            have hUlz : 0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) := by rw [hUn']; exact Int.lt_of_lt_of_le HnloPos HnloLe
            have hb2 : bv_unsigned a + (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) ≤ 2 ^ 64 := by
              have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
              have h2 := Int.lt_of_le_of_lt Hceil hC
              rw [show (2 : Int) ^ 64 = two_pow_64 from rfl]
              exact Int.le_of_lt h2
            have hli : lazy_interior a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = [(a, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))))] :=
              AsanNodesMmLib.lazy_interior_fresh a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) Hal (by simpa only [hUn'] using HnZal) hUlz
                (by simpa only [hUn'] using hb2)
            have GPo : AsanNodesMmLib.grant_post .KNONELAZY a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model
                (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) := by
              refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              · rw [Hkindn]; rfl
              · unfold vm_add_lazy
                rw [m_vm_lazy_with_vm_backing, hli, Hkln]
                simp only [ite_true]
                rfl
            have GM : AsanNodesMmLib.grant_mem .KNONELAZY a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) := by
              refine ⟨?_, ?_⟩
              · intro x hx
                refine MmapSim.unfill_out _ _ _ _ ?_
                simpa only [hUn'] using hx
              · intro x hx
                have h1 : unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL x = none :=
                  AsanNodesMmLib.unfill_in _ _ _ _ (by simpa only [hUn'] using hx)
                rw [h1, Hkindn]
                rfl
            obtain ⟨HC1, Hbase, HneE', HUn, Hag0, NEW⟩ :=
              GRANT a (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL) Hg GPo GM
            rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
            refine HK (AsanNodesMmLib.mmEnv E cs a) (regupd R 10 a) (unfill a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) FULL)
              (vm_add_lazy a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) (noaccess_model a (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) model)) ⟨Hag0, ext1_agree E (nxt cs) _⟩
              (Hn ▸ HC1) rfl

theorem mmap_fixed_grant_sound2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (cs : acs) (ms0 : List amap) (top : Int) (b : expr) (off : Int) (ne : expr)
    (nlo nhi : Int) (kd : mkind) (eager visible : Bool) (cs' : acs)
    (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model) (TA TB : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hec : is_ecall_at SEGS cs = true)
    (H17 : reg_lit cs 17 = some 222)
    (H12 : reg_lit cs 12 = some (if AsanNodesMmLib.kind_none kd then 0 else 3))
    (H13 : reg_lit cs 13 = some (if AsanNodesMmLib.kind_lazy kd then 16434 else 50))
    (H14 : reg_lit cs 14 = some (two64 - 1)) (H15 : reg_lit cs 15 = some 0)
    (Hkind : (AsanNodesMmLib.kind_none kd || AsanNodesMmLib.kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false)
    (Hvisible : visible = eager)
    (HFA : fixed_args A cs top = some (b, off, ne, nlo, nhi)) (Htop : top ≤ CEIL)
    (Hbud : (!eager || budget_ok LIMIT cs nhi) = true)
    (HC0 : cs_ok SEGS A LIMIT SINV argH FS0 E (with_maps0 cs ms0) R FULL model)
    (Hrf : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
        (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true)
    (Hholes : ∀ m, m ∈ ms0 → is_hole m = true →
        bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) ≤ AsanPlanSound.uE E m.am_base ∨
        AsanPlanSound.uE E m.am_base + AsanPlanSound.uE E m.am_len
          ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hside : bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) ≤ KHI ∨
        cs.a_ylo ≤ bv_unsigned (edenot E (reg cs 10)))
    (Hn : mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = some cs')
    (HKA : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA)
    (HK : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') TB) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB) := by
  obtain ⟨w, Hf, He, Hp0, Hp4⟩ := AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec
  have Hbudget : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
    intro he
    rw [he] at Hbud
    simp only [Bool.not_true, Bool.false_or] at Hbud
    unfold budget_ok at Hbud
    simpa only [decide_eq_true_eq] using Hbud
  unfold mmap_fixed_grant at Hn
  dsimp only at Hn
  have R17 : getr R 17 = Z_to_bv 64 222 :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 222
      HC (by decide) H17).1
  have R12 : getr R 12 = Z_to_bv 64 (if AsanNodesMmLib.kind_none kd then 0 else 3) :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12
      (if AsanNodesMmLib.kind_none kd then 0 else 3) HC (by decide) H12).1
  have R13 : getr R 13 = Z_to_bv 64 (if AsanNodesMmLib.kind_lazy kd then 16434 else 50) :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 13
      (if AsanNodesMmLib.kind_lazy kd then 16434 else 50) HC (by decide) H13).1
  have R14 : getr R 14 = Z_to_bv 64 (-1) := by
    have h := (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 14
      (two64 - 1) HC (by decide) H14).1
    rw [AsanNodesMmLib.Z_to_bv64_m1 (two64 - 1) rfl] at h
    exact h
  have R15 : getr R 15 = Z_to_bv 64 0 :=
    (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 15 0
      HC (by decide) H15).1
  obtain ⟨-, HML, -, -, -, -, -, -⟩ :=
    AsanNodesMmLib.fixed_args_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model top b off
      ne nlo nhi HC HFA
  obtain ⟨R11, Hlenpos, Hlenlt, HneN0, HnloPos, HnloLe, HnhiLe, HnZal0, HneE1⟩ :=
    AsanNodesMmLib.mmap_len_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model ne nlo nhi
      HC HML
  obtain ⟨HneN, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZpos, HnZhi⟩ :=
    AsanNodesMmLib.fixed_pre SEGS A LIMIT nx0 SINV argH FS0 cs top b off ne nlo nhi E R FULL
      model (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) HC HFA Htop rfl
  have Hhalt : m_halted model = none := HC.co_halt
  have Hisp : init_sp_ok (m_vmmaps model) := HC.co_wf.2.2.2
  have HaK : bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) ≤ CEIL := Int.le_trans HtopA Htop
  have hUlz : 0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) := by rw [Un]; exact HnZpos
  have hb2 : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) ≤ 2 ^ 64 := by
    have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
    rw [Un, show (2 : Int) ^ 64 = two_pow_64 from rfl]
    exact Int.le_trans HaK (Int.le_of_lt hC)
  have hli : lazy_interior (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) =
      [(edenot E (reg cs 10), Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))] :=
    AsanNodesMmLib.lazy_interior_fresh _ _ Hal (by rw [Un]; exact HnZal) hUlz hb2
  have CONTA : srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (errno_ret ENOMEM))
      (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA :=
    AsanNodesMmLib.refuse_cont SEGS A LIMIT nx0 SINV argH FS0 cs E R FULL model TA HC Hp0 Hp4 HKA
  have CONT : ∀ (model' : Model) (FULL' : word → Option byte),
      AsanNodesMmLib.grant_post kd (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model model' →
      AsanNodesMmLib.grant_mem kd (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL FULL' →
      m_fs model' = m_fs model →
      srealizes SEGS (ShapeAlg.mkCfg (mkst (regupd R 10 (edenot E (reg cs 10)))
        (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB := by
    intro model' FULL' GPo GM Hfs
    obtain ⟨HC1, NEW⟩ :=
      AsanNodesMmLib.mmap_fixed_grant_cs1 SEGS A LIMIT nx0 SINV argH FS0 SHADOW_ok argH_high
        SINV_frame cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
        HC HFA Htop HC0 rfl Hrf Hholes Hside Hbudget Hkind Hkfog GPo GM
    have Hpc : pc cs' = pc cs + 4 := by
      cases visible with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at Hn
        rw [← Hn]
        rfl
      | true =>
        simp only [ite_true] at Hn
        obtain ⟨_, _, hEcs⟩ := AsanNodesMmLib.vis_add_inv A LIMIT _ (reg cs 10) ne _ cs' Hn
        rw [hEcs]
        rfl
    have HC2 : cs_ok SEGS A LIMIT SINV argH FS0 E cs'
        (regupd R (Z_to_bv 5 (10 : Int)) (edenot E (reg cs 10))) FULL' model' := by
      cases visible with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at Hn
        rw [← Hn]
        exact HC1
      | true =>
        simp only [ite_true] at Hn
        have hkn : AsanNodesMmLib.kind_none kd = false := by
          have he : eager = true := Hvisible.symm
          rw [he] at Hkind
          simp only [Bool.not_true] at Hkind
          exact or_eq_false_left Hkind
        have Hkh : kimg_in_hull A (kn (AsanNodesMmLib.fixed_cs1 A (with_maps0 cs ms0) kd eager ne nhi)) := by
          have hksh : kimg_in_hull A (if mkind_eqb kd mkind.KRWLAZY then
              cs.a_vis.flatMap (fun p => shadow_facts A (kn cs)
                [amap.mk (reg cs 10) ne kd] p.1 p.2) else []) := by
            by_cases hkd : mkind_eqb kd mkind.KRWLAZY = true
            · rw [ite_eq_left hkd]
              refine AsanNodesMmLib.kimg_in_hull_pure A _ ?_
              intro K hK
              obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hK
              unfold shadow_facts at hp
              split at hp
              split at hp
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                rcases hp with rfl | rfl <;> simp
              · simp only [List.not_mem_nil] at hp
            · rw [ite_eq_right hkd]
              intro K hK
              simp only [List.not_mem_nil] at hK
          have hrest : kimg_in_hull A (kn_grant_filter A (kn cs) ms0) := kimg_clip_in_hull A _
          have hboth := kimg_in_hull_app A _ _ hksh hrest
          exact hboth
        refine AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT nx0 SINV argH FS0 SEGS_in_hull
          HULL_ok SHADOW_ok argH_high E _ cs' (reg cs 10) b off ne
          (regupd R (Z_to_bv 5 (10 : Int)) (edenot E (reg cs 10))) FULL' model'
          (bv_unsigned (edenot E (reg cs 10))) (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) HC1 Hn Hkh ?_ Hest ?_ ?_ HnZpos HaK ?_
        · rfl
        · simp only [elenZ, HneN, Un]
        · have h0 : (0 : Int) ≤ ↑(BitVec.toNat (edenot E (reg cs 10))) := Int.natCast_nonneg _
          simpa only [bv_unsigned] using h0
        · intro x hx
          obtain ⟨N1, N2, N3⟩ := NEW x hx
          refine ⟨N1, ?_, N3, ?_⟩
          · rw [GPo.gp_noacc, hkn]
            simpa only [Bool.false_eq_true, ite_false, List.nil_append] using N2
          · have hx' := hx
            rw [← Un] at hx'
            have hGM : FULL' x = (if AsanNodesMmLib.kind_none kd then none else some (Z_to_bv 8 0)) := GM.2 x hx'
            rw [hGM, hkn]
            simp only [Bool.false_eq_true, ite_false]
    rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
    exact HK E (regupd R (Z_to_bv 5 (10 : Int)) (edenot E (reg cs 10))) FULL' model'
      ⟨AsanNodesMmLib.env_agree_refl' _ _, AsanNodesMmLib.env_agree_refl' _ _⟩ HC2 Hfs
  unfold cfg_of
  cases kd with
  | KFOG =>
    simp only [is_tok_kind] at Hkfog
    exact absurd Hkfog (by decide)
  | KHOLE =>
    simp only [is_tok_kind] at Hkfog
    exact absurd Hkfog (by decide)
  | KRW =>
    simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_false,
      Bool.not_false, Bool.not_true] at Hkind H12 H13
    cases eager with
    | false => simp at Hkind
    | true =>
      have HbudB : budget_ok LIMIT cs nhi = true := by
        simpa only [Bool.not_true, Bool.false_or] using Hbud
      have Hkindr : AsanNodesMmLib.kind_none mkind.KRW = false := rfl
      have Hklr : AsanNodesMmLib.kind_lazy mkind.KRW = false := rfl
      refine AsanNodesMmLib.srz_mmap_fixed_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL
        (seg_rom SEGS) model w (edenot E (reg cs 10))
        (bv_unsigned (edenot E (reg cs 11))) (Z_to_bv 64 50) TA TB
        Hf He Hhalt R17 R10 Hal Hpos R11 Hlenpos HaK Hisp R12 R13
        AsanNodesMmLib.mmap_flags_core_32 R14 R15
        (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) rfl Hrf ?_ CONTA ?_
      · unfold mmap_noreserve_backed_ok
        rw [AsanNodesMmLib.mmap_noreserve_b_32]
        simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq]
        exact Int.le_trans (Int.add_le_add_left HnZhi (vm_backing_used model))
          (AsanNodesMmLib.budget_slack SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model nhi HC HbudB)
      · rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _
          AsanNodesMmLib.mmap_noreserve_b_32]
        refine CONT (mmap_model (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)
          (zfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
        · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [Hkindr]; rfl
          · rw [Hklr]; rfl
        · refine ⟨?_, ?_⟩
          · intro x hx
            refine MmapSim.zfill_out _ _ _ _ ?_
            simpa only [Un] using hx
          · intro x hx
            refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
            simpa only [Un] using hx
  | KRWLAZY =>
    simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
      Bool.not_false, Bool.not_true] at Hkind H12 H13
    cases eager with
    | true => simp at Hkind
    | false =>
      have Hkindr : AsanNodesMmLib.kind_none mkind.KRWLAZY = false := rfl
      have Hklr : AsanNodesMmLib.kind_lazy mkind.KRWLAZY = true := rfl
      refine AsanNodesMmLib.srz_mmap_fixed_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL
        (seg_rom SEGS) model w (edenot E (reg cs 10))
        (bv_unsigned (edenot E (reg cs 11))) (Z_to_bv 64 16434) TA TB
        Hf He Hhalt R17 R10 Hal Hpos R11 Hlenpos HaK Hisp R12 R13
        AsanNodesMmLib.mmap_flags_core_4032 R14 R15
        (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) rfl Hrf ?_ CONTA ?_
      · unfold mmap_noreserve_backed_ok
        rw [AsanNodesMmLib.mmap_noreserve_b_4032]
        simp only [ite_true]
      · rw [AsanNodesMmLib.with_mmap_backing_lazy _ _ _ _
          AsanNodesMmLib.mmap_noreserve_b_4032]
        refine CONT (vm_add_lazy (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (mmap_model (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model))
          (zfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
        · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [Hkindr]; rfl
          · unfold vm_add_lazy
            rw [m_vm_lazy_with_vm_backing, hli, Hklr]
            simp only [ite_true]
            rfl
        · refine ⟨?_, ?_⟩
          · intro x hx
            refine MmapSim.zfill_out _ _ _ _ ?_
            simpa only [Un] using hx
          · intro x hx
            refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
            simpa only [Un] using hx
  | KNONE =>
    simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
      Bool.not_false, Bool.not_true] at Hkind H12 H13
    cases eager with
    | true => simp at Hkind
    | false =>
      have Hkindn : AsanNodesMmLib.kind_none mkind.KNONE = true := rfl
      have Hkln : AsanNodesMmLib.kind_lazy mkind.KNONE = false := rfl
      refine AsanNodesMmLib.srz_mmap_fixed_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL
        (seg_rom SEGS) model w (edenot E (reg cs 10))
        (bv_unsigned (edenot E (reg cs 11))) (Z_to_bv 64 50) TA TB
        Hf He Hhalt R17 R10 Hal Hpos R11 Hlenpos HaK Hisp R12 R13
        AsanNodesMmLib.mmap_flags_core_32 R14 R15
        (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) rfl Hrf CONTA ?_
      · rw [AsanNodesMmLib.with_mmap_backing_plain _ _ _ _
          AsanNodesMmLib.mmap_noreserve_b_32]
        refine CONT (noaccess_model (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model)
          (unfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
        · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [Hkindn]; rfl
          · rw [Hkln]; rfl
        · refine ⟨?_, ?_⟩
          · intro x hx
            refine MmapSim.unfill_out _ _ _ _ ?_
            simpa only [Un] using hx
          · intro x hx
            refine AsanNodesMmLib.unfill_in _ _ _ _ ?_
            simpa only [Un] using hx
  | KNONELAZY =>
    simp only [AsanNodesMmLib.kind_none, AsanNodesMmLib.kind_lazy, Bool.or_true,
      Bool.not_false, Bool.not_true] at Hkind H12 H13
    cases eager with
    | true => simp at Hkind
    | false =>
      have Hkindn : AsanNodesMmLib.kind_none mkind.KNONELAZY = true := rfl
      have Hkln : AsanNodesMmLib.kind_lazy mkind.KNONELAZY = true := rfl
      refine AsanNodesMmLib.srz_mmap_fixed_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL
        (seg_rom SEGS) model w (edenot E (reg cs 10))
        (bv_unsigned (edenot E (reg cs 11))) (Z_to_bv 64 16434) TA TB
        Hf He Hhalt R17 R10 Hal Hpos R11 Hlenpos HaK Hisp R12 R13
        AsanNodesMmLib.mmap_flags_core_4032 R14 R15
        (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))) rfl (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) rfl Hrf CONTA ?_
      · rw [AsanNodesMmLib.with_mmap_backing_lazy _ _ _ _
          AsanNodesMmLib.mmap_noreserve_b_4032]
        refine CONT (vm_add_lazy (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11)))))
          (noaccess_model (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) model))
          (unfill (edenot E (reg cs 10)) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) FULL) ?_ ?_ rfl
        · refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · rw [Hkindn]; rfl
          · unfold vm_add_lazy
            rw [m_vm_lazy_with_vm_backing, hli, Hkln]
            simp only [ite_true]
            rfl
        · refine ⟨?_, ?_⟩
          · intro x hx
            refine MmapSim.unfill_out _ _ _ _ ?_
            simpa only [Un] using hx
          · intro x hx
            refine AsanNodesMmLib.unfill_in _ _ _ _ ?_
            simpa only [Un] using hx

theorem mmap_fixed_free_sound2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (cs : acs) (kd : mkind) (eager visible : Bool) (cs' : acs)
    (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model) (TA TB : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hec : is_ecall_at SEGS cs = true)
    (H17 : reg_lit cs 17 = some 222)
    (H12 : reg_lit cs 12 = some (if AsanNodesMmLib.kind_none kd then 0 else 3))
    (H13 : reg_lit cs 13 = some (if AsanNodesMmLib.kind_lazy kd then 16434 else 50))
    (H14 : reg_lit cs 14 = some (two64 - 1)) (H15 : reg_lit cs 15 = some 0)
    (Hkind : (AsanNodesMmLib.kind_none kd || AsanNodesMmLib.kind_lazy kd) = !eager)
    (Hkfog : is_tok_kind kd = false)
    (Hvisible : visible = eager)
    (Hn : mmap_fixed_free A nx0 LIMIT cs kd eager visible = some cs')
    (HKA : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA)
    (HK : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') TB) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB) := by
  unfold mmap_fixed_free at Hn
  dsimp only at Hn
  split at Hn
  · -- the classic path: no tokens, every tracked entry provably apart
    rename_i b off ne nlo nhi HFA
    cases hcond : (no_fog cs.a_maps
        && cs.a_maps.all (fun m => ranges_apart_x (kn cs) b off ne m.am_base 0 m.am_len)
        && (!eager || budget_ok LIMIT cs nhi) && AsanPlanCore.expr_vars_lt (nxt cs) ne
        && AsanPlanCore.expr_vars_lt (nxt cs) (AsanPlanCore.reg cs 10)) with
    | false => rw [hcond] at Hn; simp at Hn
    | true =>
      rw [hcond] at Hn
      simp only [ite_true] at Hn
      have hcond' := hcond
      simp only [Bool.and_eq_true, and_assoc] at hcond'
      obtain ⟨Hnf, Hall, Hbud, -, -⟩ := hcond'
      have HbudT : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
        intro he
        rw [he] at Hbud
        simp only [Bool.not_true, Bool.false_or] at Hbud
        unfold budget_ok at Hbud
        simpa only [decide_eq_true_eq] using Hbud
      obtain ⟨HC0, Hrf, Hholes, Hside⟩ :=
        AsanNodesMmLib.mmap_fixed_old_facts SEGS A LIMIT nx0 SINV argH FS0 RES_hull cs b off ne
          nlo nhi E R FULL model (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
          HC HFA Hnf Hall rfl
      exact mmap_fixed_grant_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok
        SHADOW_ok argH_high SINV_frame cs cs.a_maps KHI b off ne nlo nhi kd eager visible cs'
        E R FULL model TA TB HC Hec H17 H12 H13 H14 H15 Hkind Hkfog Hvisible HFA (by decide)
        Hbud HC0 Hrf Hholes Hside Hn HKA HK
  · -- the HOLE path
    split at Hn
    · rename_i b off ne nlo nhi HFA2
      split at Hn
      · rename_i h Hfh
        cases hcond : ((unhole cs.a_maps h).all (fun m =>
            !is_hole m || ranges_apart_x (kn cs) b off ne m.am_base 0 m.am_len)
            && (!eager || budget_ok LIMIT cs nhi) && AsanPlanCore.expr_vars_lt (nxt cs) ne
            && AsanPlanCore.expr_vars_lt (nxt cs) (AsanPlanCore.reg cs 10)) with
        | false => rw [hcond] at Hn; simp at Hn
        | true =>
          rw [hcond] at Hn
          simp only [ite_true] at Hn
          have hcond' := hcond
          simp only [Bool.and_eq_true, and_assoc] at hcond'
          obtain ⟨Hap, Hbud, -, -⟩ := hcond'
          have HbudT : eager = true → cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
            intro he
            rw [he] at Hbud
            simp only [Bool.not_true, Bool.false_or] at Hbud
            unfold budget_ok at Hbud
            simpa only [decide_eq_true_eq] using Hbud
          obtain ⟨HC0, Hrf, Hholes, Hside⟩ :=
            AsanNodesMmLib.mmap_fixed_hole_facts SEGS A LIMIT nx0 SINV argH FS0 cs b off ne nlo
              nhi h E R FULL model (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))
              HC HFA2 Hfh Hap rfl
          exact mmap_fixed_grant_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok
            SHADOW_ok argH_high SINV_frame cs (unhole cs.a_maps h) CEIL b off ne nlo nhi kd eager
            visible cs' E R FULL model TA TB HC Hec H17 H12 H13 H14 H15 Hkind Hkfog Hvisible
            HFA2 (Int.le_refl CEIL) Hbud HC0 Hrf Hholes Hside Hn HKA HK
      · simp at Hn
    · simp at Hn

theorem node_mmap2_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT) := by
  intro cs csa csb E R FULL model TA TB HC Hec Hn HKA HKB
  unfold node_mmap2 at Hn
  dsimp only at Hn
  split at Hn
  · rename_i prot flags isnull Hg
    obtain ⟨H17, H12, H13, H14, H15, H10⟩ := mmap_gate_sound cs prot flags isnull Hg
    cases isnull with
    | true =>
      simp only [ite_true] at Hn
      split at Hn
      · rename_i csG heq
        split at heq
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_null_sound2 SEGS A nx0 LIMIT SINV argH FS0 PLACEMENT SEGS_in_hull RES_len
            HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree cs .KRW true true _
            E R FULL model TA TB HC Hec H17 (H10 rfl) H12 H13 H14 H15 (by decide) (by decide)
            (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_null_sound2 SEGS A nx0 LIMIT SINV argH FS0 PLACEMENT SEGS_in_hull RES_len
            HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree cs .KRWLAZY false true _
            E R FULL model TA TB HC Hec H17 (H10 rfl) H12 H13 H14 H15 (by decide) (by decide)
            (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_null_sound2 SEGS A nx0 LIMIT SINV argH FS0 PLACEMENT SEGS_in_hull RES_len
            HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree cs .KNONE false false _
            E R FULL model TA TB HC Hec H17 (H10 rfl) H12 H13 H14 H15 (by decide) (by decide)
            (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_null_sound2 SEGS A nx0 LIMIT SINV argH FS0 PLACEMENT SEGS_in_hull RES_len
            HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree cs .KNONELAZY false false
            _ E R FULL model TA TB HC Hec H17 (H10 rfl) H12 H13 H14 H15 (by decide) (by decide)
            (by decide) heq HKA HKB
        · simp at heq
      · simp at Hn
    | false =>
      simp only [Bool.false_eq_true, ite_false] at Hn
      split at Hn
      · rename_i csG heq
        split at heq
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_fixed_free_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len
            RES_hull HULL_ok SHADOW_ok argH_high SINV_frame cs .KRWLAZY false false _ E R FULL
            model TA TB HC Hec H17 H12 H13 H14 H15 (by decide) (by decide) (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_fixed_free_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len
            RES_hull HULL_ok SHADOW_ok argH_high SINV_frame cs .KRW true true _ E R FULL model
            TA TB HC Hec H17 H12 H13 H14 H15 (by decide) (by decide) (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_fixed_free_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len
            RES_hull HULL_ok SHADOW_ok argH_high SINV_frame cs .KNONELAZY false false _ E R FULL
            model TA TB HC Hec H17 H12 H13 H14 H15 (by decide) (by decide) (by decide) heq HKA HKB
        · simp only [Option.some.injEq, Prod.mk.injEq] at Hn
          obtain ⟨rfl, rfl⟩ := Hn
          exact mmap_fixed_free_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len
            RES_hull HULL_ok SHADOW_ok argH_high SINV_frame cs .KNONE false false _ E R FULL
            model TA TB HC Hec H17 H12 H13 H14 H15 (by decide) (by decide) (by decide) heq HKA HKB
        · simp at heq
      · simp at Hn
  · simp at Hn

theorem node_mmap2_sound_OBL (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    OBL_mmap2 SEGS A nx0 LIMIT SINV argH FS0 := by
  unfold OBL_mmap2
  exact node_mmap2_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_hull
    HULL_ok SHADOW_ok argH_high argH_agree SINV_frame SINV_agree PLACEMENT

theorem node_mmapin_sound_OBL (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    OBL_mmapin SEGS A nx0 LIMIT SINV argH FS0 := by
  intro hole
  exact node_mmapin_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_hull
    HULL_ok SHADOW_ok argH_high SINV_frame hole

/-! ## 11. mprotect of a slice of a PROT_NONE entry -/

theorem node_mprotect_sound2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (cs cs' : acs) (E : env) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (TA TB : TSet)
    (HC : cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model)
    (Hec : is_ecall_at SEGS cs = true)
    (Hn : node_mprotect A LIMIT cs = some cs')
    (HKA : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' (refuse cs) R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc (refuse cs)) FULL' model') TA)
    (HK : ∀ E' R' FULL' model', env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
      cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL' model' →
      m_fs model' = m_fs model →
      srealizes SEGS (cfg_of SEGS R' (pc cs') FULL' model') TB) :
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB) := by
  obtain ⟨w, Hf, He, Hp0, Hp4⟩ := AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec
  rw [node_mprotect_eq] at Hn
  unfold node_mprotect_ref at Hn
  dsimp only at Hn
  split at Hn
  case h_2 => exact absurd Hn (by simp)
  case h_1 =>
    rename_i _e1 _e2 _e3 b off ne nlo nhi h17 h12 hfa
    cases hfc : find_containing (kn cs) cs.a_maps [.KNONE, .KNONELAZY] b off ne with
    | none => rw [hfc] at Hn; simp at Hn
    | some m =>
      rw [hfc] at Hn
      cases hbud : (budget_ok LIMIT cs nhi && AsanPlanCore.expr_vars_lt (nxt cs) ne &&
          AsanPlanCore.expr_vars_lt (nxt cs) (AsanPlanCore.reg cs 10)) with
      | false => rw [hbud] at Hn; simp at Hn
      | true =>
        rw [hbud] at Hn
        simp only [ite_true] at Hn
        have HbudB : budget_ok LIMIT cs nhi = true := by
          have h := hbud
          simp only [Bool.and_eq_true, and_assoc] at h
          exact h.1
        have HbudT : cs.a_eager + cs.a_abytes + nhi ≤ LIMIT := by
          unfold budget_ok at HbudB
          simpa only [decide_eq_true_eq] using HbudB
        have R17 : getr R 17 = Z_to_bv 64 226 :=
          (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 17 226
            HC (by decide) h17).1
        have R12 : getr R 12 = Z_to_bv 64 3 :=
          (AsanPlanSound.reg_lit_sound SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model 12 3
            HC (by decide) h12).1
        obtain ⟨Hm, ⟨Hkind, Hnf⟩, R10, R11, Hlenpos, Hlenlt, Hne, hbvnZ, HnZpos, HnZle,
          HnZal, Hal, Hapos, Himg, Hest, Hin1, Hin2, HmC, Hmc, Hrfres, Hov⟩ :=
          AsanNodesMmLib.slice_args SEGS A LIMIT nx0 SINV argH FS0 RES_hull E cs R FULL model
            b off ne nlo nhi [.KNONE, .KNONELAZY] m _ HC hfa hfc rfl
        have Hkind' : m.am_kind = .KNONE ∨ m.am_kind = .KNONELAZY := by
          simpa using Hkind
        have Hna : map_contains (m_vmmaps model).vm_noaccess (edenot E (AsanPlanCore.reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = true := by
          refine AsanNodesMmLib.map_contains_intro _ _ _ _ _ (HC.co_none m Hm Hkind') Hin1 ?_
          simp only [hbvnZ]
          exact Hin2
        have Hhalt : m_halted model = none := HC.co_halt
        have Hsum : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) +
            page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) ≤ CEIL := by
          have h := Int.le_trans Hin2 HmC
          simpa only [hbvnZ] using h
        have Hbnd : bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) +
            page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) < two_pow_64 := by
          have hC : CEIL < two_pow_64 := by unfold CEIL two_pow_64; decide
          exact Int.lt_of_le_of_lt Hsum hC
        have Hbudget : vm_backing_used model +
            page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) ≤
            (m_vmmaps model).vm_limit := by
          have h := AsanNodesMmLib.budget_slack SEGS A LIMIT nx0 SINV argH FS0 E cs R FULL model
            nhi HC HbudB
          exact Int.le_trans (Int.add_le_add_left HnZle (vm_backing_used model)) h
        have Hmb : mprotect_budget_ok model (edenot E (AsanPlanCore.reg cs 10))
            (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) = true := by
          refine mprotect_budget_ok_intro_gen model _ _ HC.co_wf ?_
          refine Int.le_trans ?_ Hbudget
          exact Int.add_le_add_left Hov (vm_backing_used model)
        unfold cfg_of
        refine AsanNodesMmLib.srz_mprotect2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w
          (edenot E (AsanPlanCore.reg cs 10))
          (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) TA TB
          Hf He Hhalt R17 R10 Hal R11 Hlenpos Hbnd R12
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))) rfl
          Hna Hmc Hmb ?_ ?_
        · exact AsanNodesMmLib.refuse_cont SEGS A LIMIT nx0 SINV argH FS0 cs E R FULL model TA
            HC Hp0 Hp4 HKA
        · -- the granted continuation
          obtain ⟨_nhi2, _hxhi, hEcs⟩ :=
            AsanNodesMmLib.vis_add_inv A LIMIT _ (AsanPlanCore.reg cs 10) ne _ cs' Hn
          have Hpc : pc cs' = pc cs + 4 := by rw [hEcs]; rfl
          have hzin : (∀ x : word,
              (bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ≤ bv_unsigned x ∧
              bv_unsigned x < bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) +
                page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))) →
              zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL x = some (Z_to_bv 8 0)) := by
            intro x hx
            refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
            simpa only [hbvnZ] using hx
          have hSPo : AsanNodesMmLib.slice_post .SlM (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              model (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) := by
            refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [AsanNodesMmLib.sl_nn]
            rfl
          have hSM : AsanNodesMmLib.slice_mem .SlM (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              FULL (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) := by
            refine ⟨?_, ?_⟩
            · intro x hx
              refine MmapSim.zfill_out _ _ _ _ ?_
              simpa only [hbvnZ] using hx
            · intro x hx
              have h1 : zfill (edenot E (AsanPlanCore.reg cs 10))
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                  FULL x = some (Z_to_bv 8 0) := by
                refine AsanNodesMmLib.zfill_in _ _ _ _ ?_
                simpa only [hbvnZ] using hx
              rw [h1]
              simp only [AsanNodesMmLib.sl_nn]
              rfl
          have hSH : AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlM m
              (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))
              (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) := by
            refine ⟨HC, Hm, Hnf, hbvnZ, HnZpos, HnZal, Hal, Hin1, Hin2, hSPo, hSM, ?_, ?_⟩
            · intro h; exact absurd h (by decide)
            · intro _ hk
              rw [hk] at Hkind'
              exact absurd Hkind' (by simp)
          have hMRout : (∀ x : word,
              bv_unsigned x < estart E (SA b off) ∨
              estart E (SA b off) + elenZ E ne ≤ bv_unsigned x →
              Mr A argH E cs (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) x = Mr A argH E cs model FULL x) := by
            intro x hx
            have hx' : bv_unsigned x < bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) ∨
                bv_unsigned (edenot E (AsanPlanCore.reg cs 10)) +
                  page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))) ≤
                  bv_unsigned x := by
              rw [Hest] at hx
              simpa only [elenZ, Hne, hbvnZ] using hx
            exact AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 E cs R FULL model .SlM m
              (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              _ (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) hSH cs x rfl hx'
          have Hregs' : regs_ok E (sr_upd cs.a_ss.s_regs 10 (.ELit 0)) (regupd R 10 0) := by
            refine AsanPlanSound.regs_ok_set_n E cs.a_ss.s_regs R 10 (.ELit 0) (Z_to_bv 64 0)
              HC.co_regs (by decide) ?_
            rfl
          have Hk' : know_ok SEGS E (Mr A argH E cs (RefNodes.mprotect_model
              (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              model) (zfill (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              FULL)) (kimg_clip A (kn_unfill (kn cs) b off ne)) := by
            refine AsanNodesMmLib.kn_unfill_clip_ok SEGS A E _ _ (kn cs) b off ne HC.co_know ?_ hMRout
            rw [Hest]
            exact Himg
          have HC1 : cs_ok SEGS A LIMIT SINV argH FS0 E
              (ACS (mk_ss (pc cs + 4) (sr_upd cs.a_ss.s_regs 10 (.ELit 0))
                (kimg_clip A (kn_unfill (kn cs) b off ne)) cs.a_ss.s_next)
                (rekind cs.a_maps m) cs.a_totsz cs.a_ylo (cs.a_eager + nhi) cs.a_vis cs.a_ghost
                cs.a_abytes cs.a_brk cs.a_fd cs.a_tidset)
              (regupd R 10 0) (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) :=
            AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 argH_high SINV_frame E cs R FULL
              model .SlM m (edenot E (AsanPlanCore.reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
              (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))
              (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) hSH (sr_upd cs.a_ss.s_regs 10 (.ELit 0)) (regupd R 10 0)
              (kimg_clip A (kn_unfill (kn cs) b off ne)) (pc cs + 4) cs.a_ss.s_next nhi
              Hregs' Hk' HnZle (fun _ => HbudT)
          have hCS2 : cs_ok SEGS A LIMIT SINV argH FS0 E cs' (regupd R 10 0)
              (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) := by
            refine AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT nx0 SINV argH FS0 SEGS_in_hull
              HULL_ok SHADOW_ok argH_high E _ cs' (AsanPlanCore.reg cs 10) b off ne (regupd R 10 0)
              (zfill (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                FULL) (RefNodes.mprotect_model (edenot E (AsanPlanCore.reg cs 10))
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                model) (bv_unsigned (edenot E (AsanPlanCore.reg cs 10)))
              (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11))))
              HC1 Hn ?_ rfl Hest ?_ (Int.le_of_lt Hapos) HnZpos Hsum ?_
            · simpa only [kn, mk_ss] using (kimg_clip_in_hull A (kn_unfill (kn cs) b off ne))
            · simp only [elenZ, Hne, hbvnZ]
            · intro x hx
              obtain ⟨hx1, hx2⟩ := hx
              refine ⟨?_, ?_, ?_, ?_⟩
              · have hmaps := AsanNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model
                  .SlM m (edenot E (AsanPlanCore.reg cs 10))
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                  _ _ _ hSH x ⟨hx1, hx2⟩
                rw [hSPo.sp_maps]
                exact hmaps
              · have hnoacc := AsanNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 E cs R FULL
                  model .SlM m (edenot E (AsanPlanCore.reg cs 10))
                  (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (AsanPlanCore.reg cs 11)))))
                  _ _ _ hSH x ⟨hx1, hx2⟩
                simpa only [AsanNodesMmLib.sl_nn] using hnoacc
              · rcases Bool.eq_false_or_eq_true (argH E x) with harg | harg
                · exact absurd (Int.lt_of_le_of_lt (argH_high E x harg)
                    (Int.lt_of_lt_of_le hx2 Hsum)) (Int.lt_irrefl CEIL)
                · exact harg
              · exact hzin x ⟨hx1, hx2⟩
          rw [AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4, ← Hpc]
          refine HK E (regupd R 10 0) _ _ ⟨AsanNodesMmLib.env_agree_refl' _ _,
            AsanNodesMmLib.env_agree_refl' _ _⟩ hCS2 rfl

theorem node_mprotect2_sound (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M') :
    mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT) := by
  intro cs csa csb E R FULL model TA TB HC Hec Hn HKA HKB
  unfold node_mprotect2 at Hn
  cases hg : node_mprotect A LIMIT cs with
  | none => rw [hg] at Hn; simp at Hn
  | some csG =>
    rw [hg] at Hn
    simp only [Option.some.injEq, Prod.mk.injEq] at Hn
    obtain ⟨rfl, rfl⟩ := Hn
    exact node_mprotect_sound2 SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_hull
      HULL_ok SHADOW_ok argH_high SINV_frame cs csG E R FULL model TA TB HC Hec hg HKA HKB

theorem node_mprotect2_sound_OBL (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs)
    (SEGS_in_hull : ∀ a : word, in_hull A (bv_unsigned a) = false →
      find_segment SEGS (bv_unsigned a) 1 = none)
    (RES_len : res_len_ok SEGS A) (RES_hull : AsanNodesMmLib.RES_hull_def SEGS A)
    (HULL_ok : hull_ok A) (SHADOW_ok : shadow_ok A)
    (argH_high : ∀ (E : env) (a : word), argH E a = true → CEIL ≤ bv_unsigned a)
    (argH_agree : ∀ (E E' : env) (a : word), env_agree nx0 E E' → argH E a = argH E' a)
    (SINV_frame : ∀ (E : env) (M M' : word → Option byte),
      (∀ a : word, argH E a = true → M' a = M a) → SINV E M → SINV E M')
    (SINV_agree : ∀ (E E' : env) (M : word → Option byte), env_agree nx0 E E' → SINV E M → SINV E' M)
    (PLACEMENT : placement_policy) :
    OBL_mprotect2 SEGS A nx0 LIMIT SINV argH FS0 := by
  unfold OBL_mprotect2
  exact node_mprotect2_sound SEGS A nx0 LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_hull
    HULL_ok SHADOW_ok argH_high SINV_frame

/-! ## COMPLETENESS — every declaration is here

  Sixteen items, all proved in this file.  The last three — the M2 chain `mmap_fixed_in_sound3` (:697),
  `node_mmapin_sound` (:886) and `node_mmapin_sound_OBL` (:939) — are the
  three-child `MAP_FIXED`-inside-one-tracked-entry node, its `mmap_gate` +
  `(prot, flags)` dispatch, and the obligation exactly as `AsanNodesIface`
  declares it .
-/

end LinuxSem.Common.AsanNodesMmA
