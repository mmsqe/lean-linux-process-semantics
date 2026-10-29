/-

  * AsanNodesIface — what helper "nodes" proves (files AsanNodesMm*)

    The plan checker [AsanPlan.AP.check] is proved sound
    ([AsanPlanSound.APS.check_sound], conclusion [SpinAlg.srealizes]) from
    per-node statements that are Section hypotheses of [APS].  This file
    CLOSES those statements over the Section parameters, under the standard
    parameter/hypothesis block every node package uses, and names one
    obligation per node.  An integration file instantiates them at the image
    and the start-up / main-phase invariants.

    PARAMETER BLOCK (open this Section verbatim in your files):

      Section Nodes.
      Variable SEGS : list Segment.            Variable A : atable.
      Variable nx0 : nat.                      Variable LIMIT : Z.
      Variable SINV : env -> (word -> option byte) -> Prop.
      Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
      Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
      Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
      Hypothesis RES_len : res_len_ok SEGS A.          (= length (segments_reserved SEGS) = n_res A)
      Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                                   (segments_reserved SEGS).
      Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
      Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
      Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
      Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
      Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    (you may add the hypothesis [LIMIT = target_alloc_limit] if a budget
    argument needs the number; nothing else).

    OBLIGATIONS (Lemma names fixed; statements are the [OBL_*] below with the
    parameters of the block; all conclusions are [srealizes] — anything you
    prove with [ShapeAlg.realizes] lifts by [SpinAlg.srealizes_of_realizes];
    two/three-child conclusions [t_alt2 TA TB] / [t_alt2 TA (t_alt2 TB TC)]
    are assembled with [SpinAlg.srz_node]/[srz_alt2] over the index type of
    the spec's resolutions — see AsanNodesMmA / AsanNodesMmB for
    the cs_ok re-establishment per arm, and RefNodes / MmapSim /
    AllocSim / NoReserve for the spec's inversion lemmas):

    M1 [node_mmap2_sound   : OBL_mmap2]     [AP.node_mmap2 A nx0 LIMIT]   (checker: AsanPlanCore §8.3)
         child a = REFUSED ([APC.refuse]: a0 := 2^64-12, pc+4, model unchanged; spec arm
         [e <- errno_from [ENOMEM];; err_ret e]);
         child b = GRANTED: NULL hint ([APC.mmap_null]; arms P (3,0x22) / A (3,0x4022) / B0 (0,0x22) / B (0,0x4022);
         spec [mmap_modeled_b]/[mmap_noaccess_b] NULL-hint branches, [choose a. …]; the grant witness comes from
         [APC.gap_ok] via [AsanPlacement.free_gap_of_totals] + [co_totsz] + [RES_len], placement LOWER bound
         (new base > KHI) from [co_split] via [AsanPlacement.kHighMemBeg_le]/[null_hint_grant_step],
         budget (arm P only) from [APC.budget_ok] + [co_eager] + [co_abytes] + [co_minv])
         or FIXED over a FREE range ([APC.mmap_fixed_free]; arms C (3,0x4032) / C0 (3,0x32) / D (0,0x4032) / D0 (0,0x32);
         spec: the [region_free (vm_reserved h ++ vm_maps h) addr n] sub-branches with [choose a. a = addr /\ …]).
    M2 [node_mmapin_sound  : OBL_mmapin]    [AP.node_mmapin A LIMIT]
         MAP_FIXED wholly inside ONE tracked entry (spec: [region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n]
         branches of [mmap_fixed_noaccess_b] / [mmap_fixed_rw_b]): child a = REFUSED-kept ([APC.refuse]);
         child b = OK ([APC.mmap_fixed_in] arm E (3,0x32) / F (3,0x4032) / G (0,0x32 or 0,0x4032); post-model
         [with_mmap_replacement flags addr n (with_vmmaps …)]); child c = REFUSED-destroyed ([APC.mmap_destroyed]:
         [with_mmap_destroyed addr n h'] with both ledgers [maps_subtract]ed, effect unmaps [addr, addr+n)).
    M3 [node_mprotect2_sound : OBL_mprotect2] [AP.node_mprotect2 A LIMIT]
         child a = REFUSED; child b = [APC.node_mprotect] (Mprotect: [map_contains noaccess && map_contains maps] branch).
    M4 [node_brk2_sound    : OBL_brk2]      [AP.node_brk2 A LIMIT]   (Mmap [brk_r_ok] GROW:
         child a = stay (r = b), child b = grow (r = req, [brk_grow_ok])).
    M5 [node_sys_sound     : OBL_sys]       [AP.node_sys A nx0 y] for y ∈ {YMunmap, YBrk, YSetTid}
         (munmap of exactly one tracked entry — deterministic; brk query / provably blocked grow — r = b only;
          set_tid_address).
    M6 [node_exit_sound    : OBL_exit]      [APC.node_exit]  (exit 93 / exit_group 94 → [t_exit]).
    The [PSpin] leaf, PRun, PX summaries, PFresh, PJoin and hooks are not node obligations.
  `Iface`.  The  file is an INTERFACE: it declares no proofs beyond
  one definitional unfolding ([OBL_mmap2_unfold]), so this module is the six
  obligation statements, their conjunction and that unfolding.

  NOTES.

  - SECTION VARIABLES.   - `Z` is `Int`, `nat` is `Nat`, `list Segment` is `List Segment`,
    `word -> option byte` is `word → Option byte`, `Fs.Fs` is `Fs.Fs`
    (`LinuxSem.LinuxProcessSem.Fs.Fs`), `env` is
    `AxSymExec3.env`, `snode` is `AsanPlan.snode`.  `OBL_exit`
    therefore passes `nx0` through.   - Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.AsanPlan

namespace LinuxSem.Common.AsanNodesIface

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
open LinuxSem.Common.AsanPlanSound
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! -/

/-- `M1`: `mmap` with both outcomes (refused / granted). -/
def OBL_mmap2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT)

/-- `M2`: `MAP_FIXED` wholly inside one tracked entry — three resolutions
    (refused-kept / ok / refused-destroyed). -/
def OBL_mmapin (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  ∀ hole : Bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A nx0 LIMIT hole)

/-- `M3`: `mprotect` with both outcomes (refused / re-kinded). -/
def OBL_mprotect2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT)

/-- `M4`: `brk` grow with both outcomes (stay / grow). -/
def OBL_brk2 (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  brk2_stmt SEGS A nx0 LIMIT SINV argH FS0

/-- `M5`: the deterministic syscall nodes (`munmap` / `brk` query /
    `set_tid_address`). -/
def OBL_sys (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  ∀ y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y

/-- `M6`: the exit leaf. -/
def OBL_exit (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  exit_stmt SEGS A nx0 LIMIT SINV argH FS0

/-- All of them — what an integration file assumes about one image / one
    invariant. -/
def OBL_all (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    Prop :=
  OBL_mmap2 SEGS A nx0 LIMIT SINV argH FS0 ∧ OBL_mmapin SEGS A nx0 LIMIT SINV argH FS0 ∧
    OBL_mprotect2 SEGS A nx0 LIMIT SINV argH FS0 ∧ OBL_brk2 SEGS A nx0 LIMIT SINV argH FS0 ∧
    OBL_sys SEGS A nx0 LIMIT SINV argH FS0 ∧ OBL_exit SEGS A nx0 LIMIT SINV argH FS0

/-- Unfolded reading of the two-child template, for reference
    (definitionally equal to `OBL_mmap2`; do not restate it differently). -/
theorem OBL_mmap2_unfold (SEGS : List Segment) (A : atable) (nx0 : Nat) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs) :
    OBL_mmap2 SEGS A nx0 LIMIT SINV argH FS0 ↔
      ∀ (cs csa csb : acs) (E : env) (R : BvMap word) (FULL : word → Option byte)
        (model : Model) (TA TB : TSet),
        cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model →
        is_ecall_at SEGS cs = true →
        node_mmap2 A nx0 LIMIT cs = some (csa, csb) →
        (∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
            env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
            cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' →
            m_fs model' = m_fs model →
            srealizes SEGS (cfg_of SEGS R' (pc csa) FULL' model') TA) →
        (∀ (E' : env) (R' : BvMap word) (FULL' : word → Option byte) (model' : Model),
            env_agree nx0 E E' ∧ env_agree (nxt cs) E E' →
            cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' →
            m_fs model' = m_fs model →
            srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) →
        srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) (t_alt2 TA TB) := by
  unfold OBL_mmap2 mm2_stmt
  exact Iff.rfl

end LinuxSem.Common.AsanNodesIface
