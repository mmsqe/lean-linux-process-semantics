/-
  * Common.AsanAcct — accounted machine steps via RESTRICTED memory

  Image-independent proof library over the trusted spec
  [LinuxSem].
  Dependencies: spec files + [CatSim] (for [msteps]) + [PropExec] (for
  [mkst]; one lemma).  Axioms used: functional extensionality only.

  ----------------------------------------------------------------------
  PURPOSE
  ----------------------------------------------------------------------
  After the ASan runtime's MAP_NORESERVE reservations, [m_vm_lazy model]
  is non-empty for the rest of the run, so EVERY instruction step goes
  through [Run.mi_account_step]: the access report of
  [RiscvSemantics.step_accesses] is fed to
  [State.materialize_model_accesses], which may charge lazy pages to the
  backing budget or FAIL (MachineFault) when the budget is exhausted.
  The stock node lemmas ([ShapeAlg.node_instr]/[rz_msteps]) assume
  [m_vm_lazy model = []] and are unusable there.

  This library lets the symbolic executor keep producing PLAIN
  [RiscvSemantics.step] chains ([CatSim.msteps]) — but on a RESTRICTED
  machine state [restrict H ms] whose overlay memory reads [None] at
  every "hidden" address ([H a = true]).  Because hidden addresses are
  off every loaded segment, an instruction that succeeds on the
  restricted state cannot have touched a hidden byte; so (1) it succeeds
  on the full state with the same result modulo the hidden bytes, (2)
  its access report avoids [H], hence (3) the only lazy pages it can
  materialize are "allowed" ones (hypothesis [lazy_cover]), whose total
  is budgeted for once and for all by the invariant [MInv].  Result: the
  accounted [sstep] exists, is the unique [sstep] from the
  configuration, preserves [MInv], and changes the model only in its
  materialized-page ledger.

  ----------------------------------------------------------------------
  DEFINITIONS (Part 1, 3)
  ----------------------------------------------------------------------
  [mrestrict H m a   := if H a then none else m a]        (overlay level)
  [munrestrict H full m' a := if H a then full a else m' a]
  [restrict H ms]    : [ms] with [ms_mem := mrestrict H (ms_mem ms)]
  [unrestrict H full ms'] : [ms'] with [ms_mem := munrestrict H full (ms_mem ms')]
  [hclean H ms]      : [forall a, H a = true -> ms_mem ms a = none]
                       (fixed points of [restrict H]; [restrict_hclean],
                       [hclean_restrict_id], [restrict_unrestrict_clean])
  [H_off_segments segs H] : [forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = none]
  [wx_segs_nowrap segs]   : every w+x segment ends <= 2^64 (vacuous for
                       an image with no w+x segment)
  [woff a k := Z_to_bv 64 (bv_unsigned a + Z.of_nat k)]  (k-th byte of a
                       range, cursor in Z like [State.access_pages_acc])
  [range_avoids H a n := forall k < n, H (woff a k) = false]
  [ranges_avoid H l  := forall (a,n) ∈ l, range_avoids H a n]
  [page_allowedb A p] : page [p] (a word, its base) fits in some interval
                       of [A : list (Z*Z)] (pairs <<(lo,hi)>>, meaning [lo,hi))
  [A_wf A]           : every interval has lo <= hi, both multiples of 4096
                       (disjointness NOT required)
  [A_bytes A]        : Σ (hi - lo)
  [lazy_cover H lazy A := forall w, page_in_ranges (page_base w) lazy = true ->
                          H w = false -> page_allowedb A (page_base w) = true]
  [eager_used m := live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m))]
                       so [vm_backing_used m = eager_used m + |materialized|*4096]
                       ([vm_backing_used_split], by reflexivity)
  [MInv A m] (Record): NoDup materialized (List.NoDup!) /\ all materialized
                       pages aligned /\ allowed /\ inside the lazy ledger /\
                       [eager_used m + A_bytes A <= vm_limit (m_vmmaps m)]
  [same_but_materialized m m' := m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m]
                       (refl/trans; [same_but_materialized_frame] lists all
                       equal accessors incl. m_halted, m_fs, m_vmmaps,
                       m_vm_lazy, eager_used)
  [node_ok segs c I evs nx] : verbatim copy of [ShapeAlg.node_ok] (convertible)
  [materialized_succ m accs] : the model after materializing [accs] (total fn)
  [mkH L A a := page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a))]
                       a canonical hidden set (Part 6)

  ----------------------------------------------------------------------
  MAIN RESULTS
  ----------------------------------------------------------------------
  Part 2 — ISA monotonicity (Section ISA: segs H, hyps HH : H_off_segments
  segs H, Hwx : wx_segs_nowrap segs; closed lemmas take (segs H HH Hwx)
  first, or fewer when unused):
  - [ov_read_bytes_restrict], [store_ok_restrict], [wview_restrict],
    [write_to_mem_restrict], [write_to_mem_hidden],
    [code_read_ov_restrict] / [fetch_word_ov_restrict] /
    [fetch_tail_any_restrict] / [fetch_failure_restrict] (plain equalities),
    [interp_eff_accesses_restrict] (induction over the effect tree),
    [decode_exec_accesses_restrict].
  - [step_accesses_restrict]:
      step_accesses segs (restrict H ms) = MachineOk (mkAccessReport msr' rs') ->
      step_accesses segs ms = MachineOk (mkAccessReport (unrestrict H (ms_mem ms) msr') rs')
      /\ ranges_avoid H rs' /\ hclean H msr'.
  - [step_restrict_sound]:
      step segs (restrict H ms) = MachineOk msr' ->
      exists rep, step_accesses segs ms = MachineOk rep
        /\ access_value rep = unrestrict H (ms_mem ms) msr'
        /\ ranges_avoid H (accessed_ranges rep) /\ hclean H msr'
        /\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
  - [step_restrict_step]: ... -> step segs ms = MachineOk (unrestrict H (ms_mem ms) msr').
  - [step_accesses_ecall_shape]: a successful step that sets svc_pending
    has no accesses, unchanged memory/registers, svc = Some (ms_reg ms 17).
  - visible-direction transfer (no hypothesis on H): [mrestrict_visible],
    [ov_read_bytes_mrestrict_eq], [rdn_mrestrict_eq] (PropExec.rdn),
    [wview_mrestrict_eq], [store_ok_mrestrict_eq] — equalities under
    [range_avoids H a n], to restate base-memory knowledge for
    [mrestrict H mem] when seeding the executor.
  - projections: [restrict_svc_pending], [restrict_pc], [restrict_regs],
    [restrict_reg], [restrict_rom], [restrict_mem], [restrict_mkst]
    (restrict H (mkst r pc mem rom) = mkst r pc (mrestrict H mem) rom), all
    by reflexivity; [unrestrict_restrict], [restrict_unrestrict].

  Part 3 — accounting (no segs):
  - [allowed_pages_bound]: A_wf A -> List.NoDup pages -> all aligned ->
      all allowed -> |pages| * 4096 <= A_bytes A           (pigeonhole)
  - [materialize_restricted]:
      lazy_cover H (m_vm_lazy m) A -> A_wf A -> MInv A m -> ranges_avoid H ranges ->
      exists mat', materialize_model_accesses m ranges
                     = Some (with_vm_backing (m_vm_lazy m) mat' m)
                   /\ MInv A (with_vm_backing (m_vm_lazy m) mat' m).
    (the result IS [same_but_materialized m _]: [with_vm_backing_same])
  - [MInv_intro_empty] (materialized = [] : only the budget is needed),
    [MInv_transport] (re-establish after a syscall that kept
    m_vm_materialized and m_vm_lazy: only the budget is re-checked),
    [MInv_wvb].

  Part 4 — nodes (Section Nodes: segs H HH Hwx, then P P_silent1 for the
  chain lemmas):
  - [mi_account_step_restricted]:
      lazy_cover.. -> A_wf A -> MInv A model -> step segs (restrict H ms) = MachineOk msr' ->
      exists mat', mi_account_step segs ms model
                     = MachineOk (unrestrict H (ms_mem ms) msr', with_vm_backing (m_vm_lazy model) mat' model)
                   /\ MInv A (with_vm_backing ..) /\ hclean H msr'.
  - [sstep_instr_det]: svc_pending = None -> mi_account_step = MachineOk (ms1, model1) ->
      sstep segs (ms,model) e st -> e = [] /\ st = SNext (ms1, model1).
  - [node_instr_restricted]: ... m_halted model = None -> ms_svc_pending ms = None ->
      step segs (restrict H ms) = MachineOk msr' ->
      exists model', MInv A model' /\ same_but_materialized model model' /\ hclean H msr'
        /\ mi_account_step segs ms model = MachineOk (unrestrict H (ms_mem ms) msr', model')
        /\ node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg (unrestrict ..) model').
  - [step_hclean], [msteps_hclean]: H-cleanliness is preserved by steps.
  - chain lemmas, for any [P : config -> Prop] with
      [P_silent1 : forall c c', node_ok segs c unit (fun _ => []) (fun _ => c') -> P c' -> P c]
    (take [P := fun c => realizes segs c T], [P_silent1 := rz_silent1 segs _ _ T];
     done in AsanAcctShape as [rz_msteps_restricted_T]):
    [rz_step_restricted], [rz_msteps_restricted] (induction form) and
    [rz_msteps_restricted']:
      lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
      msteps segs (restrict H ms) msr' ->
      (forall model', MInv A model' -> same_but_materialized model model' -> hclean H msr' ->
                      P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
      P (mkCfg ms model).

  Part 5 — generic lazy-tolerant SYSCALL node [node_syscall_restricted]
  (Section SyscallNode: segs H): given the pure characterisation of
  [syscall_spec] at (ms, x8, model) by an index type [I] with outcome
  functions eff/mdl/evs (sound + complete, no outcome halts), and
    forall i, lazy_cover H (m_vm_lazy (mdl i)) A /\ MInv A (mdl i)
              /\ ranges_avoid H (syscall_effect_accesses (eff i)),
  conclude MInv + same_but_materialized for [materialized_succ (mdl i) _]
  and  node_ok segs (mkCfg ms model) I evs
         (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i))) (materialized_succ (mdl i) ..)).
  Also [materialize_model_accesses_nil] (effects without copyins/writes:
  mmap, munmap, brk, mprotect, close, exit...: materialized_succ m [] = m).

  Part 6 — instantiation helpers: [mkH], [lazy_cover_mkH] (incl lazy L ->
  lazy_cover (mkH L A) lazy A), boolean checkers [wx_segs_nowrap_b] /
  [segs_below_b] / [ranges_from_b] with [wx_segs_nowrap_of_b],
  [H_off_segments_above] (segments end below [top] and H only hides
  addresses >= top), [H_off_segments_mkH].  Per-image instances
  close the boolean checkers by [vm_compute].

  ----------------------------------------------------------------------
  INTENDED USE (one block of straight-line code between two syscalls)
  ----------------------------------------------------------------------
  1. Fix H (any boolean predicate; two natural choices: [mkH L A] with L ⊇
     all lazy ranges, or [fun a => negb (visible a)] with [visible] a
     whitelist containing all segments, the stack window, the heap and the
     allowed shadow pages) and A (page-aligned Z intervals covering
     every lazy page the code may touch).  Prove once: H_off_segments
     (AsanAcctImages: enough that hidden addresses are >= 0x672000),
     lazy_cover, A_wf (vm_compute for concrete A), and MInv at the first
     model with a non-empty lazy ledger ([MInv_intro_empty]: budget
     eager_used + A_bytes A <= vm_limit).
  2. Run the executor from [restrict H ms] = [mkst regs pc (mrestrict H mem) rom];
     it never needs a hidden byte, so its knowledge facts are unchanged.
  3. Apply [rz_msteps_restricted'] (or [_T]); continue from
     [mkCfg (unrestrict H mem msr') model'] for an arbitrary [model']
     with [MInv A model'] and [same_but_materialized model model']
     (so every accessor but m_vm_materialized is that of [model]:
     rewrite with [same_but_materialized_frame]).  [hclean H msr'] gives
     [restrict H (unrestrict H mem msr') = msr'] for the next block.
  4. At the syscall: either an existing node lemma whose materialization
     premise is discharged by [materialize_model_accesses_nil] /
     [materialize_restricted], or [node_syscall_restricted]; re-establish
     MInv for the post-model by [MInv_transport] (budget re-check only).

  ----------------------------------------------------------------------
  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `bv n` → `BitVec n`,
    `Z_to_bv 64 z` → `BitVec.ofInt 64 z`, `bv_unsigned w` →
    `(w.toNat : Int)`; `negb` → `!`, `andb`/`orb` → `&&`/`||`,
    `Z.eqb`/`Z.ltb`/`Z.leb` → `==`/`decide (· < ·)`/`decide (· ≤ ·)`.
  - `machine_result` constructors are `MachineOk`/`MachineFault`/
    `MachineUnmodeled`; `step_to` constructors are `SNext`/`SError`.
  - `RiscvSemantics.memory_read` / `wview` / `store_ok` /
    `ov_read_bytes` / `step_accesses` take the loaded segments as their
    first explicit argument (this tree's spelling of the `WithMemImage`
    section variable), so the `(segs : list Segment)` parameter is
    spelled explicitly throughout and the `Section ISA` hypotheses become
    explicit leading parameters — the same convention `CatSim.lean` and
    `PropExec.lean` follow.
  - `Z.of_nat`/`Z.to_nat`/`Z2Nat`/`Z.div_mul`/`Z_mod_plus_full` steps are
    spelled with `Int`/`Nat` lemmas and `omega`.
-/
import LinuxSem.Common.CatSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.SharedFacts

set_option autoImplicit false

namespace LinuxSem.Common.AsanAcct

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Common.CatSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.SharedFacts

/-- `Local Instance asanreflect_fx : PropExec.FPState :=
    PropExec.fx0`: the FP state at process entry, so that [mkst] can be
    used in the restricted-state lemmas. -/
local instance asanreflect_fx : PropExec.FPState := PropExec.fx0

/-- `mkCfg`.  `config` is a structure, so this is the anonymous
    constructor; keeping the name makes the statements readable
    (the same spelling `CatSim.lean` uses). -/
def mkCfg (ms : machine_state) (model : Model) : config := ⟨ms, model⟩

/- ===================================================================== -/
/- ** Part 1.  Definitions                                             -/
/- ===================================================================== -/

/-- Memory-level restriction: hide (read as [none]) every address in [H]. -/
def mrestrict (H : word → Bool) (m : word → Option byte) :
    word → Option byte :=
  fun a => if H a then none else m a

/-- Memory-level un-restriction: put back the hidden bytes of [full]. -/
def munrestrict (H : word → Bool) (full m' : word → Option byte) :
    word → Option byte :=
  fun a => if H a then full a else m' a

/-- The restricted machine state: same registers, pc, reservation, fcsr and
    rom; the writable overlay hidden at every address of [H]. -/
def restrict (H : word → Bool) (ms : machine_state) : machine_state :=
  { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms.ms_pc_val,
    ms_svc_pending := ms.ms_svc_pending, ms_resv := ms.ms_resv,
    ms_fcsr := ms.ms_fcsr, ms_mem := mrestrict H ms.ms_mem,
    ms_rom := ms.ms_rom }

/-- Put the hidden bytes of [full] back into the overlay of [ms']. -/
def unrestrict (H : word → Bool) (full : word → Option byte)
    (ms' : machine_state) : machine_state :=
  { ms_regs := ms'.ms_regs, ms_fregs := ms'.ms_fregs,
    ms_pc_val := ms'.ms_pc_val, ms_svc_pending := ms'.ms_svc_pending,
    ms_resv := ms'.ms_resv, ms_fcsr := ms'.ms_fcsr,
    ms_mem := munrestrict H full ms'.ms_mem, ms_rom := ms'.ms_rom }

/-- No hidden address lies inside any loaded segment. -/
def H_off_segments (segs : List Segment) (H : word → Bool) : Prop :=
  ∀ a, H a = true → find_segment segs (a.toNat : Int) 1 = none

/-- Every WRITABLE+EXECUTABLE segment ends below [2^64] (so the byte cursor
    of an overlay fetch [seg_ov_read_bytes] never wraps).  Holds vacuously
    for an image without w+x segments. -/
def wx_segs_nowrap (segs : List Segment) : Prop :=
  ∀ seg, seg ∈ segs →
    (seg_executable seg && seg_writable seg) = true →
    ((seg.seg_base : Int) + (seg.seg_size : Int) ≤ 2 ^ 64)

/-- The [k]-th byte address of a range starting at [a]: computed in [Int]
    from [bv_unsigned a] (exactly like [State.access_pages_acc]'s cursor)
    and wrapped back to a word. -/
def woff (a : word) (k : Nat) : word :=
  BitVec.ofInt 64 ((a.toNat : Int) + (k : Int))

/-- Every address in the [n]-byte range starting at [a] is visible. -/
def range_avoids (H : word → Bool) (a : word) (n : Nat) : Prop :=
  ∀ k, k < n → H (woff a k) = false

/-- Every range of the report list is visible. -/
def ranges_avoid (H : word → Bool) (l : List (word × Nat)) : Prop :=
  ∀ a n, (a, n) ∈ l → range_avoids H a n

/- ===================================================================== -/
/- ** Small word facts                                                 -/
/- ===================================================================== -/

theorem woff_0 (a : word) : woff a 0 = a := by
  unfold woff
  simp [BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem woff_succ (a : word) (k : Nat) : woff (a + 1) k = woff a (k + 1) := by
  unfold woff
  bv_omega

theorem range_avoids_hd (H : word → Bool) (a : word) (n : Nat) :
    range_avoids H a (n + 1) → H a = false := by
  intro Hr
  have h := Hr 0 (by omega)
  simpa [woff_0] using h

theorem range_avoids_tl (H : word → Bool) (a : word) (n : Nat) :
    range_avoids H a (n + 1) → range_avoids H (a + 1) n := by
  intro Hr k hk
  rw [woff_succ]
  exact Hr (k + 1) (by omega)

theorem range_avoids_cons (H : word → Bool) (a : word) (n : Nat) :
    H a = false → range_avoids H (a + 1) n → range_avoids H a (n + 1) := by
  intro H0 Hr k hk
  cases k with
  | zero => simpa [woff_0] using H0
  | succ k =>
    rw [← woff_succ]
    exact Hr k (by omega)

theorem ranges_avoid_nil (H : word → Bool) : ranges_avoid H [] := by
  intro a n hin
  simp at hin

theorem ranges_avoid_cons (H : word → Bool) (a : word) (n : Nat)
    (l : List (word × Nat)) :
    range_avoids H a n → ranges_avoid H l → ranges_avoid H ((a, n) :: l) := by
  intro Ha Hl a' n' hin
  rcases List.mem_cons.mp hin with heq | hin
  · injection heq with h1 h2
    subst h1; subst h2
    exact Ha
  · exact Hl a' n' hin

theorem ranges_avoid_app (H : word → Bool) (l1 l2 : List (word × Nat)) :
    ranges_avoid H l1 → ranges_avoid H l2 → ranges_avoid H (l1 ++ l2) := by
  intro H1 H2 a n hin
  rcases List.mem_append.mp hin with hin | hin
  · exact H1 a n hin
  · exact H2 a n hin

/- Trivial projections. -/
theorem restrict_svc_pending (H : word → Bool) (ms : machine_state) :
    (restrict H ms).ms_svc_pending = ms.ms_svc_pending := rfl

theorem restrict_pc (H : word → Bool) (ms : machine_state) :
    ms_pc (restrict H ms) = ms_pc ms := rfl

theorem restrict_regs (H : word → Bool) (ms : machine_state) :
    (restrict H ms).ms_regs = ms.ms_regs := rfl

theorem restrict_reg (H : word → Bool) (ms : machine_state) (r : reg) :
    ms_reg (restrict H ms) r = ms_reg ms r := rfl

theorem restrict_rom (H : word → Bool) (ms : machine_state) :
    (restrict H ms).ms_rom = ms.ms_rom := rfl

theorem restrict_mem (H : word → Bool) (ms : machine_state) :
    (restrict H ms).ms_mem = mrestrict H ms.ms_mem := rfl

theorem unrestrict_svc_pending (H : word → Bool) (full : word → Option byte)
    (ms : machine_state) :
    (unrestrict H full ms).ms_svc_pending = ms.ms_svc_pending := rfl

theorem unrestrict_mem (H : word → Bool) (full : word → Option byte)
    (ms : machine_state) :
    (unrestrict H full ms).ms_mem = munrestrict H full ms.ms_mem := rfl

/-- The symbolic executor's state constructor commutes with [restrict]. -/
theorem restrict_mkst (H : word → Bool) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) :
    restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom := rfl

theorem mrestrict_idem (H : word → Bool) (m : word → Option byte) :
    mrestrict H (mrestrict H m) = mrestrict H m := by
  funext a
  unfold mrestrict
  cases h : H a <;> simp

theorem munrestrict_mrestrict (H : word → Bool) (m : word → Option byte) :
    munrestrict H m (mrestrict H m) = m := by
  funext a
  unfold munrestrict mrestrict
  cases h : H a <;> simp

theorem mrestrict_munrestrict (H : word → Bool) (full m : word → Option byte) :
    mrestrict H (munrestrict H full m) = mrestrict H m := by
  funext a
  unfold munrestrict mrestrict
  cases h : H a <;> simp [h]

theorem unrestrict_restrict (H : word → Bool) (ms : machine_state) :
    unrestrict H ms.ms_mem (restrict H ms) = ms := by
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
  simp only [unrestrict, restrict, munrestrict_mrestrict]

theorem restrict_unrestrict (H : word → Bool) (full : word → Option byte)
    (ms : machine_state) :
    restrict H (unrestrict H full ms) = restrict H ms := by
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
  simp only [unrestrict, restrict, mrestrict_munrestrict]

/-- A state is "H-clean" when its overlay holds nothing at hidden
    addresses; exactly the fixed points of [restrict H]. -/
def hclean (H : word → Bool) (ms : machine_state) : Prop :=
  ∀ a, H a = true → ms.ms_mem a = none

theorem restrict_hclean (H : word → Bool) (ms : machine_state) :
    hclean H (restrict H ms) := by
  intro a Ha
  show (restrict H ms).ms_mem a = none
  simp only [restrict_mem]
  unfold mrestrict
  rw [Ha]
  rfl

theorem hclean_restrict_id (H : word → Bool) (ms : machine_state) :
    hclean H ms → restrict H ms = ms := by
  intro Hc
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
  simp only [restrict]
  congr 1
  funext a
  unfold mrestrict
  cases h : H a with
  | true => simp; exact (Hc a h).symm
  | false => simp

theorem restrict_unrestrict_clean (H : word → Bool) (full : word → Option byte)
    (ms : machine_state) :
    hclean H ms → restrict H (unrestrict H full ms) = ms := by
  intro Hc
  rw [restrict_unrestrict H full ms]
  exact hclean_restrict_id H ms Hc

/- ===================================================================== -/
/- ** Part 2.  ISA monotonicity                                        -/
/- ===================================================================== -/

/- Section ISA : `segs`, `H`, `HH : H_off_segments segs H`,
   `Hwx : wx_segs_nowrap segs` become explicit leading parameters on every
   lemma below that mentions them, in that order . -/

/-- A data read that succeeds on the restricted overlay succeeds with the
    same bytes on the full overlay, and touched no hidden byte. -/
theorem memory_read1_hidden (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (a : word) (Ha : H a = true) :
    memory_read segs a 1 = none := by
  simp [memory_read, HH a Ha]

/- *** Transfer of knowledge in the VISIBLE direction: on ranges that
    avoid [H] the restricted overlay behaves exactly like the full one
    (no hypothesis on [H] needed).  These let facts about [mem] be
    restated for [mrestrict H mem] when seeding the symbolic executor. -/
theorem mrestrict_visible (H : word → Bool) (m : word → Option byte) (a : word) :
    H a = false → mrestrict H m a = m a := by
  intro Ha
  unfold mrestrict
  simp [Ha]

theorem ov_read_bytes_mrestrict_eq (segs : List Segment) (H : word → Bool)
    (n : Nat) :
    ∀ (m : word → Option byte) (a : word), range_avoids H a n →
      ov_read_bytes segs (mrestrict H m) a n = ov_read_bytes segs m a n := by
  induction n with
  | zero => intro m a _; rfl
  | succ n ih =>
    intro m a Hav
    simp only [ov_read_bytes]
    rw [mrestrict_visible H m a (range_avoids_hd H a n Hav)]
    rw [ih m (a + 1) (range_avoids_tl H a n Hav)]

theorem rdn_mrestrict_eq (segs : List Segment) (H : word → Bool) (n : Nat)
    (m : word → Option byte) (a : word) :
    range_avoids H a n →
    rdn segs (mrestrict H m) a n = rdn segs m a n := by
  intro Hav
  rw [← ov_rdn, ← ov_rdn]
  exact ov_read_bytes_mrestrict_eq segs H n m a Hav

theorem wview_mrestrict_eq (segs : List Segment) (H : word → Bool)
    (m : word → Option byte) (a : word) :
    H a = false → wview segs (mrestrict H m) a = wview segs m a := by
  intro Ha
  unfold wview
  rw [mrestrict_visible H m a Ha]

theorem store_ok_mrestrict_eq (segs : List Segment) (H : word → Bool) (n : Nat) :
    ∀ (m : word → Option byte) (a : word), range_avoids H a n →
      store_ok segs (mrestrict H m) a n = store_ok segs m a n := by
  induction n with
  | zero => intro m a _; rfl
  | succ n ih =>
    intro m a Hav
    rw [show store_ok segs (mrestrict H m) a (n + 1)
          = (match wview segs (mrestrict H m) a with
             | some _ => store_ok segs (mrestrict H m) (a + 1) n
             | none => false) from rfl]
    rw [show store_ok segs m a (n + 1)
          = (match wview segs m a with
             | some _ => store_ok segs m (a + 1) n
             | none => false) from rfl]
    rw [wview_mrestrict_eq segs H m a (range_avoids_hd H a n Hav)]
    cases hw : wview segs m a with
    | none => rfl
    | some b => exact ih m (a + 1) (range_avoids_tl H a n Hav)

theorem ov_read_bytes_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (n : Nat) :
    ∀ (m : word → Option byte) (a : word) (bs : List byte),
      ov_read_bytes segs (mrestrict H m) a n = some bs →
      ov_read_bytes segs m a n = some bs ∧ range_avoids H a n := by
  induction n with
  | zero =>
    intro m a bs Hr
    simp only [ov_read_bytes, Option.some.injEq] at Hr
    subst Hr
    exact ⟨rfl, fun k hk => by omega⟩
  | succ n ih =>
    intro m a bs Hr
    simp only [ov_read_bytes] at Hr ⊢
    cases ha : H a with
    | true =>
      have hmn : mrestrict H m a = none := by
        unfold mrestrict
        simp [ha]
      simp only [hmn] at Hr
      rw [memory_read1_hidden segs H HH a ha] at Hr
      simp at Hr
    | false =>
      have hmv : mrestrict H m a = m a := mrestrict_visible H m a ha
      simp only [hmv] at Hr ⊢
      cases hm : m a with
      | none =>
        simp only [hm] at Hr ⊢
        cases hseg : memory_read segs a 1 with
        | none => simp only [hseg] at Hr; simp at Hr
        | some l =>
          cases l with
          | nil => simp only [hseg] at Hr; simp at Hr
          | cons b' rest =>
            simp only [hseg] at Hr ⊢
            rcases htail : ov_read_bytes segs (mrestrict H m) (a + 1) n with _ | rest'
            · simp only [htail] at Hr; simp at Hr
            · simp only [htail] at Hr
              obtain ⟨rfl, rfl⟩ := Hr
              obtain ⟨hfull, hav⟩ := ih m (a + 1) rest' htail
              refine ⟨?_, range_avoids_cons H a n ha hav⟩
              simp only [hfull]
      | some b0 =>
        simp only [hm] at Hr ⊢
        rcases htail : ov_read_bytes segs (mrestrict H m) (a + 1) n with _ | rest'
        · simp only [htail] at Hr; simp at Hr
        · simp only [htail] at Hr
          obtain ⟨rfl, rfl⟩ := Hr
          obtain ⟨hfull, hav⟩ := ih m (a + 1) rest' htail
          refine ⟨?_, range_avoids_cons H a n ha hav⟩
          simp only [hfull]

/-- The writable view on the restricted overlay: hidden addresses read
    [none], everything else as before. -/
theorem wview_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (m : word → Option byte) (a : word) :
    wview segs (mrestrict H m) a = if H a then none else wview segs m a := by
  unfold wview
  cases ha : H a with
  | true => simp [mrestrict, ha, HH a ha]
  | false => simp [mrestrict, ha]

theorem store_ok_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (n : Nat) :
    ∀ (m : word → Option byte) (a : word),
      store_ok segs (mrestrict H m) a n = true →
      store_ok segs m a n = true ∧ range_avoids H a n := by
  induction n with
  | zero =>
    intro m a _
    exact ⟨rfl, fun k hk => by omega⟩
  | succ n ih =>
    intro m a Hs
    simp only [store_ok] at Hs ⊢
    cases ha : H a with
    | true =>
      have hmn : wview segs (mrestrict H m) a = none := by
        unfold wview
        simp [mrestrict, ha, HH a ha]
      simp only [hmn] at Hs
      simp at Hs
    | false =>
      have hmv : wview segs (mrestrict H m) a = wview segs m a :=
        wview_mrestrict_eq segs H m a ha
      simp only [hmv] at Hs ⊢
      cases hw : wview segs m a with
      | none => simp only [hw] at Hs; simp at Hs
      | some b =>
        simp only [hw] at Hs
        obtain ⟨hfull, hav⟩ := ih m (a + 1) Hs
        exact ⟨hfull, range_avoids_cons H a n ha hav⟩

/-- Writing bytes that avoid [H] commutes with restriction and leaves the
    hidden part of the overlay untouched. -/
theorem write_to_mem_restrict (H : word → Bool) :
    ∀ (bs : List byte) (m : word → Option byte) (a : word),
      range_avoids H a bs.length →
      write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs) := by
  intro bs
  induction bs with
  | nil => intro m a _; rfl
  | cons b bs ih =>
    intro m a Hav
    simp only [write_to_mem, List.length_cons] at *
    have Ha : H a = false := range_avoids_hd H a bs.length Hav
    have Htl : range_avoids H (a + 1) bs.length := range_avoids_tl H a bs.length Hav
    rw [← ih (fun x => if bv_eqb x a then some b else m x) (a + 1) Htl]
    congr 1
    funext x
    unfold mrestrict
    by_cases hx : x = a
    · subst hx
      simp [bv_eqb, Ha]
    · have hb : bv_eqb x a = false := by simp [bv_eqb, hx]
      simp [hb]

theorem write_to_mem_hidden (H : word → Bool) :
    ∀ (bs : List byte) (m : word → Option byte) (a x : word),
      range_avoids H a bs.length → H x = true →
      write_to_mem m a bs x = m x := by
  intro bs
  induction bs with
  | nil => intro m a x _ _; rfl
  | cons b bs ih =>
    intro m a x Hav Hx
    simp only [write_to_mem, List.length_cons] at *
    have Ha : H a = false := range_avoids_hd H a bs.length Hav
    have Htl : range_avoids H (a + 1) bs.length := range_avoids_tl H a bs.length Hav
    rw [ih (fun x => if bv_eqb x a then some b else m x) (a + 1) x Htl Hx]
    by_cases hx : x = a
    · subst hx
      rw [Ha] at Hx
      exact absurd Hx (by simp)
    · have hb : bv_eqb x a = false := by simp [bv_eqb, hx]
      simp [hb]

/- *** Segment lookups: what a found segment covers, and that a miss means
    no segment covers the range. -/

theorem find_segment_some_spec (l : List Segment) (addr n : Int) (seg : Segment)
    (Hf : find_segment l addr n = some seg) :
    seg ∈ l ∧ (seg.seg_base : Int) ≤ addr ∧
      addr + n ≤ (seg.seg_base : Int) + (seg.seg_size : Int) := by
  induction l generalizing addr n with
  | nil => simp [find_segment] at Hf
  | cons s l ih =>
    simp only [find_segment] at Hf
    split at Hf
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq] at Hf
      subst Hf
      exact ⟨by simp, hc.1, hc.2⟩
    · obtain ⟨hin, h1, h2⟩ := ih addr n Hf
      exact ⟨List.mem_cons_of_mem _ hin, h1, h2⟩

theorem find_segment_none_spec (l : List Segment) (addr n : Int) :
    find_segment l addr n = none →
    ∀ seg, seg ∈ l →
      ¬ ((seg.seg_base : Int) ≤ addr ∧
         addr + n ≤ (seg.seg_base : Int) + (seg.seg_size : Int)) := by
  induction l generalizing addr n with
  | nil => intro _ seg hin; simp at hin
  | cons s l ih =>
    intro Hf seg hin
    simp only [find_segment] at Hf
    split at Hf
    · simp at Hf
    · rename_i hc
      rcases List.mem_cons.mp hin with rfl | hin
      · intro ⟨h1, h2⟩
        simp [h1, h2] at hc
      · exact ih addr n Hf seg hin

/-- A byte inside some segment is not hidden. -/
theorem in_segment_not_hidden (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (x : word) (seg : Segment) (Hin : seg ∈ segs)
    (H1 : (seg.seg_base : Int) ≤ (x.toNat : Int))
    (H2 : (x.toNat : Int) + 1 ≤ (seg.seg_base : Int) + (seg.seg_size : Int)) :
    H x = false := by
  cases hx : H x with
  | false => rfl
  | true =>
    exfalso
    exact find_segment_none_spec segs (x.toNat : Int) 1 (HH x hx) seg Hin ⟨H1, H2⟩

/- *** Fetch through the overlay: within a found w+x segment no byte is
    hidden, so restricted and full overlay fetch identically. -/
theorem seg_ov_read_bytes_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (n : Nat) :
    ∀ (m : word → Option byte) (seg : Segment) (a : word),
      seg ∈ segs →
      (seg.seg_base : Int) ≤ (a.toNat : Int) →
      (a.toNat : Int) + (n : Int) ≤ (seg.seg_base : Int) + (seg.seg_size : Int) →
      (seg.seg_base : Int) + (seg.seg_size : Int) ≤ 2 ^ 64 →
      seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n := by
  induction n with
  | zero => intro m seg a _ _ _ _; rfl
  | succ n ih =>
    intro m seg a Hin Hlo Hhi Htop
    simp only [seg_ov_read_bytes]
    have Ha : H a = false := in_segment_not_hidden segs H HH a seg Hin Hlo (by omega)
    rw [mrestrict_visible H m a Ha]
    cases n with
    | zero => rfl
    | succ n' =>
      have hstep : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := by
        rw [BitVec.toNat_add]
        have h1 : (1 : word).toNat = 1 := rfl
        rw [h1]
        have hlt : a.toNat + 1 < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      rw [ih m seg (a + 1) Hin (by omega) (by omega) Htop]

theorem code_read_ov_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) (n : Nat) :
    code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n := by
  unfold code_read_ov
  cases hf : find_segment segs (a.toNat : Int) (n : Int) with
  | none => rfl
  | some seg =>
    simp only []
    cases hwx : (seg_executable seg && seg_writable seg) with
    | false => simp
    | true =>
      obtain ⟨hin, h1, h2⟩ :=
        find_segment_some_spec segs (a.toNat : Int) (n : Int) seg hf
      simpa [hwx] using
        seg_ov_read_bytes_restrict segs H HH n m seg a hin h1 h2 (Hwx seg hin hwx)

theorem fetch_word_ov_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) :
    fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a := by
  simp only [fetch_word_ov, code_read_ov_restrict segs H HH Hwx m a 4]

theorem fetch_half_ov_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) :
    fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a := by
  simp only [fetch_half_ov, code_read_ov_restrict segs H HH Hwx m a 2]

theorem fetch_half_any_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) :
    fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a := by
  simp only [fetch_half_any, fetch_half_ov_restrict segs H HH Hwx]

theorem fetch_tail_any_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) :
    fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a := by
  simp only [fetch_tail_any, fetch_half_any_restrict segs H HH Hwx]

theorem fetch_failure_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (m : word → Option byte) (a : word) :
    fetch_failure segs (mrestrict H m) a = fetch_failure segs m a := by
  simp only [fetch_failure, fetch_half_any_restrict segs H HH Hwx]

/- *** The effect-tree interpreter on a restricted overlay. -/
theorem interp_eff_accesses_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) :
    ∀ (t : eff) (m : word → Option byte) (c : core) (mr' : word → Option byte)
      (rs : List (word × Nat)),
      interp_eff_accesses segs t (mrestrict H m)
        = .MachineOk (mkAccessReport (c, mr') rs) →
      ∃ mf', interp_eff_accesses segs t m = .MachineOk (mkAccessReport (c, mf') rs)
        ∧ mr' = mrestrict H mf'
        ∧ (∀ x, H x = true → mf' x = m x)
        ∧ ranges_avoid H rs := by
  intro t
  induction t with
  | eDone c0 =>
    intro m c mr' rs Hi
    simp only [interp_eff_accesses] at Hi
    simp only [machine_result.MachineOk.injEq, mkAccessReport, access_report.mk.injEq,
      Prod.mk.injEq, List.nil_eq] at Hi
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Hi
    exact ⟨m, rfl, rfl, fun x _ => rfl, ranges_avoid_nil H⟩
  | eEbreak x => intro m c mr' rs Hi; simp [interp_eff_accesses] at Hi
  | eFault x => intro m c mr' rs Hi; simp [interp_eff_accesses] at Hi
  | eDefinedIllegal x => intro m c mr' rs Hi; simp [interp_eff_accesses] at Hi
  | eIllegal x => intro m c mr' rs Hi; simp [interp_eff_accesses] at Hi
  | eEcall x => intro m c mr' rs Hi; simp [interp_eff_accesses] at Hi
  | eLoad n a k ih =>
    intro m c mr' rs Hi
    simp only [interp_eff_accesses] at Hi ⊢
    cases hrd : ov_read_bytes segs (mrestrict H m) a (width_bytes n) with
    | none => simp [hrd] at Hi
    | some bs =>
      obtain ⟨hfull, hav⟩ :=
        ov_read_bytes_restrict segs H HH (width_bytes n) m a bs hrd
      simp only [hrd, hfull] at Hi ⊢
      cases hk : interp_eff_accesses segs (k (bits 0 n (le_bytes_to_word bs)))
          (mrestrict H m) with
      | MachineOk report =>
        cases report with
        | mk v rs1 =>
          obtain ⟨c1, m1⟩ := v
          obtain ⟨mf', hint, hmr, hhid, hrs⟩ :=
            ih (bits 0 n (le_bytes_to_word bs)) m c1 m1 rs1 hk
          simp only [hk] at Hi ⊢
          simp only [machine_result.MachineOk.injEq, mkAccessReport] at Hi
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Hi
          refine ⟨mf', ?_, hmr, hhid,
            ranges_avoid_cons H a (width_bytes n) rs1 hav hrs⟩
          simp only [hint, mkAccessReport]
      | MachineFault => simp [hk] at Hi
      | MachineUnmodeled => simp [hk] at Hi
  | eStore n a v k ih =>
    intro m c mr' rs Hi
    simp only [interp_eff_accesses] at Hi ⊢
    cases hso : store_ok segs (mrestrict H m) a (width_bytes n) with
    | false => simp [hso] at Hi
    | true =>
      obtain ⟨hfull, hav⟩ := store_ok_restrict segs H HH (width_bytes n) m a hso
      simp only [hso, hfull] at Hi ⊢
      have hlen : (Z_to_le_bytes (width_bytes n) (v.toNat : Int)).length = width_bytes n :=
        length_Z_to_le_bytes (width_bytes n) (v.toNat : Int)
      have hwtr :
          write_to_mem (mrestrict H m) a (Z_to_le_bytes (width_bytes n) (v.toNat : Int))
            = mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (v.toNat : Int))) :=
        write_to_mem_restrict H (Z_to_le_bytes (width_bytes n) (v.toNat : Int)) m a
          (by rw [hlen]; exact hav)
      simp only [hwtr] at Hi ⊢
      cases hk : interp_eff_accesses segs k
          (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (v.toNat : Int)))) with
      | MachineOk report =>
        cases report with
        | mk v1 rs1 =>
          obtain ⟨c1, m1⟩ := v1
          obtain ⟨mf', hint, hmr, hhid, hrs⟩ :=
            ih (write_to_mem m a (Z_to_le_bytes (width_bytes n) (v.toNat : Int)))
              c1 m1 rs1 hk
          simp only [hk] at Hi ⊢
          simp only [mkAccessReport] at Hi
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Hi
          refine ⟨mf', ?_, hmr, ?_, ranges_avoid_cons H a (width_bytes n) rs1 hav hrs⟩
          · simp only [hint, mkAccessReport, ite_true]
          intro x hx
          rw [hhid x hx]
          exact write_to_mem_hidden H (Z_to_le_bytes (width_bytes n) (v.toNat : Int)) m a x
            (by rw [hlen]; exact hav) hx
      | MachineFault => simp [hk] at Hi
      | MachineUnmodeled => simp [hk] at Hi

/- *** Decode-and-execute, and the full step. -/
theorem decode_exec_accesses_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (ms : machine_state) (w : BitVec 32)
    (msr' : machine_state) (rs' : List (word × Nat))
    (Hd : decode_exec_accesses segs (restrict H ms) w
        = .MachineOk (mkAccessReport msr' rs')) :
    decode_exec_accesses segs ms w
        = .MachineOk (mkAccessReport (unrestrict H ms.ms_mem msr') rs')
      ∧ ranges_avoid H rs' ∧ hclean H msr' := by
  unfold decode_exec_accesses at Hd ⊢
  cases hec : is_ecall w with
  | true =>
    simp only [hec, ite_true] at Hd ⊢
    obtain ⟨rfl, rfl⟩ := Hd
    refine ⟨?_, ranges_avoid_nil H, ?_⟩
    · obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
      simp only [unrestrict, restrict, munrestrict_mrestrict, ms_reg]
    · obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
      intro a ha
      simp only [restrict, mrestrict]
      rw [ha]
      rfl
  | false =>
    simp only [hec, ite_false, Bool.false_eq_true] at Hd ⊢
    cases hdec : decodeAny w with
    | none =>
      cases hdi : isDefinedIllegal w <;> simp [hdec, hdi] at Hd
    | some p =>
      obtain ⟨i, isz⟩ := p
      simp only [hdec, restrict] at Hd ⊢
      cases hint : interp_eff_accesses segs
          (exec (BitVec.ofInt 64 isz) i
            { c_regs := ms.ms_regs, c_fregs := ms.ms_fregs, c_pc := ms.ms_pc_val,
              c_fcsr := ms.ms_fcsr, c_resv := ms.ms_resv })
          (mrestrict H ms.ms_mem) with
      | MachineOk report =>
        cases report with
        | mk v rs1 =>
          obtain ⟨c1, m1⟩ := v
          obtain ⟨mf', hfull, hmr, hhid, hrs⟩ :=
            interp_eff_accesses_restrict segs H HH
              (exec (BitVec.ofInt 64 isz) i
                { c_regs := ms.ms_regs, c_fregs := ms.ms_fregs, c_pc := ms.ms_pc_val,
                  c_fcsr := ms.ms_fcsr, c_resv := ms.ms_resv })
              ms.ms_mem c1 m1 rs1 hint
          simp only [hint] at Hd ⊢
          simp only [mkAccessReport] at Hd ⊢
          obtain ⟨rfl, rfl⟩ := Hd
          have hmun : munrestrict H ms.ms_mem (mrestrict H mf') = mf' := by
            funext x
            unfold munrestrict mrestrict
            cases hx : H x with
            | true => simpa using (hhid x hx).symm
            | false => simp
          refine ⟨?_, hrs, ?_⟩
          · simp only [unrestrict, hmun, hfull, mkAccessReport, hmr]
          · intro x hx
            rw [hmr]
            simp [mrestrict, hx]
      | MachineFault => simp [hint] at Hd
      | MachineUnmodeled => simp [hint] at Hd

/-- [fetch_failure] classifies a declined fetch as a fault or as the model
    giving up; it never produces a machine state.   -/
theorem fetch_failure_ne_ok (segs : List Segment) (m : word → Option byte) (a : word)
    (ms' : machine_state) : fetch_failure segs m a ≠ .MachineOk ms' := by
  intro h
  unfold fetch_failure at h
  cases hh : fetch_half_any segs m a <;> simp only [hh] at h
  · split at h
    · simp at h
    · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h <;> simp at h

theorem step_accesses_restrict (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (ms : machine_state) (msr' : machine_state) (rs' : List (word × Nat))
    (Hs : step_accesses segs (restrict H ms) = .MachineOk (mkAccessReport msr' rs')) :
    step_accesses segs ms = .MachineOk (mkAccessReport (unrestrict H ms.ms_mem msr') rs')
      ∧ ranges_avoid H rs' ∧ hclean H msr' := by
  unfold step_accesses at Hs ⊢
  simp only [restrict, ms_pc] at Hs ⊢
  rw [fetch_word_ov_restrict segs H HH Hwx, fetch_tail_any_restrict segs H HH Hwx,
    fetch_failure_restrict segs H HH Hwx] at Hs
  cases hw : fetch_word segs ms.ms_pc_val with
  | some w =>
    simp only [hw] at Hs
    exact decode_exec_accesses_restrict segs H HH ms w msr' rs' Hs
  | none =>
    simp only [hw] at Hs
    cases hov : fetch_word_ov segs ms.ms_mem ms.ms_pc_val with
    | some w =>
      simp only [hov] at Hs
      exact decode_exec_accesses_restrict segs H HH ms w msr' rs' Hs
    | none =>
      simp only [hov] at Hs
      cases htail : fetch_tail_any segs ms.ms_mem ms.ms_pc_val with
      | some w =>
        simp only [htail] at Hs
        exact decode_exec_accesses_restrict segs H HH ms w msr' rs' Hs
      | none =>
        simp only [htail] at Hs
        exfalso
        cases hf : fetch_failure segs ms.ms_mem ms.ms_pc_val with
        | MachineOk st' => exact absurd hf (fetch_failure_ne_ok segs ms.ms_mem ms.ms_pc_val st')
        | MachineFault => simp [hf] at Hs
        | MachineUnmodeled => simp [hf] at Hs

/-- From a PLAIN step on the restricted state to the access-reporting step on
    the full state. -/
theorem step_restrict_sound (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (ms : machine_state) (msr' : machine_state)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr') :
    ∃ rep, step_accesses segs ms = .MachineOk rep
      ∧ rep.access_value = unrestrict H ms.ms_mem msr'
      ∧ ranges_avoid H rep.accessed_ranges
      ∧ hclean H msr'
      ∧ restrict H (unrestrict H ms.ms_mem msr') = msr' := by
  unfold RiscvSemantics.step drop_access_report at Hs
  cases hsa : step_accesses segs (restrict H ms) with
  | MachineOk report =>
    simp only [hsa, machine_result.MachineOk.injEq] at Hs
    subst Hs
    obtain ⟨hfull, hrs, hcl⟩ :=
      step_accesses_restrict segs H HH Hwx ms report.access_value
        report.accessed_ranges hsa
    exact ⟨_, hfull, rfl, hrs, hcl,
      restrict_unrestrict_clean H ms.ms_mem report.access_value hcl⟩
  | MachineFault => simp [hsa] at Hs
  | MachineUnmodeled => simp [hsa] at Hs

/-- Consequently the plain step on the full state also succeeds. -/
theorem step_restrict_step (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (ms : machine_state) (msr' : machine_state)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr') :
    RiscvSemantics.step segs ms = .MachineOk (unrestrict H ms.ms_mem msr') := by
  obtain ⟨rep, hsa, hv, _, _, _⟩ := step_restrict_sound segs H HH Hwx ms msr' Hs
  unfold RiscvSemantics.step drop_access_report
  simp only [hsa, hv]

/-- The ecall case, for reference: no accesses and [svc_pending] set. -/
theorem step_accesses_ecall_shape (segs : List Segment) (ms : machine_state)
    (msr' : machine_state) (rs' : List (word × Nat))
    (Hs : step_accesses segs ms = .MachineOk (mkAccessReport msr' rs'))
    (Hsvc : msr'.ms_svc_pending ≠ none) :
    rs' = [] ∧ msr'.ms_mem = ms.ms_mem ∧ msr'.ms_regs = ms.ms_regs
      ∧ msr'.ms_svc_pending = some (ms_reg ms 17) := by
  have Hdec : ∀ w, decode_exec_accesses segs ms w = .MachineOk (mkAccessReport msr' rs') →
      rs' = [] ∧ msr'.ms_mem = ms.ms_mem ∧ msr'.ms_regs = ms.ms_regs
        ∧ msr'.ms_svc_pending = some (ms_reg ms 17) := by
    intro w Hd
    unfold decode_exec_accesses at Hd
    cases hec : is_ecall w with
    | true =>
      simp only [hec, ite_true] at Hd
      obtain ⟨rfl, rfl⟩ := Hd
      exact ⟨rfl, rfl, rfl, rfl⟩
    | false =>
      simp only [hec, ite_false, Bool.false_eq_true] at Hd
      cases hdec : decodeAny w with
      | none =>
        cases hdi : isDefinedIllegal w <;> simp [hdec, hdi] at Hd
      | some p =>
        obtain ⟨i, isz⟩ := p
        simp only [hdec] at Hd
        cases hint : interp_eff_accesses segs
            (exec (BitVec.ofInt 64 isz) i
              { c_regs := ms.ms_regs, c_fregs := ms.ms_fregs, c_pc := ms.ms_pc_val,
                c_fcsr := ms.ms_fcsr, c_resv := ms.ms_resv })
            ms.ms_mem with
        | MachineOk report =>
          cases report with
          | mk v rs1 =>
            obtain ⟨c1, m1⟩ := v
            simp only [hint] at Hd
            obtain ⟨rfl, rfl⟩ := Hd
            exact absurd rfl Hsvc
        | MachineFault => simp [hint] at Hd
        | MachineUnmodeled => simp [hint] at Hd
  unfold step_accesses at Hs
  simp only [ms_pc] at Hs ⊢
  cases hw : fetch_word segs ms.ms_pc_val with
  | some w =>
    simp only [hw] at Hs
    exact Hdec w Hs
  | none =>
    simp only [hw] at Hs
    cases hov : fetch_word_ov segs ms.ms_mem ms.ms_pc_val with
    | some w =>
      simp only [hov] at Hs
      exact Hdec w Hs
    | none =>
      simp only [hov] at Hs
      cases htail : fetch_tail_any segs ms.ms_mem ms.ms_pc_val with
      | some w =>
        simp only [htail] at Hs
        exact Hdec w Hs
      | none =>
        simp only [htail] at Hs
        exfalso
        cases hf : fetch_failure segs ms.ms_mem ms.ms_pc_val with
        | MachineOk st' => exact absurd hf (fetch_failure_ne_ok segs ms.ms_mem ms.ms_pc_val st')
        | MachineFault => simp [hf] at Hs
        | MachineUnmodeled => simp [hf] at Hs

/- ===================================================================== -/
/- ** Part 3.  Accounting: materialization under a budget invariant      -/
/- ===================================================================== -/

/-- The allowed set: a list of [Int] intervals <<[lo, hi)>>.  A page (given
    by its base word [p]) is allowed when it fits wholly inside one of
    them. -/
def page_allowedb (A : List (Int × Int)) (p : word) : Bool :=
  A.any (fun iv =>
    decide (iv.1 ≤ (p.toNat : Int)) && decide ((p.toNat : Int) + page_size ≤ iv.2))

/-- Well-formed allowed set: every interval is non-negative-length and
    page-aligned at both ends.  (Pairwise disjointness is NOT needed.) -/
def A_wf (A : List (Int × Int)) : Prop :=
  ∀ iv ∈ A, iv.1 ≤ iv.2 ∧ iv.1 % page_size = 0 ∧ iv.2 % page_size = 0

/-- Total bytes of the allowed set. -/
def A_bytes : List (Int × Int) → Int
  | [] => 0
  | iv :: r => (iv.2 - iv.1) + A_bytes r

/-- [lazy_cover H lazy A]: every non-hidden byte whose page lies wholly in
    a lazy range has an allowed page. -/
def lazy_cover (H : word → Bool) (lazy : List (word × word))
    (A : List (Int × Int)) : Prop :=
  ∀ w : word,
    page_in_ranges (page_base w) lazy = true → H w = false →
    page_allowedb A (page_base w) = true

/-- The part of [vm_backing_used] an instruction step never changes. -/
def eager_used (m : Model) : Int :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m))

theorem vm_backing_used_split (m : Model) :
    vm_backing_used m
      = eager_used m + (m_vm_materialized m).length * page_size := rfl

/-- The budget invariant on the model. -/
structure MInv (A : List (Int × Int)) (m : Model) : Prop where
  minv_nodup : (m_vm_materialized m).Nodup
  minv_aligned : ∀ p, p ∈ m_vm_materialized m → (p.toNat : Int) % page_size = 0
  minv_allowed : ∀ p, p ∈ m_vm_materialized m → page_allowedb A p = true
  minv_lazy : ∀ p, p ∈ m_vm_materialized m → page_in_ranges p (m_vm_lazy m) = true
  minv_budget : eager_used m + A_bytes A ≤ (m_vmmaps m).vm_limit

/-- Two models equal except for the materialized-page ledger. -/
def same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m

theorem same_but_materialized_refl (m : Model) : same_but_materialized m m := rfl

theorem same_but_materialized_trans (m1 m2 m3 : Model)
    (h1 : same_but_materialized m1 m2) (h2 : same_but_materialized m2 m3) :
    same_but_materialized m1 m3 := by
  unfold same_but_materialized at *
  rw [h2, h1]
  rfl

theorem with_vm_backing_same (m : Model) (mat' : List word) :
    same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m) := rfl

/-- Frame: everything but [m_vm_materialized] (and hence [m_vm]) agrees. -/
theorem same_but_materialized_frame (m m' : Model)
    (h : same_but_materialized m m') :
    m'.m_fd = m.m_fd ∧ m_vmmaps m' = m_vmmaps m ∧ m_vm_lazy m' = m_vm_lazy m
      ∧ m'.m_io = m.m_io ∧ m'.m_fsys = m.m_fsys ∧ m'.m_proc = m.m_proc
      ∧ m'.m_lim = m.m_lim ∧ m'.m_time = m.m_time
      ∧ m_fds m' = m_fds m ∧ m_pipes m' = m_pipes m ∧ m_stdin m' = m_stdin m
      ∧ m_fs m' = m_fs m ∧ m_halted m' = m_halted m ∧ m_tid m' = m_tid m
      ∧ m_rlimit_core m' = m_rlimit_core m ∧ m_clock m' = m_clock m
      ∧ eager_used m' = eager_used m := by
  unfold same_but_materialized at h
  rw [h]
  repeat' (first | apply And.intro | rfl)

/- ---------------------------------------------------------------- -/
/- *** Pigeonhole: distinct aligned allowed pages are at most
        [A_bytes A / page_size] many.                                 -/
/- ---------------------------------------------------------------- -/

/-- All page bases of the allowed set, as a list of [Int].  Each interval
    <<[lo, hi)>> contributes the [Int] bases it is page-aligned to, so
    [A_pages] counts every page the allowed set can possibly name; entries
    of [A] need not be disjoint, so the list may repeat values — it is an
    upper bound on the number of DISTINCT allowed pages, which is all the
    cardinality argument below needs. -/
def A_pages : List (Int × Int) → List Int
  | [] => []
  | iv :: r =>
      ((List.range ((iv.2 - iv.1) / page_size).toNat).map
        (fun i => iv.1 + page_size * Int.ofNat i)) ++ A_pages r

/-- Sanity checks: [A_pages] enumerates the aligned bases of an interval. -/
example : A_pages [(0, 8192)] = [0, 4096] := by decide
example : A_pages [(0, 4096), (8192, 12288)] = [0, 8192] := by decide

/-- An aligned [Int] is a multiple of [page_size]. -/
theorem Zmod0_multiple (a : Int) (h : a % page_size = 0) :
    ∃ q : Int, a = page_size * q := by
  refine ⟨a / page_size, ?_⟩
  have hdm := Int.mul_ediv_add_emod a page_size
  rw [h] at hdm
  unfold page_size at *
  omega

/- Small projections of [A_wf] used by the induction below. -/
theorem A_wf_tail (iv : Int × Int) (r : List (Int × Int))
    (h : A_wf (iv :: r)) : A_wf r := by
  intro x hx
  exact h x (List.mem_cons_of_mem iv hx)

theorem A_wf_head (iv : Int × Int) (r : List (Int × Int))
    (h : A_wf (iv :: r)) :
    iv.1 ≤ iv.2 ∧ iv.1 % page_size = 0 ∧ iv.2 % page_size = 0 :=
  h iv List.mem_cons_self

/-- [A_pages] has exactly one entry per [page_size] bytes of the allowed
    set: the page count of the allowed set, in bytes. -/
theorem A_pages_length (A : List (Int × Int)) (Hwf : A_wf A) :
    ((A_pages A).length : Int) * page_size = A_bytes A := by
  induction A with
  | nil => simp [A_pages, A_bytes]
  | cons iv r ih =>
    obtain ⟨lo, hi⟩ := iv
    obtain ⟨hle, hlo, hhi⟩ := A_wf_head (lo, hi) r Hwf
    have hwf' := A_wf_tail (lo, hi) r Hwf
    have hih := ih hwf'
    obtain ⟨qlo, hqlo⟩ := Zmod0_multiple lo hlo
    obtain ⟨qhi, hqhi⟩ := Zmod0_multiple hi hhi
    unfold page_size at *
    have hdiff : hi - lo = (qhi - qlo) * 4096 := by omega
    have hdiv : (hi - lo) / 4096 = qhi - qlo := by
      rw [hdiff, Int.mul_ediv_cancel _ (by decide : (4096 : Int) ≠ 0)]
    have hcast : (((hi - lo) / 4096).toNat : Int) = qhi - qlo := by
      rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ (hi - lo) / 4096), hdiv]
    simp only [A_pages, A_bytes, List.length_append, List.length_map,
      List.length_range, Int.natCast_add]
    unfold page_size at *
    rw [hcast, Int.add_mul, ← hih, ← hdiff]

/-- Every aligned page that the allowed set allows appears in [A_pages]. -/
theorem A_pages_in (A : List (Int × Int)) (p : word) (Hwf : A_wf A)
    (Hal : (p.toNat : Int) % page_size = 0)
    (Hpa : page_allowedb A p = true) :
    (p.toNat : Int) ∈ A_pages A := by
  induction A with
  | nil => simp [page_allowedb] at Hpa
  | cons iv r ih =>
    obtain ⟨lo, hi⟩ := iv
    obtain ⟨hle, hlo, hhi⟩ := A_wf_head (lo, hi) r Hwf
    have hwf' := A_wf_tail (lo, hi) r Hwf
    simp only [page_allowedb, List.any_cons] at Hpa
    rw [Bool.or_eq_true] at Hpa
    simp only [A_pages]
    rcases Hpa with hpa | hpa
    · rw [Bool.and_eq_true] at hpa
      obtain ⟨h1, h2⟩ := hpa
      rw [decide_eq_true_eq] at h1 h2
      obtain ⟨qlo, hqlo⟩ := Zmod0_multiple lo hlo
      obtain ⟨qhi, hqhi⟩ := Zmod0_multiple hi hhi
      obtain ⟨qp, hqp⟩ := Zmod0_multiple (p.toNat : Int) Hal
      have hq : qlo ≤ qp := by
        unfold page_size at *
        omega
      have hcast : Int.ofNat (qp - qlo).toNat = qp - qlo :=
        Int.toNat_of_nonneg (by omega)
      have hmem : (qp - qlo).toNat ∈ List.range ((hi - lo) / page_size).toNat := by
        rw [List.mem_range, Int.toNat_lt (by omega : (0 : Int) ≤ qp - qlo)]
        have hdiv : (hi - lo) / page_size = qhi - qlo := by
          have hd : hi - lo = (qhi - qlo) * page_size := by
            rw [hqhi, hqlo]; unfold page_size at *; omega
          rw [hd, Int.mul_ediv_cancel _ (by decide : page_size ≠ 0)]
        rw [Int.toNat_of_nonneg (Int.ediv_nonneg (by omega)
          (by unfold page_size; decide : (0 : Int) ≤ page_size)), hdiv]
        unfold page_size at *
        omega
      apply List.mem_append_left
      refine List.mem_map.mpr ⟨(qp - qlo).toNat, hmem, ?_⟩
      unfold page_size at *
      omega
    · exact List.mem_append_right _ (ih hwf' hpa)

/-- [bv_unsigned] is injective on words (it is [BitVec.toNat], cast). -/
theorem NoDup_map_bv_unsigned (l : List word) (h : l.Nodup) :
    (l.map (fun w => (w.toNat : Int))).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons] at ⊢
    rw [List.nodup_cons] at h ⊢
    obtain ⟨ha, hnd⟩ := h
    refine ⟨?_, ih hnd⟩
    intro hmem
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hmem
    have h1 : y.toNat = a.toNat := by
      have h2 : (y.toNat : Int) = (a.toNat : Int) := hyx
      omega
    rw [BitVec.toNat_inj.mp h1] at hy
    exact ha hy

/-- A duplicate-free list of members of [l₂] is no longer than [l₂]. -/
theorem nodup_length_le_of_mem {α : Type} :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ a, a ∈ l₁ → a ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => by simp
  | a :: l, l₂, h₁, hm => by
    rw [List.nodup_cons] at h₁
    obtain ⟨ha, hnd⟩ := h₁
    obtain ⟨s, t, hs⟩ := List.mem_iff_append.mp (hm a List.mem_cons_self)
    subst hs
    have hm' : ∀ b, b ∈ l → b ∈ s ++ t := by
      intro b hb
      have hb' := hm b (List.mem_cons_of_mem a hb)
      rcases List.mem_append.mp hb' with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with hEq | h
        · subst hEq; exact absurd hb ha
        · exact List.mem_append_right _ h
    have ih := nodup_length_le_of_mem hnd hm'
    simp only [List.length_cons, List.length_append] at ih ⊢
    omega

/-- PIGEONHOLE: distinct aligned allowed pages are at most
    [A_bytes A / page_size] many. -/
theorem allowed_pages_bound (A : List (Int × Int)) (pages : List word)
    (Hwf : A_wf A) (Hnd : pages.Nodup)
    (Hal : ∀ p, p ∈ pages → (p.toNat : Int) % page_size = 0)
    (Hpa : ∀ p, p ∈ pages → page_allowedb A p = true) :
    (pages.length : Int) * page_size ≤ A_bytes A := by
  rw [← A_pages_length A Hwf]
  have hlen : pages.length ≤ (A_pages A).length := by
    rw [← List.length_map (f := fun w : word => (w.toNat : Int)) (as := pages)]
    refine nodup_length_le_of_mem (NoDup_map_bv_unsigned pages Hnd) ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact A_pages_in A p Hwf (Hal p hp) (Hpa p hp)
  unfold page_size at *
  omega

/- *** Pages named by an access report                               -/
/- ---------------------------------------------------------------- -/
theorem two64_as_pages : (2 ^ 64 : Int) = page_size * 2 ^ 52 := by decide

/- page_base_woff -/
theorem page_base_of_mod (z : Int) :
    page_base_of (Int.toNat (z % ((2 ^ 64 : Nat) : Int))) = page_base_of z := by
  unfold page_base_of
  have hw : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  have hps : page_size = 4096 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, hw, hps]
  apply congrArg Int.toNat
  have hz : z % 18446744073709551616
      + 18446744073709551616 * (z / 18446744073709551616) = z := by
    have h := Int.mul_ediv_add_emod z 18446744073709551616
    omega
  have hcast : ((Int.toNat (z % 18446744073709551616) : Int)) = z % 18446744073709551616 :=
    Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))
  rw [hcast]
  have hz' : z = z % 18446744073709551616
      + 4096 * (4503599627370496 * (z / 18446744073709551616)) := by
    rw [← hz]
    omega
  have hdiv : z / 4096 = (z % 18446744073709551616) / 4096
      + 4503599627370496 * (z / 18446744073709551616) := by
    have h1 : z / 4096 = (z % 18446744073709551616
        + 4096 * (4503599627370496 * (z / 18446744073709551616))) / 4096 :=
      congrArg (fun t => t / 4096) hz'
    rw [h1, Int.add_mul_ediv_left (a := z % 18446744073709551616)
      (c := 4503599627370496 * (z / 18446744073709551616))
      (by decide : (4096 : Int) ≠ 0)]
  have hmul : (z / 4096) * 4096
      = (z % 18446744073709551616) / 4096 * 4096
        + (z / 18446744073709551616) * 18446744073709551616 := by
    rw [hdiv, Int.add_mul]
    have hcoef : 4503599627370496 * (z / 18446744073709551616) * 4096
        = (z / 18446744073709551616) * 18446744073709551616 := by omega
    rw [hcoef]
  rw [hmul]
  have hcomm : (z % 18446744073709551616) / 4096 * 4096
        + (z / 18446744073709551616) * 18446744073709551616
      = (z % 18446744073709551616) / 4096 * 4096
        + 18446744073709551616 * (z / 18446744073709551616) := by omega
  rw [hcomm, Int.add_mul_emod_self_left]

theorem page_base_woff (a : word) (k : Nat) :
    page_base (woff a k) = page_base_of ((a.toNat : Int) + (k : Int)) := by
  unfold page_base woff
  rw [BitVec.toNat_ofInt]
  exact page_base_of_mod _

/- page_base_of_aligned -/
theorem page_base_of_aligned (z : Int) :
    ((page_base_of z).toNat : Int) % page_size = 0 := by
  unfold page_base_of
  have hw : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
  have hps : page_size = 4096 := rfl
  rw [BitVec.toNat_ofInt, hw]
  have hcast : ((Int.toNat ((z / page_size) * page_size
      % 18446744073709551616) : Int)) = (z / page_size) * page_size
      % 18446744073709551616 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [hcast, hps]
  have hsub : (z / 4096) * 4096 % 18446744073709551616
      = (z / 4096) * 4096
        - 18446744073709551616 * ((z / 4096) * 4096 / 18446744073709551616) := by
    have h := Int.mul_ediv_add_emod ((z / 4096) * 4096) 18446744073709551616
    omega
  rw [hsub, Int.sub_emod]
  have h1 : (z / 4096) * 4096 % 4096 = 0 := by
    rw [Int.mul_emod, Int.emod_self]
    simp
  have h2 : (18446744073709551616
      * ((z / 4096) * 4096 / 18446744073709551616)) % 4096 = 0 := by
    rw [Int.mul_emod]
    simp
  rw [h1, h2]
  decide

/- Pages named by an access report -/
theorem page_mem_false_not_in (p : word) (pages : List word)
    (h : page_mem p pages = false) : p ∉ pages := by
  intro hin
  have ht : pages.any (fun q => p == q) = true :=
    List.any_eq_true.mpr ⟨p, hin, by simp⟩
  unfold page_mem at h
  rw [ht] at h
  simp at h

theorem page_insert_nodup (p : word) (pages : List word)
    (h : pages.Nodup) : (page_insert p pages).Nodup := by
  unfold page_insert
  split
  · exact h
  · rename_i hmem
    rw [List.nodup_cons]
    exact ⟨page_mem_false_not_in p pages (by simpa using hmem), h⟩

theorem access_pages_acc_nodup (base : Int) (n : Nat) (pages : List word)
    (h : pages.Nodup) : (access_pages_acc base n pages).Nodup := by
  induction n generalizing base pages with
  | zero => simpa [access_pages_acc] using h
  | succ k ih =>
    show (access_pages_acc (base + 1) k (page_insert (page_base_of base) pages)).Nodup
    exact ih (base + 1) _ (page_insert_nodup _ _ h)

theorem accesses_pages_nodup (accs : List (word × Nat)) (pages : List word)
    (h : pages.Nodup) : (accesses_pages accs pages).Nodup := by
  induction accs generalizing pages with
  | nil => simpa [accesses_pages] using h
  | cons x accs ih =>
    obtain ⟨aw, n⟩ := x
    show (accesses_pages accs (access_pages_acc (aw.toNat : Int) n pages)).Nodup
    exact ih _ (access_pages_acc_nodup _ _ _ h)

theorem nodup_filter (p : word → Bool) (l : List word) (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    obtain ⟨ha, hnd⟩ := h
    rw [List.filter_cons]
    split
    · rw [List.nodup_cons]
      exact ⟨fun hmem => ha (List.mem_filter.mp hmem).1, ih hnd⟩
    · exact ih hnd

theorem new_pages_props (H : word → Bool) (A : List (Int × Int))
    (lazy : List (word × word)) (mat : List word) (ranges : List (word × Nat))
    (Hcov : lazy_cover H lazy A) (Hav : ranges_avoid H ranges) :
    (newly_materialized_pages lazy mat ranges).Nodup
    ∧ (∀ p, p ∈ newly_materialized_pages lazy mat ranges → p ∉ mat)
    ∧ (∀ p, p ∈ newly_materialized_pages lazy mat ranges →
        (p.toNat : Int) % page_size = 0)
    ∧ (∀ p, p ∈ newly_materialized_pages lazy mat ranges →
        page_in_ranges p lazy = true)
    ∧ (∀ p, p ∈ newly_materialized_pages lazy mat ranges →
        page_allowedb A p = true) := by
  have Hchar : ∀ p, p ∈ newly_materialized_pages lazy mat ranges →
      page_in_ranges p lazy = true ∧ page_mem p mat = false
      ∧ ∃ a n k, (a, n) ∈ ranges ∧ k < n
          ∧ p = page_base_of ((a.toNat : Int) + (k : Int)) := by
    intro p hin
    rw [newly_materialized_pages, List.mem_filter] at hin
    obtain ⟨hin, hf⟩ := hin
    rw [Bool.and_eq_true] at hf
    obtain ⟨hl, hm⟩ := hf
    refine ⟨hl, ?_, ?_⟩
    · simpa using hm
    · rcases accesses_pages_in ranges [] p hin with hin' | hex
      · simp at hin'
      · exact hex
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [newly_materialized_pages]
    exact nodup_filter _ _ (accesses_pages_nodup ranges [] List.nodup_nil)
  · intro p hp
    exact page_mem_false_not_in p mat (Hchar p hp).2.1
  · intro p hp
    obtain ⟨-, -, a, n, k, -, -, rfl⟩ := Hchar p hp
    exact page_base_of_aligned _
  · intro p hp
    exact (Hchar p hp).1
  · intro p hp
    obtain ⟨hl, -, a, n, k, hin, hk, rfl⟩ := Hchar p hp
    have hw : H (woff a k) = false := Hav a n hin k hk
    rw [← page_base_woff] at hl ⊢
    exact Hcov (woff a k) hl hw


/-- Accessor computation rules for [with_vm_backing]. -/
theorem m_vm_materialized_wvb (l : List (word × word)) (X : List word) (m : Model) :
    m_vm_materialized (with_vm_backing l X m) = X := rfl
theorem m_vm_lazy_wvb (l : List (word × word)) (X : List word) (m : Model) :
    m_vm_lazy (with_vm_backing l X m) = l := rfl
theorem m_vmmaps_wvb (l : List (word × word)) (X : List word) (m : Model) :
    m_vmmaps (with_vm_backing l X m) = m_vmmaps m := rfl
theorem m_halted_wvb (l : List (word × word)) (X : List word) (m : Model) :
    m_halted (with_vm_backing l X m) = m_halted m := rfl
theorem eager_used_wvb (X : List word) (m : Model) :
    eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m := rfl

theorem with_vm_backing_id (m : Model) :
    with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m := rfl

theorem MInv_wvb (A : List (Int × Int)) (m : Model) (X : List word)
    (H1 : X.Nodup)
    (H2 : ∀ p, p ∈ X → (p.toNat : Int) % page_size = 0)
    (H3 : ∀ p, p ∈ X → page_allowedb A p = true)
    (H4 : ∀ p, p ∈ X → page_in_ranges p (m_vm_lazy m) = true)
    (H5 : eager_used m + A_bytes A ≤ (m_vmmaps m).vm_limit) :
    MInv A (with_vm_backing (m_vm_lazy m) X m) := by
  constructor
  · simpa only [m_vm_materialized_wvb (m_vm_lazy m) X m] using H1
  · intro p hp
    simpa only [m_vm_materialized_wvb (m_vm_lazy m) X m] using H2 p hp
  · intro p hp
    simpa only [m_vm_materialized_wvb (m_vm_lazy m) X m] using H3 p hp
  · intro p hp
    simpa only [m_vm_materialized_wvb (m_vm_lazy m) X m, m_vm_lazy_wvb] using H4 p hp
  · simpa only [m_vmmaps_wvb, eager_used_wvb] using H5

/-- Establishing [MInv] on a model with an EMPTY materialized ledger (e.g.
    right after the shadow reservations): only the budget is needed. -/
theorem MInv_intro_empty (A : List (Int × Int)) (m : Model)
    (He : m_vm_materialized m = [])
    (Hb : eager_used m + A_bytes A ≤ (m_vmmaps m).vm_limit) :
    MInv A m := by
  constructor
  · rw [He]; exact List.nodup_nil
  · intro p hp; rw [He] at hp; simp at hp
  · intro p hp; rw [He] at hp; simp at hp
  · intro p hp; rw [He] at hp; simp at hp
  · exact Hb

/-- Re-establishing [MInv] after a syscall that changed only [m_vmmaps]
    (plain mmap/munmap of non-lazy memory, brk, mprotect): the page facts
    carry over, the budget must be re-checked. -/
theorem MInv_transport (A : List (Int × Int)) (m m' : Model)
    (hm : MInv A m)
    (Hm : m_vm_materialized m' = m_vm_materialized m)
    (Hl : m_vm_lazy m' = m_vm_lazy m)
    (Hb : eager_used m' + A_bytes A ≤ (m_vmmaps m').vm_limit) :
    MInv A m' := by
  constructor
  · rw [Hm]; exact hm.minv_nodup
  · intro p hp; rw [Hm] at hp; exact hm.minv_aligned p hp
  · intro p hp; rw [Hm] at hp; exact hm.minv_allowed p hp
  · intro p hp; rw [Hm] at hp; rw [Hl]; exact hm.minv_lazy p hp
  · exact Hb

/-- THE ACCOUNTING THEOREM.  Under the invariant, an H-avoiding access
    report always materializes (never hits the budget), the invariant is
    preserved, and only the materialized ledger changes. -/
theorem materialize_restricted (H : word → Bool) (A : List (Int × Int))
    (m : Model) (ranges : List (word × Nat))
    (Hcov : lazy_cover H (m_vm_lazy m) A) (Hwf : A_wf A) (Hinv : MInv A m)
    (Hav : ranges_avoid H ranges) :
    ∃ mat', materialize_model_accesses m ranges
        = some (with_vm_backing (m_vm_lazy m) mat' m)
      ∧ MInv A (with_vm_backing (m_vm_lazy m) mat' m) := by
  obtain ⟨Hnd, Hal, Hpa, Hlz, Hbud⟩ := Hinv
  obtain ⟨Nnd, Nfresh, Nal, Nlz, Npa⟩ :=
    new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav
  have Happ_nd : (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges
      ++ m_vm_materialized m).Nodup := by
    rw [List.nodup_append]
    exact ⟨Nnd, Hnd, fun a ha b hb heq => Nfresh a ha (heq ▸ hb)⟩
  have Happ_al : ∀ p, p ∈ newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges
      ++ m_vm_materialized m → (p.toNat : Int) % page_size = 0 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nal p hp
    · exact Hal p hp
  have Happ_pa : ∀ p, p ∈ newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges
      ++ m_vm_materialized m → page_allowedb A p = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Npa p hp
    · exact Hpa p hp
  have Happ_lz : ∀ p, p ∈ newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges
      ++ m_vm_materialized m → page_in_ranges p (m_vm_lazy m) = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact Nlz p hp
    · exact Hlz p hp
  have Hbound := allowed_pages_bound A
    (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges
      ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa
  rw [List.length_append, Int.natCast_add, Int.add_mul] at Hbound
  cases hnew : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges with
  | nil =>
    refine ⟨m_vm_materialized m, ?_,
      MInv_wvb A m (m_vm_materialized m) Hnd Hal Hpa Hlz Hbud⟩
    unfold materialize_model_accesses materialize_accesses
    dsimp only
    rw [hnew]
  | cons p0 new' =>
    rw [hnew] at Nnd Nfresh Nal Nlz Npa Happ_nd Happ_al Happ_pa Happ_lz Hbound
    have hc : vm_backing_used m + ((p0 :: new').length : Int) * page_size
        ≤ (m_vmmaps m).vm_limit := by
      rw [vm_backing_used_split]
      omega
    refine ⟨(p0 :: new') ++ m_vm_materialized m, ?_,
      MInv_wvb A m _ Happ_nd Happ_al Happ_pa Happ_lz Hbud⟩
    unfold materialize_model_accesses materialize_accesses
    dsimp only
    rw [hnew]
    rw [ite_eq_left hc]

/- ===================================================================== -/
/- ** Part 4.  Node lemmas: accounted steps, [node_ok], chains           -/
/- ===================================================================== -/

/- Section Nodes : `segs`, `H`, `HH`, `Hwx` are explicit leading
   parameters here, as in Part 2. -/

/-- Exact characterisation of the [sstep] successors of a configuration
    (verbatim copy of [ShapeAlg.node_ok], so the two are convertible). -/
def node_ok (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) : Prop :=
  (∀ i, sstep segs c (evs i) (.SNext (nx i)))
    ∧ (∀ e st, sstep segs c e st → ∃ i, e = evs i ∧ st = .SNext (nx i))

/-- H-cleanliness is preserved by plain steps. -/
theorem step_hclean (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (ms ms' : machine_state) (Hc : hclean H ms)
    (Hs : RiscvSemantics.step segs ms = .MachineOk ms') :
    hclean H ms' := by
  rw [← hclean_restrict_id H ms Hc] at Hs
  obtain ⟨_, _, _, _, hcl, _⟩ := step_restrict_sound segs H HH Hwx ms ms' Hs
  exact hcl

/-- ... and by [msteps] chains. -/
theorem msteps_hclean (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (ms ms' : machine_state) (Hms : msteps segs ms ms')
    (Hc : hclean H ms) : hclean H ms' := by
  induction Hms with
  | mst_refl ms => exact Hc
  | mst_step ms ms1 ms2 hsvc hstep hrest ih =>
    exact ih (step_hclean segs H HH Hwx ms ms1 Hc hstep)

theorem unrestrict_munrestrict (H : word → Bool) (f g : word → Option byte)
    (ms' : machine_state) :
    unrestrict H (munrestrict H f g) ms' = unrestrict H f ms' := by
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms'
  simp only [unrestrict]
  congr 1
  funext x
  unfold munrestrict
  cases h : H x <;> rfl

/-- The accounted step from a restricted plain step. -/
theorem mi_account_step_restricted (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms : machine_state) (msr' : machine_state)
    (model : Model)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A) (Hinv : MInv A model)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr') :
    ∃ mat', mi_account_step segs ms model
        = .MachineOk (unrestrict H ms.ms_mem msr',
                      with_vm_backing (m_vm_lazy model) mat' model)
      ∧ MInv A (with_vm_backing (m_vm_lazy model) mat' model)
      ∧ hclean H msr' := by
  obtain ⟨rep, hsa, hv, hrs, hcl, _⟩ :=
    step_restrict_sound segs H HH Hwx ms msr' Hs
  obtain ⟨mat', hmat, hinv⟩ :=
    materialize_restricted H A model rep.accessed_ranges Hcov Hwf Hinv hrs
  refine ⟨mat', ?_, hinv, hcl⟩
  unfold mi_account_step
  rw [hsa]
  simp only [hmat, hv]

/-- Determinism of instruction steps of [sstep]. -/
theorem sstep_instr_det (segs : List Segment) (ms : machine_state) (model : Model)
    (ms1 : machine_state) (model1 : Model) (e : List event) (st : step_to)
    (Hsvc : ms.ms_svc_pending = none)
    (Hacc : mi_account_step segs ms model = .MachineOk (ms1, model1))
    (Hss : sstep segs (mkCfg ms model) e st) :
    e = [] ∧ st = .SNext (mkCfg ms1 model1) := by
  cases Hss <;> simp_all [machine_result.MachineOk.injEq, Prod.mk.injEq, mkCfg]

/-- The instruction node on a state whose RESTRICTION steps. -/
theorem node_instr_restricted (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (A : List (Int × Int)) (ms : machine_state) (msr' : machine_state)
    (model : Model)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A) (Hinv : MInv A model)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr') :
    ∃ model', MInv A model' ∧ same_but_materialized model model' ∧ hclean H msr'
      ∧ mi_account_step segs ms model
          = .MachineOk (unrestrict H ms.ms_mem msr', model')
      ∧ node_ok segs (mkCfg ms model) Unit (fun _ => [])
          (fun _ => mkCfg (unrestrict H ms.ms_mem msr') model') := by
  obtain ⟨mat', hacc, hinv, hcl⟩ :=
    mi_account_step_restricted segs H HH Hwx A ms msr' model Hcov Hwf Hinv Hs
  refine ⟨with_vm_backing (m_vm_lazy model) mat' model, hinv,
    with_vm_backing_same model mat', hcl, hacc, ?_⟩
  refine ⟨fun _ => sstep.instr ms model _ _ Hh Hsvc hacc, ?_⟩
  intro e st hss
  obtain ⟨he, hst⟩ := sstep_instr_det segs ms model _ _ e st Hsvc hacc hss
  exact ⟨Unit.unit, he, hst⟩

/-- The chain step: one restricted instruction step discharges [P]. -/
theorem rz_step_restricted (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (P : config → Prop)
    (P_silent1 : ∀ c c', node_ok segs c Unit (fun _ => []) (fun _ => c') → P c' → P c)
    (A : List (Int × Int)) (ms : machine_state) (msr' : machine_state)
    (model : Model)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A) (Hinv : MInv A model)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hs : RiscvSemantics.step segs (restrict H ms) = .MachineOk msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        P (mkCfg (unrestrict H ms.ms_mem msr') model')) :
    P (mkCfg ms model) := by
  obtain ⟨model', hinv, hsame, _, _, hnode⟩ :=
    node_instr_restricted segs H HH Hwx A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs
  exact P_silent1 _ _ hnode (Hk model' hinv hsame)

/-- The induction form of the chain: [msteps] on the RESTRICTED state, with
    [P] closed under silent unit nodes, discharges [P] at the full
    configuration. -/
theorem rz_msteps_restricted (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (P : config → Prop)
    (P_silent1 : ∀ c c', node_ok segs c Unit (fun _ => []) (fun _ => c') → P c' → P c)
    (A : List (Int × Int)) (msr0 msr' : machine_state)
    (Hms : msteps segs msr0 msr') :
    ∀ (ms : machine_state) (model : Model), msr0 = restrict H ms →
      lazy_cover H (m_vm_lazy model) A → A_wf A → MInv A model →
      m_halted model = none →
      (∀ model', MInv A model' → same_but_materialized model model' →
          P (mkCfg (unrestrict H ms.ms_mem msr') model')) →
      P (mkCfg ms model) := by
  induction Hms with
  | mst_refl msr =>
    intro ms model heq Hcov Hwf Hinv Hh Hk
    subst msr
    have hk := Hk model Hinv (same_but_materialized_refl model)
    rwa [unrestrict_restrict] at hk
  | mst_step msr msr1 msr2 hsvc hstep hrest ih =>
    intro ms model heq Hcov Hwf Hinv Hh Hk
    subst msr
    obtain ⟨model1, hinv1, hsame1, hcl1, _, hnode⟩ :=
      node_instr_restricted segs H HH Hwx A ms msr1 model Hcov Hwf Hinv Hh hsvc hstep
    refine P_silent1 _ _ hnode ?_
    obtain ⟨-, -, hlazy, -, -, -, -, -, -, -, -, -, hhalted, -⟩ :=
      same_but_materialized_frame model model1 hsame1
    refine ih (unrestrict H ms.ms_mem msr1) model1
      (restrict_unrestrict_clean H ms.ms_mem msr1 hcl1).symm
      (by rw [hlazy]; exact Hcov) Hwf hinv1 (by rw [hhalted]; exact Hh) ?_
    intro model' hinv' hsame'
    have htr := same_but_materialized_trans model model1 model' hsame1 hsame'
    have hk := Hk model' hinv' htr
    simpa only [unrestrict_mem, unrestrict_munrestrict] using hk

/-- The user-facing form of the chain: [msteps] computed on the RESTRICTED
    state discharges [P] at the full configuration, given [P] at every
    admissible successor (full memory put back; model changed only in its
    materialized ledger, still [MInv]).  The continuation also learns that
    the chain's final restricted state is H-clean. -/
theorem rz_msteps_restricted' (segs : List Segment) (H : word → Bool)
    (HH : H_off_segments segs H) (Hwx : wx_segs_nowrap segs)
    (P : config → Prop)
    (P_silent1 : ∀ c c', node_ok segs c Unit (fun _ => []) (fun _ => c') → P c' → P c)
    (A : List (Int × Int)) (ms : machine_state) (msr' : machine_state)
    (model : Model)
    (Hcov : lazy_cover H (m_vm_lazy model) A) (Hwf : A_wf A) (Hinv : MInv A model)
    (Hh : m_halted model = none)
    (Hms : msteps segs (restrict H ms) msr')
    (Hk : ∀ model', MInv A model' → same_but_materialized model model' →
        hclean H msr' → P (mkCfg (unrestrict H ms.ms_mem msr') model')) :
    P (mkCfg ms model) := by
  have hcl := msteps_hclean segs H HH Hwx (restrict H ms) msr' Hms (restrict_hclean H ms)
  exact rz_msteps_restricted segs H HH Hwx P P_silent1 A (restrict H ms) msr' Hms
    ms model rfl Hcov Hwf Hinv Hh (fun model' hinv hsame => Hk model' hinv hsame hcl)

/- ===================================================================== -/
/- ** Part 5.  Generic lazy-tolerant SYSCALL node                        -/
/- ===================================================================== -/

/-- The computable successor model after materializing [accs]. -/
def materialized_succ (m : Model) (accs : List (word × Nat)) : Model :=
  match materialize_model_accesses m accs with
  | some m' => m'
  | none => m

/-- A generic non-exiting syscall node through a non-empty lazy ledger.
    The per-syscall content is the pure characterisation of
    [syscall_spec] at this input ([Hsound]/[Hcompl]); the lazy-page side
    conditions are that every outcome's effect accesses (copyins ++
    writes) avoid [H] and every outcome's model satisfies the budget
    invariant.  The successor of resolution [i] carries the materialized
    model [materialized_succ (mdl i) _], which is [MInv] and equal to
    [mdl i] up to the materialized ledger. -/
theorem node_syscall_restricted (segs : List Segment) (H : word → Bool)
    (A : List (Int × Int)) (ms : machine_state) (model : Model) (x8 : word)
    (I : Type) (eff : I → SyscallEffect) (mdl : I → Model) (evs : I → List event)
    (Hwf : A_wf A) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hsound : ∀ i, syscall_spec (sys_input segs ms x8) model
      (.ok (eff i) (mdl i) (evs i)))
    (Hcompl : ∀ r, syscall_spec (sys_input segs ms x8) model r →
      ∃ i, r = .ok (eff i) (mdl i) (evs i))
    (Hnh : ∀ i, m_halted (mdl i) = none)
    (Hcov : ∀ i, lazy_cover H (m_vm_lazy (mdl i)) A)
    (Hinv : ∀ i, MInv A (mdl i))
    (Hav : ∀ i, ranges_avoid H (syscall_effect_accesses (eff i))) :
    (∀ i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
      ∧ same_but_materialized (mdl i)
          (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
    ∧ node_ok segs (mkCfg ms model) I evs
        (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
          (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))) := by
  have Hmat : ∀ i, ∃ mat',
      materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
        = some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
      ∧ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i)) := by
    intro i
    exact materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)
  constructor
  · intro i
    obtain ⟨mat', hmat, hinv'⟩ := Hmat i
    have hsucc : materialized_succ (mdl i) (syscall_effect_accesses (eff i))
        = with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i) := by
      unfold materialized_succ
      rw [hmat]
    rw [hsucc]
    exact ⟨hinv', with_vm_backing_same (mdl i) mat'⟩
  · refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨mat', hmat, -⟩ := Hmat i
      have hsucc : materialized_succ (mdl i) (syscall_effect_accesses (eff i))
          = with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i) := by
        unfold materialized_succ
        rw [hmat]
      simp only []
      rw [hsucc]
      exact sstep.syscall ms model x8 (eff i) (mdl i) _ (evs i) Hh Hsvc
        (Hsound i) (Hnh i) hmat
    · intro e st hss
      cases hss with
      | instr ms1 model1 ms2 model2 hh hsvc hstep =>
        rw [Hsvc] at hsvc
        simp at hsvc
      | instr_fault ms1 model1 hh hsvc hstep =>
        rw [Hsvc] at hsvc
        simp at hsvc
      | instr_unmodeled ms1 model1 hh hsvc hstep =>
        rw [Hsvc] at hsvc
        simp at hsvc
      | syscall ms1 model1 x8' eff' mdl1 mdl2 evs1 hh hsvc hspec hh' hmat =>
        rw [Hsvc] at hsvc
        injection hsvc with hx8
        subst hx8
        obtain ⟨i, hi⟩ := Hcompl _ hspec
        injection hi with heff hmdl hevs
        subst heff
        subst hmdl
        subst hevs
        refine ⟨i, rfl, ?_⟩
        simp only []
        unfold materialized_succ
        rw [hmat]
        simp only [mkCfg]
      | syscall_materialization_fault ms1 model1 x8' eff' mdl1 evs1 hh hsvc hspec hh' hmat =>
        rw [Hsvc] at hsvc
        injection hsvc with hx8
        subst hx8
        obtain ⟨i, hi⟩ := Hcompl _ hspec
        injection hi with heff hmdl hevs
        subst heff
        subst hmdl
        subst hevs
        obtain ⟨mat', hmat', -⟩ := Hmat i
        rw [hmat] at hmat'
        simp at hmat'
      | exit ms1 model1 x8' eff' mdl1 evs1 code hh hsvc hspec hh' hk =>
        rw [Hsvc] at hsvc
        injection hsvc with hx8
        subst hx8
        obtain ⟨i, hi⟩ := Hcompl _ hspec
        injection hi with heff hmdl hevs
        subst hmdl
        rw [Hnh i] at hh'
        simp at hh'
      | killed ms1 model1 x8' eff' mdl1 evs1 sig hh hsvc hspec hk =>
        rw [Hsvc] at hsvc
        injection hsvc with hx8
        subst hx8
        obtain ⟨i, hi⟩ := Hcompl _ hspec
        injection hi with heff hmdl hevs
        subst hmdl
        rw [m_killed_of_m_halted_none (mdl i) (Hnh i)] at hk
        simp at hk
      | syscall_unmodeled ms1 model1 x8' hh hsvc hspec =>
        rw [Hsvc] at hsvc
        injection hsvc with hx8
        subst hx8
        obtain ⟨i, hi⟩ := Hcompl _ hspec
        simp at hi

/- ===================================================================== -/
/- ** Part 6.  Instantiation helpers                                     -/
/- ===================================================================== -/

/-- A canonical hidden-set: the pages of the ranges [L] (typically all lazy
    ranges the run will ever hold) minus the allowed pages. -/
def mkH (L : List (word × word)) (A : List (Int × Int)) : word → Bool :=
  fun a => page_in_ranges (page_base a) L && !(page_allowedb A (page_base a))

/-- Boolean checkers (close by [decide] on a concrete image). -/
def seg_top (seg : Segment) : Int :=
  (seg.seg_base : Int) + (seg.seg_size : Int)

def wx_segs_nowrap_b (segs : List Segment) : Bool :=
  segs.all (fun seg =>
    !(seg_executable seg && seg_writable seg) || decide (seg_top seg ≤ 2 ^ 64))

def segs_below_b (segs : List Segment) (top : Int) : Bool :=
  segs.all (fun seg => decide (seg_top seg ≤ top))

/-- For [mkH]: hidden addresses lie in pages inside [L]'s ranges, so it is
    enough that every range of [L] starts at or above [top] (page-aligned
    [top]). -/
def ranges_from_b (L : List (word × word)) (top : Int) : Bool :=
  L.all (fun r => decide (top ≤ (r.1.toNat : Int)))

theorem wx_segs_nowrap_of_b (segs : List Segment)
    (Hb : wx_segs_nowrap_b segs = true) : wx_segs_nowrap segs := by
  intro seg hin hwx
  unfold wx_segs_nowrap_b at Hb
  rw [List.all_eq_true] at Hb
  have h := Hb seg hin
  rw [hwx] at h
  exact of_decide_eq_true h

theorem page_in_ranges_incl (p : word) (l L : List (word × word))
    (Hincl : ∀ r, r ∈ l → r ∈ L) (Hp : page_in_ranges p l = true) :
    page_in_ranges p L = true := by
  unfold page_in_ranges at *
  rw [List.any_eq_true] at *
  obtain ⟨r, hr, hpr⟩ := Hp
  exact ⟨r, Hincl r hr, hpr⟩

theorem lazy_cover_mkH (L : List (word × word)) (A : List (Int × Int))
    (lazy : List (word × word)) (Hincl : ∀ r, r ∈ lazy → r ∈ L) :
    lazy_cover (mkH L A) lazy A := by
  intro w Hl Hw
  unfold mkH at Hw
  rw [page_in_ranges_incl (page_base w) lazy L Hincl Hl] at Hw
  simp only [Bool.true_and] at Hw
  cases hp : page_allowedb A (page_base w) with
  | true => rfl
  | false => rw [hp] at Hw; simp at Hw

theorem find_segment1_none_above (segs : List Segment) (top x : Int)
    (Hb : segs_below_b segs top = true) (Hx : top ≤ x) :
    find_segment segs x 1 = none := by
  induction segs with
  | nil => rfl
  | cons s l ih =>
    unfold segs_below_b at Hb
    rw [List.all_eq_true] at Hb
    have hs : seg_top s ≤ top := by simpa using Hb s (by simp)
    have hl : segs_below_b l top = true := by
      unfold segs_below_b
      rw [List.all_eq_true]
      intro a ha
      simpa using Hb a (List.mem_cons_of_mem _ ha)
    unfold find_segment
    have hfalse :
        (decide ((s.seg_base : Int) ≤ x) &&
          decide (x + 1 ≤ (s.seg_base : Int) + (s.seg_size : Int))) = false := by
      have h2 : decide (x + 1 ≤ (s.seg_base : Int) + (s.seg_size : Int)) = false := by
        apply decide_eq_false
        unfold seg_top at hs
        omega
      rw [h2]
      simp
    simp only []
    rw [hfalse]
    simp only [Bool.false_eq_true, ite_false]
    exact ih hl

/-- If every segment ends at or below [top] and every hidden address is at
    or above it, [H] is off-segments. -/
theorem H_off_segments_above (segs : List Segment) (H : word → Bool) (top : Int)
    (Hb : segs_below_b segs top = true)
    (Ha : ∀ a, H a = true → top ≤ (a.toNat : Int)) :
    H_off_segments segs H := by
  intro a ha
  exact find_segment1_none_above segs top (a.toNat : Int) Hb (Ha a ha)

/-- The page of an address is at or below it. -/
theorem page_base_le (a : word) : (page_base a).toNat ≤ a.toNat := by
  have hz : (0 : Int) ≤ (a.toNat : Int) / page_size * page_size := by
    apply Int.mul_nonneg
    · exact Int.ediv_nonneg (by omega) (by decide)
    · decide
  have hle : (a.toNat : Int) / page_size * page_size ≤ (a.toNat : Int) := by
    simpa [Int.mul_comm] using Int.ediv_mul_le (a.toNat : Int) (by decide : page_size ≠ 0)
  unfold page_base page_base_of
  rw [← Int.toNat_of_nonneg hz, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  have hlt : (((a.toNat : Int) / page_size * page_size).toNat) < 2 ^ 64 := by
    have h1 := Int.toNat_lt (n := 2 ^ 64)
      (z := (a.toNat : Int) / page_size * page_size) hz
    rw [h1]
    have h2 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by simp
    rw [h2]
    have := a.isLt
    omega
  rw [Nat.mod_eq_of_lt hlt]
  exact Int.toNat_le_toNat hle

theorem mkH_above (L : List (word × word)) (A : List (Int × Int)) (top : Int)
    (a : word) (Hb : ranges_from_b L top = true) (Ha : mkH L A a = true) :
    top ≤ (a.toNat : Int) := by
  unfold mkH at Ha
  rw [Bool.and_eq_true] at Ha
  obtain ⟨Hp, _⟩ := Ha
  unfold page_in_ranges at Hp
  rw [List.any_eq_true] at Hp
  obtain ⟨r, hr, hpr⟩ := Hp
  obtain ⟨lo, sz⟩ := r
  simp only [] at hpr
  rw [Bool.and_eq_true] at hpr
  obtain ⟨h1, _⟩ := hpr
  have h1' : (lo.toNat : Int) ≤ ((page_base a).toNat : Int) := of_decide_eq_true h1
  unfold ranges_from_b at Hb
  rw [List.all_eq_true] at Hb
  have hb := Hb (lo, sz) hr
  simp only [] at hb
  have hb' : top ≤ (lo.toNat : Int) := of_decide_eq_true hb
  have hp := page_base_le a
  omega

theorem H_off_segments_mkH (segs : List Segment) (L : List (word × word))
    (A : List (Int × Int)) (top : Int)
    (Hs : segs_below_b segs top = true) (HL : ranges_from_b L top = true) :
    H_off_segments segs (mkH L A) := by
  apply H_off_segments_above segs (mkH L A) top Hs
  intro a ha
  exact mkH_above L A top a HL ha

/- ===================================================================== -/
/- Sanity checks for the decidable definitions (convention: every -/
/- decidable definition gets a couple of `by decide` checks).           -/
/- ===================================================================== -/
example : A_bytes [(0, 4096), (8192, 12288)] = 4096 + 4096 := by decide
example : page_allowedb [(0, 8192)] (BitVec.ofInt 64 4096) = true := by decide
example : page_allowedb [(0, 8192)] (BitVec.ofInt 64 8192) = false := by decide

/- ===================================================================== -/
/- COMPLETE.  Every declaration of Parts 1-6 is present, no proof      -/
/- obligation is left open, and no escape hatch is used anywhere in     -/
/- this file.                                                          -/
/-                                                                     -/
/- The pigeonhole chain (`A_pages` -> `A_pages_length` / `A_pages_in` -> -/
/- `allowed_pages_bound`) closes Part 3's accounting theorem            -/
/- [`materialize_restricted`], and the node lemmas of Parts 4-5         -/
/- [`mi_account_step_restricted`, [`node_instr_restricted`], the        -/
/- [`rz_*_restricted`] chain and [`node_syscall_restricted`] follow     -/
/- from it.  The instantiation of the chain lemmas at a particular      -/
/- [P] ( `AsanAcctShape`: [P := realizes segs · T] with      -/
/- [P_silent1 := rz_silent1 segs _ _ T], giving                          -/
/- `rz_msteps_restricted_T`) lives in its own downstream file, as it    -/
/- does .                                                       -/
/-                                                                     -/
/- on ordering: this tree puts `MInv_intro_empty` /            -/
/- `MInv_transport` at the very END (Part 6); here they sit right after -/
/- the other `MInv` lemmas because they belong with them.  Statements   -/
/- are , unchanged.                                           -/
/- ===================================================================== -/








