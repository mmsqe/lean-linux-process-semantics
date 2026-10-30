/-
  * LinuxProcessSem.Sys.Mm.Mremap — mremap (216)


  This file answers to Linux [mm/mremap.c]: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  What each dependency supplies:

  - `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
    so a spec's type is `SysSpec SyscallEffect`, and `getModelSpec` is the
    state accessor;
  - `Sys.Syscall` supplies `ret_only`, `err_ret`, `errno_from` and
    `w_is0`;
  - `Sys.Uapi` supplies `MREMAP_MAYMOVE`;
  - `StateVm` supplies `iv_overlap`, `region_free`, `map_remove`,
    `iv_subtract`, `maps_subtract`, `maps_subtract_all`, `map_contains`,
    `map_has`, `noaccess_pages_owned`, `vm_backed_maps`,
    `vm_backing_used`, `vm_backing_within_limit`, `page_outside_range`,
    `lazy_interior`, `vm_resize_backing`, `page_in_half_open` and
    `move_page_base` — the module that owns the `State.lean` VM layer;
  - `StateLedger` supplies the ledger accessors `m_vmmaps`, `m_vm_lazy`,
    `m_vm_materialized`, the setters `with_vmmaps` / `with_vm_backing`,
    `alloc_top`, `live_bytes`, and the constructors
    `VmMaps.mkVmMapsFull` / `mkVmMaps` / `mkModel` the checks below use;
  - `State` supplies `page_size`, `page_round_up_Z`,
    `page_round_down_Z_within`, `two_pow_64` and `EINVAL`/`ENOMEM`.

  `Sys.Mm.Mmap` is NOT imported.  It is where the shared mm vocabulary
  lives (`Mmap.brk_grow_ok`, `Mmap.mmap_spec`,
  `Mmap.brk_budget_refused_b`), and the comments below CITE it as an
  argument, but no definition of this file evaluates anything from it —
  the citations are prose.  Leaving the dependency out keeps this file's
  build to the state modules it actually reads.

  NOTATION.  `Z` is `Int`, `word` is `BitVec 64`, `list` is `List`;
  `Z_to_bv 64 z` is `BitVec.ofInt 64 z`; `bv_unsigned w` is
  `(w.toNat : Int)`, the same function on the same carrier (see
  `StateLedger`'s note on the absent `bv_unsigned`); `negb` is `!`;
  `Z.eqb a b` is `a == b`; `Z.ltb`/`Z.leb` are `decide (· < ·)` /
  `decide (· ≤ ·)`; `Z.min`/`Z.max` are `min`/`max` on `Int`; the
  `VmMaps` projections `vm_maps h` / `vm_reserved h` / `vm_noaccess h`
  are structure fields here (`h.vm_maps`, …).

  UNUSED-VARIABLE LINTER.  `mremap_inplace_grow_b`
  and `mremap_fresh_b` bind an `old_nZ` they do not read — the kernel's
  in-place test and its placement test both need only the NEW length's
  rounding — and the signatures below keep it, because a caller passes
  the pair `(old_nZ, new_nZ)` and a future arm may read it.  Lean's
  `linter.unusedVariables` warns on that, so it is switched off once for
  the whole file rather than silenced by renaming the arguments.

  HELPER LEMMAS.  Five `private`
  facts are proved beside their one consumer because nothing else states
  them: `page_round_up_Z_aligned` and
  `page_round_down_Z_aligned` (the `Z.div_exact` half of
  `lazy_interior_aligned`), `maps_subtract_all_append_cuts` (two cut
  lists in sequence), and `iv_overlap_false_mp` / `iv_overlap_false_intro`
  (the two directions between `iv_overlap = false` and the interval
  inequalities).  The checks below add `private` demo fixtures on top.  No
  statement is omitted or weakened; the helpers only name steps the proofs
  carry inline.

  `decide`.  There is no closed computation to re-use in this file.  The
  `by decide` checks below mirror the boundary cases the spec's own
  `Checks.Examples` names, plus the arithmetic identities the proofs lean
  on, and are marked as such.

  `Checks/` CITATIONS.  The comments below cite three checker modules as
  design rationale: `Checks/Examples.lean` (this spec's concrete boundary
  states), `Checks/BudgetPremise.lean` (the budget mark's refusal and
  separating lemmas) and `Checks/VmMapsDisjoint.lean` (the ledger frame
  cascade).  A citation names the module where the declaration lives; each
  load-bearing one is also marked with its home where it occurs.  This
  file does not depend on any of the three (they sit above it), so it
  cites rather than applies, and no statement in this file is proved by one
  of them.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

set_option linter.unusedVariables false

namespace LinuxSem.LinuxProcessSem.Sys.Mm.Mremap

/-- mremap's modeled private-anonymous shape has no externally tracked
    failure condition beyond address-space exhaustion.  Bad arguments and
    unsupported VMA shapes are handled deterministically/fail-closed below.

    Traced through [SYSCALL_DEFINE5(mremap, ...)] (mm/mremap.c:1961-1994,
    Linux v6.18.46; the walk is its body [do_mremap], :1911-1952, and the
    helpers it calls, in mm/mremap.c unless another file is named) for
    exactly that shape — flags exactly MREMAP_MAYMOVE, [old] page
    aligned, both sizes nonzero, the source one tracked private anonymous
    rw mapping.  Every errno the call can still reach at RUN time is
    ENOMEM, and only on a RESIZING call:

    - equal size: NONE.  [check_prep_vma] returns at :1676-1677 before
      any allocation, split or accounting, and [mremap_at] answers [addr]
      at :1559, so nothing on that branch can fail — see [mremap_spec],
      which is why the equal-size arm sits outside the [alt] that offers
      this list;
    - shrink: a failed [do_vmi_munmap] ([shrink_vma], :1337-1338), which
      has to split the vma, so it can fail to allocate ([__split_vma],
      mm/vma.c:510-512, 523-524, 530-532) and, when the kernel's vma
      extends past the modeled entry, exceed [sysctl_max_map_count]
      ([vms_gather_munmap_vmas], mm/vma.c:1389-1393);
    - grow in place: [security_vm_enough_memory_mm] ([vrm_calc_charge],
      :990, overcommit) and a failed [vma_merge_extend]
      ([expand_vma_in_place], :1470, answered at :1471-1473);
    - grow by moving: [may_expand_vm] (mm/mmap.c:1326-1330 —
      RLIMIT_AS / RLIMIT_DATA) reached through [check_prep_vma] at
      :1742-1743, a failed [get_unmapped_area] ([vrm_set_new_addr],
      :957-960), and [move_vma]'s map-count check ([prep_move_vma],
      :1043-1044), its overcommit check (:1281-1282), a failed [copy_vma]
      ([copy_vma_and_data], :1193-1198), and a short [move_page_tables]
      (:1208-1209).

    Every other errno the function can return is a GATE this shape has
    already passed, or one the spec answers itself — not a runtime
    failure, so none of them is injectable:

    - EINVAL: unknown flag bits ([check_mremap_params], :1759-1760),
      FIXED without MAYMOVE (:1791-1792) and DONTUNMAP resizing
      (:1795-1796) are all excluded by the exact-flags test;
      [offset_in_page(addr)] (:1763-1764) and a zero [new_len]
      (:1771-1772) are the deterministic -EINVAL the spec returns itself;
      a rounded [new_len] above TASK_SIZE (:1775-1776) is deterministic
      -EINVAL too, which the spec returns itself; that gate is younger
      than the MAYMOVE-only path (a v2.5 kernel tested it only when the
      caller gave [new_addr], and the request went on to -ENOMEM from
      [get_unmapped_area]), and v6.18.46 tests it before any VMA is
      looked up;
      a zero [old_len] on a private vma ([check_prep_vma], :1690-1693) is
      excluded by the clone gate; DONTUNMAP over a VM_DONTEXPAND /
      VM_PFNMAP vma (:1696-1698) is excluded for the same reason as :1795,
      the exact-flags test never lets DONTUNMAP through;
      the pgoff-overflow check (:1733-1734) needs [pgoff + (new_len >> 12)]
      to wrap 64 bits, and for an anonymous vma [do_mmap] sets
      [pgoff = addr >> PAGE_SHIFT] (mm/mmap.c [do_mmap]), so [alloc_top]
      ([State.alloc_top_lt]) caps it under 2^52 against a
      [new_len >> 12] below 2^52.
    - EFAULT: no vma at [addr] ([check_prep_vma], :1658-1659, after
      [vma_lookup] at :1931) and [old_len] running past the vma end
      (:1720-1721) are both excluded by [mremap_source_b], which demands
      the source be exactly one tracked mapping; VM_DONTEXPAND /
      VM_PFNMAP (:1736-1737) is never set on an anonymous mmap grant —
      their only setters are [remap_pfn_range_internal]
      (mm/memory.c:2953), [remap_vmalloc_range_partial]
      (mm/vmalloc.c:4615) and [__install_special_mapping]
      (mm/mmap.c:1440, flags at :1454-1455), and the anonymous leg of
      [do_mmap] reaches none of them: the driver hook sits behind
      [if (map->file)] at mm/vma.c:2520 ([__mmap_new_vma]), and the
      anonymous path is [vma_set_anonymous] at :2525.
    - EAGAIN: [mlock_future_ok] (:1739-1740) returns true immediately
      unless VM_LOCKED (mm/mmap.c:233-234), which can only arrive via
      MAP_LOCKED or [mlockall] (mm/mlock.c:747) — both outside the modeled
      surface, so no vma here is ever locked.

    Two errnos a real kernel CAN still return are deliberately outside the
    modeled surface, rather than silently absorbed:

    - EINTR from [mmap_write_lock_killable] ([do_mremap],
      mm/mremap.c:1924-1925) cannot be observed by any program.  That
      helper (include/linux/mmap_lock.h:325-332) is a thin wrapper around
      [down_write_killable] (kernel/locking/rwsem.c:1598-1610), whose wait
      state is TASK_KILLABLE (:1331, :1496), and
      [signal_pending_state] aborts a TASK_KILLABLE wait only on a FATAL
      signal (include/linux/sched/signal.h:408-416: TASK_KILLABLE lacks
      TASK_INTERRUPTIBLE, so the result is [__fatal_signal_pending]).  A
      fatal signal kills the task before it returns to userspace, so the
      -EINTR never reaches a register the program can read.  This is the
      same argument [Mprotect.mprotect_errnos] makes for its own killable lock.

    - EPERM for an mseal'd VMA ([vma_is_sealed] in [check_prep_vma],
      mm/mremap.c:1662-1663, testing VM_SEALED, include/linux/mm.h:447-448;
      v6.12's [can_modify_vma]) is unreachable because
      [mseal] (__NR_mseal, 462) is not in [syscall_spec]'s modeled surface
      (mm/mseal.c:71-78 is its only setter), so VM_SEALED is never set
      on a modeled run. -/
def mremap_errnos : List Int := [ENOMEM]

/-- Replace the one mapping based at [old] with [(dst,new_n)].  The source
    is required below to have no [vm_noaccess] overlap, while a moved
    destination is fresh, so the no-access ledger is preserved verbatim. -/
def mremap_maps_next (h : VmMaps) (old dst new_n : word) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved ((dst, new_n) :: map_remove h.vm_maps old)
    h.vm_noaccess h.vm_start_brk h.vm_brk h.vm_limit
    h.vm_mmap_base h.vm_init_sp

/-- A source is either uniformly lazy or wholly eager.  A MAP_FIXED inside
    it can split the backing provenance without splitting [vm_maps]; mremap
    fails closed on that mixed representation rather than guessing which
    provenance a grown tail inherits. -/
def mremap_backing_uniform_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n ||
  region_free (m_vm_lazy m) old old_n

/-- The source's sparse provenance: is it a LAZY (MAP_NORESERVE)
    reservation rather than an eagerly charged mapping? -/
def mremap_source_lazy_b (m : Model) (old old_n : word) : Bool :=
  map_contains (m_vm_lazy m) old old_n

/-- Update ownership and sparse-backing ledgers as one state transition.
    Materialized pages move with their source-relative offsets; a shrink
    releases pages beyond the new end, and a lazy grow extends the lazy range
    without eagerly charging its tail. -/
def mremap_model_next (m : Model) (old old_n dst new_n : word) : Model :=
  vm_resize_backing (mremap_source_lazy_b m old old_n) old old_n dst new_n
    (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m)

/-- The grown delta reads as fresh zeroes.  Neither [vma_merge_extend]
    ([expand_vma_in_place], mm/mremap.c:1470, Linux v6.18.46) on the
    in-place path nor [copy_vma] ([copy_vma_and_data], mm/mremap.c:1193)
    on the move path installs page tables for it, and a [pte_none] fault
    on a PRIVATE|ANONYMOUS VMA is served by [do_anonymous_page]
    (mm/memory.c:5149-5262) — a read from the shared zero page
    (mm/memory.c:5170-5172), a write from a zeroed folio
    ([alloc_anon_folio], mm/memory.c:5059, called at :5198).

    The [old_nZ < new_nZ] guard never fires false where this is used:
    [mremap_spec] answers the equal case before [mremap_inplace_effect] is
    built, and the shrink case takes that function's other branch, so both
    call sites have already established growth.  It is kept because the
    function is total in its arguments and its name promises the tail of a
    grow; no trace can distinguish dropping it. -/
def mremap_tail (base old_n : word) (old_nZ new_nZ : Int)
    : List (word × word) :=
  if old_nZ < new_nZ
  then [(base + old_n, BitVec.ofInt 64 (new_nZ - old_nZ))]
  else []

/-- Linux's [PAGE_ALIGN(len)] ([do_mremap], mm/mremap.c:1917-1918, Linux
    v6.18.46) expands to [(len + 4095) & ~4095] on an [unsigned long]
    (include/linux/mm.h:222 -> include/vdso/align.h:8 ->
    include/uapi/linux/const.h:48-49), which
    WRAPS.  It yields zero on exactly two kinds of input: [len = 0], and
    [len] in the top partial page [[2^64-4095, 2^64-1]].  (Not the whole
    top page: [2^64-4096] is already aligned and survives.)  Computing the
    round in [Z], that is [page_round_up_Z len = 0 \/ = 2^64], which is
    what this decides — so the two arms of Linux's [!new_len] test at
    mm/mremap.c:1771-1772 ([check_mremap_params]) need no separate
    treatment. -/
def page_align_is0_b (len : word) : Bool :=
  w_is0 len || decide (two_pow_64 ≤ page_round_up_Z (len.toNat : Int))

/-- The modeled source.  Linux needs only [vma_lookup(mm, addr)] to
    succeed (mm/mremap.c:1043, v6.12); requiring an EXACT tracked entry is
    stricter, hence fail closed, and it is what lets [mremap_model_next]
    carry [vm_noaccess] over untouched.  The [vm_reserved] and
    [vm_noaccess] conjuncts keep the image and PROT_NONE guards out: the
    model has no ledger shape for remapping either.

    Two of the four conjuncts pull their weight only jointly.
    [region_free (vm_reserved h) old old_n] is implied by
    [map_has (vm_maps h) old old_n] whenever the two ledgers are disjoint —
    which they are, but NOT because [region_free] gates every grant: a brk
    grow inside one page enters [vm_maps] with no address-space test at all
    ([Mmap.brk_grow_ok]'s [else true], and [Checks/VmMapsDisjoint] Part 1
    for a checked execution reaching it).  It holds for two separate
    reasons — [Mmap.mmap_spec] and [mremap_spec] place only where
    [region_free] accepts against [vm_reserved ++ vm_maps], and brk grants
    cannot reach the image because [Run.valid_brk] puts the break base at
    or above the page-rounded image top and the break never goes below
    [min_brk].  So no trace can distinguish dropping it; it is kept because
    the disjointness is an invariant of the other specs rather than
    something stated here.  The [alloc_top]
    bound is what [mremap_source_ret_not_errno] needs to know that a
    successful in-place return cannot be mistaken for an encoded errno. -/
def mremap_source_b (h : VmMaps) (old old_n : word)
    (old_nZ : Int) : Bool :=
  decide ((old.toNat : Int) + old_nZ ≤ alloc_top h) &&
  region_free h.vm_reserved old old_n &&
  map_has h.vm_maps old old_n &&
  region_free h.vm_noaccess old old_n

/-- The budget analogue of [may_expand_vm] (mm/mmap.c:1324-1346, Linux
    v6.18.46), which mremap reaches from [check_prep_vma] at
    mm/mremap.c:1742-1743 (v6.12's [vma_to_resize]) with
    [npages = delta >> PAGE_SHIFT] — i.e. Linux charges the
    NET DELTA, never a transient peak of both mappings.  The model checks the
    complete post-state instead: that is the same delta for eager mappings,
    while a MAP_NORESERVE tail remains lazy and costs nothing until touched.
    Since [check_prep_vma] runs from [do_mremap] at mm/mremap.c:1932, before
    [mremap_at] (:1937) picks the in-place or the move branch
    ([expand_vma], :1512), the same gate applies to both
    paths; the model does the same. -/
def mremap_final_budget_b (m : Model)
    (old old_n dst new_n : word) : Bool :=
  vm_backing_within_limit (mremap_model_next m old old_n dst new_n)

/-- Linux grows in place when [old_len == vma->vm_end - addr]
    (mm/mremap.c:1116, v6.12) and [vma_expandable] holds (:1120, defined at
    :966-978).  This is a coarser predicate in both directions — see
    [mremap_spec] for why the resulting over-admission is presented as an
    [alt] rather than a claim.

    Both halves of the [region_free] conjunct are LIVE.  The [vm_maps] half
    is the ordinary case; the [vm_reserved]
    half — an in-place grow running into the binary image — no trace reaches,
    because the only modeled way to choose an anonymous mapping's address is
    the PROT_NONE MAP_FIXED guard ([Mmap.mmap_fixed_noaccess_b]), which must land
    inside a mapping the process already owns, so no trace can put a tracked
    mapping below a LOAD segment.  It is not dead either:
    [Checks.Examples.mremap_inplace_grow_into_image_rejected] flips
    [mremap_inplace_grow_accepts] to [CheckReject] by adding one reserved
    entry and changing nothing else.

    The [alloc_top] conjunct is LIVE too, and it is the only thing
    keeping a grown mapping clear of the dynamic stack — the stack is in
    neither [vm_reserved] nor [vm_maps], so [region_free] cannot see it.
    No
    kernel places an ordinary anonymous mapping near this address for the
    in-place arm to grow from.  The pair
    [Checks.Examples.mremap_inplace_grow_past_ceiling_rejected] /
    [Checks.Examples.mremap_inplace_grow_to_ceiling_accepts] pins it, against
    [mremap_inplace_grow_to_ceiling_accepts] one page below: the pair
    differs only in the source's base address, so the flipped verdict is
    attributable to this conjunct alone. -/
def mremap_inplace_grow_b (m : Model) (old old_n new_n : word)
    (old_nZ new_nZ : Int) : Bool :=
  let h := m_vmmaps m
  decide ((old.toNat : Int) + new_nZ ≤ alloc_top h) &&
  region_free (h.vm_reserved ++ map_remove h.vm_maps old) old new_n &&
  mremap_final_budget_b m old old_n old new_n

/-- A moved destination, and the argument for what this guard says is
    mremap's own rather than a loan from [Mmap.mmap_spec].

    A MAYMOVE destination IS a preference-free placement: Linux picks it
    with [get_unmapped_area] at [addr = 0] and no MAP_FIXED
    ([vrm_set_new_addr], mm/mremap.c:957-960, Linux v6.18.46; some line
    citations in this file are against v6.12 instead).
    So the conditions that hold of one
    hold of the other — page-aligned, nonzero, below
    [State.alloc_top], disjoint from every recorded mapping — and
    the conditions that do NOT are the same conditions, for the same
    reason.  This guard carries no search-order conjunct, for the
    reason its mmap twin carries none: a highest-fit conjunct would be
    read on the model's ledger, and the ledger does not carry the
    kernel's own vdso/vvar VMAs, so a real move destination the kernel
    reached by descending past them would be one the model called impossible.
    Excluding a destination Linux produces costs the theorem, exactly as
    it does for a fresh grant.

    DISJOINTNESS DOES MORE WORK HERE than in an ordinary grant, and that
    is the mremap-specific half.  [dst] can never overlap the source:
    Linux picks it
    with [get_unmapped_area] in [vrm_set_new_addr] (mm/mremap.c:957-960,
    Linux v6.18.46), passing [addr = 0] and no
    MAP_FIXED, so the search runs over the maple tree while the source VMA
    is still live (it is not unmapped until [move_vma] reaches
    [unmap_source_vma], mm/mremap.c:1122).  The model gets the same
    exclusion for free, because
    [old] is still in [vm_maps h] when [region_free] is evaluated.

    [dst <> old] is therefore redundant against a well-formed ledger, and
    [check_mremap] never evaluates it (it dispatches on [r = old] first).
    It is load-bearing in the SPEC: without it the [choose] would let the
    move arm produce move-shaped effects at [old], which the checker would
    classify as the in-place arm and reject — i.e. completeness would fail.
    [mremap_fresh_neq_old] is what discharges that.

    [vm_noaccess] is deliberately ABSENT from the [region_free] list, and
    that is not an oversight this predicate gets away with.  [State.v]'s
    purpose (c) says protected ranges are ORDINARILY subranges of
    [vm_maps], which the [vm_maps] half already excludes.  It names ONE
    exception, and it is a real one: a brk shrink inside its final page
    drops the byte-granular tail from [vm_maps] while [Mmap.brk_unmaps]
    (page-rounded) removes nothing from [vm_noaccess], so a strict
    sub-page slice [[r, PAGE_ALIGN r)] is left protected and owned by no
    [vm_maps] entry.  [Checks.Examples.m_brk_same_page_shrunk] is a
    checked-in state in exactly that shape.

    No destination can reach such a slice, for a reason this predicate
    does check.  [dst] is page aligned, and the entry that owned the
    protected range is TRUNCATED to [[e0, r)], never removed — a nonempty
    orphan forces the protected base [a] to satisfy
    [a <= page_floor r < r], so [[page_floor r, r)] is still in
    [vm_maps].  A page-aligned [dst] overlapping the orphan needs
    [dst <= page_floor r] and [dst + new_n > r], which puts it across
    [[e0, r)], and [region_free] refuses it.  The pair
    [mremap_move_onto_brk_orphan_page_rejected] /
    [mremap_move_above_brk_orphan_accepts] in [Checks/Examples.v] pins
    that boundary: the two differ only in the destination, one page apart
    across the orphan's end.

    Note WHICH half of that does the work.
    [mremap_move_onto_orphan_without_residual_accepts] takes the residual
    entry out of the same state, and the move onto the orphan page is
    then ACCEPTED — so the property this predicate leans on is "the
    shrink TRUNCATES the owning entry rather than removing it", not the
    containment prose itself.  The orphan's presence in [vm_noaccess]
    contributes nothing here, because the predicate never reads it.  That
    state is unreachable, for the [a <= page_floor r < r] reason above;
    the example is checked in so the load-bearing property is visible
    rather than inferred.

    Adding [region_free (vm_noaccess h) dst new_n] here would be
    redundant on every reachable state by the argument above, and it
    would be a conjunct no example or test could ever flip — which is
    the opposite of how every other conjunct in this file is justified.
    The consumer half of that argument is mechanized:
    [mremap_fresh_avoids_noaccess] below derives the missing conjunct
    from [State.noaccess_pages_owned], the page-granular weakening of the
    containment that survives the brk-shrink exception.  The other half
    is mechanized too: [Checks/NoaccessOwned.lean] proves a stronger
    ledger invariant ([sys_inv]) true of [init_model] and kept by every
    modeled system call, and derives [noaccess_pages_owned] from it
    ([sys_inv_noaccess_pages_owned]). -/
def mremap_fresh_b (m : Model) (old_nZ new_nZ : Int)
    (old old_n dst new_n : word) : Bool :=
  let h := m_vmmaps m
  !(dst == old) &&
  decide ((dst.toNat : Int) % page_size = 0) &&
  decide (0 < (dst.toNat : Int)) &&
  decide ((dst.toNat : Int) + new_nZ ≤ alloc_top h) &&
  region_free (h.vm_reserved ++ h.vm_maps) dst new_n &&
  mremap_final_budget_b m old old_n dst new_n

/-- Half of the argument above, mechanized: GIVEN the ledger invariant
    [State.noaccess_pages_owned], a destination this predicate accepts is
    disjoint from [vm_noaccess] — exactly the conjunct the definition
    leaves out.  So the unproved part is one named hypothesis about
    the state rather than prose about a syscall.

    The proof is the page-granularity argument, with no appeal to the brk
    shrink's shape: [dst] is page aligned and [new_n] is a whole number of
    pages, so any protected byte the request touches drags its WHOLE page
    inside [[dst, dst+new_n)]; the invariant hands back a [vm_maps] entry
    meeting that page, and [region_free] against [vm_reserved ++ vm_maps]
    has already excluded every such entry.

    The two side conditions on [new_n] are what [mremap_spec] supplies at
    the call site: it passes [new_n = Z_to_bv 64 (page_round_up_Z
    (bv_unsigned new_size))] under [page_align_is0_b new_size = false],
    which is precisely "page-sized and nonzero".  Both are load-bearing
    rather than convenient — [iv_overlap] treats an empty interval on
    either side as overlapping anything that straddles it, so a zero-length
    request has no protected BYTE to reason about while [region_free] can
    still answer false.

    That [noaccess_pages_owned] holds of every reachable state is
    [Checks/NoaccessOwned.lean]'s: [init_model_sys_inv],
    [star_preserves_sys_inv] and [sys_inv_noaccess_pages_owned]. -/
theorem mremap_fresh_avoids_noaccess (m : Model) (old_nZ new_nZ : Int)
    (old old_n dst new_n : word)
    (Hown : noaccess_pages_owned (m_vmmaps m))
    (Hpos : 0 < (new_n.toNat : Int))
    (Hmod : (new_n.toNat : Int) % page_size = 0)
    (Hfresh : mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) :
    region_free (m_vmmaps m).vm_noaccess dst new_n = true := by
  -- the gate's conjuncts, in the order the definition states them
  have Hsplit := Hfresh
  unfold mremap_fresh_b at Hsplit
  dsimp only at Hsplit
  simp only [Bool.and_eq_true, decide_eq_true_eq] at Hsplit
  have Hrf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      dst new_n = true := Hsplit.1.2
  have Halign : (dst.toNat : Int) % page_size = 0 := Hsplit.1.1.1.1.2
  -- a page-aligned request ends on a page boundary
  have Hhi : ((dst.toNat : Int) + (new_n.toNat : Int)) % page_size = 0 := by
    rw [Int.add_emod, Halign, Hmod]
    decide
  refine region_free_intro _ _ _ ?_
  intro a n Hin
  obtain ⟨Hn, Hpage⟩ := Hown a n Hin
  cases hov : iv_overlap dst new_n a n with
  | false => rfl
  | true =>
      exfalso
      unfold iv_overlap at hov
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hov
      obtain ⟨hov1, hov2⟩ := hov
      -- the protected byte the request cannot serve: the top of the two bases
      have hx : (a.toNat : Int) ≤ max (dst.toNat : Int) (a.toNat : Int) ∧
          max (dst.toNat : Int) (a.toNat : Int) <
            (a.toNat : Int) + (n.toNat : Int) := by
        constructor <;> omega
      obtain ⟨b, s, Hinm, Hb1, Hb2⟩ := Hpage _ hx
      -- its whole page is inside the request, which is page aligned
      have hxmem : (dst.toNat : Int) ≤ max (dst.toNat : Int) (a.toNat : Int) ∧
          max (dst.toNat : Int) (a.toNat : Int) <
            (dst.toNat : Int) + (new_n.toNat : Int) := by
        constructor <;> omega
      obtain ⟨Hf1, Hf2⟩ :=
        page_round_down_Z_within (dst.toNat : Int)
          ((dst.toNat : Int) + (new_n.toNat : Int))
          (max (dst.toNat : Int) (a.toNat : Int)) Halign Hhi hxmem
      -- …so that entry of `vm_maps` overlaps the destination, which the
      -- gate already refused
      have hno := region_free_In _ _ _ b s Hrf (List.mem_append_right _ Hinm)
      have hyes : iv_overlap dst new_n b s = true := by
        simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> omega
      rw [hyes] at hno
      exact absurd hno (by simp)

/-- Staying at [old]: a shrink drops exactly the tail
    [[addr+new_len, addr+old_len)] — the range [do_vmi_munmap] is given at
    mm/mremap.c:1096, v6.12 — and a grow zero-fills exactly the delta. -/
def mremap_inplace_effect (old old_n new_n : word)
    (old_nZ new_nZ : Int) : SyscallEffect :=
  if new_nZ < old_nZ then
    SyscallEffect.mkEffectU old [] [] [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] [] []
  else mkEffect old [] (mremap_tail old old_n old_nZ new_nZ)

/-- A move relocates the whole source: [move_ptes] (mm/mremap.c:193-315,
    Linux v6.18.46) clears each source PTE with [get_and_clear_ptes]
    (:287) and installs it at the destination with [set_ptes] (:300), so
    the same physical pages appear at [dst]; untouched [pte_none] entries
    are skipped (:268-269) and refault as zeroes through
    [do_anonymous_page] (mm/memory.c:5149-5262) for a PRIVATE|ANONYMOUS
    VMA.  Hence the copy length
    is the WHOLE source, [old_n] — not [min old_n new_n].  A move only
    happens on growth ([mremap_spec] reaches [mremap_move_effect] only
    under [old_nZ < new_nZ], because Linux serves [old_len >= new_len] in
    place at mm/mremap.c:1088-1103), so the two agree and the [min] was
    dead generality.

    The source is then unmapped by [do_vmi_munmap] at mm/mremap.c:792,
    which is why the copy source is inside [eff_unmaps]: [Run.apply_copies]
    reads the PRE-EFFECT snapshot (Run.v:180), matching the kernel's order.
    The grown tail carries no page tables — neither [copy_vma] nor
    [vma_merge_extend] installs any for the delta — so it reads as fresh
    zeroes, which is [mremap_tail]. -/
def mremap_move_effect (old old_n dst : word) (old_nZ new_nZ : Int)
    : SyscallEffect :=
  SyscallEffect.mkEffectU dst [] (mremap_tail dst old_n old_nZ new_nZ) [(old, old_n)]
    [MemCopy.mkCopy old dst old_n] []

/-- The bounded [mremap(old,old_size,new_size,MREMAP_MAYMOVE)] shape used
    by musl realloc.  The source must be exactly one tracked readable/writable
    anonymous mapping.  Equal-size calls are no-ops; shrink removes/refunds
    the tail; grow may extend into a free adjacent range; and MAYMOVE permits
    a fresh disjoint placement that symbolically copies the preserved prefix,
    unmaps the old range, and zero-fills only a grown tail.

    ORDER, against [SYSCALL_DEFINE5(mremap)] (mm/mremap.c:1961-1994, Linux
    v6.18.46, whose body is [do_mremap], :1911-1952; the line numbers in
    this ORDER and RESULTS walk are v6.12's, when the whole walk sat in the
    syscall body, except where a citation names v6.18.46).  Which
    gate fires first is as much a part of the syscall as its result, so the
    branches below are in the kernel's order:

    - mm/mremap.c:1012, 1015, 1022 validate [flags] before any other
      argument is inspected.  One read does precede them — :1010,
      [addr = untagged_addr(addr)] — but on riscv64 it cannot change an
      answer: RISC-V pointer masking (Supm) postdates v6.12, so the arch
      defines no override and [untagged_addr] is the generic identity
      (include/linux/uaccess.h:25-26, v6.12).  A tagged [old] therefore
      keeps its tag through [offset_in_page] (:1027) and into [vma_lookup]
      (:1043), where arm64 would have stripped it at :1010, so Linux
      answers EFAULT for such an address while the model fails closed at
      [mremap_source_b] — the safe direction, and the reason the flag test
      really is the first gate that can decide the answer.  The model's
      narrower shape (exactly MREMAP_MAYMOVE) therefore fails closed
      first, ahead of the deterministic EINVAL below.  Linux answers a deterministic
      EINVAL for a flag word outside {FIXED, MAYMOVE, DONTUNMAP} (:1013) and
      serves [flags = 0] on exactly the same path as MAYMOVE (which nothing
      between :1080 and :1103 consults; its next read is :1165); modeling
      neither is a deliberate narrowing, not a fidelity claim.
    - mm/mremap.c:1027, [offset_in_page(addr)] -> EINVAL.
    - mm/mremap.c:1030-1031 round BOTH lengths with the wrapping
      [PAGE_ALIGN] (see [page_align_is0_b]) — before the
      [old_len == new_len] test at :1091, which is why a 4095-byte new size
      against a one-page source is an equal-size no-op and not a shrink —
      and then :1038 answers EINVAL when the rounded NEW length is zero.
      So a [new_size] in the top partial page is EINVAL, exactly like
      [new_size = 0]; the model says so rather than failing closed on the
      wrap.
    - a rounded OLD length of zero is the "duplicate a mapping" shape, which
      Linux refuses with EINVAL for a private mapping in [check_prep_vma]
      (mm/mremap.c:1690-1693, Linux v6.18.46; v6.12's [vma_to_resize] at
      :839-842) — but only after [vma_lookup] (:1043) and the
      seal check (:1050), and only on the growth path (:1108).  The model
      does not track enough to reproduce that EINVAL's preconditions, so it
      fails closed; it does so HERE, after the two EINVAL gates above, so
      that a misaligned address or a zero new size still gets Linux's answer.
      (An unmodeled answer need not precede a modeled one: being unmodeled
      says nothing about position, and Linux's position is :839, below both.
      [PAGE_ALIGN] at :1030 wraps a near-2^64 [old_size] to 0, so the wrap
      and the literal zero are the same case and share this gate.)
      The gate's two halves are NOT equally observable, and a trace pins
      neither, because both are
      fail-closed and any fail-closed route gives the same answer.  Delete the
      ZERO half and control reaches [mremap_source_b], whose
      [map_has] then needs a ledger entry of size exactly 0 — nothing a
      run can produce, but the [VmMaps] record carries no
      well-formedness predicate, so such a ledger is writable by hand.
      [Checks.Examples.mremap_zero_entry_passes_the_source_gate] /
      [mremap_old_size_zero_gate_precedes_the_source_gate] is that pair:
      the first shows the fall-through would ACCEPT, the second that the
      answer is [Unmodeled] anyway, so the flip is attributable to this
      gate alone.  Delete the WRAP half and there is no such state:
      [old_nZ = 2^64] fails [mremap_source_b]'s [alloc_top] conjunct
      for EVERY address and every ledger, so no trace and no hand-built
      state can tell the two spellings apart.  It is kept because the
      gate must answer for the argument Linux actually rounds, and the
      honest pin is the redundancy itself —
      [mremap_wrapping_old_size_cannot_pass_the_source_gate], a [forall]
      over both.
    - mm/mremap.c:1043 requires a VMA at [addr], and nothing more on the
      equal-size and shrink paths: they never call [vma_to_resize], so
      [old_len] is never compared against [vma->vm_end - addr] (:849).  An
      equal-size call therefore succeeds and returns [addr] even when
      [[addr, addr+old_len)] spans a hole, several VMAs, or runs off the end
      of the mapping — the only other requirement is that the VMA is
      unsealed (:1050).  The model instead demands an exact tracked entry,
      which is a much larger narrowing than "not an exact entry" reads as;
      it is the safe direction (fail closed).

    RESULTS.  For [old_len >= new_len] Linux never moves: nothing between
    mm/mremap.c:1080 and :1103 reads MREMAP_MAYMOVE (its next read is
    :1165, the one place the flag decides whether a mapping may move; the
    earlier reads at :1015 and :1023 only reject FIXED and DONTUNMAP
    combinations), and the :1088 block returns [addr] outright — at :1092
    for the equal case, at :1101 once [do_vmi_munmap] has dropped the tail
    at :1096.  The two use different exits: the equal case leaves through
    [goto out] (:1093), which unlocks mmap_lock on the way out, while the
    shrink leaves through [goto out_unlocked] (:1102), because
    [do_vmi_munmap] was passed [unlock = true] (:1097) and has already
    dropped the lock.  Growth is the only case that can move, and it
    reaches :1165 only after the in-place expansion guarded by
    [vma_expandable] at :1120 has failed to return [addr] at :1155.

    The equal-size arm carries NO injectable failure.  Walking
    mm/mremap.c:1041-1093 for [flags = MREMAP_MAYMOVE], a non-hugetlb VMA
    that exists and is unsealed, and [old_len = new_len], the only exits are
    EINTR (:1042), EFAULT (:1045), EPERM (:1051), the hugetlb EINVALs
    (:1062-1072) and [ret = addr] (:1092) — all four errnos excluded by the
    modeled shape (see [mremap_errnos]).  There is no allocation, no VMA
    split and no accounting on that branch, so ENOMEM is unreachable and the
    [alt] with [Syscall.errno_from] must not cover it.  The shrink arm is different:
    [do_vmi_munmap] (:1096) splits the VMA and can fail to allocate
    (mm/vma.c:384-405) or exceed [sysctl_max_map_count] (mm/vma.c:1197).

    The choice between growing in place and moving is a genuine [alt],
    because Linux's in-place test reads state the model's ledger does not
    have: [vma_expandable] (mm/mremap.c:1415-1427, Linux v6.18.46) consults
    the next VMA in the maple tree, plus [TASK_SIZE], [mmap_min_addr] and
    the LSM hook through [get_unmapped_area] under MAP_FIXED
    ([__get_unmapped_area], mm/mmap.c:824, 857, 862, and
    [generic_get_unmapped_area], :697, or its topdown twin, :747);
    and :1116 requires [old_len == vma->vm_end - addr], which a kernel-side
    VMA merge can defeat.  Any of those can send Linux to the move path
    where the model sees free space, so the model admits both.  That
    argument does NOT apply to the equal-size and shrink arms — they never
    reach [vma_expandable] — which is why those two are deterministic.

    An injected ENOMEM leaves no memory effects: [move_vma] moves the page
    tables back (mm/mremap.c:730-737), swaps its bookkeeping (:738-741) and
    unmaps the NEW area at :792, i.e. it rolls back.  The argument is
    specific to MAYMOVE: under MREMAP_FIXED the destination is destroyed at
    :918 before the source is validated at :930, so THAT errno does have
    memory effects.  FIXED is unmodeled.

    BOUNDED APPROXIMATION, and it is on the SUCCESS path, not only the
    failure one.  The unmap at mm/mremap.c:792 is the same call site for
    both, and when it fails its error is SWALLOWED (:793-797, "OOM: unable
    to split vma, just get accounts right"): [move_vma] carries on and
    returns [new_addr] at :817.  So a successful Linux mremap can leave the
    source range still mapped, at an address the program knows.  The model
    always emits [eff_unmaps [(old, old_n)]] and always drops [old] from the
    ledger, so it says that range is gone when a doubly-unlucky kernel would
    still serve its bytes.

    What makes it reachable is the same thing named for the shrink path in
    [mremap_errnos]: Linux only requires [old_len <= vma->vm_end - addr]
    (mm/mremap.c:849), so the model's exact ledger entry can be a strict
    prefix of a merged kernel VMA; [do_vmi_munmap] then has to split, and a
    split can fail on allocation (mm/vma.c:384, 394, 399, 403) or on
    [sysctl_max_map_count] (mm/vma.c:1197).  The model has no shape for
    "mapped at both addresses" and does not attempt one.  The cost is a
    fidelity gap in the modeled semantics, not a checker unsoundness: what
    the model's ledger claims is FREE stays a superset of what is really
    free, so no real placement is ever refused because of it.  That is the
    claim [Checks.Examples.mremap_move_gap_is_the_retained_source]
    proves, together with the bound — the two free sets differ only over the
    retained source.

    The fifth syscall argument is ignored, and the reason is not that only
    MREMAP_FIXED reads it.  Linux reads [new_addr] in three places:
    mm/mremap.c:1064 unconditionally inside the hugetlb block, and
    mm/mremap.c:1075 for FIXED *or* DONTUNMAP (both routed into
    [mremap_to]).  Under this shape the hugetlb block is unreachable (the
    source is one tracked PRIVATE|ANONYMOUS mapping) and both flags are
    unmodeled, so the only remaining use is :1170, where
    [get_unmapped_area] OVERWRITES [new_addr] before it is read.

    Size rounding is done in [Z] and checked before conversion back to
    [word].  Protected/mixed/non-exact sources, FIXED, DONTUNMAP, and every
    other flag combination fail closed. -/
def mremap_spec (old old_size new_size flags : word)
    : SysSpec SyscallEffect :=
  -- This gate declines TWO different kernel answers, and only one of them
  -- is a refusal.  Linux rejects a flag word outside
  -- {FIXED, MAYMOVE, DONTUNMAP} with a deterministic EINVAL
  -- (mm/mremap.c:1012-1024), but it ACCEPTS [flags = 0]: nothing between
  -- :1088 and :1103 reads MREMAP_MAYMOVE, so equal-size, shrink and
  -- in-place grow all succeed exactly as they do under MAYMOVE, and the
  -- flag first matters at :1165, where a call that must MOVE gets the
  -- -ENOMEM parked at :1164.  Declining [flags = 0] is therefore a
  -- deliberate narrowing of the modeled surface -- announced here and in
  -- the ORDER note above -- not a claim that Linux fails.  It is the safe
  -- direction: [unmodeled] never asserts a wrong result.
  if !((flags.toNat : Int) == MREMAP_MAYMOVE)
  then unmodeled
  else if !(((old.toNat : Int) % page_size) == 0)
  then err_ret EINVAL                              -- mm/mremap.c:1027
  else if page_align_is0_b new_size
  then err_ret EINVAL                              -- mm/mremap.c:1031, 1038
  else if (TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)
  then err_ret EINVAL
    -- `check_mremap_params` (mm/mremap.c:1775-1776, Linux v6.18.46): a
    -- page-aligned new length over TASK_SIZE is -EINVAL before any VMA
    -- is looked up.  Without this gate a grow past TASK_SIZE fell through
    -- to the arm's injected -ENOMEM, an answer Linux never gives for it.
  else if page_align_is0_b old_size
  then unmodeled                                   -- clone: mm/mremap.c:839
  else
    bind getModel fun m =>
      let h := m_vmmaps m
      let old_nZ := page_round_up_Z (old_size.toNat : Int)
      let new_nZ := page_round_up_Z (new_size.toNat : Int)
      let old_n := BitVec.ofInt 64 old_nZ
      let new_n := BitVec.ofInt 64 new_nZ
      if !(mremap_source_b h old old_n old_nZ &&
           mremap_backing_uniform_b m old old_n)
      then unmodeled                               -- mm/mremap.c:1043
      else if old_nZ == new_nZ
      then ret_only old                            -- mm/mremap.c:1091-1093
      else
        alt
          (bind (errno_from mremap_errnos) fun e => err_ret e)
          (if new_nZ < old_nZ then
             bind (modify fun _ => mremap_model_next m old old_n old new_n)
               fun _ => pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ)
           else
             let move :=
               bind (choose fun dst =>
                   mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true)
                 fun dst =>
                 bind (modify fun _ => mremap_model_next m old old_n dst new_n)
                   fun _ => pure (mremap_move_effect old old_n dst old_nZ new_nZ)
             if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
             then
               alt
                 (bind (modify fun _ => mremap_model_next m old old_n old new_n)
                   fun _ =>
                     pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
                 move
             else move)


/- =========================================================================
   THE BUDGET MARK for mremap (see [Mmap.brk_budget_refused_b] for what
   a mark is)
   ========================================================================= -/

/-- THE MOVE'S CHARGE, WITH THE DESTINATION FACTORED OUT.

    A grow's budget gate is [mremap_final_budget_b] on the complete
    post-state, and the moved resolution's post-state depends on the
    destination [dst] the [choose] picks — which the mark, reading only
    the request and the state, does not have.  It does not need it.  At
    a destination that is FRESH — disjoint from every live mapping and
    carrying no protected bytes, no lazy reservation and no materialized
    page — the re-created mapping is charged in full when the source is
    eager and not at all when it is lazy (its materialized pages move
    with it and are charged by count), and nothing else in the
    post-state mentions [dst]: [mremap_maps_next] drops [old] and conses
    the destination, [State.vm_resize_backing] cuts the source's own
    reservation and pages out of the two backing ledgers and re-records
    the moved pages at destination-relative offsets, whose COUNT is what
    [State.vm_backing_used] reads.  So the charge is one number for every
    fresh destination, and this is that number, written out of the same
    pieces [vm_resize_backing] assembles: what is left of the ledger once
    [old] is gone, the re-created mapping's own charge, and the page
    count.  [mremap_move_charge_at_fresh] proves it equal to the gate's
    reading at any destination of that shape; [mremap_fresh_b] supplies
    the live-mapping half of "fresh" and [State.noaccess_pages_owned]
    (through [mremap_fresh_avoids_noaccess]) the protected half; the
    lazy and materialized halves are the ledger invariant the writers of
    [vm_lazy] keep — every reservation lies under a live mapping — which
    is not yet a proved invariant and is taken as a hypothesis where
    the lemma is used. -/
def mremap_move_charge (m : Model) (old old_n new_n : word) : Int :=
  let h := m_vmmaps m
  let old_lo := (old.toNat : Int)
  let old_hi := old_lo + (old_n.toNat : Int)
  let source_lazy := mremap_source_lazy_b m old old_n
  let kept_lazy := maps_subtract (m_vm_lazy m) old_lo old_hi
  let kept_pages :=
    List.filter (page_outside_range old_lo old_hi) (m_vm_materialized m)
  let moved_pages :=
    if source_lazy then
      List.filter
        (fun p => page_in_half_open old_lo old_hi p &&
                  decide ((p.toNat : Int) - old_lo < (new_n.toNat : Int)))
        (m_vm_materialized m)
    else []
  live_bytes
     (maps_subtract_all
        (maps_subtract_all (map_remove h.vm_maps old) h.vm_noaccess)
        kept_lazy)
   + (if source_lazy then 0 else (new_n.toNat : Int))
   + ((moved_pages.length + kept_pages.length : Nat) : Int) * page_size

/-- The move's budget gate, destination-free: the same comparison
    [State.vm_backing_within_limit] makes, on the charge above. -/
def mremap_move_budget_b (m : Model) (old old_n new_n : word) : Bool :=
  decide (mremap_move_charge m old old_n new_n ≤ (m_vmmaps m).vm_limit)

/-- Only a GROW charges, and a grow has two non-errno resolutions, each
    behind its own reading of [mremap_final_budget_b]: in place, on the
    mapping grown at [old], admitted when [mremap_inplace_grow_b] holds
    (room above the source AND its budget gate passing); and moved, on
    the mapping re-created at a fresh [dst], whose gate reads the same
    charge at every fresh destination, [mremap_move_budget_b].

    THE MARK FIRES WHEN NO PLACEMENT FITS THE BUDGET: the in-place
    resolution is not admitted AND the move's budget gate refuses.  That
    is the request Linux refuses for want of memory: where the in-place
    resolution is unavailable and a move fits, Linux moves the mapping
    ([expand_vma], mm/mremap.c:1520-1543, Linux v6.18.46, which picks
    the new address in [vrm_set_new_addr], :957-960) and the call
    succeeds.  Neither gate alone is the right test, because neither
    post-state is charged at least as much as the other on every state:

    - the in-place post-state can be charged MORE.  The grown tail may
      lie over a lazy neighbour; the in-place evaluation clears that
      neighbour's reservation under the tail and charges its bytes
      eagerly, where a move leaves the neighbour alone.  On such a state
      the in-place gate refuses while a move fits, and the mark is
      silent (`Checks.BudgetPremise.ov_mark_silent_while_a_move_fits`
      over the `ov_model` fixture, with `ov_charges` and
      `ov_pre_state_within_budget` beside it so the state is
      reachable-and-in-budget rather than merely inhabited);
    - the in-place post-state can be charged LESS.  The charge is
      [State.live_bytes] of [State.vm_backed_maps], which subtracts
      [vm_noaccess] — NOT of [vm_maps].  A PROT_NONE mapping directly
      above the source leaves the grown tail's bytes uncharged in place,
      while a move re-creates the whole mapping at a fresh destination
      and is charged every byte of it.  In-place growth is unavailable
      there (the tail meets a live mapping), so the move is the only
      non-errno resolution, it is budget-refused, and the mark fires
      although the in-place gate alone passes
      (`Checks.BudgetPremise.un_mark_fires_on_the_move_refusal` over the
      `un_model` fixture, with `un_charges` and
      `un_inplace_gate_passes`).

    The mark stays placement-independent: it reads neither which
    resolution the [alt] takes nor the destination the [choose] picks,
    only whether in-place growth is admitted and the destination-free
    charge of a move.  It does not ask whether a fresh destination
    EXISTS: an address space with no free range is a refusal of its own
    kind, not of the budget, and is not marked unless the move's charge
    is also over the budget.  That is the same direction of
    approximation the in-place gate alone has — an in-place grow past
    [State.alloc_top] or into the image is not marked either.

    An earlier version fired when EITHER gate refused, and so over-marked
    the first case above: an execution Linux completes by moving counted
    as budget-refused, and [Run.source_within_budget] dropped the input.
    The present mark implies that one and not conversely
    (`Checks.BudgetPremise.mremap_budget_refused_implies_two_gate` and
    `.ov_two_gate_fires_where_the_mark_is_silent`; the earlier mark is
    kept in that module as `mremap_budget_refused_two_gate_b`, and
    nowhere else).

    `Checks.BudgetPremise` PINS the rule:
    `.mremap_budget_refused_iff` (the mark, on a grow past the argument
    gates, is exactly "not admitted in place and the move's gate
    refuses"); `.mremap_budget_refused_inv` (what a fired mark says);
    `.mremap_budget_refused_refuses_inplace` (where the mark fires, the
    in-place resolution is not admitted — no ledger hypothesis, because
    the mark reads the in-place admission directly) and
    `.mremap_budget_refused_refuses_move` (where the mark fires, no
    fresh destination that carries no backing metadata is admitted) —
    together, a marked request has no non-errno resolution on a state
    keeping the ledger invariants;
    `.mremap_budget_refused_fires_on_move_refusal` (in-place unavailable
    and the move refused at one fresh destination that carries no
    backing metadata fires the mark); and the concrete states above.
    Shrinks, the equal-size answer, and every shape the arm declines or
    answers -EINVAL are not budget refusals.

    **THE MODULE IS PORTED.**  `Checks.BudgetPremise` carries every
    declaration named above, so each pin above exists in this tree at
    the same name; what is left HERE is the definition of
    [mremap_budget_refused_b] and the argument.  The four ledger
    hypotheses `mremap_budget_refused_refuses_move` takes — no live
    mapping above the source, nothing protected under the destination,
    and the lazy and materialized ledgers unchanged by the move — are
    invariants of reachable states that are not yet DERIVED from one, so
    the hedge sits on those four and not on the lemma: where a consumer
    relies on the mark's reading through [Run.source_within_budget] it
    has to supply them. -/
def mremap_budget_refused_b (old old_size new_size flags : word)
    (m : Model) : Bool :=
  if !((flags.toNat : Int) == MREMAP_MAYMOVE) then false
  else if !(((old.toNat : Int) % page_size) == 0) then false
  else if page_align_is0_b new_size then false
  else if (TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int) then false
  else if page_align_is0_b old_size then false
  else
    let h := m_vmmaps m
    let old_nZ := page_round_up_Z (old_size.toNat : Int)
    let new_nZ := page_round_up_Z (new_size.toNat : Int)
    let old_n := BitVec.ofInt 64 old_nZ
    let new_n := BitVec.ofInt 64 new_nZ
    if !(mremap_source_b h old old_n old_nZ &&
         mremap_backing_uniform_b m old old_n)
    then false
    else if new_nZ ≤ old_nZ then false
    else !(mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ ||
           mremap_move_budget_b m old old_n new_n)

/- -------------------------------------------------------------------------
   Destination independence of the move's charge
   ------------------------------------------------------------------------- -/

/-- The list arithmetic behind [mremap_move_charge_at_fresh].  Every
    lemma here is about [State.maps_subtract] and its iteration
    [State.maps_subtract_all], read as a byte count through
    [State.live_bytes]; none of them is specific to mremap, and none is
    stated elsewhere, so they live beside their one consumer. -/
theorem mremap_word_range (w : word) :
    0 ≤ (w.toNat : Int) ∧ (w.toNat : Int) < two_pow_64 :=
  bv_unsigned_range_u64 w

/-- The `Z_to_bv 64` / `bv_unsigned` round trip, at the width the ledger
    arithmetic uses.  (`bv_unsigned_Z_to_bv_u64`;
    `StateVm` states the same fact, and this names it as the lemma below
    does.) -/
theorem mremap_u64 (z : Int) (hz : 0 ≤ z ∧ z < two_pow_64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  bv_unsigned_Z_to_bv_u64 z hz

theorem live_bytes_app (l1 l2 : List (word × word)) :
    live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2 := by
  induction l1 with
  | nil => simp [live_bytes]
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [List.cons_append, live_bytes]
      rw [ih]
      omega

theorem live_bytes_nonneg (l : List (word × word)) :
    0 ≤ live_bytes l := by
  induction l with
  | nil => simp [live_bytes]
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [live_bytes]
      have := mremap_word_range sz
      omega

theorem maps_subtract_app (l1 l2 : List (word × word)) (lo hi : Int) :
    maps_subtract (l1 ++ l2) lo hi
      = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi := by
  induction l1 with
  | nil => simp [maps_subtract]
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [List.cons_append, maps_subtract, ih, List.append_assoc]

theorem maps_subtract_all_app (cuts l1 l2 : List (word × word)) :
    maps_subtract_all (l1 ++ l2) cuts
      = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts := by
  revert l1 l2
  induction cuts with
  | nil => intro l1 l2; simp [maps_subtract_all]
  | cons hd rest ih =>
      intro l1 l2
      obtain ⟨a, n⟩ := hd
      simp only [maps_subtract_all]
      rw [maps_subtract_app, ih]


/-- A cut that misses an entry leaves it exactly as it was.  The entry
    must be nonempty: [iv_subtract] drops an empty entry sitting at the
    cut's base, and an empty entry is not something the two [region_free]
    readings agree about either. -/
theorem iv_subtract_disjoint (a sz : word) (lo hi : Int)
    (Hpos : 0 < (sz.toNat : Int)) (Hlohi : lo ≤ hi)
    (Hdisj : (a.toNat : Int) + (sz.toNat : Int) ≤ lo ∨ hi ≤ (a.toNat : Int)) :
    iv_subtract a sz lo hi = [(a, sz)] := by
  unfold iv_subtract
  dsimp only
  by_cases h1 : (a.toNat : Int) < lo
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h1, ite_eq_left h2]
      exfalso; omega
    · rw [ite_eq_left h1, ite_eq_right h2, List.append_nil]
      have hmin : min (sz.toNat : Int) (lo - (a.toNat : Int)) = (sz.toNat : Int) := by
        omega
      rw [hmin]
      simp
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_right h1, ite_eq_left h2, List.nil_append]
      have hmax : max (a.toNat : Int) hi = (a.toNat : Int) := by omega
      have hsub : (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi
          = (sz.toNat : Int) := by omega
      rw [hsub, hmax]
      simp
    · rw [ite_eq_right h1, ite_eq_right h2]
      exfalso; omega

/-- ...so a nonempty entry that is [region_free] of a cut list survives
    the whole list. -/
theorem maps_subtract_all_disjoint_entry (cuts : List (word × word))
    (a sz : word)
    (Hpos : 0 < (sz.toNat : Int))
    (Hfree : region_free cuts a sz = true) :
    maps_subtract_all [(a, sz)] cuts = [(a, sz)] := by
  induction cuts with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨lo, n⟩ := hd
      unfold region_free at Hfree
      rw [Bool.and_eq_true] at Hfree
      obtain ⟨Hov, Hfree'⟩ := Hfree
      have hno : ¬ ((a.toNat : Int) < (lo.toNat : Int) + (n.toNat : Int) ∧
          (lo.toNat : Int) < (a.toNat : Int) + (sz.toNat : Int)) := by
        intro h
        have : iv_overlap a sz lo n = true := by
          simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
          exact h
        rw [this] at Hov
        exact absurd Hov (by simp)
      have hdisj : (a.toNat : Int) + (sz.toNat : Int) ≤ (lo.toNat : Int) ∨
          ((lo.toNat : Int) + (n.toNat : Int)) ≤ (a.toNat : Int) := by omega
      simp only [maps_subtract_all]
      rw [show maps_subtract [(a, sz)] (lo.toNat : Int)
            ((lo.toNat : Int) + (n.toNat : Int))
          = iv_subtract a sz (lo.toNat : Int) ((lo.toNat : Int) + (n.toNat : Int))
            ++ maps_subtract [] (lo.toNat : Int) ((lo.toNat : Int) + (n.toNat : Int))
          from rfl]
      rw [iv_subtract_disjoint a sz (lo.toNat : Int)
        ((lo.toNat : Int) + (n.toNat : Int)) Hpos (by omega) hdisj]
      simp only [maps_subtract, List.append_nil]
      exact ih Hfree'

/-- Cuts only remove bytes. -/
theorem live_bytes_iv_subtract_le (a sz : word) (lo hi : Int)
    (Hlohi : lo ≤ hi) :
    live_bytes (iv_subtract a sz lo hi) ≤ (sz.toNat : Int) := by
  have ha := mremap_word_range a
  have hsz := mremap_word_range sz
  unfold iv_subtract
  dsimp only
  by_cases h1 : (a.toNat : Int) < lo
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h1, ite_eq_left h2]
      simp only [List.singleton_append, live_bytes]
      rw [mremap_u64 _ (by omega), mremap_u64 _ (by omega)]
      omega
    · rw [ite_eq_left h1, ite_eq_right h2, List.append_nil]
      simp only [live_bytes]
      rw [mremap_u64 _ (by omega)]
      omega
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_right h1, ite_eq_left h2, List.nil_append]
      simp only [live_bytes]
      rw [mremap_u64 _ (by omega)]
      omega
    · rw [ite_eq_right h1, ite_eq_right h2, List.nil_append]
      simp only [live_bytes]
      omega

theorem live_bytes_maps_subtract_le (l : List (word × word)) (lo hi : Int)
    (Hlohi : lo ≤ hi) :
    live_bytes (maps_subtract l lo hi) ≤ live_bytes l := by
  induction l with
  | nil => simp [maps_subtract, live_bytes]
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [maps_subtract, live_bytes]
      rw [live_bytes_app]
      have h1 := live_bytes_iv_subtract_le a sz lo hi Hlohi
      have h2 := ih
      omega

theorem live_bytes_maps_subtract_all_le (cuts l : List (word × word)) :
    live_bytes (maps_subtract_all l cuts) ≤ live_bytes l := by
  revert l
  induction cuts with
  | nil => intro l; simp [maps_subtract_all]
  | cons hd rest ih =>
      intro l
      obtain ⟨a, n⟩ := hd
      simp only [maps_subtract_all]
      have hn := mremap_word_range n
      have h1 := live_bytes_maps_subtract_le l (a.toNat : Int)
        ((a.toNat : Int) + (n.toNat : Int)) (by omega)
      have h2 := ih (maps_subtract l (a.toNat : Int)
        ((a.toNat : Int) + (n.toNat : Int)))
      omega


/-- A cut that misses every entry of a ledger changes no byte count,
    whatever cuts follow it.  Stated on the count rather than the list
    because an EMPTY entry at the cut's base is dropped by [iv_subtract]
    and kept by the identity — a difference no byte count can see. -/
theorem live_bytes_subtract_free (cuts l : List (word × word)) (lo hi : Int)
    (Hlohi : lo ≤ hi)
    (Hfree : ∀ (b s : word), (b, s) ∈ l →
      (b.toNat : Int) + (s.toNat : Int) ≤ lo ∨ hi ≤ (b.toNat : Int)) :
    live_bytes (maps_subtract_all (maps_subtract l lo hi) cuts)
      = live_bytes (maps_subtract_all l cuts) := by
  revert lo hi
  induction l with
  | nil => intro lo hi _ _; rfl
  | cons hd r ih =>
      intro lo hi Hlohi Hfree
      obtain ⟨a, sz⟩ := hd
      have hL : live_bytes
          (maps_subtract_all (maps_subtract ((a, sz) :: r) lo hi) cuts)
          = live_bytes (maps_subtract_all (iv_subtract a sz lo hi) cuts)
            + live_bytes (maps_subtract_all (maps_subtract r lo hi) cuts) := by
        rw [show maps_subtract ((a, sz) :: r) lo hi
              = iv_subtract a sz lo hi ++ maps_subtract r lo hi from rfl]
        rw [maps_subtract_all_app, live_bytes_app]
      have hR : live_bytes (maps_subtract_all ((a, sz) :: r) cuts)
          = live_bytes (maps_subtract_all [(a, sz)] cuts)
            + live_bytes (maps_subtract_all r cuts) := by
        rw [show ((a, sz) :: r) = [(a, sz)] ++ r from rfl]
        rw [maps_subtract_all_app, live_bytes_app]
      rw [hL, hR, ih lo hi Hlohi (fun b s h => Hfree b s (by simp [h]))]
      by_cases hz : (sz.toNat : Int) = 0
      · -- an empty entry is weightless on both sides
        have h1 : live_bytes (maps_subtract_all (iv_subtract a sz lo hi) cuts) = 0 := by
          have hle := live_bytes_maps_subtract_all_le cuts (iv_subtract a sz lo hi)
          have hle2 := live_bytes_iv_subtract_le a sz lo hi Hlohi
          have hge := live_bytes_nonneg (maps_subtract_all (iv_subtract a sz lo hi) cuts)
          omega
        have h2 : live_bytes (maps_subtract_all [(a, sz)] cuts) = 0 := by
          have hle := live_bytes_maps_subtract_all_le cuts [(a, sz)]
          have hlv : live_bytes [(a, sz)] = (sz.toNat : Int) := by simp [live_bytes]
          have hge := live_bytes_nonneg (maps_subtract_all [(a, sz)] cuts)
          omega
        omega
      · have hpos : 0 < (sz.toNat : Int) := by
          have := mremap_word_range sz
          omega
        have hdisj := Hfree a sz (by simp)
        rw [iv_subtract_disjoint a sz lo hi hpos Hlohi hdisj]

/-- Each remnant of a cut lies inside the entry it came from, provided
    the entry lies inside the address space (a right remnant's base is
    re-wrapped through [Z_to_bv]). -/
theorem iv_subtract_within (a sz : word) (lo hi : Int) (b s : word)
    (Hfit : (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hin : (b, s) ∈ iv_subtract a sz lo hi) :
    (a.toNat : Int) ≤ (b.toNat : Int) ∧
    (b.toNat : Int) + (s.toNat : Int) ≤ (a.toNat : Int) + (sz.toNat : Int) := by
  have ha := mremap_word_range a
  have hsz := mremap_word_range sz
  unfold iv_subtract at Hin
  dsimp only at Hin
  by_cases h1 : (a.toNat : Int) < lo
  · rw [ite_eq_left h1] at Hin
    by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2] at Hin
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at Hin
      rcases Hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · constructor
        · omega
        · rw [mremap_u64 _ (by omega)]
          omega
      · constructor
        · rw [mremap_u64 _ (by omega)]
          omega
        · rw [mremap_u64 _ (by omega), mremap_u64 _ (by omega)]
          omega
    · rw [ite_eq_right h2] at Hin
      simp only [List.append_nil, List.mem_singleton, Prod.mk.injEq] at Hin
      obtain ⟨rfl, rfl⟩ := Hin
      constructor
      · omega
      · rw [mremap_u64 _ (by omega)]
        omega
  · rw [ite_eq_right h1] at Hin
    by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2] at Hin
      simp only [List.nil_append, List.mem_singleton, Prod.mk.injEq] at Hin
      obtain ⟨rfl, rfl⟩ := Hin
      constructor
      · rw [mremap_u64 _ (by omega)]
        omega
      · rw [mremap_u64 _ (by omega), mremap_u64 _ (by omega)]
        omega
    · rw [ite_eq_right h2] at Hin
      simp at Hin

theorem maps_subtract_In (l : List (word × word)) (lo hi : Int) (b s : word)
    (Hin : (b, s) ∈ maps_subtract l lo hi) :
    ∃ (a sz : word), (a, sz) ∈ l ∧ (b, s) ∈ iv_subtract a sz lo hi := by
  induction l with
  | nil => simp [maps_subtract] at Hin
  | cons hd r ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [maps_subtract, List.mem_append] at Hin
      rcases Hin with h | h
      · exact ⟨a, sz, by simp, h⟩
      · obtain ⟨a', sz', hin', hiv⟩ := ih h
        exact ⟨a', sz', by simp [hin'], hiv⟩

theorem maps_subtract_all_within (cuts l : List (word × word)) (b s : word)
    (Hfit : ∀ (a sz : word), (a, sz) ∈ l →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hin : (b, s) ∈ maps_subtract_all l cuts) :
    ∃ (a sz : word),
      (a, sz) ∈ l ∧
      ((a.toNat : Int) ≤ (b.toNat : Int) ∧
       (b.toNat : Int) + (s.toNat : Int) ≤ (a.toNat : Int) + (sz.toNat : Int)) := by
  revert l
  induction cuts with
  | nil =>
      intro l Hfit Hin
      exact ⟨b, s, Hin, by omega⟩
  | cons hd rest ih =>
      intro l Hfit Hin
      obtain ⟨c, n⟩ := hd
      simp only [maps_subtract_all] at Hin
      have Hfit' : ∀ (a sz : word),
          (a, sz) ∈ maps_subtract l (c.toNat : Int) ((c.toNat : Int) + (n.toNat : Int)) →
          (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64 := by
        intro a sz Hin'
        obtain ⟨a0, sz0, Hin0, Hiv⟩ := maps_subtract_In _ _ _ _ _ Hin'
        have h0 := Hfit a0 sz0 Hin0
        have hw := iv_subtract_within a0 sz0 (c.toNat : Int)
          ((c.toNat : Int) + (n.toNat : Int)) a sz h0 Hiv
        omega
      obtain ⟨a', sz', Hin', Hw'⟩ :=
        ih (maps_subtract l (c.toNat : Int) ((c.toNat : Int) + (n.toNat : Int)))
          Hfit' Hin
      obtain ⟨a0, sz0, Hin0, Hiv⟩ := maps_subtract_In _ _ _ _ _ Hin'
      have h0 := Hfit a0 sz0 Hin0
      have hw := iv_subtract_within a0 sz0 (c.toNat : Int)
        ((c.toNat : Int) + (n.toNat : Int)) a' sz' h0 Hiv
      exact ⟨a0, sz0, Hin0, by omega⟩

/-- The remnants of a cut miss the cut: what [iv_subtract] keeps is the
    part of the entry BELOW the cut's base and the part AT OR ABOVE its
    end.  The end must be an address, since the right remnant's base is
    re-wrapped through [Z_to_bv]. -/
theorem iv_subtract_misses_cut (c sz : word) (lo hi : Int) (b s : word)
    (Hlo : 0 ≤ lo) (Hhi : hi < two_pow_64)
    (Hin : (b, s) ∈ iv_subtract c sz lo hi) :
    (b.toNat : Int) + (s.toNat : Int) ≤ lo ∨ hi ≤ (b.toNat : Int) := by
  have hc := mremap_word_range c
  have hsz := mremap_word_range sz
  unfold iv_subtract at Hin
  dsimp only at Hin
  by_cases h1 : (c.toNat : Int) < lo
  · rw [ite_eq_left h1] at Hin
    by_cases h2 : hi < (c.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2] at Hin
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at Hin
      rcases Hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        rw [mremap_u64 _ (by omega)]
        omega
      · right
        rw [mremap_u64 _ (by omega)]
        omega
    · rw [ite_eq_right h2] at Hin
      simp only [List.append_nil, List.mem_singleton, Prod.mk.injEq] at Hin
      obtain ⟨rfl, rfl⟩ := Hin
      left
      rw [mremap_u64 _ (by omega)]
      omega
  · rw [ite_eq_right h1] at Hin
    by_cases h2 : hi < (c.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2] at Hin
      simp only [List.nil_append, List.mem_singleton, Prod.mk.injEq] at Hin
      obtain ⟨rfl, rfl⟩ := Hin
      right
      rw [mremap_u64 _ (by omega)]
      omega
    · rw [ite_eq_right h2] at Hin
      simp at Hin

theorem maps_subtract_misses_cut (l : List (word × word)) (lo hi : Int) (b s : word)
    (Hlo : 0 ≤ lo) (Hhi : hi < two_pow_64)
    (Hin : (b, s) ∈ maps_subtract l lo hi) :
    (b.toNat : Int) + (s.toNat : Int) ≤ lo ∨ hi ≤ (b.toNat : Int) := by
  obtain ⟨a, sz, _, Hiv⟩ := maps_subtract_In l lo hi b s Hin
  exact iv_subtract_misses_cut a sz lo hi b s Hlo Hhi Hiv

/-- Cutting an entry out of itself leaves nothing, and nothing stays
    nothing under further cuts. -/
theorem iv_subtract_self (a n : word) :
    iv_subtract a n (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) = [] := by
  unfold iv_subtract
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

theorem maps_subtract_all_nil (cuts : List (word × word)) :
    maps_subtract_all [] cuts = [] := by
  induction cuts with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨a, n⟩ := hd
      simp only [maps_subtract_all]
      exact ih


/- Two page-rounding facts the `lazy_interior` lemma needs and `State` does
   not state: an already page-aligned bound survives the round.  They are
   the `Z.div_exact` half of the [lazy_interior_aligned] proof,
   named once instead of inlined twice. -/

/-- A page-aligned value's round-up is itself. -/
private theorem page_round_up_Z_aligned (x : Int) (h : x % page_size = 0) :
    page_round_up_Z x = x := by
  have hps : page_size = 4096 := by decide
  unfold page_round_up_Z
  rw [hps] at h ⊢
  have hq : x = 4096 * (x / 4096) := by
    have := Int.mul_ediv_add_emod x 4096
    omega
  have hdiv : (x + 4096 - 1) / 4096 = x / 4096 := by
    conv => lhs; rw [hq]
    rw [show 4096 * (x / 4096) + 4096 - 1 = 4095 + (x / 4096) * 4096 by omega]
    rw [Int.add_mul_ediv_right 4095 (x / 4096) (by decide : (4096 : Int) ≠ 0)]
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  rw [hdiv]
  exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)

/-- A page-aligned value's round-down is itself. -/
private theorem page_round_down_Z_aligned (x : Int) (h : x % page_size = 0) :
    page_round_down_Z x = x := by
  have hps : page_size = 4096 := by decide
  unfold page_round_down_Z
  rw [hps] at h ⊢
  exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)

/-- A page-aligned, page-sized, nonempty reservation is its own
    interior. -/
theorem lazy_interior_aligned (a n : word)
    (Ha : (a.toNat : Int) % page_size = 0)
    (Hn : (n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (n.toNat : Int)) :
    lazy_interior a n = [(a, n)] := by
  have hsum : ((a.toNat : Int) + (n.toNat : Int)) % page_size = 0 := by
    rw [Int.add_emod, Ha, Hn]
    decide
  have hlo : ((a.toNat : Int) + page_size - 1) / page_size * page_size
      = (a.toNat : Int) := page_round_up_Z_aligned _ Ha
  have hhi : (((a.toNat : Int) + (n.toNat : Int)) / page_size) * page_size
      = (a.toNat : Int) + (n.toNat : Int) := page_round_down_Z_aligned _ hsum
  unfold lazy_interior
  dsimp only
  rw [hlo, hhi]
  rw [ite_eq_left (by omega)]
  have hsub : (a.toNat : Int) + (n.toNat : Int) - (a.toNat : Int)
      = (n.toNat : Int) := by omega
  rw [hsub]
  simp

/-- `maps_subtract_all` applied to two cut lists in sequence: the first
    list's cuts are taken first, then the second's. -/
private theorem maps_subtract_all_append_cuts
    (cuts1 cuts2 maps : List (word × word)) :
    maps_subtract_all maps (cuts1 ++ cuts2)
      = maps_subtract_all (maps_subtract_all maps cuts1) cuts2 := by
  revert maps
  induction cuts1 with
  | nil => intro maps; rfl
  | cons hd rest ih =>
      intro maps
      obtain ⟨a, n⟩ := hd
      simp only [List.cons_append, maps_subtract_all]
      exact ih _

/-- An overlap that is FALSE, read as the two interval inequalities. -/
private theorem iv_overlap_false_mp (a1 n1 a2 n2 : word)
    (H : iv_overlap a1 n1 a2 n2 = false) :
    ¬ ((a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int) ∧
       (a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int)) := by
  intro h
  have htrue : iv_overlap a1 n1 a2 n2 = true := by
    simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
    exact h
  rw [htrue] at H
  exact absurd H (by simp)

/-- An overlap that is FALSE, discharged from the two interval
    inequalities. -/
private theorem iv_overlap_false_intro (a1 n1 a2 n2 : word)
    (H : ¬ ((a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int) ∧
            (a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int))) :
    iv_overlap a1 n1 a2 n2 = false := by
  cases h : iv_overlap a1 n1 a2 n2 with
  | false => rfl
  | true =>
      exfalso
      simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq] at h
      exact H h


/-- THE LEMMA: at any destination that is fresh and carries no backing
    metadata, the moved post-state's charge is [mremap_move_charge].

    The hypotheses are the "fresh" of the header, spelled ledger by
    ledger: [dst] is page aligned and the request page-sized and
    nonempty (so the lazy interior a lazy source re-records is exactly
    the destination); the request ends inside the address space (so a
    remnant's re-wrapped base is its base); every live mapping other than
    the source lies inside the address space and misses the destination;
    so does every protected range; cutting the destination out of the
    lazy ledger — after the source's own reservation is gone — changes
    nothing; and no materialized page outside the source lies under the
    destination.  The last two are the identity form of "the destination
    carries no lazy reservation and no materialized page", taken on the
    ledgers [State.vm_resize_backing] actually reads. -/
theorem mremap_move_charge_at_fresh (m : Model) (old old_n dst new_n : word)
    (Halign : (dst.toNat : Int) % page_size = 0)
    (Hnalign : (new_n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (new_n.toNat : Int))
    (Hend : (dst.toNat : Int) + (new_n.toNat : Int) < two_pow_64)
    (Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hmaps : region_free (map_remove (m_vmmaps m).vm_maps old) dst new_n = true)
    (Hnoacc : region_free (m_vmmaps m).vm_noaccess dst new_n = true)
    (Hlazy : maps_subtract
        (maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int)))
        (dst.toNat : Int) ((dst.toNat : Int) + (new_n.toNat : Int))
      = maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int)))
    (Hpages : List.filter (page_outside_range (dst.toNat : Int)
          ((dst.toNat : Int) + (new_n.toNat : Int)))
        (List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m))
      = List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m)) :
    vm_backing_used (mremap_model_next m old old_n dst new_n)
      = mremap_move_charge m old old_n new_n := by
  -- KL misses the destination: by the identity, every entry of KL is a
  -- remnant of cutting the destination out of it
  have HKL : region_free
      (maps_subtract (m_vm_lazy m) (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int))) dst new_n = true := by
    refine region_free_intro _ _ _ ?_
    intro a n Hin
    rw [← Hlazy] at Hin
    exact iv_overlap_false_intro _ _ _ _ (by
      have hm := maps_subtract_misses_cut _ (dst.toNat : Int)
        ((dst.toNat : Int) + (new_n.toNat : Int)) a n (by omega) Hend Hin
      omega)
  -- remnants of R0 miss the destination
  have HR : ∀ (b s : word),
      (b, s) ∈ maps_subtract_all (map_remove (m_vmmaps m).vm_maps old)
        (m_vmmaps m).vm_noaccess →
      (b.toNat : Int) + (s.toNat : Int) ≤ (dst.toNat : Int) ∨
        (dst.toNat : Int) + (new_n.toNat : Int) ≤ (b.toNat : Int) := by
    intro b s Hin
    obtain ⟨a, sz, Hin0, Hw⟩ := maps_subtract_all_within _ _ b s Hfit Hin
    have hov := region_free_In _ _ _ a sz Hmaps Hin0
    have hno := iv_overlap_false_mp _ _ _ _ hov
    omega
  -- cutting the destination out of itself removes everything
  have hself : maps_subtract_all [(dst, new_n)] [(dst, new_n)] = [] := by
    simp only [maps_subtract_all, maps_subtract, List.append_nil]
    exact iv_subtract_self dst new_n
  -- the post-state's projections, by conversion: the accessors are
  -- `simpl never`, so the unfold below is paired with these six identities
  -- rather than left to `simp`
  have P1 : ∀ (L : List (word × word)) (P : List word) (m' : Model),
      m_vmmaps (with_vm_backing L P m') = m_vmmaps m' := fun _ _ _ => rfl
  have P2 : ∀ (L : List (word × word)) (P : List word) (m' : Model),
      m_vm_lazy (with_vm_backing L P m') = L := fun _ _ _ => rfl
  have P3 : ∀ (L : List (word × word)) (P : List word) (m' : Model),
      m_vm_materialized (with_vm_backing L P m') = P := fun _ _ _ => rfl
  have P4 : ∀ (h : VmMaps) (m' : Model), m_vmmaps (with_vmmaps h m') = h :=
    fun _ _ => rfl
  have P5 : ∀ (h : VmMaps) (m' : Model),
      m_vm_lazy (with_vmmaps h m') = m_vm_lazy m' := fun _ _ => rfl
  have P6 : ∀ (h : VmMaps) (m' : Model),
      m_vm_materialized (with_vmmaps h m') = m_vm_materialized m' := fun _ _ => rfl
  -- the source leaves `vm_maps` and the destination enters it
  have hmapless : maps_subtract_all
      (mremap_maps_next (m_vmmaps m) old dst new_n).vm_maps
      (mremap_maps_next (m_vmmaps m) old dst new_n).vm_noaccess
      = [(dst, new_n)] ++
        maps_subtract_all (map_remove (m_vmmaps m).vm_maps old)
          (m_vmmaps m).vm_noaccess := by
    simp only [mremap_maps_next]
    rw [← List.singleton_append, maps_subtract_all_app,
      maps_subtract_all_disjoint_entry _ dst new_n Hpos Hnoacc]
  unfold vm_backing_used mremap_move_charge mremap_model_next vm_resize_backing
    vm_backed_maps
  dsimp only
  rw [P1, P4, P2, P3, P5, P6]
  rw [Hlazy, Hpages, hmapless]
  rw [maps_subtract_all_app, live_bytes_app]
  by_cases hsl : mremap_source_lazy_b m old old_n = true
  · -- a lazy source: the re-created mapping is its own lazy interior
    simp only [hsl, ite_true]
    rw [lazy_interior_aligned dst new_n Halign Hnalign Hpos]
    rw [maps_subtract_all_append_cuts]
    rw [hself, maps_subtract_all_nil]
    rw [maps_subtract_all_append_cuts]
    simp only [maps_subtract_all]
    rw [live_bytes_subtract_free
      (maps_subtract (m_vm_lazy m) (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int)))
      (maps_subtract_all (map_remove (m_vmmaps m).vm_maps old)
        (m_vmmaps m).vm_noaccess)
      (dst.toNat : Int) ((dst.toNat : Int) + (new_n.toNat : Int))
      (by omega) HR]
    simp only [live_bytes]
    rw [List.length_append, List.length_map]
    simp only [Int.natCast_add, Int.add_mul]
    omega
  · -- an eager source: the re-created mapping is charged whole
    have hsl' : mremap_source_lazy_b m old old_n = false := by
      cases h : mremap_source_lazy_b m old old_n <;> simp_all
    simp only [hsl', Bool.false_eq_true, ite_false, List.nil_append]
    rw [maps_subtract_all_disjoint_entry _ dst new_n Hpos HKL]
    simp only [live_bytes, List.length_nil, Nat.zero_add]
    omega

/- =========================================================================
   Sanity checks

   There is no closed computation to re-use in this file, so the checks
   below pin what the header argues and what the arms claim: the
   injectable-errno set, the two deterministic -EINVAL gates, the flag
   arms (MREMAP_MAYMOVE versus MREMAP_FIXED and `flags = 0`), the
   clone gate, the shape of the two effects (copy/unmap for a move,
   unmap-tail for a shrink, zero-fill for a growth), and the ENOMEM
   decline, which carries no memory effect.

   The spec is a RELATION, not a function, so an arm is not a
   `by decide` equality.  As in `Mm/Madvise.lean`, each arm shape is
   stated once over symbolic arguments, with the `let`-bound lengths
   spelled out (a `let` is definitionally its body), and the examples
   instantiate it, discharging the gates with `decide`.
   ========================================================================= -/

/-- mremap's injectable set is ENOMEM alone (see `mremap_errnos`). -/
example : mremap_errnos = [ENOMEM] := rfl

/-- …and `errno_from` really offers it. -/
example {i : SyscallInput} {m : Model} :
    errno_from mremap_errnos i m (.ok ENOMEM m []) :=
  choose_ok _ ENOMEM _ _ (by decide : ENOMEM ∈ mremap_errnos)

/-- THE FLAG TEST reads the flag word only: MREMAP_MAYMOVE (1) is the one
    modeled value, so MREMAP_FIXED (2), the kernel-served `flags = 0`, and
    `MAYMOVE | FIXED` (3) all decline.  MREMAP_FIXED is `#define
    MREMAP_FIXED 2` (include/uapi/linux/mman.h:10); `Uapi` carries only the
    MAYMOVE bit, so the numbers are spelled out here. -/
example : (((1 : Nat) : Int) == MREMAP_MAYMOVE) = true := by decide
example : (((2 : Nat) : Int) == MREMAP_MAYMOVE) = false := by decide
example : (((0 : Nat) : Int) == MREMAP_MAYMOVE) = false := by decide
example : (((3 : Nat) : Int) == MREMAP_MAYMOVE) = false := by decide

/-- THE WRAPPING `PAGE_ALIGN` TEST: a zero length and the top partial page
    round to zero or to 2^64 — both EINVAL — while a whole page and the
    last ALIGNED page do not. -/
example : page_align_is0_b (BitVec.ofInt 64 0) = true := by decide
example : page_align_is0_b (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF) = true := by decide
example : page_align_is0_b (BitVec.ofInt 64 0x1000) = false := by decide
example : page_align_is0_b (BitVec.ofInt 64 0xFFFFFFFFFFFFF000) = false := by decide

/-- The demo ledger and model the concrete checks run over: ONE live
    anonymous mapping `[0x1000, 0x2000)`, nothing reserved, nothing
    protected, nothing lazy, nothing materialized. -/
private def demoVm : VmMaps :=
  mkVmMaps [] [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)]
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000

private def demoModel : Model :=
  mkModel [] demoVm IEof []

/-- A second demo ledger: ONE live anonymous mapping of three pages,
    `[0x1000, 0x4000)`, for the calls that have to resize a tracked entry
    (the first ledger is exactly one page, so an `old_size` above it would
    fail the source gate's exact-entry test). -/
private def demoVmLarge : VmMaps :=
  mkVmMaps [] [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x3000)]
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000

private def demoModelLarge : Model :=
  mkModel [] demoVmLarge IEof []

/-- A syscall input for `mremap` (216).  The spec reads none of it; it is
    here because a `SysSpec` is a relation on an input as well as a model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 216, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-! ### The four gate shapes, stated once over symbolic arguments -/

/-- A MISALIGNED OLD ADDRESS IS -EINVAL — the second gate, which only a
    MAYMOVE flag word ever reaches (mm/mremap.c:1027). -/
private theorem misalignedCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Hmis : (((old.toNat : Int) % page_size) == 0) = false) :
    mremap_spec old old_size new_size flags i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [mremap_spec, Hflag, Hmis, err_ret, ret_only, pure]

/-- A FLAG WORD WITHOUT MAYMOVE DECLINES, before any argument is read. -/
private theorem flagsCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = false) :
    mremap_spec old old_size new_size flags i m .unmodeled := by
  simp [mremap_spec, Hflag, unmodeled]

/-- A ROUNDED NEW LENGTH OF ZERO IS -EINVAL — `new_size = 0` and the top
    partial page at once (mm/mremap.c:1031, 1038). -/
private theorem zerolenCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = true) :
    mremap_spec old old_size new_size flags i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [mremap_spec, Hflag, Halign, Hnew, err_ret, ret_only, pure]

/-- A ROUNDED OLD LENGTH OF ZERO IS THE CLONE SHAPE AND DECLINES — after
    the two EINVAL gates, so a misaligned address or a zero new length
    still gets Linux's answer. -/
private theorem cloneCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Htask : ((TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)) = false)
    (Hold : page_align_is0_b old_size = true) :
    mremap_spec old old_size new_size flags i m .unmodeled := by
  simp [mremap_spec, Hflag, Halign, Hnew, Htask, Hold, unmodeled]

/-- AN EQUAL-SIZE CALL IS A NO-OP RETURNING [old] — and it sits OUTSIDE the
    [alt] that offers ENOMEM, which is why Linux's equal-size arm carries no
    injectable failure (see `mremap_errnos`). -/
private theorem equalCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Htask : ((TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)) = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : (mremap_source_b (m_vmmaps m) old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
        (page_round_up_Z (old_size.toNat : Int)) &&
      mremap_backing_uniform_b m old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true)
    (Heq : page_round_up_Z (old_size.toNat : Int)
        = page_round_up_Z (new_size.toNat : Int)) :
    mremap_spec old old_size new_size flags i m
      (.ok (mkEffect old [] []) m []) := by
  simp only [mremap_spec, Hflag, Halign, Hnew, Htask, Hold, bind_getModel, Hsrc,
    Bool.not_true, Bool.false_eq_true, ite_false]
  rw [Heq]
  simp [ret_only, pure]

/-- A DECLINE PAST THE GATES: every argument gate passes, the source gate
    does not, so the call is `unmodeled` — no state change and no errno. -/
private theorem sourceDeclineCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Htask : ((TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)) = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : mremap_source_b (m_vmmaps m) old
          (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
          (page_round_up_Z (old_size.toNat : Int)) = false ∨
        mremap_backing_uniform_b m old
          (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) = false) :
    mremap_spec old old_size new_size flags i m .unmodeled := by
  simp only [mremap_spec, Hflag, Halign, Hnew, Htask, Hold, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [bind_getModel]
  simp [Hsrc, unmodeled]

/-- A SHRINK MOVES TO `mremap_model_next` AND EMITS THE TAIL UNMAP — the
    resolution the spec's shrinking arm admits, with the model's ledger
    already updated.  It is one disjunct of the [alt], so a caller sees it
    beside the ENOMEM decline. -/
private theorem shrinkCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Htask : ((TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)) = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : (mremap_source_b (m_vmmaps m) old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
        (page_round_up_Z (old_size.toNat : Int)) &&
      mremap_backing_uniform_b m old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true)
    (Hne : (page_round_up_Z (old_size.toNat : Int)
        == page_round_up_Z (new_size.toNat : Int)) = false)
    (Hsh : page_round_up_Z (new_size.toNat : Int)
        < page_round_up_Z (old_size.toNat : Int)) :
    mremap_spec old old_size new_size flags i m
      (.ok (mremap_inplace_effect old
          (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
          (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))
          (page_round_up_Z (old_size.toNat : Int))
          (page_round_up_Z (new_size.toNat : Int)))
        (mremap_model_next m old
          (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) old
          (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))) []) := by
  simp only [mremap_spec, Hflag, Halign, Hnew, Htask, Hold, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [bind_getModel]
  simp only [Hsrc, Hne, Bool.not_true, Bool.false_eq_true, ite_false, alt]
  refine Or.inr ?_
  rw [ite_eq_left Hsh]
  exact bind_ok _ _ _ _ () _ [] _ _ [] (modify_ok _ _ _) (pure_ok _ _ _)

/-- THE ENOMEM DECLINE: on a resizing call every gate passes, so the
    failure-injection arm of the [alt] is admissible — and it leaves the
    model UNTOUCHED, which is the rollback `move_vma` performs
    (mm/mremap.c:730-741, 792). -/
private theorem errnoCheck {old old_size new_size flags : word}
    {i : SyscallInput} {m : Model}
    (Hflag : ((flags.toNat : Int) == MREMAP_MAYMOVE) = true)
    (Halign : (((old.toNat : Int) % page_size) == 0) = true)
    (Hnew : page_align_is0_b new_size = false)
    (Htask : ((TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)) = false)
    (Hold : page_align_is0_b old_size = false)
    (Hsrc : (mremap_source_b (m_vmmaps m) old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
        (page_round_up_Z (old_size.toNat : Int)) &&
      mremap_backing_uniform_b m old
        (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))) = true)
    (Hne : (page_round_up_Z (old_size.toNat : Int)
        == page_round_up_Z (new_size.toNat : Int)) = false) :
    mremap_spec old old_size new_size flags i m
      (.ok (mkEffect (errno_ret ENOMEM) [] []) m []) := by
  simp only [mremap_spec, Hflag, Halign, Hnew, Htask, Hold, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [bind_getModel]
  simp only [Hsrc, Hne, Bool.not_true, Bool.false_eq_true, ite_false, alt]
  exact Or.inl (bind_ok (errno_from mremap_errnos) (fun e => err_ret e) i m
    ENOMEM m [] (mkEffect (errno_ret ENOMEM) [] []) m []
    (choose_ok _ ENOMEM _ _ (by decide)) (by simp [err_ret, ret_only, pure]))

/-! ### The arm shapes at the concrete model -/

section
set_option maxRecDepth 1000000

/-- A misaligned old address is -EINVAL under MAYMOVE… -/
example :
    mremap_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 1) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_ ?_
  · decide
  · decide

/-- …and MREMAP_FIXED (2) declines rather than answering EINVAL, because
    the flag gate comes first. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 2) demoInput demoModel
      .unmodeled := by
  refine flagsCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- The kernel-served `flags = 0` declines too: a deliberate narrowing,
    announced in `mremap_spec`. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0) demoInput demoModel
      .unmodeled := by
  refine flagsCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- A ZERO NEW SIZE IS -EINVAL (mm/mremap.c:1038). -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 1) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine zerolenCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_
  · decide
  · decide
  · decide

/-- A new size in the TOP PARTIAL PAGE rounds to 2^64 and is -EINVAL, not a
    wrap into a successful zero-length call. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF) (BitVec.ofInt 64 1) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine zerolenCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_
  · decide
  · decide
  · decide

/-- A ZERO OLD SIZE IS THE CLONE SHAPE and declines (before the source is
    read at all, so the demo model's ledger is never consulted). -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 1) demoInput demoModel
      .unmodeled := by
  refine cloneCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- AN EQUAL-SIZE CALL answers `old` and moves nothing: the ledger and the
    backing ledgers come back unchanged. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 1) demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0x1000) [] []) demoModel []) := by
  refine equalCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- A RANGE THE LEDGER DOES NOT OWN DECLINES: the source is not one exact
    tracked entry, so the arm fails closed. -/
example :
    mremap_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 1) demoInput demoModel
      .unmodeled := by
  refine sourceDeclineCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- THE SHRINK RESOLUTION on that ledger: shrinking the three-page entry
    from `0x3000` to `0x2000` bytes admits `.ok` on the tail-unmap effect
    with the ledger already resized — the arm a caller must handle beside
    ENOMEM. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x3000)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 1) demoInput demoModelLarge
      (.ok (mremap_inplace_effect (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 (page_round_up_Z 0x3000))
          (BitVec.ofInt 64 (page_round_up_Z 0x2000))
          (page_round_up_Z 0x3000) (page_round_up_Z 0x2000))
        (mremap_model_next demoModelLarge (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 (page_round_up_Z 0x3000)) (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 (page_round_up_Z 0x2000))) []) := by
  refine shrinkCheck (i := demoInput) (m := demoModelLarge) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals decide

/-- THE ENOMEM DECLINE on the answered shape: the source is one tracked
    entry and the call resizes, so `alt` offers ENOMEM — with no memory
    effect and the model unchanged. -/
example :
    mremap_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 1) demoInput demoModel
      (.ok (mkEffect (errno_ret ENOMEM) [] []) demoModel []) := by
  refine errnoCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end

/-! ### The effect shapes -/

/-- A MOVE UNMAPS THE WHOLE SOURCE, COPIES IT FROM THE PRE-EFFECT SNAPSHOT,
    and zero-fills only the grown tail — here `[0x5000, 0x6000)`, one page,
    because the source was one page and the request two.  The copy length is
    the source's, `old_n`, not `min old_n new_n`: a move only happens on
    growth. -/
example :
    (mremap_move_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x5000) 0x1000 0x2000).eff_unmaps
      = [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)] := by decide

example :
    (mremap_move_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x5000) 0x1000 0x2000).eff_copies
      = [MemCopy.mkCopy (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x5000)
          (BitVec.ofInt 64 0x1000)] := rfl

example :
    (mremap_move_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x5000) 0x1000 0x2000).eff_zeros
      = [(BitVec.ofInt 64 0x6000, BitVec.ofInt 64 0x1000)] := by decide

example :
    (mremap_move_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x5000) 0x1000 0x2000).eff_ret
      = BitVec.ofInt 64 0x5000 := by decide

/-- A SHRINK UNMAPS EXACTLY THE DROPPED TAIL and zero-fills nothing; it
    returns the unchanged base (mm/mremap.c:1096). -/
example :
    (mremap_inplace_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x3000)
        (BitVec.ofInt 64 0x1000) 0x3000 0x1000).eff_unmaps
      = [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x2000)] := by decide

example :
    (mremap_inplace_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x3000)
        (BitVec.ofInt 64 0x1000) 0x3000 0x1000).eff_zeros = [] := by decide

example :
    (mremap_inplace_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x3000)
        (BitVec.ofInt 64 0x1000) 0x3000 0x1000).eff_ret
      = BitVec.ofInt 64 0x1000 := by decide

/-- AN IN-PLACE GROW ZERO-FILLS EXACTLY THE DELTA and unmaps nothing. -/
example :
    (mremap_inplace_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x3000) 0x1000 0x3000).eff_zeros
      = [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x2000)] := by decide

example :
    (mremap_inplace_effect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x3000) 0x1000 0x3000).eff_unmaps = [] := by decide

/-- An equal-size tail contributes no zero-fill at all. -/
example :
    mremap_tail (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      0x1000 0x1000 = [] := by decide

/-- The errno really is the kernel's number in the return word, and the
    answered return really is `old`. -/
example : errno_ret ENOMEM = BitVec.ofInt 64 (-12) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide







