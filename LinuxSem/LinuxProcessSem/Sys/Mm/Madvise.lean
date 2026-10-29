/-
  * LinuxProcessSem.Sys.Mm.Madvise — madvise (233)

  This file answers to Linux [mm/madvise.c]: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  [Specs.lean] carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  [Specs.lean] holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  [madvise addr len advice].  ONE advice value is answered, MADV_DONTNEED,
  over a range the ledger describes completely; every other advice value
  declines.  What the arm exists for is the backed-memory budget: a
  MAP_NORESERVE page is charged to [State.vm_limit] on its first touch
  ([State.materialize_model_accesses]), and without this arm only an
  unmap of the whole mapping would give that charge back.  A runtime
  that returns its shadow pages with MADV_DONTNEED when large chunks are
  freed keeps the mapping and reuses the same pages, so under heavy
  alloc/free traffic it stays inside its memory on Linux, while without
  this arm the model would spend its budget on every page ever touched.

  THE KERNEL'S ORDER, which the spec follows because the order is
  behavior.  [do_madvise] (mm/madvise.c, Linux v6.18.46) opens with
  [madvise_should_skip], which is [is_valid_madvise] and then the
  zero-length exit:

    static bool is_valid_madvise(unsigned long start, size_t len_in,
                                 int behavior)
    {
            if (!madvise_behavior_valid(behavior)) return false;
            if (!PAGE_ALIGNED(start)) return false;
            len = PAGE_ALIGN(len_in);
            if (len_in && !len) return false;
            if (start + len < start) return false;
            return true;
    }...
            if (!is_valid_madvise(start, len_in, behavior)) {
                    *err = -EINVAL; return true; }
            if (start + PAGE_ALIGN(len_in) == start) {
                    *err = 0; return true; }

  Every refusal in [is_valid_madvise] is -EINVAL, so the order AMONG
  them is unobservable, and the arm tests alignment first: a misaligned
  [addr] is -EINVAL for every advice value, known or not, before the
  advice is read — [madvise_behavior_valid] is a pure switch on the
  value, and a value it rejects is -EINVAL just the same.  What IS
  observable is that all four precede the zero-length exit: [len = 0]
  answers 0 only for a valid advice value at an aligned address, which
  is why the [w_is0 len] branch below sits behind both gates.  The
  advice gate declines rather than answering -EINVAL for an unknown
  value because [madvise_behavior_valid]'s list depends on the kernel
  configuration (MADV_MERGEABLE needs CONFIG_KSM, MADV_HUGEPAGE
  CONFIG_TRANSPARENT_HUGEPAGE, MADV_HWPOISON CONFIG_MEMORY_FAILURE), so
  which values are "unknown" is not a fact about the source alone.

  The last two refusals are one test in [Z]: [PAGE_ALIGN(len_in)] wraps
  to 0 exactly when [page_round_up_Z len = 2^64], and [start + len]
  wraps exactly when [addr + nZ >= 2^64] for an [nZ] below it; both are
  [two_pow_64 <= addr + nZ].  That test is [Mprotect.mprotect_spec]'s
  fourth gate with -EINVAL in place of -ENOMEM — errno choice is
  behavior, and [do_mprotect_pkey] and [is_valid_madvise] pick
  different ones for the same shape.  QEMU's user-mode emulation agrees
  on both refusals ([target_madvise], linux-user/mmap.c, 8.2.2: a
  misaligned start and a [TARGET_PAGE_ALIGN] that wraps to zero or a
  range [guest_range_valid_untagged] refuses are each -EINVAL, and a
  zero [len_in] is 0), so the two argument errnos and the zero-length
  success are inside the intersection the design priorities (README.md)
  require.

  THE ANSWERED SHAPE.  Past the gates the kernel walks the VMAs the
  range meets ([madvise_walk_vmas]), applying [madvise_vma_behavior] to
  each; for MADV_DONTNEED that is [madvise_dontneed_free] and, unless
  the VMA is VM_LOCKED, VM_PFNMAP or hugetlb (-EINVAL,
  [madvise_dontneed_free_valid_vma]), [madvise_dontneed_single_vma],
  which zaps the page range and returns 0.  A zapped anonymous private
  page reads back as zeros and is faulted in fresh on the next touch.
  None of the three refusing VMA kinds can arise on a modeled run:
  mlock (228) and mlockall (230) are outside the modeled surface, so no
  VMA is VM_LOCKED; the model maps no device memory, so none is
  VM_PFNMAP; and [Mmap.mmap_spec] declines MAP_HUGETLB.  Nor can the
  -EPERM of [can_madvise_modify] (a sealed VMA) — mseal (462) is
  unmodeled, as [Mprotect.mprotect_errnos] already argues for its
  twin — nor the userfaultfd retry, since no modeled call arms one.

  So over a range that lies inside ONE live anonymous mapping of the
  ledger, every page of it read-write, the answer is forced: 0, the
  range reads back as zeros, and no event.  That is the
  [madvise_dontneed_ok] gate below, one conjunct per way the ledger's
  picture could fall short of the kernel's:

  - [map_contains (vm_maps h)]: inside one recorded anonymous mapping
    — an mmap grant, a MAP_FIXED commit, or a recorded brk grow (the
    heap is an anonymous private VMA to Linux, and zapping its pages
    is what a brk shrink-and-regrow already models: fresh zeros).  The
    model never merges adjacent entries, so a range one kernel VMA
    covers can lie across two entries here and decline — the safe
    direction, as [State.map_contains] says.  A range with a page the
    ledger does not own declines rather than answering the -ENOMEM
    [madvise_walk_vmas] reports, and the reason is the SHAPE of that
    answer: the walk applies the advice to every mapped part it meets
    and only then returns [unmapped_error], so a hole means a state
    change AND an errno at once, and the ledger — which carries neither
    the stack nor the kernel's own vdso/vvar pair — cannot say which
    parts Linux zapped.
  - [region_free (vm_reserved h)]: never the image's LOAD pages.  The
    file-backed private ones read back FILE CONTENTS after a zap, not
    zeros, and the model cannot state them; the anonymous BSS ones are
    not in the ledger's replaceable representation either
    ([Mmap.mmap_spec]'s MAP_FIXED arms give the same reason).  No
    reachable state has an image page in [vm_maps], so the conjunct is
    documentary there and load-bearing only for a hand-built ledger;
    `Checks/Cases/Mm/Madvise.lean`'s
    [madvise_image_range_is_unmodeled] pins it on exactly such a ledger,
    the [noaccess_image_overlap] fixture, which is the one shape a
    reachable state never has.
  - [region_free (vm_noaccess h)]: every page read-write.  Linux zaps a
    PROT_NONE anonymous page just the same and answers 0, but the
    machine overlay holds no bytes for a protected page, and the
    zero-fill that re-exposes one belongs to [Mprotect.mprotect_spec];
    declaring [eff_zeros] over a range the process cannot read would
    claim bytes the machine cannot serve.  A decline, not a wrong
    answer, and one no modeled runtime reaches.

  THE EFFECT is [eff_zeros] over the whole page-rounded range, as the
  rw MAP_FIXED replacement and the mprotect exposure emit: every byte
  of it reads back as zero on Linux, including bytes written a moment
  ago.  [Run.apply_effect] materializes it in the overlay, and
  [State.syscall_effect_accesses] deliberately omits zero ranges, so
  the zero-fill charges nothing — the pages are lazy again, not touched.

  THE LEDGER.  [madvise_dontneed_next] drops every materialized page in
  the range and changes nothing else: the mapping stays in [vm_maps]
  with its size, its lazy provenance stays in [m_vm_lazy], and the
  budget falls by exactly the charges those pages took, so the next
  access re-charges them through [State.materialize_model_accesses]
  as a first touch does.  An EAGERLY charged mapping keeps its charge:
  Linux keeps the commit charge of a VM_ACCOUNT VMA across a zap too
  ([madvise_dontneed_single_vma] touches no accounting), and the
  model's eager charge is that commit-time guarantee, not the pages'
  residency.  Only [m_vm_materialized] shrinks; [m_vm_lazy] is passed
  through unchanged, so the page-alignment invariant
  [State.vm_backing_used] rests on is untouched — this is a reader of
  the lazy ledger, not a third writer.

  Nothing here is nondeterministic and no errno is injectable: the
  only failures [do_madvise] can report on the answered shape are the
  -EINTR of a killable write lock, which DONTNEED does not take
  ([get_lock_mode] gives it MADVISE_VMA_READ_LOCK), and the walk's
  -ENOMEM, which the containment gate excludes.  A forged nonzero
  return, a forged 0 on a misaligned address, and a 0 without the
  zero-fill are each rejected, and `Checks/Cases/Mm/Madvise.lean` pins
  all three: [madvise_unaligned_forged_success_rejected],
  [madvise_without_zeros_rejected] and
  [madvise_nonzero_return_rejected].

      From LinuxSem.LinuxProcessSem Require Import BvBase Fs State Monad.
      From LinuxSem.LinuxProcessSem.Sys Require Export
        Syscall Uapi.

  and opens the `sys`/`bv` scopes.  Here:

  - `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
    so a spec's type is `SysSpec SyscallEffect`, and `getModelSpec` is `get_model`;
  - `Sys.Syscall` supplies `ret_only`, `err_ret` and `w_is0`;
  - `Sys.Uapi` supplies `MADV_DONTNEED`;
  - `StateVm` supplies `iv_overlap`, `region_free` (and its
    `region_free_false` inversion), `map_contains`, `page_outside_range`
    and `vm_noaccess_entries_nonzero` — chunk B7 of `State.lean`;
  - `StateLedger` supplies the ledger accessors `m_vmmaps`,
    `m_vm_lazy`, `m_vm_materialized`, the setter `with_vm_backing`, and
    the constructors `mkVmMaps`/`mkModel` the checks below use;
  - `State` supplies `page_size`, `page_round_up_Z`, `two_pow_64` and
    `EINVAL`.

  `Sys.Uaccess` is not imported: `madvise` reads no user buffer at all
  in this spec — the range is described by the ledger, and the model
  writes the zero-fill as an EFFECT (`eff_zeros`) rather than as a
  copy-to-user.

  `x <- c;; k` has no Lean counterpart, so it is `bind c (fun x => k)` here; `;; ` at
  the head of a chain is `bind`. `Z_to_bv 64 z` is `BitVec.ofInt 64 z`; `negb` is
  `!`; `Z.eqb a b` is `a == b`; `Z.ltb`/`Z.leb` are `decide (· < ·)` / `decide (· ≤
  ·)`, and `(two_pow_64 <=? e)%Z` in an `if` is just the `Int` comparison `two_pow_64
  ≤ e` (the same decision, unboxed — the form the sanity checks below read). The
  `VmMaps` projections `vm_maps h` / `vm_reserved h` / `vm_noaccess h` are structure
  fields here (`h.vm_maps`, …).

  The lemma below names its witness with
  `max (a.toNat: Int) (addr.toNat: Int)`, this tree of
  `Z.max (bv_unsigned a) (bv_unsigned addr)`; `omega` closes the
  resulting interval goals directly (it understands `Int.max`), which
  is why no `Z.max_spec` case analysis appears.
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

namespace LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

/-! ## The advice test -/

/-- Is the advice MADV_DONTNEED?  [advice] arrives narrowed by
    [Syscall.int32]: the kernel declares it [int]
    ([SYSCALL_DEFINE3(madvise, unsigned long, start, size_t, len_in,
    int, behavior)], mm/madvise.c, Linux v6.18.46), so the register's
    high half is discarded before the switch reads it. -/
def madvise_dontneed_b (advice : word) : Bool :=
  (advice.toNat : Int) == MADV_DONTNEED

/-! ## The answered shape's ledger gate -/

/-- The answered shape's ledger gate (see the header): inside one live
    anonymous mapping, clear of the image, every page read-write. -/
def madvise_dontneed_ok (h : VmMaps) (addr n : word) : Bool :=
  region_free h.vm_reserved addr n &&
  map_contains h.vm_maps addr n &&
  region_free h.vm_noaccess addr n

/-! ## The protected-byte lemma -/

/-- THE THIRD CONJUNCT DECLINES ONLY OVER A REAL PROTECTED BYTE.

    [region_free] folds [State.iv_overlap], which reports an overlap
    against a ZERO-SIZE interval strictly inside the queried range:
    [iv_overlap addr n a 0] is [addr < a && a < addr + n], true for any
    [a] strictly between.  So an entry of [vm_noaccess] naming no byte
    would close this gate over a range the process can read and write
    throughout, and the call would decline where the header says it
    answers.  Fail closed rather than wrong, which is why no example or
    test would catch it.

    No writer can make one. [State.vm_noaccess_entries_nonzero] is the
    property, [State.init_model_noaccess_nonzero] its base case, and
    every writer of the list carries a preservation lemma —
    [Mm/Mmap.lean]'s section "the protected ledger names real bytes" lists
    the writers by name and holds the lemmas, [Mm/Mprotect.lean] the one
    writer outside that file.  Two things that section says and this
    must not overstate: the lemmas for the arms that write their
    post-state inline RESTATE the record rather than naming it, so a
    re-shaped arm would not break them; and nothing in the tree
    COMPOSES the lemmas into "every reachable model satisfies it",
    because the induction over the specs' branch structure is not
    carried out.  That is why the lemma below takes the property as a
    HYPOTHESIS rather than proving it of the state it is handed.  A
    caller discharges it from the writer that produced the state, and
    this tree HAS such a caller: `Checks/Cases/Mm/Madvise.lean`'s
    [madvise_noaccess_remnant_decline_names_a_byte] builds a protected
    ledger by cutting a recorded range in two with
    [Mprotect.mprotect_model_next], feeds it to the lemma below, and
    discharges the hypothesis with
    [Mprotect.mprotect_model_next_noaccess_nonzero] — the writer's own
    preservation lemma read at that whole state rather than the remnant
    list off the fixture.  What it therefore shows is that the cut
    COULD NOT have left a vacuous remnant, not merely that this one did
    not, which is the strength the premise is there to give the
    decline.

    Under it, a decline attributed to [vm_noaccess] exhibits an address
    the request covers and the process cannot touch — which is exactly
    the situation the conjunct is here to keep the model out of.

    THE SIDE CONDITION on [n] is supplied by [madvise_spec] at the call
    site: it passes [n = Z_to_bv 64 (page_round_up_Z (bv_unsigned len))]
    past a [w_is0 len] gate and the [two_pow_64] bound on the rounded
    end, which is [Mmap.mmap_request_len_nonzero]'s exact shape. It is
    load-bearing rather than tidy: with [n = 0] the request covers no
    address at all, while [region_free] can still answer false. -/
theorem madvise_noaccess_decline_names_a_protected_byte (h : VmMaps)
    (addr n : word)
    (Hnz : vm_noaccess_entries_nonzero h)
    (Hn : 0 < (n.toNat : Int))
    (Hfree : region_free h.vm_noaccess addr n = false) :
    ∃ a sz x,
      (a, sz) ∈ h.vm_noaccess ∧
      0 < (sz.toNat : Int) ∧
      ((a.toNat : Int) ≤ x ∧ x < (a.toNat : Int) + (sz.toNat : Int)) ∧
      ((addr.toNat : Int) ≤ x ∧
        x < (addr.toNat : Int) + (n.toNat : Int)) := by
  obtain ⟨a, sz, Hin, Hov⟩ :=
    region_free_false h.vm_noaccess addr n Hfree
  have Hsz := Hnz a sz Hin
  unfold iv_overlap at Hov
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at Hov
  obtain ⟨H1, H2⟩ := Hov
  exact ⟨a, sz, max (a.toNat : Int) (addr.toNat : Int), Hin, Hsz,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-! ## The post-state and the specification -/

/-- The post-state: the range's first-touch charges are given back and
    nothing else moves.  The bounds are taken in [Z], as every ledger
    range is; the gate above has already bounded [addr + n] below 2^64. -/
def madvise_dontneed_next (m : Model) (addr n : word) : Model :=
  with_vm_backing (m_vm_lazy m)
    (List.filter
       (page_outside_range (addr.toNat : Int)
                           ((addr.toNat : Int) + (n.toNat : Int)))
       (m_vm_materialized m)) m

/-- [madvise addr len advice] (233).

    THE ANSWERED SHAPE is the last `else` arm: the range is page-rounded,
    the ledger's gate passes, the materialized pages are given back, and
    the effect zero-fills the whole rounded range and returns 0.  Every
    other shape declines (`unmodeled`) or is refused before the model is
    read at all:

    - misaligned [addr] is -EINVAL for EVERY advice value, known or not,
      before the advice is read ([is_valid_madvise] and the kernel order
      argument in the file header);
    - any advice but MADV_DONTNEED declines — a value the kernel's
      configuration-dependent [madvise_behavior_valid] rejects is
      -EINVAL on Linux and "unknown" is not a fact about the source
      alone, so the arm declines in both cases;
    - [len = 0] answers 0, and only here — behind both gates above,
      which is what makes the kernel's ordering observable;
    - a page-rounded end at or above 2^64 is -EINVAL (the two wrapping
      refusals of [is_valid_madvise], [Mmap.mmap_spec]'s shape with
      -EINVAL in place of -ENOMEM);
    - a range the ledger does not describe completely — outside one live
      anonymous mapping, over the image, or over a protected page —
      declines rather than answering the walk's -ENOMEM, because a hole
      means a state change AND an errno at once (see the header). -/
def madvise_spec (addr len advice : word) : SysSpec SyscallEffect :=
  if !(((addr.toNat : Int) % page_size) == 0) then err_ret EINVAL
  else if !(madvise_dontneed_b advice) then unmodeled
  else if w_is0 len then ret_only (BitVec.ofInt 64 0)
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
  then err_ret EINVAL
  else
    bind getModel fun m =>
      let h := m_vmmaps m
      let nZ := page_round_up_Z (len.toNat : Int)
      let n := BitVec.ofInt 64 nZ
      if madvise_dontneed_ok h addr n then
        bind (modify fun _ => madvise_dontneed_next m addr n)
          fun _ => pure (mkEffect (BitVec.ofInt 64 0) [] [(addr, n)])
      else unmodeled

/- =========================================================================
   Sanity checks

  the ones below pin the parts that are decidable and that the header argues for: the
  advice test, the ledger gate, the page-range refusals, the three "nothing else
  moves" fields of the post-state, and the answered and refused arm shapes against a
  concrete model.

   The spec is a RELATION, not a function, so an arm is not a `by decide`
   equality.  The arm lemmas state each shape once over symbolic
   arguments and the examples instantiate them, discharging the gate
   hypotheses with `decide`: symbolically the `if`-conditions are built
   from the variables the hypotheses name, whereas at the concrete
   `BitVec.ofInt`/`toNat` literals `simp` cannot normalize them
   syntactically (the kernel can, which is what `decide` uses).
   ========================================================================= -/

/-- The advice test reads the ADVICE value only: MADV_DONTNEED (4) is the
    one answered value. -/
example : madvise_dontneed_b (BitVec.ofInt 64 4) = true := by decide
example : madvise_dontneed_b (BitVec.ofInt 64 3) = false := by decide
example : madvise_dontneed_b (BitVec.ofInt 64 0) = false := by decide

/-- A ledger the checks run over: ONE live anonymous mapping
    `[0x1000, 0x4000)`, nothing reserved, nothing protected. -/
private def demoVm : VmMaps :=
  mkVmMaps [] [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x3000)]
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000

/-- The gate accepts a range inside that mapping… -/
example : madvise_dontneed_ok demoVm (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 0x3000) = true := by decide

/-- …and refuses one that runs off the end of it (a page the ledger does
    not own). -/
example : madvise_dontneed_ok demoVm (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 0x3001) = false := by decide

/-- …and one that is not contained in a SINGLE entry: two ADJACENT model
    entries a kernel VMA could cover answer "no" here — the safe
    direction `State.map_contains` documents. -/
example :
    madvise_dontneed_ok
      (mkVmMaps []
        [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000),
         (BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)]
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x2000) = false := by
  decide

/-- The image is refused even where a mapping entry covers it: reserved
    LOAD pages read back FILE CONTENTS after a zap, not zeros. -/
example :
    madvise_dontneed_ok
      (mkVmMaps [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)]
        [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x3000)]
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000) = false := by decide

/-- …and so is a protected page: the overlay serves no bytes there, so
    declaring a zero-fill would claim bytes the machine cannot serve. -/
example :
    madvise_dontneed_ok
      { demoVm with
        vm_noaccess :=
          [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)] }
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) = false := by
  decide

/-- THE PAGE-RANGE REFUSALS, exactly as `is_valid_madvise` computes them
    in [Z]: a length whose rounding wraps to 2^64, and a rounded end that
    reaches 2^64, are both at or above the bound — and a length one byte
    below that floor stays inside it. -/
example : page_round_up_Z (0xFFFFFFFFFFFFFFFF : Int) = two_pow_64 := by decide
example : page_round_up_Z (0xFFFFFFFFFFFFEFFF : Int) = 0xFFFFFFFFFFFFF000 := by
  decide
example : page_round_up_Z (0xFFFFFFFFFFFFF000 : Int) = 0xFFFFFFFFFFFFF000 := by
  decide
example : (0 : Int) + page_round_up_Z (0xFFFFFFFFFFFFFFFF : Int) = two_pow_64 := by
  decide
example : (0x1000 : Int) + page_round_up_Z 0x1000 < two_pow_64 := by decide
example : two_pow_64 ≤ (0x1000 : Int) + page_round_up_Z 0xFFFFFFFFFFFFFFFF := by
  decide
example : two_pow_64 ≤ (0x1000 : Int) + page_round_up_Z 0xFFFFFFFFFFFFF000 := by
  decide
example : ¬ (two_pow_64 ≤ (0 : Int) + page_round_up_Z 0xFFFFFFFFFFFFEFFF) := by
  decide

/-- The model the arm checks run in: the ledger above, with two of its
    pages materialized (one inside the range the checks zap, one
    outside). -/
private def demoModel : Model :=
  with_vm_backing [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x3000)]
    [BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x2000,
     BitVec.ofInt 64 0x5000]
    (mkModel [] demoVm IEof [])

/-- THE POST-STATE drops every materialized page in the rounded range
    `[0x1000, 0x2000)`, keeps the two outside it, and moves nothing
    else: `vm_maps` and the lazy provenance are passed through
    untouched (only `m_vm_materialized` shrinks). -/
example :
    m_vm_materialized
      (madvise_dontneed_next demoModel (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x1000)) =
      [BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x5000] := by decide

example :
    m_vm_lazy
      (madvise_dontneed_next demoModel (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x1000)) = m_vm_lazy demoModel := by decide

example :
    m_vmmaps
      (madvise_dontneed_next demoModel (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x1000)) = m_vmmaps demoModel := by decide

/-- A syscall input for `madvise` (233).  The spec reads none of it; it
    is here because a `SysSpec` is a relation on an input as well as a
    model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 233, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-! ### The four arm shapes, stated once over symbolic arguments -/

/-- THE ANSWERED SHAPE: past all four gates the spec reads the model,
    checks the ledger gate, moves to `madvise_dontneed_next`, and returns
    0 with the whole page-rounded range zero-filled and no event. -/
private theorem armCheck {addr len advice : word} {i : SyscallInput} {m : Model}
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hadv : madvise_dontneed_b advice = true)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hok : madvise_dontneed_ok (m_vmmaps m) addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true) :
    madvise_spec addr len advice i m
      (.ok (mkEffect (BitVec.ofInt 64 0) []
        [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))])
        (madvise_dontneed_next m addr
          (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) []) := by
  simp [madvise_spec, Halign, Hadv, Hlen, Hbound, Hok, bind_getModel]
  exact bind_ok _ _ _ _ _ _ _ _ _ _ (modify_ok _ _ _) (pure_ok _ _ _)

/-- THE DECLINE PAST THE GATES: every argument gate passes but the ledger's
    gate does not, so the call is `unmodeled` — no state change and no
    errno, because a hole means both at once (see the header). -/
private theorem declineCheck {addr len advice : word} {i : SyscallInput} {m : Model}
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hadv : madvise_dontneed_b advice = true)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hok : madvise_dontneed_ok (m_vmmaps m) addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false) :
    madvise_spec addr len advice i m .unmodeled := by
  simp [madvise_spec, Halign, Hadv, Hlen, Hbound, Hok, bind_getModel, unmodeled]

/-- A MISALIGNED ADDRESS IS -EINVAL, before the advice is read at all —
    which is the kernel's order, and the reason the check below passes
    for an unknown advice value too. -/
private theorem misalignedCheck {addr len advice : word} {i : SyscallInput}
    {m : Model} (Halign : ((addr.toNat : Int) % page_size == 0) = false) :
    madvise_spec addr len advice i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [madvise_spec, Halign, err_ret, ret_only, pure]

/-- ZERO LENGTH ANSWERS 0 — behind the alignment and advice gates, which
    is what makes the kernel's ordering observable. -/
private theorem zerolenCheck {addr len advice : word} {i : SyscallInput}
    {m : Model}
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hadv : madvise_dontneed_b advice = true)
    (Hlen : w_is0 len = true) :
    madvise_spec addr len advice i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  simp [madvise_spec, Halign, Hadv, Hlen, ret_only, pure]

/-- A PAGE-ROUNDED END AT OR ABOVE 2^64 IS -EINVAL: the two wrapping
    refusals of `is_valid_madvise` in one test, exactly as the header
    argues. -/
private theorem wrapCheck {addr len advice : word} {i : SyscallInput} {m : Model}
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hadv : madvise_dontneed_b advice = true)
    (Hlen : w_is0 len = false)
    (Hbound : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)) :
    madvise_spec addr len advice i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [madvise_spec, Halign, Hadv, Hlen, Hbound, err_ret, ret_only, pure]

/-! ### The arm shapes at the concrete model -/

-- The concrete arm checks need a deeper recursion budget than the default:
-- the `decide` hypotheses are closed `BitVec`/`Int` computations, and
-- unifying the instantiated arm lemmas with the goal runs through them.
section
set_option maxRecDepth 1000000

/-- THE SUCCESS ARM: a page-aligned range inside the one live anonymous
    mapping answers 0, declares the whole page-rounded range zero-filled,
    and lands on `madvise_dontneed_next` — the mapping still there, the
    pages inside the range given back. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 4) demoInput demoModel
      (.ok
        (mkEffect (BitVec.ofInt 64 0) []
          [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)])
        (madvise_dontneed_next demoModel (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 0x1000)) []) := by
  refine armCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- A RANGE THE LEDGER DOES NOT OWN DECLINES rather than answering the
    walk's -ENOMEM: the arguments pass every gate, but the range runs past
    the mapping's end. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x4000)
      (BitVec.ofInt 64 4) demoInput demoModel .unmodeled := by
  refine declineCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- …and so does an unknown advice value at an aligned address: the
    kernel's configuration-dependent switch may reject it, so the arm
    cannot answer -EINVAL (see the header). -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 99) demoInput demoModel .unmodeled := by
  simp [madvise_spec, madvise_dontneed_b, page_size, MADV_DONTNEED, unmodeled]

/-- A misaligned address is -EINVAL for a KNOWN advice value… -/
example :
    madvise_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 4) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- …and for an UNKNOWN one: alignment is tested first, so the errno does
    not depend on the advice at all. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 99) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- Zero length answers 0 with an empty effect. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 4) demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  refine zerolenCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_
  · decide
  · decide
  · decide

/-- A length of 2^64 - 1 rounds to 2^64: -EINVAL at a page-aligned
    address. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 4) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine wrapCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide

/-- …and a rounded end landing EXACTLY on 2^64 is -EINVAL too — the
    kernel's `start + len < start` after wrapping. -/
example :
    madvise_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFF000)
        (BitVec.ofInt 64 4) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine wrapCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide

/-- The errno really is the kernel's number in the return word, and the
    answered return really is a zero word. -/
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end

end LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
