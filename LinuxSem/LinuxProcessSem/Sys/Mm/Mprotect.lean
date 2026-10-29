/-
  * LinuxProcessSem.Sys.Mm.Mprotect — mprotect (226)


  This file answers to Linux [mm/mprotect.c]: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines the
  syscall.  [Specs.v] carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.  [Specs.v]
  holds the dispatcher and re-exports this module; see that file's header
  for the representation and fail-closed conventions every spec here
  follows.

  mprotect: ENOMEM only, and only on the branch that turns an inaccessible
  range read-write.  Every other failure a real kernel could report is
  either impossible once the argument gates below have passed, or outside
  the modeled syscall surface (Linux v6.18.46, mm/mprotect.c
  [do_mprotect_pkey] / [mprotect_fixup], on riscv64):

  - ENOMEM is genuine: making a range writable can exceed RLIMIT_AS /
    RLIMIT_DATA ([may_expand_vm], mm/mprotect.c:801-803) or the commit
    charge ([security_vm_enough_memory_mm], :807-808), and splitting the VMA
    at the range's edges can fail on the map_count limit or on allocation
    ([vma_modify_flags], mm/vma.c:1682-1705, through [vma_modify], :1665 and
    :1673, calling [split_vma], :587-594, whose [__split_vma] allocates at
    :510-512, :523-524 and :530-532).  None of that is tracked, so it stays
    injectable.

  - EINVAL is UNREACHABLE past the gates.  Every -EINVAL in
    [do_mprotect_pkey] is one of: the PROT_GROWSDOWN|PROT_GROWSUP conflict
    (:876-877), decided by `mprotect_grows_conflict_b` before the spec
    reaches here; the GROWSDOWN/GROWSUP VMA checks (:913-915, :921-923),
    which that gate does NOT cover — `grows` is read at :867 before `prot`
    is masked at :875, so a SINGLE grows bit survives to them — but which
    `mprotect_modeled_b` excludes, since it admits only `prot` equal to
    PROT_READ|PROT_WRITE and any grows bit sends the call to `unmodeled`
    instead; the alignment check (:879-880), decided first as well;
    [arch_validate_prot] (:887-888), which on riscv64 takes the generic
    definition (include/linux/mman.h:106-110) and accepts anything within
    PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM, so it accepts the modeled rw;
    the pkey check (:899-901), dead because
    [SYSCALL_DEFINE3(mprotect)] (mm/mprotect.c:1008-1011) passes pkey = -1
    and riscv64 selects no ARCH_HAS_PKEYS; and [arch_validate_flags]
    (:971-974), also the generic always-true definition on riscv64
    (include/linux/mman.h:119-123, and riscv64 has no
    arch/riscv/include/asm/mman.h to override either hook).
    [mprotect_fixup] returns no -EINVAL at all.

  Two errnos a real kernel CAN still return are deliberately outside the
  modeled surface, rather than silently absorbed:

  - EINTR from [mmap_write_lock_killable] (mm/mprotect.c:892-893) cannot be
    observed by any program.  It comes from [down_write_killable]
    (kernel/locking/rwsem.c:1598-1610), whose wait state is TASK_KILLABLE
    (:1331, :1496), and [signal_pending_state] aborts a TASK_KILLABLE wait
    only on a FATAL signal (include/linux/sched/signal.h:408-416:
    TASK_KILLABLE lacks TASK_INTERRUPTIBLE, so the result is
    [__fatal_signal_pending]).  A fatal signal kills the task before it
    returns to userspace, so the -EINTR never reaches a register the program
    can read.

  - EPERM for an mseal'd VMA ([vma_is_sealed], mm/mprotect.c:766-767,
    defined in mm/vma.h:611-614; v6.12's [can_modify_vma]) is unreachable
    because [mseal] (__NR_mseal, 462) is not in [syscall_spec]'s modeled
    surface, so VM_SEALED is never set on a modeled run.

  An LSM may also fail [security_file_mprotect] (mm/mprotect.c:824), but the
  default hook returns 0 (include/linux/lsm_hook_defs.h:198).
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

namespace LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect

/-! ## The injectable errno set -/

/-- The only errno `mprotect` can produce on the modeled surface.

    ENOMEM is genuine, and only on the branch that turns an inaccessible
    range read-write: see the file header for the kernel citations
    (`may_expand_vm`, the commit charge, and the VMA split) and for why
    every EINVAL is unreachable past the argument gates, why EINTR and EPERM
    are outside the modeled surface, and why the LSM hook never fails here. -/
def mprotect_errnos : List Int := [ENOMEM]

/- =========================================================================
   The argument tests and the four gates

   `mprotect addr len prot`.  Linux decides FOUR things about the arguments
   before it ever looks at the address space, and the spec follows that
   order exactly because the order is behavior — a zero-length call must
   answer 0 for a `prot` the model could not otherwise interpret, a
   grows-conflict must answer -EINVAL even for a `prot` that is otherwise
   fine, and a range whose end wraps must answer -ENOMEM even for a `prot`
   that would itself be -EINVAL.  Linux v6.12, mm/mprotect.c
   [do_mprotect_pkey] (:715, :721-736):

     715  const int grows = prot & (PROT_GROWSDOWN|PROT_GROWSUP);
     721  start = untagged_addr(start);
     723  prot &= ~(PROT_GROWSDOWN|PROT_GROWSUP);
     724  if (grows == (PROT_GROWSDOWN|PROT_GROWSUP))
     725      return -EINVAL;
     727  if (start & ~PAGE_MASK) return -EINVAL;
     729  if (!len) return 0;
     731  len = PAGE_ALIGN(len);
     732  end = start + len;
     733  if (end <= start) return -ENOMEM;

   [untagged_addr] is the identity on riscv64 — only arm64 and x86 override
   it (include/linux/uaccess.h:25-27, arch/arm64/include/asm/memory.h:286,
   arch/x86/include/asm/uaccess_64.h:37) — so the alignment test sees the
   address the program passed.  A zero `len` returns 0 for EVERY `prot` that
   clears the grows conflict, including PROT_EXEC and unknown high bits:
   nothing is mapped, nothing is protected, and the prot word is never
   validated ([arch_validate_prot] is at :735, past the [!len] return).
   The wrap check at :733 sits in that same window, so a wrapping range is
   -ENOMEM for every `prot` too.

   The supported NONEMPTY operation is exactly PROT_READ|PROT_WRITE over one
   tracked anonymous range.  On an already-rw subrange it is a no-op; on one
   contained `vm_noaccess` interval it removes that interval (splitting when
   necessary) and exposes fresh zeroes through `eff_zeros`, provided the
   resulting backing fits `vm_limit`.  Ordinary mappings charge at the
   permission transition; MAP_NORESERVE mappings keep their lazy provenance
   and charge on first data access.  That split is Linux's:
   [mprotect_fixup] (mm/mprotect.c, Linux v6.12) takes the commit charge
   when a private mapping turns writable, but guards it with
   [if (!(oldflags & VM_NORESERVE))], so a range mapped MAP_NORESERVE is
   never charged at the transition.  Unmapped, mixed-protection, image, and
   spanning ranges fail closed.  Every other `prot` is unmodeled at nonzero
   length:

   - PROT_EXEC (bit 2) would make a data page executable.  The model cannot
     fetch from it AT ALL, so answering 0 and letting the source jump into
     the page reports a [MachineFault] for a program that runs fine on
     Linux — [Run.all_traces_error] holds, [Equivalence.equiv]'s escape
     fires, and any target is accepted.  Declining instead makes the call
     [Run.unmodeled_at], which [Equivalence.modeled] rejects.
   - mprotect to PROT_NONE, or dropping 'w'/'r', would require preserving
     arbitrary old contents behind a permission transition.  The bounded
     ledger intentionally supports only zero-backed pages created as
     PROT_NONE by anonymous mmap/MAP_FIXED.

     PROT_READ ALONE is the shape a real allocator reaches for — fill a
     buffer, then downgrade it — so it is worth saying what stops it here
     rather than leaving the reader to conclude the gap is an oversight.
     Linux takes it on the ordinary path — mm/mprotect.c [do_mprotect_pkey]
     / [mprotect_fixup] compute newflags from prot and clear VM_WRITE — so
     the mapping stays live and readable with its contents intact.  What the
     MODEL lacks is anywhere to put such a page.  Anonymous memory has
     exactly one representation, [RiscvSemantics.machine_state]'s writable
     overlay [ms_mem], and that one map answers two different questions: it
     is the only source of readable anonymous bytes
     ([RiscvSemantics.ov_read_bytes] falls back to the loaded segments,
     never to [ms_rom]), and it is the whole of the writable view
     ([RiscvSemantics.wview], hence [RiscvSemantics.store_ok] and the
     [State.in_wmem] gate every spec checks an output buffer against).  So a
     page that is readable and not writable has no encoding: leave the bytes
     in [ms_mem] and the model admits a store Linux answers with SIGSEGV and
     a syscall output buffer Linux answers with -EFAULT; take them out and a
     load Linux serves faults instead — the direction the PROT_EXEC note
     above rejects, since [Run.all_traces_error] then frees the target.
     Modelling it is therefore not a new arm but a new dimension: a channel
     from a [State.SyscallEffect] to the read-only view (nothing else reaches
     [Run.apply_effect]), an [ms_rom] fallback in [RiscvSemantics.ov_read_bytes]
     so a downgraded page still loads, and a ledger beside [State.vm_noaccess]
     so [munmap], [mremap], [brk] and the already-rw branch below decline
     over a downgraded range instead of silently re-exposing it.

   A range that is NOT fully contained in the tracked mappings is
   `unmodeled` rather than the -ENOMEM Linux returns for a start outside
   every VMA (mm/mprotect.c [do_mprotect_pkey]), and that is deliberate: the
   ledger is not a complete picture of the address space, so "absent from
   [vm_maps]" does not entail "absent from every VMA".  The stack is the
   standing counterexample — it carries no entry at all, by the argument at
   [State.alloc_top] — so answering that errno would be a guess wherever the
   model's picture is thinner than Linux's.

   NO 32-bit truncation here, deliberately, and it is not an oversight of
   the kind [Syscall.fd32] fixes: the kernel's own prototype is
   [SYSCALL_DEFINE3(mprotect, unsigned long, start, size_t, len, unsigned
   long, prot)], so `prot` is a full register, and [arch_validate_prot]
   rejects any bit outside PROT_READ|PROT_WRITE|PROT_EXEC|PROT_SEM with
   -EINVAL (mm/mprotect.c:735-736, include/linux/mman.h:108-111).  A `prot`
   with garbage in its high half is therefore a real -EINVAL on Linux at
   nonzero length, and comparing the whole 64-bit word makes it unmodeled
   here — fail closed, which is the safe direction (answering 0 would have
   the model admit a success no kernel produces).  At zero length the same
   garbage is a real 0, which is why the [!len] branch below does not
   consult `prot` at all.
   ========================================================================= -/

/-- The one `prot` the model can answer for at nonzero length: exactly the
    rw permissions its anonymous memory already has.

     `Z.eqb (bv_unsigned prot) (PROT_READ + PROT_WRITE)` becomes
    `(prot.toNat : Int) == PROT_READ + PROT_WRITE` — the port's standing
    `bv_unsigned`/`Z.eqb` translation. -/
def mprotect_modeled_b (prot : word) : Bool :=
  (prot.toNat : Int) == PROT_READ + PROT_WRITE

/-- Both stack-extension modifiers at once — the ONE argument error the
    modeled surface takes from `prot`'s grows bits (mm/mprotect.c:715,
    :724-725, "can't be both").  Either one alone is legal, and both are
    masked out of `prot` (:723) either way; only the pair is -EINVAL, and a
    lone bit goes on to gate the vma checks at :757 and :767.

     Lean core has no `Int.land`, so the `Z.land` of
    `Uapi.z_land` is used (it is the port's existing `Z.land` — `bv_unsigned
    prot` is nonnegative, so the `Nat` land agrees). -/
def mprotect_grows_conflict_b (prot : word) : Bool :=
  !((z_land (prot.toNat : Int) PROT_GROWSDOWN) == 0) &&
  !((z_land (prot.toNat : Int) PROT_GROWSUP) == 0)

 /- =========================================================================
    The post-state and the protected-ledger lemma
    ========================================================================= -/

/-- Expose one protected range while carrying MAP_NORESERVE provenance and
    already-materialized pages across unchanged.  The post-state budget test
    therefore charges an ordinary mapping now, but leaves a lazy mapping to
    first-touch accounting.

    Only `vm_noaccess` moves: `vm_reserved`, `vm_maps`, the break, the
    budget, the placement base and the initial stack pointer are rebuilt
    from `m` unchanged. -/
def mprotect_model_next (m : Model) (addr n : word) : Model :=
  let h := m_vmmaps m
  with_vmmaps
    (VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
      (maps_subtract h.vm_noaccess
         (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
      h.vm_start_brk h.vm_brk h.vm_limit
      h.vm_mmap_base h.vm_init_sp) m

/-- The protected list only SHRINKS here — exposing a range cuts it out — so
    the ledger goes on naming real bytes.  This is `mprotect`'s share of the
    obligation the section in [Mm/Mmap.v] sets out; see
    [State.entries_nonzero] for why the property is worth having and
    [Madvise.madvise_noaccess_decline_names_a_protected_byte] for who reads
    it. -/
theorem mprotect_model_next_noaccess_nonzero (m : Model) (addr n : word)
    (H : vm_noaccess_entries_nonzero (m_vmmaps m)) :
    vm_noaccess_entries_nonzero (m_vmmaps (mprotect_model_next m addr n)) := by
  unfold vm_noaccess_entries_nonzero at *
  -- `mprotect_model_next` rebuilds the record, so `m_vmmaps` of the result is
  -- the rebuilt record and its `vm_noaccess` is the `maps_subtract`; both
  -- projections are definitional, so the lemma applies directly.
  exact maps_subtract_nonzero (m_vmmaps m).vm_noaccess
    (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) H

/-- The post-state budget test: the exposure's backing must fit `vm_limit`.
    `vm_backing_within_limit` reads the whole `Model` (sparse provenance and
    first-touch charges live in `VmState`), which is why the gate is stated
    on `mprotect_model_next` rather than on a reconstructed byte total. -/
def mprotect_budget_ok (m : Model) (addr n : word) : Bool :=
  vm_backing_within_limit (mprotect_model_next m addr n)

/-! ## The specification -/

/-- `mprotect addr len prot` (226).

    FOUR argument gates, in the kernel's order (`do_mprotect_pkey`,
    :715-736 — see the block above), then the address-space decision:

    - both grows bits set is -EINVAL, whatever else `prot` holds;
    - a misaligned `addr` is -EINVAL;
    - `len = 0` answers 0 — for EVERY `prot`, which is why this gate
      precedes the prot test;
    - a page-rounded end at or above 2^64 is -ENOMEM, also for every
      `prot`;
    - then, and only then, `prot` is read: exactly PROT_READ|PROT_WRITE is
      modeled, everything else declines at nonzero length.

    THE FOURTH GATE, and it too precedes any reading of `prot`
    (mm/mprotect.c:731-734, before [arch_validate_prot] at :735):

        731  len = PAGE_ALIGN(len);
        732  end = start + len;
        733  if (end <= start) return -ENOMEM;

    `start`, `len` and `end` are all 64 bits wide on riscv64
    ([do_mprotect_pkey]'s `unsigned long` / `size_t`), so `end` is the
    WRAPPED sum and `end <= start` is precisely "the sum reached 2^64" —
    which is what this test says in `Int`.  The two ways to reach it agree:
    a `len` in the top 4095 values makes C's own PAGE_ALIGN wrap to 0,
    leaving `end == start`, and `page_round_up_Z` (exact in `Int`) answers
    2^64 there, so `addr + nZ >= 2^64` holds for every `addr`.  Below the
    gate `len ≠ 0` already holds, so `nZ >= 4096` and the sum can never be
    `<= start` any other way.

    This REPLACES a narrower `two_pow_64 <=? nZ` test that fired only when
    the page rounding alone overflowed: `mprotect(2^63, 2^63, rw)` rounds to
    `nZ = 2^63`, passed that test, and reached the containment gate to be
    answered `unmodeled` — where Linux wraps `end` to 0 and returns -ENOMEM.

    PASSING THIS GATE IS WHAT KEEPS THE ARITHMETIC BELOW HONEST, and the old
    test's real job: `bv_unsigned addr + nZ < 2^64` with `bv_unsigned addr >=
    0` gives `nZ < 2^64`, so `Z_to_bv 64 nZ` cannot wrap; and it bounds the
    SUM as well, so the whole range fits the address space and the
    `(addr, n)` pair below names the range asked for.  The narrower test
    bounded only `nZ` and left that sum free: at `addr = 2^63`, `nZ = 2^63`
    the range's end reaches 2^64 exactly, and any `word` reconstruction of
    it lands on 0.  Nothing reachable hit that (the containment gate rejects
    such a range first), but the bound is now structural rather than
    incidental — and the end handed to `maps_subtract` is carried in `Int`,
    so no reconstruction happens in the first place.

    THE ANSWERED SHAPE.  A range contained in ONE tracked `vm_noaccess`
    interval AND in ONE tracked `vm_maps` entry is exposed: the effect
    zero-fills the whole page-rounded range and returns 0, the post-state
    cuts the range out of `vm_noaccess`, and the only failure the branch
    admits is an injected -ENOMEM (from `mprotect_errnos`) or the
    `mprotect_budget_ok` gate. -/
def mprotect_spec (addr len prot : word) : SysSpec SyscallEffect :=
  if mprotect_grows_conflict_b prot then err_ret EINVAL
  else if !(((addr.toNat : Int) % page_size) == 0) then err_ret EINVAL
  else if w_is0 len then ret_only (BitVec.ofInt 64 0)
  /- The fourth gate, and it too precedes any reading of `prot`
     (mm/mprotect.c:731-734, before [arch_validate_prot] at :735); see the
     docstring above for why the sum is taken in `Int` and why that is what
     keeps `Z_to_bv 64 nZ` lossless below. -/
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    err_ret ENOMEM
  else if mprotect_modeled_b prot then
    bind getModel fun m =>
      let h := m_vmmaps m
      let nZ := page_round_up_Z (len.toNat : Int)
      let n := BitVec.ofInt 64 nZ
      /- The `vm_maps` conjunct is what makes this branch sound on its own,
         including during the documented same-page brk-shrink state where a
         physical `vm_noaccess` tail may extend past byte-granular `vm_maps`
         (State.v, purpose (c)).  Linux answers -ENOMEM, not 0, for a range
         that starts outside every VMA (mm/mprotect.c:753, :765-766), so
         without it a ledger violating the invariant would have the model
         return 0 AND zero-fill unmapped memory.

         `vm_noaccess ⊆ vm_maps` is NOT an invariant of reachable states, so
         the conjunct is not implied and it does change the answer: the
         same-page brk-shrink state above is reachable, and an rw `mprotect`
         of that page names a range `vm_noaccess` contains and `vm_maps`
         does not.  [noaccess_vm.c]'s [brk-samepage-protect] mode reaches
         exactly that state and is the only case in the conformance suite
         that fails when the conjunct is dropped.  Nothing in the tree
         states the containment, and nothing should. -/
      if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
        alt
          (bind (errno_from mprotect_errnos) fun e => err_ret e)
          (bind (choose fun (_ : Unit) => mprotect_budget_ok m addr n = true) fun _ =>
            bind (modify fun _ => mprotect_model_next m addr n) fun _ =>
              pure (mkEffect (BitVec.ofInt 64 0) [] [(addr, n)]))
      /- An already-rw range CANNOT fail: [mprotect_fixup] short-circuits on
         [newflags == oldflags] (mm/mprotect.c:617-620) before [may_expand_vm]
         (:649), the commit charge (:655) and [vma_modify_flags] (:664), so
         there is no split, no map_count check and no accounting to fail.
         The equality holds even for a strict subrange, because [newflags] is
         computed from `prot` and the VMA's own flags rather than from the
         range (:801-805; VM_FLAGS_CLEAR is 0 on riscv64 —
         include/linux/mm.h:486-490, include/linux/pkeys.h:16).  Neither
         -EACCES fires either: [do_mmap] sets VM_MAYREAD|VM_MAYWRITE|VM_MAYEXEC
         unconditionally (mm/mmap.c:347-348) so :807-811 cannot trip, and
         :813-816 needs VM_EXEC in [newflags] (include/linux/mman.h:201-220),
         which rw does not set.  -EAGAIN does not exist on this path. -/
      else if map_contains h.vm_maps addr n && region_free h.vm_noaccess addr n then
        ret_only (BitVec.ofInt 64 0)
      else unmodeled
  else unmodeled

/- =========================================================================
   THE BUDGET MARK for mprotect (see [Mmap.brk_budget_refused_b] for what a
   mark is)
   ========================================================================= -/

/-- The one charging branch is the exposure of a PROT_NONE range inside a
    live mapping, gated by `mprotect_budget_ok` on the post-state; its
    `choose` is over `unit`, so the gate reads nothing but the request and
    the pre-state and the mark is exact.  The four argument gates, the
    already-rw no-op and the unmodeled shapes never fire it. -/
def mprotect_budget_refused_b (addr len prot : word) (m : Model) : Bool :=
  if mprotect_grows_conflict_b prot then false
  else if !(((addr.toNat : Int) % page_size) == 0) then false
  else if w_is0 len then false
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    false
  else if mprotect_modeled_b prot then
    let h := m_vmmaps m
    let nZ := page_round_up_Z (len.toNat : Int)
    let n := BitVec.ofInt 64 nZ
    if map_contains h.vm_noaccess addr n && map_contains h.vm_maps addr n then
      !(mprotect_budget_ok m addr n)
    else false
  else false

/- =========================================================================
   Sanity checks

   There is no closed computation to re-use in this file; the checks
   below pin what the header argues for and what the spec computes:

   - the `prot` test: rw (3) is the one modeled value; PROT_NONE (0),
     PROT_READ (1), rwx (7) and a `prot` whose high half is garbage are not;
   - the grows-bits test: only the PAIR is a conflict, and a lone bit is
     none (it declines later, in the `prot` test — the header's point that
     `mprotect_modeled_b` excludes it);
   - the page-range refusal: a length whose rounding reaches 2^64 is at the
     bound, and a page-rounded end landing exactly on 2^64 is too;
   - the post-state: the exposed range leaves `vm_noaccess`, and `vm_maps`,
     the budget and the break do not move;
   - the four argument gates and their ORDER, at the concrete model:
     -EINVAL for a misaligned address and for both grows bits, 0 for a zero
     length even with a `prot` nothing else would interpret, -ENOMEM for a
     wrapping range even with such a `prot`, and `unmodeled` for PROT_NONE
     at nonzero length (the "unmap-shaped" downgrade the model cannot
     represent — its PROT_NONE ledger entry is what the rw arm EXPOSES, in
     the success check below);
   - the answered shapes: the exposure (0, whole page-rounded range
     zero-filled, `vm_noaccess` cut), the already-rw no-op, and the decline
     for a range the ledger does not own;
   - the budget mark: `true` only on the exposure arm whose post-state
     exceeds the budget, `false` on every other shape.

   The spec is a RELATION, not a function, so an arm is not a `by decide`
   equality.  The arm lemmas state each shape once over symbolic arguments
   and the examples instantiate them, discharging the gate hypotheses with
   `decide`: symbolically the `if`-conditions are built from the variables
   the hypotheses name, whereas at the concrete `BitVec.ofInt`/`toNat`
   literals `simp` cannot normalize them syntactically (the kernel can,
   which is what `decide` uses).
   ========================================================================= -/

/-! ### The `prot` and grows-bit tests -/

/-- PROT_READ|PROT_WRITE is the one modeled `prot`… -/
example : mprotect_modeled_b (BitVec.ofInt 64 3) = true := by decide

/-- …and nothing else is: PROT_NONE (the unmap-shaped downgrade), PROT_READ
    alone (the allocator's shape the header argues about), PROT_EXEC, and
    an rw word with garbage in its high half. -/
example : mprotect_modeled_b (BitVec.ofInt 64 PROT_NONE) = false := by decide
example : mprotect_modeled_b (BitVec.ofInt 64 PROT_READ) = false := by decide
example : mprotect_modeled_b (BitVec.ofInt 64 (PROT_WRITE)) = false := by decide
example : mprotect_modeled_b (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + 4)) = false :=
  by decide
example : mprotect_modeled_b (BitVec.ofInt 64 0x100000003) = false := by decide

/-- The grows bits: the PAIR is the one argument error, each alone is
    legal. -/
example :
    mprotect_grows_conflict_b (BitVec.ofInt 64 (PROT_GROWSDOWN + PROT_GROWSUP)) =
      true := by decide
example :
    mprotect_grows_conflict_b
      (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN + PROT_GROWSUP)) =
      true := by decide
example :
    mprotect_grows_conflict_b (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN)) =
      false := by decide
example :
    mprotect_grows_conflict_b (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSUP)) =
      false := by decide
example : mprotect_grows_conflict_b (BitVec.ofInt 64 3) = false := by decide

/-- The page-range refusal, exactly as `do_mprotect_pkey` computes it in
    `Int`: a length whose rounding reaches 2^64, and a page-rounded end
    landing exactly on 2^64, are both at the bound. -/
example : page_round_up_Z (0xFFFFFFFFFFFFFFFF : Int) = two_pow_64 := by decide
example : two_pow_64 ≤ (0x1000 : Int) + page_round_up_Z 0xFFFFFFFFFFFFFFFF := by
  decide
example : two_pow_64 ≤ (0x1000 : Int) + page_round_up_Z 0xFFFFFFFFFFFFF000 := by
  decide
example : ¬ two_pow_64 ≤ (0x1000 : Int) + page_round_up_Z 0x1000 := by decide

/-! ### A ledger and a model the arm checks run over -/

/-- ONE live anonymous mapping `[0x1000, 0x4000)`, nothing protected.
    Nothing is reserved, the break sits at 0, and the budget is 1 MiB. -/
private def demoVm : VmMaps :=
  mkVmMaps [] [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x3000)]
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000

/-- The same ledger with its first page, `[0x1000, 0x2000)`, recorded as
    PROT_NONE in `vm_noaccess`: the exposure's shape. -/
private def demoProtectedVm : VmMaps :=
  { demoVm with
    vm_noaccess := [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)] }

/-- The model the arm checks run in: that ledger, no lazy reservation and
    no materialized page. -/
private def demoModel : Model :=
  mkModel [] demoProtectedVm IEof []

/-- The same model with the budget spent, so the exposure's post-state does
    not fit `vm_limit`: the budget mark's charging case. -/
private def demoBrokeModel : Model :=
  mkModel [] { demoProtectedVm with vm_limit := 0 } IEof []

/-- A syscall input for `mprotect` (226).  The spec reads none of it; it is
    here because a `SysSpec` is a relation on an input as well as a model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 226, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-! ### The post-state: the PROT_NONE range is cut out, nothing else moves -/

/-- Exposing `[0x1000, 0x2000)` removes the whole `vm_noaccess` entry — the
    ledger's PROT_NONE range is "unmapped" from the protected list. -/
example :
    (m_vmmaps (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000))).vm_noaccess = [] := by decide

/-- …and leaves `vm_maps`, the budget and the break exactly as they were. -/
example :
    (m_vmmaps (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000))).vm_maps = demoProtectedVm.vm_maps := by decide
example :
    (m_vmmaps (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000))).vm_limit = demoProtectedVm.vm_limit := by decide
example :
    (m_vmmaps (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x1000))).vm_brk = demoProtectedVm.vm_brk := by decide

/-- A SUBRANGE splits: exposing the first half of the entry keeps the second
    half protected — `maps_subtract`'s remnant, the reason the definition is
    not a delete. -/
example :
    (m_vmmaps (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x800))).vm_noaccess =
      [(BitVec.ofInt 64 0x1800, BitVec.ofInt 64 0x800)] := by decide

/-- The budget gate passes on the demo model… -/
example : mprotect_budget_ok demoModel (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 0x1000) = true := by decide

/-- …and fails once the budget is spent (the exposure's post-state charges
    the backing). -/
example : mprotect_budget_ok demoBrokeModel (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 0x1000) = false := by decide

/-! ### The arm shapes, stated once over symbolic arguments -/

/-- THE EXPOSURE ARM: past all five gates, over a range contained in one
    `vm_noaccess` interval and one `vm_maps` entry, the spec reads the
    model, offers the injected errno, and on the `choose` branch moves to
    `mprotect_model_next` and returns 0 with the whole page-rounded range
    zero-filled and no event.  (The `alt` means this is ONE of the admitted
    outcomes; the injected -ENOMEM is the other.)

    The page-rounded length is taken as `n`, with `Hnz` naming the term the
    spec computes, so the lemma applies where the caller already has the
    word in hand. -/
private theorem exposeCheck {addr len prot n : word} {i : SyscallInput} {m : Model}
    (Hnz : n = BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hmod : mprotect_modeled_b prot = true)
    (Hn : map_contains (m_vmmaps m).vm_noaccess addr n = true)
    (Hm : map_contains (m_vmmaps m).vm_maps addr n = true)
    (Hbudget : mprotect_budget_ok m addr n = true) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [(addr, n)])
        (mprotect_model_next m addr n) []) := by
  subst Hnz
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, Hmod, Hn, Hm,
    bind_getModel, alt]
  refine Or.inr ?_
  -- `bind`'s `ok` case, spelled out: the `choose` picks `()`, moves nothing,
  -- emits nothing; the continuation modifies and returns.
  refine ⟨(), m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ _ _ _ Hbudget
  · refine
      ⟨(), mprotect_model_next m addr
          (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))), [], [], ?_, ?_, rfl⟩
    · exact modify_ok _ _ _
    · exact pure_ok _ _ _

/-- THE INJECTED -ENOMEM: the other side of the `alt`.  The exposure branch
    is genuinely injectable — `mprotect_errnos` is nonempty — so a caller
    may see the errno with the state untouched. -/
private theorem injectCheck {addr len prot n : word} {i : SyscallInput} {m : Model}
    (Hnz : n = BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hmod : mprotect_modeled_b prot = true)
    (Hn : map_contains (m_vmmaps m).vm_noaccess addr n = true)
    (Hm : map_contains (m_vmmaps m).vm_maps addr n = true) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (errno_ret ENOMEM) [] []) m []) := by
  subst Hnz
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, Hmod, Hn, Hm,
    bind_getModel, alt]
  refine Or.inl ?_
  refine ⟨ENOMEM, m, [], [], ?_, ?_, rfl⟩
  · exact ⟨ENOMEM, by simp [mprotect_errnos], rfl⟩
  · exact pure_ok _ i m

/-- THE ALREADY-RW NO-OP: a range inside a live `vm_maps` entry and clear of
    `vm_noaccess` answers 0 with an empty effect and does not touch the
    state. -/
private theorem noopCheck {addr len prot : word} {i : SyscallInput} {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hmod : mprotect_modeled_b prot = true)
    (Hn : map_contains (m_vmmaps m).vm_noaccess addr
        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false)
    (Hmaps : map_contains (m_vmmaps m).vm_maps addr
        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true)
    (Hfree : region_free (m_vmmaps m).vm_noaccess addr
        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, Hmod, Hn,
    Hmaps, Hfree, bind_getModel, ret_only, pure]

/-- THE DECLINE PAST THE GATES: every argument gate passes but the range is
    not inside a live mapping, so the call is `unmodeled` — no state change
    and no errno, because a hole names both at once (see the header). -/
private theorem declineCheck {addr len prot : word} {i : SyscallInput} {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hmod : mprotect_modeled_b prot = true)
    (Hn : map_contains (m_vmmaps m).vm_noaccess addr
        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false)
    (Hmaps : map_contains (m_vmmaps m).vm_maps addr
        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false) :
    mprotect_spec addr len prot i m .unmodeled := by
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, Hmod, Hn,
    Hmaps, bind_getModel, unmodeled]

/-! ### The argument gates, in the kernel's order -/

/-- A MISALIGNED ADDRESS IS -EINVAL, and this check needs no hypothesis on
    `prot`: alignment is decided after the grows conflict and before the
    prot word is read. -/
private theorem misalignedCheck {addr len prot : word} {i : SyscallInput}
    {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : ((addr.toNat : Int) % page_size == 0) = false) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [mprotect_spec, Hgrows, Halign, err_ret, ret_only, pure]

/-- BOTH GROWS BITS ARE -EINVAL, before anything else — even for an
    otherwise-legal rw `prot` and a wrapping length. -/
private theorem growsConflictCheck {addr len prot : word} {i : SyscallInput}
    {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = true) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp [mprotect_spec, Hgrows, err_ret, ret_only, pure]

/-- ZERO LENGTH ANSWERS 0 — for EVERY `prot` that clears the grows conflict,
    including PROT_NONE and a garbage high half, because the `[!len]` return
    precedes `arch_validate_prot`. -/
private theorem zerolenCheck {addr len prot : word} {i : SyscallInput}
    {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = true) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  simp [mprotect_spec, Hgrows, Halign, Hlen, ret_only, pure]

/-- A PAGE-ROUNDED END AT OR ABOVE 2^64 IS -ENOMEM — for every `prot`, since
    the wrap check also precedes `arch_validate_prot`. -/
private theorem wrapCheck {addr len prot : word} {i : SyscallInput} {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)) :
    mprotect_spec addr len prot i m
      (.ok (mkEffect (errno_ret ENOMEM) [] []) m []) := by
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, err_ret, ret_only, pure]

/-- A `prot` THE MODEL DOES NOT ANSWER — PROT_NONE, PROT_READ alone,
    PROT_EXEC — declines at nonzero length rather than inventing a
    permission transition. -/
private theorem unmodeledProtCheck {addr len prot : word} {i : SyscallInput}
    {m : Model}
    (Hgrows : mprotect_grows_conflict_b prot = false)
    (Halign : (addr.toNat : Int) % page_size = 0)
    (Hlen : w_is0 len = false)
    (Hbound : ¬ two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int))
    (Hmod : mprotect_modeled_b prot = false) :
    mprotect_spec addr len prot i m .unmodeled := by
  simp [mprotect_spec, Hgrows, Halign, Hlen, Hbound, Hmod, unmodeled]

/-! ### The argument gates at the concrete model -/

/-- A misaligned address is -EINVAL for a modeled rw `prot`. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_ ?_
  · decide
  · decide

/-- …and for a PROT_NONE one: the errno does not depend on `prot` at all. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 PROT_NONE) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_ ?_
  · decide
  · decide

/-- Both grows bits are -EINVAL even for an rw `prot` over an aligned,
    in-range request. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN + PROT_GROWSUP))
        demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine growsConflictCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- …and it still is for a WRAPPING length: the grows gate comes first, so
    the errno is -EINVAL and not -ENOMEM. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN + PROT_GROWSUP))
        demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine growsConflictCheck (i := demoInput) (m := demoModel) ?_
  decide

/-- A LONE grows bit is NOT a conflict: it passes the first gate and is then
    excluded by the `prot` test, so the call declines. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN))
        demoInput demoModel .unmodeled := by
  refine unmodeledProtCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Zero length answers 0 — with PROT_NONE as `prot`, which nothing else
    would interpret. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 PROT_NONE) demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  refine zerolenCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_
  · decide
  · decide
  · decide

/-- …even at a MISALIGNED address: `[!len]` is tested after the alignment
    gate on Linux (:729), and here too, so this is -EINVAL and not 0. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 PROT_NONE) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  refine misalignedCheck (i := demoInput) (m := demoModel) ?_ ?_
  · decide
  · decide

/-- A length of 2^64 - 1 rounds to 2^64: -ENOMEM at a page-aligned address. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok (mkEffect (errno_ret ENOMEM) [] []) demoModel []) := by
  refine wrapCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide

/-- …and it is -ENOMEM even for a `prot` the model would otherwise refuse —
    the wrap gate comes before the prot word is read. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 0x100000003) demoInput demoModel
      (.ok (mkEffect (errno_ret ENOMEM) [] []) demoModel []) := by
  refine wrapCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide

/-- A page-rounded end landing EXACTLY on 2^64 is -ENOMEM too — the kernel's
    `start + len < start` after wrapping. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFF000)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok (mkEffect (errno_ret ENOMEM) [] []) demoModel []) := by
  refine wrapCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide

/-! ### The answered and declined shapes at the concrete model -/

-- The concrete arm checks need a deeper recursion budget than the default:
-- the `decide` hypotheses are closed `BitVec`/`Int` computations, and
-- unifying the instantiated arm lemmas with the goal runs through them.
section
set_option maxRecDepth 1000000

/-- THE SUCCESS ARM: a page-aligned range covering the PROT_NONE page, asked
    for at rw, answers 0, declares the whole page-rounded range zero-filled,
    and lands on `mprotect_model_next` — the mapping still there, the
    protected interval cut out. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok
        (mkEffect (BitVec.ofInt 64 0) []
          [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)])
        (mprotect_model_next demoModel (BitVec.ofInt 64 0x1000)
          (BitVec.ofInt 64 0x1000)) []) := by
  refine exposeCheck (n := BitVec.ofInt 64 0x1000)
    (addr := BitVec.ofInt 64 0x1000) (len := BitVec.ofInt 64 0x1000)
    (prot := BitVec.ofInt 64 3) (i := demoInput) (m := demoModel)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- THE INJECTED -ENOMEM on that same call: the `alt`'s other arm, with the
    state untouched. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok (mkEffect (errno_ret ENOMEM) [] []) demoModel []) := by
  refine injectCheck (n := BitVec.ofInt 64 0x1000)
    (addr := BitVec.ofInt 64 0x1000) (len := BitVec.ofInt 64 0x1000)
    (prot := BitVec.ofInt 64 3) (i := demoInput) (m := demoModel)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- THE ALREADY-RW NO-OP: `[0x2000, 0x3000)` lies inside the live mapping and
    clear of the protected page, so it answers 0 with an empty effect. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  refine noopCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- A RANGE THE LEDGER DOES NOT OWN DECLINES rather than answering the
    kernel's -ENOMEM: the arguments pass every gate, but the range runs past
    the mapping's end. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x4000)
        (BitVec.ofInt 64 3) demoInput demoModel .unmodeled := by
  refine declineCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

/-- PROT_NONE AT NONZERO LENGTH DECLINES: the unmap-shaped downgrade would
    require preserving arbitrary contents behind a permission transition, so
    the model does not answer it — and it does not answer 0 either. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 PROT_NONE) demoInput demoModel .unmodeled := by
  refine unmodeledProtCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- PROT_READ ALONE declines too, for the reason the header argues: the
    model has no readable-but-not-writable page. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 PROT_READ) demoInput demoModel .unmodeled := by
  refine unmodeledProtCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- PROT_EXEC declines: the model cannot fetch the page at all, so answering
    0 would free the target on `Run.all_traces_error` (see the header). -/
example :
    mprotect_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + 4)) demoInput demoModel
      .unmodeled := by
  refine unmodeledProtCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

/-- A `prot` WITH GARBAGE IN ITS HIGH HALF declines (fail closed): Linux
    would answer -EINVAL through `arch_validate_prot`, and the model never
    answers 0. -/
example :
    mprotect_spec (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x100000003) demoInput demoModel .unmodeled := by
  refine unmodeledProtCheck (i := demoInput) (m := demoModel) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide

end

/-! ### The budget mark -/

/-- The mark fires on the one charging branch when the post-state does not
    fit: here the demo model's budget is spent. -/
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 3) demoBrokeModel = true := by decide

/-- …and it does not fire when the exposure fits. -/
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 3) demoModel = false := by decide

/-- The already-rw no-op never fires it, whatever the budget: no `choose`
    guards that arm. -/
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 3) demoBrokeModel = false := by decide

/-- The argument gates never fire it, even with the budget spent. -/
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 3) demoBrokeModel = false := by decide
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
      (BitVec.ofInt 64 3) demoBrokeModel = false := by decide
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
      (BitVec.ofInt 64 3) demoBrokeModel = false := by decide

/-- …and neither does an unmodeled `prot`: PROT_NONE at nonzero length is
    never charged. -/
example :
    mprotect_budget_refused_b (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 PROT_NONE) demoBrokeModel = false := by decide

/-- The errnos really are the kernel's numbers in the return word, and the
    answered return really is a zero word. -/
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : errno_ret ENOMEM = BitVec.ofInt 64 (-12) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
