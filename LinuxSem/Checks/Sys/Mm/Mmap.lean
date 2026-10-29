/-
  * LinuxProcessSem.Checks.Sys.Mm.Mmap — the brk (214), mmap (222), munmap (215) checkers, and their proofs

  Answers to Linux [mm/mmap.c]: this file
  holds the checkers for the syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher and the four top-level
  theorems and re-exports this module. The checkers here are executable,
  and their proofs relate them to the relational specs in the matching
  [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous constructor
  pattern `⟨r, [], zs, us, cs, []⟩` over `SyscallEffect` (`State.lean`).

  The wrap test is the `Prop` `two_pow_64 ≤ …` — the same inequality
  `Sys/Mm/Mprotect.lean`'s `mprotect_spec` states — as are the three Prop
  gates `¬ (addr + nZ ≤ alloc_top h)`, `¬ (0 < addr)` and the `region_free`
  conjunction.

  Each branch's `choose` guard mixes `Z` comparisons with `Bool` calls; the
  `Z` conjuncts are `decide (…)` and the `Bool` ones stand as they are, so
  `Bool.and_eq_true` + `decide_eq_true_eq` recover exactly the spec's
  conjunction — the same tactic `Checks/Sys/Mm/Mremap.lean` uses.

  Each proof peels the spec's model reader with `bind_getModel`, which
  rewrites `bind getModel k i m o` to `k m i m o` in one go (see
  `Checks/Sys/Mm/Mprotect.lean` for the same idiom).  A `Bool` gate is
  `by_cases` plus `rw [ite_eq_left h]` / `rw [ite_eq_right h]`, `dsimp only` performs
  the beta/iota/zeta reduction, and a `CheckX = CheckY` equation is
  eliminated by `nomatch`.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap

namespace LinuxSem.Checks.Sys.Mm.Mmap

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Sys.Prelude

-- The checkers' last arms are `match`es on the effect nested under long
-- `if` chains, and the proofs below drive the same tree on both sides —
-- the spec's and the checker's — so the default recursion budget is not
-- enough to unify the instantiated arms (and `bind_getModel` at a large
-- continuation exceeds it on its own).  The same option guards the
-- analogous proofs in `Checks/Sys/Mm/Mprotect.lean` and `Mremap.lean`.
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-! ## brk (214) -/

/-- The `brk` (214) checker.

    The spec answers `brk_spec req` with the environment's choice of
    resolution `r` (`brk_r_ok m req r`), and then emits that resolution's
    zero-fill and unmap ledgers and steps the model with
    `with_brk_next m req r`.  So an accepted effect is exactly

      `⟨r, [], brk_zeros req r (vm_brk h), brk_unmaps r (vm_brk h), [], []⟩`

    at `with_brk_next m req r` with no events, and `r` must pass
    `brk_r_ok`.  Everything else — a write, copy or copy-in ledger, or a
    ledger that is not the computed one — is `CheckReject`: the spec
    emits no such event. -/
def check_brk (req : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨r, [], zs, us, [], []⟩ =>
      if brk_r_ok m req r &&
          listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk) &&
          listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)
      then .CheckOk (with_brk_next m req r) []
      else .CheckReject
  | _ => .CheckReject

/-! ## mmap (222) -/

-- The `fd` argument is part of the ABI but no arm reads it (see the note
-- on the definition), so the unused-variable linter is off here.
section

set_option linter.unusedVariables false

/-- The `mmap` (222) checker.

    Gate for gate the spec's argument tests (`mmap_off_aligned_b`, the
    `mmap_pglen_ok_b` -EINVAL, the `mmap_anon_b` decline, a zero `len` in
    the plain anonymous shape), each answered with the same `err_ret`,
    then one arm per modeled shape:

    - the hint-placed rw grant (`mmap_modeled_b`): an injected errno with
      no ledger, or the grant at an address the placement guard accepts,
      with the zero ledger `[(r, n)]` and post-state `with_mmap_backing`;
    - the PROT_NONE reservation (`mmap_noaccess_b`): the same, with the
      unmap ledger and the request added to `vm_noaccess`;
    - the four `MAP_FIXED` shapes (`mmap_fixed_noaccess_b`,
      `mmap_fixed_rw_b`, `mmap_noreplace_noaccess_b`,
      `mmap_noreplace_rw_b`): the shared argument gate (a wrapping length
      is -ENOMEM, `¬ (addr + nZ ≤ alloc_top)` is `CheckUnmodeled`, a
      misaligned address is -EINVAL, address 0 is `CheckUnmodeled`), then
      the ledger split the spec makes, with one effect shape per
      resolution it offers.

    The ledger's three-way split for the `MAP_FIXED` pair is the spec's:
    the request inside one live mapping (`region_free vm_reserved &&
    map_contains vm_maps`) admits an errno with the range preserved, the
    replacement, or an errno with the range destroyed; a request clear of
    both ledgers admits the errno or the fresh reservation; and a request
    that meets live mappings without being inside one admits the errno,
    the spanning replacement, or the destroyed errno.  A request meeting
    `vm_reserved` is `CheckUnmodeled`, exactly where the spec declines.

    `MAP_FIXED_NOREPLACE` splits only once: free range → the fresh
    reservation; occupied range → -EEXIST beside the environment errno.

    `fd` is carried because the ABI hands it to the syscall, not because
    any arm reads it — Linux does not either (see [Mmap.mmap_fd_none]),
    the same note `Sys/Mm/Mmap.lean`'s `mmap_spec` carries.  Hence the
    `nolint` on the definition. -/
def check_mmap (addr len prot flags fd off : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then check_ret_only eff (errno_ret EINVAL) m []
     else .CheckUnmodeled)
  else if !(mmap_anon_b flags) then .CheckUnmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then check_ret_only eff (errno_ret EINVAL) m []
     else .CheckUnmodeled)
  else if mmap_modeled_b prot flags off then
    match eff with
    | ⟨r, [], zs, [], [], []⟩ =>
        if errno_ret_in mmap_errnos r then
          match zs with
          | [] => .CheckOk m []
          | _ => .CheckReject
        else
          let nZ := page_round_up_Z (len.toNat : Int)
          let n := BitVec.ofInt 64 nZ
          if decide ((r.toNat : Int) % page_size = 0) && decide (0 < (r.toNat : Int)) &&
              decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
              region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
              mmap_noreserve_backed_ok flags m nZ &&
              listNN_eqb zs [(r, n)]
          then .CheckOk
            (with_mmap_backing flags r n
              (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                 ((r, n) :: (m_vmmaps m).vm_maps)
                 (m_vmmaps m).vm_noaccess
                 (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                 (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                 (m_vmmaps m).vm_init_sp) m)) []
          else .CheckReject
    | _ => .CheckReject
  else if mmap_noaccess_b prot flags off then
    match eff with
    | ⟨r, [], [], us, [], []⟩ =>
        if errno_ret_in mmap_errnos r then
          match us with
          | [] => .CheckOk m []
          | _ => .CheckReject
        else
          let nZ := page_round_up_Z (len.toNat : Int)
          let n := BitVec.ofInt 64 nZ
          if decide ((r.toNat : Int) % page_size = 0) && decide (0 < (r.toNat : Int)) &&
              decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
              region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
              listNN_eqb us [(r, n)]
          then .CheckOk
            (with_mmap_backing flags r n
              (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                 ((r, n) :: (m_vmmaps m).vm_maps)
                 ((r, n) :: (m_vmmaps m).vm_noaccess)
                 (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                 (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                 (m_vmmaps m).vm_init_sp) m)) []
          else .CheckReject
    | _ => .CheckReject
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then
      check_ret_only eff (errno_ret ENOMEM) m []
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .CheckUnmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      check_ret_only eff (errno_ret EINVAL) m []
    else if ¬ (0 < (addr.toNat : Int)) then .CheckUnmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n &&
          map_contains (m_vmmaps m).vm_maps addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match us with
              | [] => .CheckOk m []                -- range preserved
              | _ =>
                  if listNN_eqb us [(addr, n)]     -- range destroyed
                  then .CheckOk
                    (with_mmap_destroyed addr n
                      (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                  else .CheckReject
            else if bv_eqb r addr && listNN_eqb us [(addr, n)] then .CheckOk
              (with_mmap_replacement flags addr n
                (with_vmmaps
                  (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                    (m_vmmaps m).vm_maps
                    ((addr, n) :: maps_subtract (m_vmmaps m).vm_noaccess
                                    (addr.toNat : Int)
                                    ((addr.toNat : Int) + (n.toNat : Int)))
                    (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                    (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                    (m_vmmaps m).vm_init_sp) m)) []
            else .CheckReject
        | _ => .CheckReject
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match us with | [] => .CheckOk m [] | _ => .CheckReject
            else if bv_eqb r addr && listNN_eqb us [(addr, n)] then .CheckOk
              (with_mmap_backing flags addr n
                (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                   ((addr, n) :: (m_vmmaps m).vm_maps)
                   ((addr, n) :: (m_vmmaps m).vm_noaccess)
                   (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                   (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                   (m_vmmaps m).vm_init_sp) m)) []
            else .CheckReject
        | _ => .CheckReject
      else if region_free (m_vmmaps m).vm_reserved addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match us with
              | [] => .CheckOk m []                -- range preserved
              | _ =>
                  if listNN_eqb us [(addr, n)]     -- range destroyed
                  then .CheckOk
                    (with_mmap_destroyed addr n
                      (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                  else .CheckReject
            else if bv_eqb r addr && listNN_eqb us [(addr, n)] then .CheckOk
              (with_mmap_replacement flags addr n
                (with_vmmaps
                  (mmap_fixed_noaccess_span_next (m_vmmaps m) addr n) m)) []
            else .CheckReject
        | _ => .CheckReject
      else .CheckUnmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then
      check_ret_only eff (errno_ret ENOMEM) m []
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .CheckUnmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      check_ret_only eff (errno_ret EINVAL) m []
    else if ¬ (0 < (addr.toNat : Int)) then .CheckUnmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n &&
          map_contains (m_vmmaps m).vm_maps addr n then
        match eff with
        | ⟨r, [], zs, us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              (match zs with
               | _ :: _ => .CheckReject       -- no failure exposes bytes
               | [] =>
                   (match us with
                    | [] => .CheckOk m []               -- range preserved
                    | _ =>
                        if listNN_eqb us [(addr, n)]    -- range destroyed
                        then .CheckOk
                          (with_mmap_destroyed addr n
                            (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                        else .CheckReject))
            else
              (match us with
               | _ :: _ => .CheckReject       -- the success unmaps nothing
               | [] =>
                   if bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                       mmap_fixed_rw_budget_ok flags m addr n
                   then .CheckOk
                     (with_mmap_replacement flags addr n
                       (with_vmmaps
                         (mmap_fixed_rw_next (m_vmmaps m) addr n) m)) []
                   else .CheckReject)
        | _ => .CheckReject
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        match eff with
        | ⟨r, [], zs, [], [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match zs with | [] => .CheckOk m [] | _ => .CheckReject
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                    mmap_noreserve_backed_ok flags m nZ
            then .CheckOk
              (with_mmap_backing flags addr n
                (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                   ((addr, n) :: (m_vmmaps m).vm_maps)
                   (m_vmmaps m).vm_noaccess
                   (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                   (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                   (m_vmmaps m).vm_init_sp) m)) []
            else .CheckReject
        | _ => .CheckReject
      else if region_free (m_vmmaps m).vm_reserved addr n then
        match eff with
        | ⟨r, [], zs, us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              (match zs with
               | _ :: _ => .CheckReject       -- no failure exposes bytes
               | [] =>
                   (match us with
                    | [] => .CheckOk m []               -- range preserved
                    | _ =>
                        if listNN_eqb us [(addr, n)]    -- range destroyed
                        then .CheckOk
                          (with_mmap_destroyed addr n
                            (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
                        else .CheckReject))
            else
              (match us with
               | _ :: _ => .CheckReject       -- the success unmaps nothing
               | [] =>
                   if bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                       mmap_fixed_rw_span_budget_ok flags m addr n
                   then .CheckOk
                     (with_mmap_replacement flags addr n
                       (with_vmmaps
                         (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m)) []
                   else .CheckReject)
        | _ => .CheckReject
      else .CheckUnmodeled
  else if mmap_noreplace_noaccess_b prot flags off then
    -- MAP_FIXED_NOREPLACE, PROT_NONE: the MAP_FIXED argument gate, then
    -- one split on the ledger — the free-range reservation, or -EEXIST
    -- beside the environment errno (see [Mmap.mmap_spec]).
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then
      check_ret_only eff (errno_ret ENOMEM) m []
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .CheckUnmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      check_ret_only eff (errno_ret EINVAL) m []
    else if ¬ (0 < (addr.toNat : Int)) then .CheckUnmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match us with | [] => .CheckOk m [] | _ => .CheckReject
            else if bv_eqb r addr && listNN_eqb us [(addr, n)] then .CheckOk
              (with_mmap_backing flags addr n
                (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                   ((addr, n) :: (m_vmmaps m).vm_maps)
                   ((addr, n) :: (m_vmmaps m).vm_noaccess)
                   (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                   (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                   (m_vmmaps m).vm_init_sp) m)) []
            else .CheckReject
        | _ => .CheckReject
      else
        match eff with
        | ⟨r, [], [], [], [], []⟩ =>
            if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
            then .CheckOk m [] else .CheckReject
        | _ => .CheckReject
  else if mmap_noreplace_rw_b prot flags off then
    -- MAP_FIXED_NOREPLACE, rw: the same gate and split, with the rw
    -- free-range grant and its budget conjunct.
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then
      check_ret_only eff (errno_ret ENOMEM) m []
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .CheckUnmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      check_ret_only eff (errno_ret EINVAL) m []
    else if ¬ (0 < (addr.toNat : Int)) then .CheckUnmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        match eff with
        | ⟨r, [], zs, [], [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              match zs with | [] => .CheckOk m [] | _ => .CheckReject
            else if bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                    mmap_noreserve_backed_ok flags m nZ
            then .CheckOk
              (with_mmap_backing flags addr n
                (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                   ((addr, n) :: (m_vmmaps m).vm_maps)
                   (m_vmmaps m).vm_noaccess
                   (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                   (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                   (m_vmmaps m).vm_init_sp) m)) []
            else .CheckReject
        | _ => .CheckReject
      else
        match eff with
        | ⟨r, [], [], [], [], []⟩ =>
            if errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)
            then .CheckOk m [] else .CheckReject
        | _ => .CheckReject
  else .CheckUnmodeled

end

/-! ## munmap (215) -/

/-- The `munmap` (215) checker.

    The spec's first gate (an unaligned `addr` or a zero `len`) is
    -EINVAL; the page-rounded end past `TASK_SIZE` is -EINVAL; a request
    that IS a recorded mapping must return 0, unmap exactly the request
    and step the model with the removal; a free range below the stack band
    is a no-op 0; and everything else declines. -/
def check_munmap (addr len : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(((addr.toNat : Int) % page_size) == 0) || w_is0 len then
    check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (len.toNat : Int)
    -- the range leaves the user address space: see [Mmap.munmap_spec]
    if TASK_SIZE < (addr.toNat : Int) + nZ then
      check_ret_only eff (errno_ret EINVAL) m []
    else
      let n := BitVec.ofInt 64 nZ
      if map_has (m_vmmaps m).vm_maps addr n then
        match eff with
        | ⟨r, [], [], us, [], []⟩ =>
            if w_is0 r && listNN_eqb us [(addr, n)]
            then .CheckOk
              (with_mmap_destroyed addr n
                (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                   (map_remove (m_vmmaps m).vm_maps addr)
                   (maps_subtract (m_vmmaps m).vm_noaccess
                      (addr.toNat : Int)
                      ((addr.toNat : Int) + (n.toNat : Int)))
                   (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                   (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                   (m_vmmaps m).vm_init_sp) m) []
            else .CheckReject
        | _ => .CheckReject
      else if munmap_free_ok (m_vmmaps m) addr nZ then
        check_ret_only eff (BitVec.ofInt 64 0) m []
      else .CheckUnmodeled

/- ------------------------------------------------------------------ mremap

   (** mremap witness: deterministic -EINVAL for the modeled flag shape's
       misaligned address and zero/wrapping new size, [Unmodeled] for
       unsupported flags, the clone shape, and non-exact/protected source
       mappings.  Past those, an equal-size call has no injectable failure at
       all (Linux cannot fail one for lack of memory — see [mremap_spec]), so
       the witness is its deterministic success; every resizing call still has
       the always-available ENOMEM branch.

       mprotect witness: the argument gates first, in Linux's order — the
       PROT_GROWSDOWN|PROT_GROWSUP conflict and a misaligned address are
       -EINVAL, a zero [len] is 0 and a page-rounded end past 2^64 is -ENOMEM,
       both for any [prot] that got past them (see
       [Mprotect.mprotect_spec]).  Past those, the no-op success for the one
       modeled [prot] (rw — the permissions the model's memory already has),
       and [Unmodeled] (fail closed) for every other, PROT_EXEC above all. *) -/

/- =========================================================================
   getrandom (278) — witness: the full delivery of a small request,
   environment failure (EINTR) for every other, or [Unmodeled] on
   unmodeled flags / an unwritable destination; readlinkat (78) —
   deterministic -EINVAL under AT_FDCWD, [Unmodeled] on any other dirfd
   ========================================================================= -/

/- (** getrandom's witness: [Unmodeled] on unmodeled flags (GRND_RANDOM or
       unknown bits — fail closed, but never stuck); the full delivery for
       a nonzero request of at most [Random.getrandom_small_max] bytes,
       which has no errno branch; otherwise the always-available errno
       branch — EINTR, the head of [getrandom_errnos].  The >= 1 lower
       bound only constrains a large request's success branch, so the
       errno witness is unaffected by it. *) -/

/-! ## The rounding lemmas the gate arithmetic needs

    These two are stated here for the `Int` arithmetic `mmap`'s `nZ`
    needs.  `Checks/Sys/Mm/Mremap.lean` states the non-negativity fact
    privately at its one call site; both are public here because the
    `alloc_top` bounds below consume them. -/

/-- The rounding of a non-negative length is non-negative. -/
theorem page_round_up_Z_nonneg (z : Int) (Hz : 0 ≤ z) :
    0 ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  apply Int.mul_nonneg
  · exact Int.ediv_nonneg (by omega) (by omega)
  · omega

/-- Rounding up is monotone. -/
theorem page_round_up_Z_mono (a b : Int) (H : a ≤ b) :
    page_round_up_Z a ≤ page_round_up_Z b := by
  unfold page_round_up_Z page_size
  apply Int.mul_le_mul_of_nonneg_right _ (by omega : (0 : Int) ≤ 4096)
  exact Int.ediv_le_ediv (by omega) (by omega : a + page_size - 1 ≤ b + page_size - 1)

/- ------------------------------------------------------------------ brk

   Turn a boolean goal condition into `true` using equalities and
   arithmetic facts already in context (robust to hypothesis naming). -/

/-- The outcome of `brk_spec`'s answered resolution, inverted: the
    resolution the environment chose, its gate, the effect verbatim, the
    stepped model and no events.  Stating it once keeps
    `check_brk_complete_ok` on the effect's shape rather than on the bind
    tree. -/
private theorem brk_ok_inv (req : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.bind
      (choose (fun r => brk_r_ok m req r = true))
      (fun r => LinuxSem.LinuxProcessSem.bind
        (modify fun _ => with_brk_next m req r)
        (fun _ => LinuxSem.LinuxProcessSem.pure
          (SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
            (brk_unmaps r (m_vmmaps m).vm_brk) [] []))) i m (.ok eff m' evs)) :
    ∃ r, brk_r_ok m req r = true ∧
      eff = SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
        (brk_unmaps r (m_vmmaps m).vm_brk) [] [] ∧
      m' = with_brk_next m req r ∧ evs = [] := by
  obtain ⟨r0, m1, e1, e2, hc, hk, hevs⟩ := H
  obtain ⟨x, hr, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hx, hm1, he1⟩ := hok
  subst hx
  subst hm1
  subst he1
  obtain ⟨u, m2, e3, e4, hmod, hpure, hevs2⟩ := hk
  cases hmod
  cases hpure
  subst hevs2
  simp only [List.nil_append] at hevs
  dsimp only
  exact ⟨r0, hr, rfl, rfl, hevs⟩

theorem check_brk_sound_ok (req : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (i : SyscallInput) (H : check_brk req eff m = .CheckOk m' evs) :
    brk_spec req i m (.ok eff m' evs) := by
  unfold check_brk at H
  unfold brk_spec
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
  · by_cases hok : (brk_r_ok m req r &&
        listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk) &&
        listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
    · rw [ite_eq_left hok] at H
      simp only [check_result.CheckOk.injEq] at H
      obtain ⟨hm, hevs⟩ := H
      subst hm
      subst hevs
      obtain ⟨h1, hu⟩ := (Bool.and_eq_true ..).mp hok
      obtain ⟨hr, hz⟩ := (Bool.and_eq_true ..).mp h1
      have hzz : zs = brk_zeros req r (m_vmmaps m).vm_brk := (listNN_eqb_eq zs _).mp hz
      have huu : us = brk_unmaps r (m_vmmaps m).vm_brk := (listNN_eqb_eq us _).mp hu
      rw [hzz, huu]
      rw [bind_getModel]
      refine bind_ok0 _ _ i m r m _ _ [] (choose_ok _ r i m hr) ?_
      exact bind_ok0 _ _ i m () (with_brk_next m req r) _ _ []
        (modify_ok _ i m) (pure_ok _ i _)
    · rw [ite_eq_right hok] at H
      exact nomatch H
  all_goals exact nomatch H

theorem check_brk_sound_unmodeled (req : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_brk req eff m = .CheckUnmodeled) :
    brk_spec req i m .unmodeled := by
  unfold check_brk at H
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
  · by_cases hok : (brk_r_ok m req r &&
        listNN_eqb zs (brk_zeros req r (m_vmmaps m).vm_brk) &&
        listNN_eqb us (brk_unmaps r (m_vmmaps m).vm_brk)) = true
    · rw [ite_eq_left hok] at H
      exact nomatch H
    · rw [ite_eq_right hok] at H
      exact nomatch H
  all_goals exact nomatch H

theorem check_brk_complete_ok (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : brk_spec req i m (.ok eff m' evs)) :
    check_brk req eff m = .CheckOk m' evs := by
  unfold check_brk
  unfold brk_spec at H
  rw [bind_getModel] at H
  obtain ⟨r, hr, heff, hm, hevs⟩ := brk_ok_inv req i m eff m' evs H
  rw [heff, hm, hevs]
  dsimp only
  have hz : listNN_eqb (brk_zeros req r (m_vmmaps m).vm_brk)
      (brk_zeros req r (m_vmmaps m).vm_brk) = true := (listNN_eqb_eq _ _).mpr rfl
  have hu : listNN_eqb (brk_unmaps r (m_vmmaps m).vm_brk)
      (brk_unmaps r (m_vmmaps m).vm_brk) = true := (listNN_eqb_eq _ _).mpr rfl
  rw [ite_eq_left (by rw [hr, hz, hu]; rfl)]

theorem check_brk_complete_unmodeled (req : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : brk_spec req i m .unmodeled) :
    check_brk req eff m = .CheckUnmodeled := by
  unfold check_brk
  unfold brk_spec at H
  rw [bind_getModel] at H
  rcases H with h | ⟨r, m1, evs1, hc, hk⟩
  · obtain ⟨x, -, hbad⟩ := h
    exact nomatch hbad
  · rcases hk with hmod | ⟨u, m2, evs2, hmod, hpure⟩
    · exact nomatch hmod
    · exact nomatch hpure
/- ---------------------------------------------------------------- mmap -/

theorem check_mmap_sound_ok (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_mmap addr len prot flags fd off eff m = .CheckOk m' evs) :
    mmap_spec addr len prot flags fd off i m (.ok eff m' evs) := by
  unfold check_mmap at H
  unfold mmap_spec
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H ⊢
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      exact pure_ok _ i _
    · rw [ite_eq_right hpl] at H
      exact nomatch H
  · rw [ite_eq_right hoff] at H ⊢
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · rw [ite_eq_left hanon] at H
      exact nomatch H
    · rw [ite_eq_right hanon] at H ⊢
      by_cases hzlen : w_is0 len = true
      · rw [ite_eq_left hzlen] at H ⊢
        by_cases hpa : mmap_plain_anon_b flags = true
        · rw [ite_eq_left hpa] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          exact pure_ok _ i _
        · rw [ite_eq_right hpa] at H
          exact nomatch H
      · rw [ite_eq_right hzlen] at H ⊢
        by_cases hmod : mmap_modeled_b prot flags off = true
        · rw [ite_eq_left hmod] at H ⊢
          simp only [alt]
          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
          cases ws <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
          · by_cases herr : errno_ret_in mmap_errnos r = true
            · rw [ite_eq_left herr] at H
              cases zs with
              | nil =>
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  subst hm
                  subst hevs
                  obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                  subst hr
                  exact Or.inl (bind_ok0 _ _ i m e m _ _ [] (choose_ok _ e i m hmem) (pure_ok _ i _))
              | cons z zs => exact nomatch H
            · rw [ite_eq_right herr] at H
              refine Or.inr ?_
              rw [bind_getModel]
              generalize hnZ : page_round_up_Z (len.toNat : Int) = nZ at H ⊢
              generalize hn : BitVec.ofInt 64 nZ = n at H ⊢
              by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                  decide (0 < (r.toNat : Int)) &&
                  decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
                  region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
                  mmap_noreserve_backed_ok flags m nZ &&
                  listNN_eqb zs [(r, n)]) = true
              · rw [ite_eq_left hguard] at H
                obtain ⟨h1, hzs⟩ := (Bool.and_eq_true ..).mp hguard
                obtain ⟨h2, hbak⟩ := (Bool.and_eq_true ..).mp h1
                obtain ⟨h3, hreg⟩ := (Bool.and_eq_true ..).mp h2
                obtain ⟨h4, hle⟩ := (Bool.and_eq_true ..).mp h3
                obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp h4
                simp only [decide_eq_true_eq] at hA hB hle
                have hzsz : zs = [(r, n)] := (listNN_eqb_eq zs _).mp hzs
                rw [hzsz]
                simp only [check_result.CheckOk.injEq] at H
                obtain ⟨hm, hevs⟩ := H
                subst hm
                subst hevs
                refine bind_ok0 _ _ i m r m _ _ [] (choose_ok _ r i m ?_) ?_
                · exact ⟨hA, hB, hle, hreg, hbak⟩
                · exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)
              · rw [ite_eq_right hguard] at H
                exact nomatch H
          all_goals exact nomatch H
        · rw [ite_eq_right hmod] at H ⊢
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · rw [ite_eq_left hnoacc] at H ⊢
            simp only [alt]
            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
            cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
            · by_cases herr : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left herr] at H
                cases us with
                | nil =>
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    subst hm
                    subst hevs
                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                    subst hr
                    exact Or.inl (bind_ok0 _ _ i m e m _ _ [] (choose_ok _ e i m hmem) (pure_ok _ i _))
                | cons u us => exact nomatch H
              · rw [ite_eq_right herr] at H
                refine Or.inr ?_
                rw [bind_getModel]
                generalize hnZ : page_round_up_Z (len.toNat : Int) = nZ at H ⊢
                generalize hn : BitVec.ofInt 64 nZ = n at H ⊢
                by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                    decide (0 < (r.toNat : Int)) &&
                    decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
                    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
                    listNN_eqb us [(r, n)]) = true
                · rw [ite_eq_left hguard] at H
                  obtain ⟨h1, hus⟩ := (Bool.and_eq_true ..).mp hguard
                  obtain ⟨h2, hreg⟩ := (Bool.and_eq_true ..).mp h1
                  obtain ⟨h3, hle⟩ := (Bool.and_eq_true ..).mp h2
                  obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp h3
                  simp only [decide_eq_true_eq] at hA hB hle
                  have hus' : us = [(r, n)] := (listNN_eqb_eq us _).mp hus
                  rw [hus']
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  subst hm
                  subst hevs
                  refine bind_ok0 _ _ i m r m _ _ [] (choose_ok _ r i m ?_) ?_
                  · exact ⟨hA, hB, hle, hreg⟩
                  · exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)
                · rw [ite_eq_right hguard] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hnoacc] at H ⊢
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · rw [ite_eq_left hfx] at H ⊢
              dsimp only at H ⊢
              by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · rw [ite_eq_left hovf] at H ⊢
                obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
                exact pure_ok _ i _
              · rw [ite_eq_right hovf] at H ⊢
                rw [bind_getModel]
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hceil] at H ⊢
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H ⊢
                    obtain ⟨rfl, rfl, rfl⟩ :=
                      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                    exact pure_ok _ i _
                  · rw [ite_eq_right halign] at H ⊢
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · rw [ite_eq_left hpos] at H ⊢
                      exact nomatch H
                    · rw [ite_eq_right hpos] at H ⊢
                      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · rw [ite_eq_left hcont] at H ⊢
                        simp only [alt]
                        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
                        · by_cases herr : errno_ret_in mmap_errnos r = true
                          · rw [ite_eq_left herr] at H
                            cases us with
                            | nil =>
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                subst hm
                                subst hevs
                                obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                subst hr
                                exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                  (choose_ok _ e i m hmem) (pure_ok _ i _))
                            | cons u us =>
                                by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                · rw [ite_eq_left hdel] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                  subst hr
                                  have hus : (u :: us) = [(addr, n)] := (listNN_eqb_eq (u :: us) _).mp hdel
                                  rw [hus]
                                  exact Or.inr (Or.inr (bind_ok0 _ _ i m e m _ _ []
                                    (choose_ok _ e i m hmem)
                                    (bind_ok0 _ _ i m ()
                                      (with_mmap_destroyed addr n
                                        (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m)
                                      _ _ [] (modify_ok _ i m) (pure_ok _ i _))))
                                · rw [ite_eq_right hdel] at H
                                  exact nomatch H
                          · rw [ite_eq_right herr] at H
                            by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                            · rw [ite_eq_left hsuc] at H
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, hevs⟩ := H
                              subst hm
                              subst hevs
                              obtain ⟨hr, hus⟩ := (Bool.and_eq_true ..).mp hsuc
                              have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                              have hus' : us = [(addr, n)] := (listNN_eqb_eq us _).mp hus
                              rw [hr']
                              rw [hus']
                              exact Or.inr (Or.inl (bind_ok0 _ _ i m ()
                                (with_mmap_replacement flags addr n
                                  (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                                     (m_vmmaps m).vm_maps
                                     ((addr, n) :: maps_subtract (m_vmmaps m).vm_noaccess
                                                     (addr.toNat : Int)
                                                     ((addr.toNat : Int) + (n.toNat : Int)))
                                     (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                                     (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                                     (m_vmmaps m).vm_init_sp) m)) _ _ [] (modify_ok _ i m)
                                (pure_ok _ i _)))
                            · rw [ite_eq_right hsuc] at H
                              exact nomatch H
                        all_goals exact nomatch H
                      · rw [ite_eq_right hcont] at H ⊢
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · rw [ite_eq_left hfresh] at H ⊢
                          simp only [alt]
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases us with
                              | nil =>
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                  subst hr
                                  exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                    (choose_ok _ e i m hmem) (pure_ok _ i _))
                              | cons u us => exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                subst hm
                                subst hevs
                                obtain ⟨hr, hus⟩ := (Bool.and_eq_true ..).mp hsuc
                                have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                have hus' : us = [(addr, n)] := (listNN_eqb_eq us _).mp hus
                                rw [hr']
                                rw [hus']
                                refine Or.inr (bind_ok0 _ _ i m addr m _ _ []
                                  (choose_ok _ addr i m rfl) ?_)
                                exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)
                              · rw [ite_eq_right hsuc] at H
                                exact nomatch H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hfresh] at H ⊢
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · rw [ite_eq_left hspan] at H ⊢
                            simp only [alt]
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil =>
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    subst hm
                                    subst hevs
                                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                    subst hr
                                    exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                      (choose_ok _ e i m hmem) (pure_ok _ i _))
                                | cons u us =>
                                    by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                    · rw [ite_eq_left hdel] at H
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      subst hm
                                      subst hevs
                                      obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                      subst hr
                                      have hus : (u :: us) = [(addr, n)] := (listNN_eqb_eq (u :: us) _).mp hdel
                                      rw [hus]
                                      exact Or.inr (Or.inr (bind_ok0 _ _ i m e m _ _ []
                                        (choose_ok _ e i m hmem)
                                        (bind_ok0 _ _ i m ()
                                          (with_mmap_destroyed addr n
                                            (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m)
                                          _ _ [] (modify_ok _ i m) (pure_ok _ i _))))
                                    · rw [ite_eq_right hdel] at H
                                      exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  obtain ⟨hr, hus⟩ := (Bool.and_eq_true ..).mp hsuc
                                  have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                  have hus' : us = [(addr, n)] := (listNN_eqb_eq us _).mp hus
                                  rw [hr']
                                  rw [hus']
                                  exact Or.inr (Or.inl (bind_ok0 _ _ i m ()
                                    (with_mmap_replacement flags addr n
                                      (with_vmmaps (mmap_fixed_noaccess_span_next (m_vmmaps m)
                                        addr n) m)) _ _ [] (modify_ok _ i m) (pure_ok _ i _)))
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hspan] at H
                            exact nomatch H
            · rw [ite_eq_right hfx] at H ⊢
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · rw [ite_eq_left hfrw] at H ⊢
                dsimp only at H ⊢
                by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · rw [ite_eq_left hovf] at H ⊢
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
                  exact pure_ok _ i _
                · rw [ite_eq_right hovf] at H ⊢
                  rw [bind_getModel]
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H ⊢
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H ⊢
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H ⊢
                      obtain ⟨rfl, rfl, rfl⟩ :=
                        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                      exact pure_ok _ i _
                    · rw [ite_eq_right halign] at H ⊢
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H ⊢
                        exact nomatch H
                      · rw [ite_eq_right hpos] at H ⊢
                        generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · rw [ite_eq_left hcont] at H ⊢
                          simp only [alt]
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases zs with
                              | cons z zs => exact nomatch H
                              | nil =>
                                  cases us with
                                  | nil =>
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      subst hm
                                      subst hevs
                                      obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                      subst hr
                                      exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                        (choose_ok _ e i m hmem) (pure_ok _ i _))
                                  | cons u us =>
                                      by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                      · rw [ite_eq_left hdel] at H
                                        simp only [check_result.CheckOk.injEq] at H
                                        obtain ⟨hm, hevs⟩ := H
                                        subst hm
                                        subst hevs
                                        obtain ⟨e, hmem, hr⟩ :=
                                          (errno_ret_in_true mmap_errnos r).mp herr
                                        subst hr
                                        have hus : (u :: us) = [(addr, n)] :=
                                          (listNN_eqb_eq (u :: us) _).mp hdel
                                        rw [hus]
                                        exact Or.inr (Or.inr (bind_ok0 _ _ i m e m _ _ []
                                          (choose_ok _ e i m hmem)
                                          (bind_ok0 _ _ i m ()
                                            (with_mmap_destroyed addr n
                                              (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m)
                                            _ _ [] (modify_ok _ i m) (pure_ok _ i _))))
                                      · rw [ite_eq_right hdel] at H
                                        exact nomatch H
                            · rw [ite_eq_right herr] at H
                              cases us with
                              | cons u us => exact nomatch H
                              | nil =>
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_fixed_rw_budget_ok flags m addr n) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    subst hm
                                    subst hevs
                                    obtain ⟨h1, hbud⟩ := (Bool.and_eq_true ..).mp hsuc
                                    obtain ⟨hr, hzs⟩ := (Bool.and_eq_true ..).mp h1
                                    have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                    have hzs' : zs = [(addr, n)] := (listNN_eqb_eq zs _).mp hzs
                                    rw [hr']
                                    rw [hzs']
                                    refine Or.inr (Or.inl (bind_ok0 _ _ i m () _ _ _ []
                                      (choose_ok _ () i m hbud) ?_))
                                    exact bind_ok0 _ _ i m ()
                                      (with_mmap_replacement flags addr n
                                        (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n)
                                          m)) _ _ [] (modify_ok _ i m) (pure_ok _ i _)
                                  · rw [ite_eq_right hsuc] at H
                                    exact nomatch H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hcont] at H ⊢
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H ⊢
                            simp only [alt]
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases zs with
                                | nil =>
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    subst hm
                                    subst hevs
                                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                    subst hr
                                    exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                      (choose_ok _ e i m hmem) (pure_ok _ i _))
                                | cons z zs => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                    mmap_noreserve_backed_ok flags m
                                      (page_round_up_Z (len.toNat : Int))) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  obtain ⟨h1, hbak⟩ := (Bool.and_eq_true ..).mp hsuc
                                  obtain ⟨hr, hzs⟩ := (Bool.and_eq_true ..).mp h1
                                  have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                  have hzs' : zs = [(addr, n)] := (listNN_eqb_eq zs _).mp hzs
                                  rw [hr']
                                  rw [hzs']
                                  refine Or.inr (bind_ok0 _ _ i m addr m _ _ []
                                    (choose_ok _ addr i m ⟨rfl, hbak⟩) ?_)
                                  exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m)
                                    (pure_ok _ i _)
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfresh] at H ⊢
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · rw [ite_eq_left hspan] at H ⊢
                              simp only [alt]
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | cons z zs => exact nomatch H
                                  | nil =>
                                      cases us with
                                      | nil =>
                                          simp only [check_result.CheckOk.injEq] at H
                                          obtain ⟨hm, hevs⟩ := H
                                          subst hm
                                          subst hevs
                                          obtain ⟨e, hmem, hr⟩ :=
                                            (errno_ret_in_true mmap_errnos r).mp herr
                                          subst hr
                                          exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                            (choose_ok _ e i m hmem) (pure_ok _ i _))
                                      | cons u us =>
                                          by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                          · rw [ite_eq_left hdel] at H
                                            simp only [check_result.CheckOk.injEq] at H
                                            obtain ⟨hm, hevs⟩ := H
                                            subst hm
                                            subst hevs
                                            obtain ⟨e, hmem, hr⟩ :=
                                              (errno_ret_in_true mmap_errnos r).mp herr
                                            subst hr
                                            have hus : (u :: us) = [(addr, n)] := (listNN_eqb_eq (u :: us) _).mp hdel
                                            rw [hus]
                                            exact Or.inr (Or.inr (bind_ok0 _ _ i m e m _ _ []
                                              (choose_ok _ e i m hmem)
                                              (bind_ok0 _ _ i m ()
                                                (with_mmap_destroyed addr n
                                                  (mmap_fixed_destroyed_next (m_vmmaps m) addr n)
                                                  m)
                                                _ _ [] (modify_ok _ i m) (pure_ok _ i _))))
                                          · rw [ite_eq_right hdel] at H
                                            exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  cases us with
                                  | cons u us => exact nomatch H
                                  | nil =>
                                      by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                          mmap_fixed_rw_span_budget_ok flags m addr n) = true
                                      · rw [ite_eq_left hsuc] at H
                                        simp only [check_result.CheckOk.injEq] at H
                                        obtain ⟨hm, hevs⟩ := H
                                        subst hm
                                        subst hevs
                                        obtain ⟨h1, hbud⟩ := (Bool.and_eq_true ..).mp hsuc
                                        obtain ⟨hr, hzs⟩ := (Bool.and_eq_true ..).mp h1
                                        have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                        have hzs' : zs = [(addr, n)] := (listNN_eqb_eq zs _).mp hzs
                                        rw [hr']
                                        rw [hzs']
                                        refine Or.inr (Or.inl (bind_ok0 _ _ i m () _ _ _ []
                                          (choose_ok _ () i m hbud) ?_))
                                        exact bind_ok0 _ _ i m ()
                                          (with_mmap_replacement flags addr n
                                            (with_vmmaps
                                              (mmap_fixed_rw_span_next (m_vmmaps m) addr n) m))
                                          _ _ [] (modify_ok _ i m) (pure_ok _ i _)
                                      · rw [ite_eq_right hsuc] at H
                                        exact nomatch H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hspan] at H
                              exact nomatch H
              · rw [ite_eq_right hfrw] at H ⊢
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · rw [ite_eq_left hnrn] at H ⊢
                  dsimp only at H ⊢
                  by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · rw [ite_eq_left hovf] at H ⊢
                    obtain ⟨rfl, rfl, rfl⟩ :=
                      (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
                    exact pure_ok _ i _
                  · rw [ite_eq_right hovf] at H ⊢
                    rw [bind_getModel]
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H ⊢
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H ⊢
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H ⊢
                        obtain ⟨rfl, rfl, rfl⟩ :=
                          (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                        exact pure_ok _ i _
                      · rw [ite_eq_right halign] at H ⊢
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H ⊢
                          exact nomatch H
                        · rw [ite_eq_right hpos] at H ⊢
                          generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                            at H ⊢
                          by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfree] at H ⊢
                            simp only [alt]
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil =>
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    subst hm
                                    subst hevs
                                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                                    subst hr
                                    exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                      (choose_ok _ e i m hmem) (pure_ok _ i _))
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  obtain ⟨hr, hus⟩ := (Bool.and_eq_true ..).mp hsuc
                                  have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                  have hus' : us = [(addr, n)] := (listNN_eqb_eq us _).mp hus
                                  rw [hr']
                                  rw [hus']
                                  refine Or.inr (bind_ok0 _ _ i m addr m _ _ []
                                    (choose_ok _ addr i m rfl) ?_)
                                  exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m)
                                    (pure_ok _ i _)
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfree] at H ⊢
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · simp only [alt]
                              by_cases hest : (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)) = true
                              · rw [ite_eq_left hest] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                subst hm
                                subst hevs
                                rcases (Bool.or_eq_true ..).mp hest with he | he
                                · obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp he
                                  subst hr
                                  exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                    (choose_ok _ e i m hmem) (pure_ok _ i _))
                                · have hr : r = errno_ret EEXIST := (Fs.bv_eqb_eq r _).mp he
                                  subst hr
                                  exact Or.inr (pure_ok _ i _)
                              · rw [ite_eq_right hest] at H
                                exact nomatch H
                            all_goals exact nomatch H
                · rw [ite_eq_right hnrn] at H ⊢
                  by_cases hnrr : mmap_noreplace_rw_b prot flags off = true
                  · rw [ite_eq_left hnrr] at H ⊢
                    dsimp only at H ⊢
                    by_cases hovf : two_pow_64 ≤
                        (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · rw [ite_eq_left hovf] at H ⊢
                      obtain ⟨rfl, rfl, rfl⟩ :=
                        (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
                      exact pure_ok _ i _
                    · rw [ite_eq_right hovf] at H ⊢
                      rw [bind_getModel]
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H ⊢
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H ⊢
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H ⊢
                          obtain ⟨rfl, rfl, rfl⟩ :=
                            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                          exact pure_ok _ i _
                        · rw [ite_eq_right halign] at H ⊢
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H ⊢
                            exact nomatch H
                          · rw [ite_eq_right hpos] at H ⊢
                            generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                              at H ⊢
                            by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · rw [ite_eq_left hfree] at H ⊢
                              simp only [alt]
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                                dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | nil =>
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      subst hm
                                      subst hevs
                                      obtain ⟨e, hmem, hr⟩ :=
                                        (errno_ret_in_true mmap_errnos r).mp herr
                                      subst hr
                                      exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                        (choose_ok _ e i m hmem) (pure_ok _ i _))
                                  | cons z zs => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_noreserve_backed_ok flags m
                                        (page_round_up_Z (len.toNat : Int))) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    subst hm
                                    subst hevs
                                    obtain ⟨h1, hbak⟩ := (Bool.and_eq_true ..).mp hsuc
                                    obtain ⟨hr, hzs⟩ := (Bool.and_eq_true ..).mp h1
                                    have hr' : r = addr := (Fs.bv_eqb_eq r addr).mp hr
                                    have hzs' : zs = [(addr, n)] := (listNN_eqb_eq zs _).mp hzs
                                    rw [hr']
                                    rw [hzs']
                                    refine Or.inr (bind_ok0 _ _ i m addr m _ _ []
                                      (choose_ok _ addr i m ⟨rfl, hbak⟩) ?_)
                                    exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m)
                                      (pure_ok _ i _)
                                  · rw [ite_eq_right hsuc] at H
                                    exact nomatch H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hfree] at H ⊢
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                                dsimp only at H
                              · simp only [alt]
                                by_cases hest : (errno_ret_in mmap_errnos r || bv_eqb r (errno_ret EEXIST)) = true
                                · rw [ite_eq_left hest] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  subst hm
                                  subst hevs
                                  rcases (Bool.or_eq_true ..).mp hest with he | he
                                  · obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mmap_errnos r).mp he
                                    subst hr
                                    exact Or.inl (bind_ok0 _ _ i m e m _ _ []
                                      (choose_ok _ e i m hmem) (pure_ok _ i _))
                                  · have hr : r = errno_ret EEXIST := (Fs.bv_eqb_eq r _).mp he
                                    subst hr
                                    exact Or.inr (pure_ok _ i _)
                                · rw [ite_eq_right hest] at H
                                  exact nomatch H
                              all_goals exact nomatch H
                  · rw [ite_eq_right hnrr] at H
                    exact nomatch H


theorem check_mmap_sound_unmodeled (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_mmap addr len prot flags fd off eff m = .CheckUnmodeled) :
    mmap_spec addr len prot flags fd off i m .unmodeled := by
  unfold check_mmap at H
  unfold mmap_spec
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H ⊢
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hpl] at H ⊢
      exact unmodeled_intro i m
  · rw [ite_eq_right hoff] at H ⊢
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · rw [ite_eq_left hanon] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hanon] at H ⊢
      by_cases hzlen : w_is0 len = true
      · rw [ite_eq_left hzlen] at H ⊢
        by_cases hpa : mmap_plain_anon_b flags = true
        · rw [ite_eq_left hpa] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hpa] at H ⊢
          exact unmodeled_intro i m
      · rw [ite_eq_right hzlen] at H ⊢
        by_cases hmod : mmap_modeled_b prot flags off = true
        · rw [ite_eq_left hmod] at H ⊢
          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
          cases ws <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
          · by_cases herr : errno_ret_in mmap_errnos r = true
            · rw [ite_eq_left herr] at H
              cases zs with
              | nil => exact nomatch H
              | cons z zs => exact nomatch H
            · rw [ite_eq_right herr] at H
              by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                  decide (0 < (r.toNat : Int)) &&
                  decide ((r.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m)) &&
                  region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r
                    (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                  mmap_noreserve_backed_ok flags m (page_round_up_Z (len.toNat : Int)) &&
                  listNN_eqb zs [(r, BitVec.ofInt 64
                    (page_round_up_Z (len.toNat : Int)))]) = true
              · rw [ite_eq_left hguard] at H
                exact nomatch H
              · rw [ite_eq_right hguard] at H
                exact nomatch H
          all_goals exact nomatch H
        · rw [ite_eq_right hmod] at H ⊢
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · rw [ite_eq_left hnoacc] at H ⊢
            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
            cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
            · by_cases herr : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left herr] at H
                cases us with
                | nil => exact nomatch H
                | cons u us => exact nomatch H
              · rw [ite_eq_right herr] at H
                by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                    decide (0 < (r.toNat : Int)) &&
                    decide ((r.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m)) &&
                    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r
                      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                    listNN_eqb us [(r, BitVec.ofInt 64
                      (page_round_up_Z (len.toNat : Int)))]) = true
                · rw [ite_eq_left hguard] at H
                  exact nomatch H
                · rw [ite_eq_right hguard] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hnoacc] at H ⊢
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · rw [ite_eq_left hfx] at H ⊢
              try dsimp only at H ⊢
              by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · rw [ite_eq_left hovf] at H
                exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
              · rw [ite_eq_right hovf] at H ⊢
                rw [bind_getModel]
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hceil] at H ⊢
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H
                    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
                  · rw [ite_eq_right halign] at H ⊢
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · rw [ite_eq_left hpos] at H ⊢
                      exact unmodeled_intro i m
                    · rw [ite_eq_right hpos] at H ⊢
                      try dsimp only at H ⊢
                      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                        at H ⊢
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · rw [ite_eq_left hcont] at H ⊢
                        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
                        · by_cases herr : errno_ret_in mmap_errnos r = true
                          · rw [ite_eq_left herr] at H
                            cases us with
                            | nil => exact nomatch H
                            | cons u us =>
                                by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                · rw [ite_eq_left hdel] at H
                                  exact nomatch H
                                · rw [ite_eq_right hdel] at H
                                  exact nomatch H
                          · rw [ite_eq_right herr] at H
                            by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                            · rw [ite_eq_left hsuc] at H
                              exact nomatch H
                            · rw [ite_eq_right hsuc] at H
                              exact nomatch H
                        all_goals exact nomatch H
                      · rw [ite_eq_right hcont] at H ⊢
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · rw [ite_eq_left hfresh] at H ⊢
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                            dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases us with
                              | nil => exact nomatch H
                              | cons u us => exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                exact nomatch H
                              · rw [ite_eq_right hsuc] at H
                                exact nomatch H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hfresh] at H ⊢
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · rw [ite_eq_left hspan] at H ⊢
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil => exact nomatch H
                                | cons u us =>
                                    by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                    · rw [ite_eq_left hdel] at H
                                      exact nomatch H
                                    · rw [ite_eq_right hdel] at H
                                      exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr &&
                                    listNN_eqb us [(addr, n)]) = true <;>
                                  simp [hsuc] at H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hspan] at H ⊢
                            exact unmodeled_intro i m
            · rw [ite_eq_right hfx] at H ⊢
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · rw [ite_eq_left hfrw] at H ⊢
                try dsimp only at H ⊢
                by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · rw [ite_eq_left hovf] at H
                  exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
                · rw [ite_eq_right hovf] at H ⊢
                  rw [bind_getModel]
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H ⊢
                    exact unmodeled_intro i m
                  · rw [ite_eq_right hceil] at H ⊢
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
                    · rw [ite_eq_right halign] at H ⊢
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H ⊢
                        exact unmodeled_intro i m
                      · rw [ite_eq_right hpos] at H ⊢
                        try dsimp only at H ⊢
                        generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                          at H ⊢
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · rw [ite_eq_left hcont] at H ⊢
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases zs with
                              | cons z zs => exact nomatch H
                              | nil =>
                                  cases us with
                                  | nil => exact nomatch H
                                  | cons u us =>
                                      by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                      · rw [ite_eq_left hdel] at H
                                        exact nomatch H
                                      · rw [ite_eq_right hdel] at H
                                        exact nomatch H
                            · rw [ite_eq_right herr] at H
                              cases us with
                              | cons u us => exact nomatch H
                              | nil =>
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_fixed_rw_budget_ok flags m addr n) = true <;>
                                    simp [hsuc] at H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hcont] at H ⊢
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H ⊢
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases zs with
                                | nil => exact nomatch H
                                | cons z zs => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                    mmap_noreserve_backed_ok flags m
                                      (page_round_up_Z (len.toNat : Int))) = true <;>
                                  simp [hsuc] at H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfresh] at H ⊢
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · rw [ite_eq_left hspan] at H ⊢
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases cs <;> cases copyins <;> dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | cons z zs => exact nomatch H
                                  | nil =>
                                      cases us with
                                      | nil => exact nomatch H
                                      | cons u us =>
                                          by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                          · rw [ite_eq_left hdel] at H
                                            exact nomatch H
                                          · rw [ite_eq_right hdel] at H
                                            exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  cases us with
                                  | cons u us => exact nomatch H
                                  | nil =>
                                      by_cases hsuc : (bv_eqb r addr &&
                                          listNN_eqb zs [(addr, n)] &&
                                          mmap_fixed_rw_span_budget_ok flags m addr n) = true <;>
                                        simp [hsuc] at H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hspan] at H ⊢
                              exact unmodeled_intro i m
              · rw [ite_eq_right hfrw] at H ⊢
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · rw [ite_eq_left hnrn] at H ⊢
                  try dsimp only at H ⊢
                  by_cases hovf : two_pow_64 ≤
                      (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · rw [ite_eq_left hovf] at H
                    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
                  · rw [ite_eq_right hovf] at H ⊢
                    rw [bind_getModel]
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H ⊢
                      exact unmodeled_intro i m
                    · rw [ite_eq_right hceil] at H ⊢
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
                      · rw [ite_eq_right halign] at H ⊢
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H ⊢
                          exact unmodeled_intro i m
                        · rw [ite_eq_right hpos] at H ⊢
                          try dsimp only at H ⊢
                          generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                            at H ⊢
                          by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfree] at H ⊢
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil => exact nomatch H
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  exact nomatch H
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfree] at H ⊢
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                              dsimp only at H
                            · by_cases hest : (errno_ret_in mmap_errnos r ||
                                bv_eqb r (errno_ret EEXIST)) = true <;> simp [hest] at H
                            all_goals exact nomatch H
                · rw [ite_eq_right hnrn] at H ⊢
                  by_cases hnrr : mmap_noreplace_rw_b prot flags off = true
                  · rw [ite_eq_left hnrr] at H ⊢
                    try dsimp only at H ⊢
                    by_cases hovf : two_pow_64 ≤
                        (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · rw [ite_eq_left hovf] at H
                      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
                    · rw [ite_eq_right hovf] at H ⊢
                      rw [bind_getModel]
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H ⊢
                        exact unmodeled_intro i m
                      · rw [ite_eq_right hceil] at H ⊢
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
                        · rw [ite_eq_right halign] at H ⊢
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H ⊢
                            exact unmodeled_intro i m
                          · rw [ite_eq_right hpos] at H ⊢
                            try dsimp only at H ⊢
                            generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                              at H ⊢
                            by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · rw [ite_eq_left hfree] at H ⊢
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                                dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | nil => exact nomatch H
                                  | cons z zs => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_noreserve_backed_ok flags m
                                        (page_round_up_Z (len.toNat : Int))) = true <;>
                                    simp [hsuc] at H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hfree] at H ⊢
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases zs <;> cases us <;> cases cs <;>
                                cases copyins <;> dsimp only at H
                              · by_cases hest : (errno_ret_in mmap_errnos r ||
                                  bv_eqb r (errno_ret EEXIST)) = true <;> simp [hest] at H
                              all_goals exact nomatch H
                  · rw [ite_eq_right hnrr] at H ⊢
                    exact unmodeled_intro i m

/-! ## The four arm inversions `check_mmap_complete_ok` needs

    Every `ok` outcome of `mmap_spec` past its gates is one of four bind
    chains: an injected errno, a `choose`-grant, a bare modify-then-pure,
    or an errno whose failure also steps the ledger.  `inv_ok` would invert
    each inline; each is stated once — the injected-errno inversion as the
    shared `errno_from_ok_inv` of `Checks.Sys.Prelude`, the other three
    here, as `Checks/Sys/Mm/Mremap.lean` does for its own spec. -/

/-- A bare `modify`-then-`pure` resolution, inverted. -/
private theorem modify_pure_ok_inv (f : Model → Model) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.bind (modify f)
      (fun _ => LinuxSem.LinuxProcessSem.pure e) i m (.ok eff m' evs)) :
    eff = e ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m1, evs1, evs2, hc, hk, hevs⟩ := H
  have hc' : (Outcome.ok u m1 evs1 : Outcome Unit Model event) = Outcome.ok () (f m) [] := hc
  simp only [Outcome.ok.injEq] at hc'
  obtain ⟨-, hm1, hevs1⟩ := hc'
  rw [hm1] at hk
  have hk' : (Outcome.ok eff m' evs2 : Outcome SyscallEffect Model event) =
      Outcome.ok e (f m) [] := hk
  simp only [Outcome.ok.injEq] at hk'
  obtain ⟨heff, hm, hevs2⟩ := hk'
  rw [hevs1] at hevs
  simp only [List.nil_append] at hevs
  rw [hevs2] at hevs
  exact ⟨heff, hm, hevs⟩

/-- A `choose`-grant, inverted: the witness the environment chose, its
    guard, the effect, the stepped ledger and no events. -/
private theorem grant_ok_inv {A : Type} (P : A → Prop) (f : A → Model → Model)
    (g : A → SyscallEffect) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.bind (choose P)
      (fun a => LinuxSem.LinuxProcessSem.bind (modify (f a))
        (fun _ => LinuxSem.LinuxProcessSem.pure (g a))) i m (.ok eff m' evs)) :
    ∃ a, P a ∧ eff = g a ∧ m' = f a m ∧ evs = [] := by
  obtain ⟨a, m1, evs1, evs2, hc, hk, hevs⟩ := H
  obtain ⟨x, hP, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hx, hm1, hevs1⟩ := hok
  rw [← hx] at hP
  rw [hm1] at hk
  obtain ⟨heff, hm, hevs2⟩ := modify_pure_ok_inv (f a) (g a) i m eff m' evs2 hk
  rw [hevs1] at hevs
  simp only [List.nil_append] at hevs
  rw [hevs2] at hevs
  exact ⟨a, hP, heff, hm, hevs⟩

/-- An errno whose failure also steps the ledger, inverted. -/
private theorem errno_modify_ok_inv (es : List Int) (f : Model → Model)
    (g : Int → SyscallEffect) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.bind (errno_from es)
      (fun e => LinuxSem.LinuxProcessSem.bind (modify f)
        (fun _ => LinuxSem.LinuxProcessSem.pure (g e))) i m (.ok eff m' evs)) :
    ∃ e, e ∈ es ∧ eff = g e ∧ m' = f m ∧ evs = [] := by
  obtain ⟨e, m1, evs1, evs2, hc, hk, hevs⟩ := H
  unfold errno_from choose at hc
  obtain ⟨e0, hmem, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hex, hm1, hevs1⟩ := hok
  rw [← hex] at hmem
  rw [hm1] at hk
  obtain ⟨heff, hm, hevs2⟩ := modify_pure_ok_inv f (g e) i m eff m' evs2 hk
  rw [hevs1] at hevs
  simp only [List.nil_append] at hevs
  rw [hevs2] at hevs
  exact ⟨e, hmem, heff, hm, hevs⟩

theorem check_mmap_complete_ok (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : mmap_spec addr len prot flags fd off i m (.ok eff m' evs)) :
    check_mmap addr len prot flags fd off eff m = .CheckOk m' evs := by
  unfold check_mmap
  unfold mmap_spec at H
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H ⊢
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hpl] at H
      exact nomatch H
  · rw [ite_eq_right hoff] at H ⊢
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · rw [ite_eq_left hanon] at H
      exact nomatch H
    · rw [ite_eq_right hanon] at H ⊢
      by_cases hzlen : w_is0 len = true
      · rw [ite_eq_left hzlen] at H ⊢
        by_cases hpa : mmap_plain_anon_b flags = true
        · rw [ite_eq_left hpa] at H ⊢
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hpa] at H
          exact nomatch H
      · rw [ite_eq_right hzlen] at H ⊢
        by_cases hmod : mmap_modeled_b prot flags off = true
        · -- the hint-placed rw grant
          rw [ite_eq_left hmod] at H ⊢
          simp only [alt] at H
          rcases H with herr | hgrant
          · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
              errno_from_ok_inv mmap_errnos i m eff m' evs herr
            rw [heff, hm, hevs]
            try dsimp only
            rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
          · rw [bind_getModel] at hgrant
            try dsimp only at hgrant
            obtain ⟨a, hP, heff, hm, hevs⟩ := grant_ok_inv _ _ _ i m eff m' evs hgrant
            obtain ⟨h1, h2, h3, h4, h5⟩ := hP
            rw [heff, hm, hevs]
            try dsimp only
            have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
              page_round_up_Z_nonneg _ (by omega)
            have htop := alloc_top_page_lt (m_vmmaps m)
            have hpg : page_size = 4096 := by decide
            have hb : (a.toNat : Int) ≤ two_pow_64 - 4096 := by omega
            have herr : errno_ret_in mmap_errnos a = false :=
              errno_ret_in_below mmap_errnos a (by decide) hb
            rw [ite_eq_right (by rw [herr]; simp)]
            rw [ite_eq_left (by
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, (listNN_eqb_eq _ _).mpr rfl⟩)]
        · rw [ite_eq_right hmod] at H ⊢
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · -- the PROT_NONE reservation
            rw [ite_eq_left hnoacc] at H ⊢
            simp only [alt] at H
            rcases H with herr | hgrant
            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                errno_from_ok_inv mmap_errnos i m eff m' evs herr
              rw [heff, hm, hevs]
              try dsimp only
              rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
            · rw [bind_getModel] at hgrant
              try dsimp only at hgrant
              obtain ⟨a, hP, heff, hm, hevs⟩ := grant_ok_inv _ _ _ i m eff m' evs hgrant
              obtain ⟨h1, h2, h3, h4⟩ := hP
              rw [heff, hm, hevs]
              try dsimp only
              have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
                page_round_up_Z_nonneg _ (by omega)
              have htop := alloc_top_page_lt (m_vmmaps m)
              have hpg : page_size = 4096 := by decide
              have hb : (a.toNat : Int) ≤ two_pow_64 - 4096 := by omega
              have herr : errno_ret_in mmap_errnos a = false :=
                errno_ret_in_below mmap_errnos a (by decide) hb
              rw [ite_eq_right (by rw [herr]; simp)]
              rw [ite_eq_left (by
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, (listNN_eqb_eq _ _).mpr rfl⟩)]
          · rw [ite_eq_right hnoacc] at H ⊢
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · -- MAP_FIXED, PROT_NONE
              rw [ite_eq_left hfx] at H ⊢
              try dsimp only at H ⊢
              by_cases hovf : two_pow_64 ≤
                  (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · rw [ite_eq_left hovf] at H ⊢
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at H
                obtain ⟨rfl, rfl, rfl⟩ := H
                simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right hovf] at H ⊢
                rw [bind_getModel] at H
                try dsimp only at H
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H
                  exact nomatch H
                · rw [ite_eq_right hceil] at H ⊢
                  have hle : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m) := by
                    simpa using Classical.not_not.mp hceil
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H ⊢
                    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                      Outcome.ok.injEq] at H
                    obtain ⟨rfl, rfl, rfl⟩ := H
                    simp [check_ret_only, bv_eqb_refl]
                  · rw [ite_eq_right halign] at H ⊢
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · rw [ite_eq_left hpos] at H
                      exact nomatch H
                    · rw [ite_eq_right hpos] at H ⊢
                      try dsimp only at H ⊢
                      generalize hn : BitVec.ofInt 64
                        (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                      have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
                        page_round_up_Z_nonneg _ (by omega)
                      have htop := alloc_top_page_lt (m_vmmaps m)
                      have hpg : page_size = 4096 := by decide
                      have hb : (addr.toNat : Int) ≤ two_pow_64 - 4096 := by omega
                      have herrA : errno_ret_in mmap_errnos addr = false :=
                        errno_ret_in_below mmap_errnos addr (by decide) hb
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · rw [ite_eq_left hcont] at H ⊢
                        simp only [alt] at H
                        rcases H with herr | hrest
                        · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                            errno_from_ok_inv mmap_errnos i m eff m' evs herr
                          rw [heff, hm, hevs]
                          try dsimp only
                          rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                        · rcases hrest with hrep | hdest
                          · obtain ⟨heff, hm, hevs⟩ :=
                              modify_pure_ok_inv _ _ i m eff m' evs hrep
                            rw [heff, hm, hevs]
                            try dsimp only
                            rw [ite_eq_right (by rw [herrA]; simp)]
                            rw [ite_eq_left (by
                              rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl)]
                          · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                              errno_modify_ok_inv mmap_errnos _ _ i m eff m' evs hdest
                            rw [heff, hm, hevs]
                            try dsimp only
                            rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                            try dsimp only
                            rw [ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
                      · rw [ite_eq_right hcont] at H ⊢
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · rw [ite_eq_left hfresh] at H ⊢
                          simp only [alt] at H
                          rcases H with herr | hgrant
                          · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                              errno_from_ok_inv mmap_errnos i m eff m' evs herr
                            rw [heff, hm, hevs]
                            try dsimp only
                            rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                          · -- the fresh reservation at the requested address
                            try dsimp only at hgrant
                            obtain ⟨a, hP, heff, hm, hevs⟩ :=
                              grant_ok_inv _ _ _ i m eff m' evs hgrant
                            rw [heff, hm, hevs]
                            rw [hP]
                            try dsimp only
                            rw [ite_eq_right (by rw [herrA]; simp)]
                            rw [ite_eq_left (by
                              rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl)]
                        · rw [ite_eq_right hfresh] at H ⊢
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · rw [ite_eq_left hspan] at H ⊢
                            simp only [alt] at H
                            rcases H with herr | hrest
                            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                errno_from_ok_inv mmap_errnos i m eff m' evs herr
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                            · rcases hrest with hrep | hdest
                              · obtain ⟨heff, hm, hevs⟩ :=
                                  modify_pure_ok_inv _ _ i m eff m' evs hrep
                                rw [heff, hm, hevs]
                                try dsimp only
                                rw [ite_eq_right (by rw [herrA]; simp)]
                                rw [ite_eq_left (by
                                  rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl)]
                              · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                  errno_modify_ok_inv mmap_errnos _ _ i m eff m' evs hdest
                                rw [heff, hm, hevs]
                                try dsimp only
                                rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                                try dsimp only
                                rw [ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
                          · rw [ite_eq_right hspan] at H
                            exact nomatch H
            · -- MAP_FIXED, rw
              rw [ite_eq_right hfx] at H ⊢
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · rw [ite_eq_left hfrw] at H ⊢
                dsimp only at H ⊢
                by_cases hovf : two_pow_64 ≤
                    (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · rw [ite_eq_left hovf] at H ⊢
                  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  simp [check_ret_only, bv_eqb_refl]
                · rw [ite_eq_right hovf] at H ⊢
                  rw [bind_getModel] at H
                  try dsimp only at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H ⊢
                    have hle : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m) := by
                      simpa using Classical.not_not.mp hceil
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H ⊢
                      simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                      obtain ⟨rfl, rfl, rfl⟩ := H
                      simp [check_ret_only, bv_eqb_refl]
                    · rw [ite_eq_right halign] at H ⊢
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H
                        exact nomatch H
                      · rw [ite_eq_right hpos] at H ⊢
                        try dsimp only at H ⊢
                        generalize hn : BitVec.ofInt 64
                          (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                        have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
                          page_round_up_Z_nonneg _ (by omega)
                        have htop := alloc_top_page_lt (m_vmmaps m)
                        have hpg : page_size = 4096 := by decide
                        have hb : (addr.toNat : Int) ≤ two_pow_64 - 4096 := by omega
                        have herrA : errno_ret_in mmap_errnos addr = false :=
                          errno_ret_in_below mmap_errnos addr (by decide) hb
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · rw [ite_eq_left hcont] at H ⊢
                          simp only [alt] at H
                          rcases H with herr | hrest
                          · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                              errno_from_ok_inv mmap_errnos i m eff m' evs herr
                            rw [heff, hm, hevs]
                            try dsimp only
                            rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                          · rcases hrest with hsuccess | hdest
                            · -- the rw replacement, gated on its budget
                              obtain ⟨u, hP, heff, hm, hevs⟩ :=
                                grant_ok_inv _ _ _ i m eff m' evs hsuccess
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_right (by rw [herrA]; simp)]
                              rw [ite_eq_left (by
                                rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl, hP]; rfl)]
                            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                errno_modify_ok_inv mmap_errnos _ _ i m eff m' evs hdest
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                              try dsimp only
                              rw [ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
                        · rw [ite_eq_right hcont] at H ⊢
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H ⊢
                            simp only [alt] at H
                            rcases H with herr | hgrant
                            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                errno_from_ok_inv mmap_errnos i m eff m' evs herr
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                            · -- the rw reservation at the requested address
                              obtain ⟨a, hP, heff, hm, hevs⟩ :=
                                grant_ok_inv _ _ _ i m eff m' evs hgrant
                              obtain ⟨ha, hbk⟩ := hP
                              rw [heff, hm, hevs]
                              rw [ha]
                              try dsimp only
                              rw [ite_eq_right (by rw [herrA]; simp)]
                              rw [ite_eq_left (by
                                rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl, hbk]; rfl)]
                          · rw [ite_eq_right hfresh] at H ⊢
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · rw [ite_eq_left hspan] at H ⊢
                              simp only [alt] at H
                              rcases H with herr | hrest
                              · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                  errno_from_ok_inv mmap_errnos i m eff m' evs herr
                                rw [heff, hm, hevs]
                                try dsimp only
                                rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                              · rcases hrest with hsuccess | hdest
                                · obtain ⟨u, hP, heff, hm, hevs⟩ :=
                                    grant_ok_inv _ _ _ i m eff m' evs hsuccess
                                  rw [heff, hm, hevs]
                                  try dsimp only
                                  rw [ite_eq_right (by rw [herrA]; simp)]
                                  rw [ite_eq_left (by
                                    rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl, hP]; rfl)]
                                · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                    errno_modify_ok_inv mmap_errnos _ _ i m eff m' evs hdest
                                  rw [heff, hm, hevs]
                                  try dsimp only
                                  rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                                  try dsimp only
                                  rw [ite_eq_left ((listNN_eqb_eq _ _).mpr rfl)]
                            · rw [ite_eq_right hspan] at H
                              exact nomatch H
              · rw [ite_eq_right hfrw] at H ⊢
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · -- MAP_FIXED_NOREPLACE, PROT_NONE
                  rw [ite_eq_left hnrn] at H ⊢
                  dsimp only at H ⊢
                  by_cases hovf : two_pow_64 ≤
                      (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · rw [ite_eq_left hovf] at H ⊢
                    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                      Outcome.ok.injEq] at H
                    obtain ⟨rfl, rfl, rfl⟩ := H
                    simp [check_ret_only, bv_eqb_refl]
                  · rw [ite_eq_right hovf] at H ⊢
                    rw [bind_getModel] at H
                    try dsimp only at H
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H ⊢
                      have hle : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m) := by
                        simpa using Classical.not_not.mp hceil
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H ⊢
                        simp only [err_ret, ret_only,
                          LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                        obtain ⟨rfl, rfl, rfl⟩ := H
                        simp [check_ret_only, bv_eqb_refl]
                      · rw [ite_eq_right halign] at H ⊢
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H
                          exact nomatch H
                        · rw [ite_eq_right hpos] at H ⊢
                          try dsimp only at H ⊢
                          generalize hn : BitVec.ofInt 64
                            (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                          have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
                            page_round_up_Z_nonneg _ (by omega)
                          have htop := alloc_top_page_lt (m_vmmaps m)
                          have hpg : page_size = 4096 := by decide
                          have hb : (addr.toNat : Int) ≤ two_pow_64 - 4096 := by omega
                          have herrA : errno_ret_in mmap_errnos addr = false :=
                            errno_ret_in_below mmap_errnos addr (by decide) hb
                          by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfree] at H ⊢
                            simp only [alt] at H
                            rcases H with herr | hgrant
                            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                errno_from_ok_inv mmap_errnos i m eff m' evs herr
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                            · -- the free-range reservation
                              obtain ⟨a, hP, heff, hm, hevs⟩ :=
                                grant_ok_inv _ _ _ i m eff m' evs hgrant
                              rw [heff, hm, hevs]
                              rw [hP]
                              try dsimp only
                              rw [ite_eq_right (by rw [herrA]; simp)]
                              rw [ite_eq_left (by
                                rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl)]
                          · rw [ite_eq_right hfree] at H ⊢
                            simp only [alt] at H
                            rcases H with herr | heexist
                            · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                errno_from_ok_inv mmap_errnos i m eff m' evs herr
                              rw [heff, hm, hevs]
                              try dsimp only
                              rw [ite_eq_left (by
                                rw [Bool.or_eq_true]
                                exact Or.inl (errno_ret_in_intro mmap_errnos e hmem))]
                            · simp only [err_ret, ret_only,
                                LinuxSem.LinuxProcessSem.pure,
                                Outcome.ok.injEq] at heexist
                              obtain ⟨rfl, rfl, rfl⟩ := heexist
                              try dsimp only
                              rw [ite_eq_left (by rw [Bool.or_eq_true]; exact Or.inr (bv_eqb_refl _))]
                · rw [ite_eq_right hnrn] at H ⊢
                  by_cases hnrr : mmap_noreplace_rw_b prot flags off = true
                  · -- MAP_FIXED_NOREPLACE, rw
                    rw [ite_eq_left hnrr] at H ⊢
                    dsimp only at H ⊢
                    by_cases hovf : two_pow_64 ≤
                        (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · rw [ite_eq_left hovf] at H ⊢
                      simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                      obtain ⟨rfl, rfl, rfl⟩ := H
                      simp [check_ret_only, bv_eqb_refl]
                    · rw [ite_eq_right hovf] at H ⊢
                      rw [bind_getModel] at H
                      try dsimp only at H
                      by_cases hceil : ¬ ((addr.toNat : Int) +
                          page_round_up_Z (len.toNat : Int) ≤ alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H ⊢
                        have hle : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                            alloc_top (m_vmmaps m) := by
                          simpa using Classical.not_not.mp hceil
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H ⊢
                          simp only [err_ret, ret_only,
                            LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                          obtain ⟨rfl, rfl, rfl⟩ := H
                          simp [check_ret_only, bv_eqb_refl]
                        · rw [ite_eq_right halign] at H ⊢
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H
                            exact nomatch H
                          · rw [ite_eq_right hpos] at H ⊢
                            try dsimp only at H ⊢
                            generalize hn : BitVec.ofInt 64
                              (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                            have hnZ : 0 ≤ page_round_up_Z (len.toNat : Int) :=
                              page_round_up_Z_nonneg _ (by omega)
                            have htop := alloc_top_page_lt (m_vmmaps m)
                            have hpg : page_size = 4096 := by decide
                            have hb : (addr.toNat : Int) ≤ two_pow_64 - 4096 := by omega
                            have herrA : errno_ret_in mmap_errnos addr = false :=
                              errno_ret_in_below mmap_errnos addr (by decide) hb
                            by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · rw [ite_eq_left hfree] at H ⊢
                              simp only [alt] at H
                              rcases H with herr | hgrant
                              · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                  errno_from_ok_inv mmap_errnos i m eff m' evs herr
                                rw [heff, hm, hevs]
                                try dsimp only
                                rw [ite_eq_left (errno_ret_in_intro mmap_errnos e hmem)]
                              · obtain ⟨a, hP, heff, hm, hevs⟩ :=
                                  grant_ok_inv _ _ _ i m eff m' evs hgrant
                                obtain ⟨ha, hbk⟩ := hP
                                rw [heff, hm, hevs]
                                rw [ha]
                                try dsimp only
                                rw [ite_eq_right (by rw [herrA]; simp)]
                                rw [ite_eq_left (by
                                  rw [bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl, hbk]; rfl)]
                            · rw [ite_eq_right hfree] at H ⊢
                              simp only [alt] at H
                              rcases H with herr | heexist
                              · obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                                  errno_from_ok_inv mmap_errnos i m eff m' evs herr
                                rw [heff, hm, hevs]
                                try dsimp only
                                rw [ite_eq_left (by
                                  rw [Bool.or_eq_true]
                                  exact Or.inl (errno_ret_in_intro mmap_errnos e hmem))]
                              · simp only [err_ret, ret_only,
                                  LinuxSem.LinuxProcessSem.pure,
                                  Outcome.ok.injEq] at heexist
                                obtain ⟨rfl, rfl, rfl⟩ := heexist
                                try dsimp only
                                rw [ite_eq_left (by rw [Bool.or_eq_true]; exact Or.inr (bv_eqb_refl _))]
                  · rw [ite_eq_right hnrr] at H
                    exact nomatch H

set_option linter.unusedSimpArgs false in
theorem check_mmap_complete_unmodeled (addr len prot flags fd off : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : mmap_spec addr len prot flags fd off i m .unmodeled) :
    check_mmap addr len prot flags fd off eff m = .CheckUnmodeled := by
  unfold check_mmap
  unfold mmap_spec at H
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H ⊢
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H
      exact nomatch H
    · rw [ite_eq_right hpl] at H ⊢
  · rw [ite_eq_right hoff] at H ⊢
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · rw [ite_eq_left hanon] at H ⊢
    · rw [ite_eq_right hanon] at H ⊢
      by_cases hzlen : w_is0 len = true
      · rw [ite_eq_left hzlen] at H ⊢
        by_cases hpa : mmap_plain_anon_b flags = true
        · rw [ite_eq_left hpa] at H
          exact nomatch H
        · rw [ite_eq_right hpa] at H ⊢
      · rw [ite_eq_right hzlen] at H ⊢
        by_cases hmod : mmap_modeled_b prot flags off = true
        · rw [ite_eq_left hmod] at H
          exfalso
          simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
        · rw [ite_eq_right hmod] at H ⊢
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · rw [ite_eq_left hnoacc] at H
            exfalso
            simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
          · rw [ite_eq_right hnoacc] at H ⊢
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · rw [ite_eq_left hfx] at H ⊢
              dsimp only at H ⊢
              by_cases hovf : two_pow_64 ≤
                  (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · rw [ite_eq_left hovf] at H
                exact nomatch H
              · rw [ite_eq_right hovf] at H ⊢
                rw [bind_getModel] at H
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H ⊢
                · rw [ite_eq_right hceil] at H ⊢
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H
                    exact nomatch H
                  · rw [ite_eq_right halign] at H ⊢
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · rw [ite_eq_left hpos] at H ⊢
                    · rw [ite_eq_right hpos] at H ⊢
                      try dsimp only at H ⊢
                      generalize hn : BitVec.ofInt 64
                        (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · rw [ite_eq_left hcont] at H
                        exfalso
                        simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                      · rw [ite_eq_right hcont] at H ⊢
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · rw [ite_eq_left hfresh] at H
                          exfalso
                          simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                        · rw [ite_eq_right hfresh] at H ⊢
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · rw [ite_eq_left hspan] at H
                            exfalso
                            simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                          · rw [ite_eq_right hspan] at H ⊢
            · rw [ite_eq_right hfx] at H ⊢
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · rw [ite_eq_left hfrw] at H ⊢
                dsimp only at H ⊢
                by_cases hovf : two_pow_64 ≤
                    (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · rw [ite_eq_left hovf] at H
                  exact nomatch H
                · rw [ite_eq_right hovf] at H ⊢
                  rw [bind_getModel] at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H ⊢
                  · rw [ite_eq_right hceil] at H ⊢
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      exact nomatch H
                    · rw [ite_eq_right halign] at H ⊢
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H ⊢
                      · rw [ite_eq_right hpos] at H ⊢
                        try dsimp only at H ⊢
                        generalize hn : BitVec.ofInt 64
                          (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · rw [ite_eq_left hcont] at H
                          exfalso
                          simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                        · rw [ite_eq_right hcont] at H ⊢
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H
                            exfalso
                            simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                          · rw [ite_eq_right hfresh] at H ⊢
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · rw [ite_eq_left hspan] at H
                              exfalso
                              simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                            · rw [ite_eq_right hspan] at H ⊢
              · rw [ite_eq_right hfrw] at H ⊢
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · rw [ite_eq_left hnrn] at H ⊢
                  dsimp only at H ⊢
                  by_cases hovf : two_pow_64 ≤
                      (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · rw [ite_eq_left hovf] at H
                    exact nomatch H
                  · rw [ite_eq_right hovf] at H ⊢
                    rw [bind_getModel] at H
                    by_cases hceil : ¬ ((addr.toNat : Int) +
                        page_round_up_Z (len.toNat : Int) ≤ alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H ⊢
                    · rw [ite_eq_right hceil] at H ⊢
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        exact nomatch H
                      · rw [ite_eq_right halign] at H ⊢
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H ⊢
                        · rw [ite_eq_right hpos] at H ⊢
                          try dsimp only at H ⊢
                          generalize hn : BitVec.ofInt 64
                            (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                          by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfree] at H
                            exfalso
                            simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                          · rw [ite_eq_right hfree] at H
                            exfalso
                            simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                · rw [ite_eq_right hnrn] at H ⊢
                  by_cases hnrr : mmap_noreplace_rw_b prot flags off = true
                  · rw [ite_eq_left hnrr] at H ⊢
                    dsimp only at H ⊢
                    by_cases hovf : two_pow_64 ≤
                        (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · rw [ite_eq_left hovf] at H
                      exact nomatch H
                    · rw [ite_eq_right hovf] at H ⊢
                      rw [bind_getModel] at H
                      by_cases hceil : ¬ ((addr.toNat : Int) +
                          page_round_up_Z (len.toNat : Int) ≤ alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H ⊢
                      · rw [ite_eq_right hceil] at H ⊢
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          exact nomatch H
                        · rw [ite_eq_right halign] at H ⊢
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H ⊢
                          · rw [ite_eq_right hpos] at H ⊢
                            try dsimp only at H ⊢
                            generalize hn : BitVec.ofInt 64
                              (page_round_up_Z (len.toNat : Int)) = n at H ⊢
                            by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · rw [ite_eq_left hfree] at H
                              exfalso
                              simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                            · rw [ite_eq_right hfree] at H
                              exfalso
                              simp [LinuxSem.LinuxProcessSem.alt,
  LinuxSem.LinuxProcessSem.bind,
  LinuxSem.LinuxProcessSem.choose,
  LinuxSem.LinuxProcessSem.getModel,
  LinuxSem.LinuxProcessSem.pure,
  LinuxSem.LinuxProcessSem.modify,
  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                  · rw [ite_eq_right hnrr] at H ⊢

/- ---------------------------------------------------------------- munmap -/

theorem check_munmap_sound_ok (addr len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_munmap addr len eff m = .CheckOk m' evs) :
    munmap_spec addr len i m (.ok eff m' evs) := by
  unfold check_munmap at H
  unfold munmap_spec
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact pure_ok _ i _
  · rw [ite_eq_right hi] at H ⊢
    dsimp only at H ⊢
    rw [bind_getModel]
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      exact pure_ok _ i _
    · rw [ite_eq_right hbig] at H ⊢
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · -- a recorded mapping is dropped, with its unmap effect
        rw [ite_eq_left hhas] at H ⊢
        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only at H
        · by_cases hc : (w_is0 r && listNN_eqb us [(addr, n)]) = true
          · rw [ite_eq_left hc] at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨hm, hevs⟩ := H
            subst hm
            subst hevs
            obtain ⟨hr, hus⟩ := (Bool.and_eq_true ..).mp hc
            have hr0 : r = BitVec.ofInt 64 0 :=
              (Fs.bv_eqb_eq r _).mp (by simpa [w_is0] using hr)
            have hus' : us = [(addr, n)] := (listNN_eqb_eq us _).mp hus
            subst hr0
            subst hus'
            exact bind_ok0 _ _ i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)
          · rw [ite_eq_right hc] at H
            exact nomatch H
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H ⊢
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
          exact pure_ok _ i _
        · rw [ite_eq_right hfree] at H
          exact nomatch H

theorem check_munmap_sound_unmodeled (addr len : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_munmap addr len eff m = .CheckUnmodeled) :
    munmap_spec addr len i m .unmodeled := by
  unfold check_munmap at H
  unfold munmap_spec
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hi] at H ⊢
    dsimp only at H ⊢
    rw [bind_getModel]
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hbig] at H ⊢
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · -- the removal answers; it cannot decline
        rw [ite_eq_left hhas] at H
        exfalso
        revert H
        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> dsimp only <;> intro H
        · by_cases hc : (w_is0 r && listNN_eqb us [(addr, n)]) = true <;>
            simp [hc] at H
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H ⊢
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
        · rw [ite_eq_right hfree] at H ⊢
          exact unmodeled_intro i m

theorem check_munmap_complete_ok (addr len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : munmap_spec addr len i m (.ok eff m' evs)) :
    check_munmap addr len eff m = .CheckOk m' evs := by
  unfold check_munmap
  unfold munmap_spec at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hi] at H ⊢
    rw [bind_getModel] at H
    dsimp only at H ⊢
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hbig] at H ⊢
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · rw [ite_eq_left hhas] at H ⊢
        obtain ⟨u, m1, e1, e2, hmod, hpure, hevs⟩ := H
        cases hmod
        cases hpure
        subst hevs
        dsimp only
        -- the spec's removal, at the effect the checker expects
        have hw0 : w_is0 (BitVec.ofInt 64 0) = true := by
          unfold w_is0
          exact bv_eqb_refl _
        have hnn : listNN_eqb [(addr, n)] [(addr, n)] = true := (listNN_eqb_eq _ _).mpr rfl
        rw [ite_eq_left (by rw [hw0, hnn]; rfl)]
        simp only [with_mmap_destroyed, with_vmmaps, List.append_nil]
      · rw [ite_eq_right hhas] at H ⊢
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H ⊢
          simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hfree] at H
          exact nomatch H

theorem check_munmap_complete_unmodeled (addr len : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : munmap_spec addr len i m .unmodeled) :
    check_munmap addr len eff m = .CheckUnmodeled := by
  unfold check_munmap
  unfold munmap_spec at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    exact nomatch H
  · rw [ite_eq_right hi] at H ⊢
    rw [bind_getModel] at H
    dsimp only at H ⊢
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      exact nomatch H
    · rw [ite_eq_right hbig] at H ⊢
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H ⊢
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · rw [ite_eq_left hhas] at H
        rcases H with h | ⟨u, m1, e1, hmod, hpure⟩
        · exact nomatch h
        · exact nomatch hpure
      · rw [ite_eq_right hhas] at H ⊢
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H
          exact nomatch H
        · rw [ite_eq_right hfree] at H ⊢

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the three
    checkers and their proofs, nothing else.  The checks below are sanity
    checks: they pin the argument gates' ORDER, so each answers exactly
    the `err_ret` / `CheckUnmodeled` the spec does at that point.  They
    are equalities of `check_result`s, not `decide` goals, because
    `check_result`'s `CheckOk` carries a `Model`, and `Model` has no
    `DecidableEq`. -/

/-- A misaligned mmap offset is the first gate, and answers -EINVAL for a
    length whose page-rounding does not wrap. -/
example (m : Model) (eff : SyscallEffect) :
    check_mmap (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) (BitVec.ofInt 64 0x22) (BitVec.ofInt 64 (-1))
        (BitVec.ofInt 64 0x1001) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mmap
  rw [ite_eq_left (by decide), ite_eq_left (by decide)]

/-- A zero `len` is -EINVAL in the plain anonymous shape — after the two
    earlier gates, and before any shape is looked at. -/
example (m : Model) (eff : SyscallEffect) :
    check_mmap (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 3) (BitVec.ofInt 64 0x22) (BitVec.ofInt 64 (-1))
        (BitVec.ofInt 64 0) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mmap
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide), ite_eq_left (by decide)]

/-- A misaligned munmap address is the first gate. -/
example (m : Model) (eff : SyscallEffect) :
    check_munmap (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_munmap
  rw [ite_eq_left (by decide)]

/- --------------------------------------------------------------- mremap -/

/- -------------------------------------------------------------- mprotect -/

/- --------------------------------------------------------------- getrandom -/

end LinuxSem.Checks.Sys.Mm.Mmap


