/-
  * LinuxProcessSem.Checks.Witness.Mm.Mmap — the brk (214), mmap (222), munmap (215) witnesses, and their proofs

  Answers to Linux [mm/mmap.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and re-exports this module. A
  witness here exhibits one admissible outcome for a spec in the matching
  [Sys] module, which is what progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`.  The `<=?` gate is the spec's `Prop` form
  `two_pow_64 ≤ …` (see `Sys/Mm/Mprotect.lean`), so it is split with
  `by_cases`, while the other gates are `Bool` equations.

  Every step has a named lemma: `exact pure_ok _ i m` closes a gate's
  `pure`; the two monadic steps are `bind_step` of
  `Checks.Witness.Prelude` with `dsimp only` after them; the errno
  alternative is `alt_l` applied to `errno_from_witness` (`witness_errno`
  IS ENOMEM, the head of `mmap_errnos`); and the fail-closed arms are
  `unmodeled_intro`.  A `Bool` gate is handled by a `by_cases` plus
  `rw [ite_eq_left h]` / `rw [ite_eq_right h]`, and `alt_l` — the `Monad`
  introduction lemma — is kept spelled out rather than as `Or.inl`, so
  the statement names the constructor it uses.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap

namespace LinuxSem.Checks.Witness.Mm.Mmap

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Witness.Prelude

-- The witnesses' last arms are long `if` chains that the proofs drive
-- together with the spec's; the default recursion budget is not enough.
set_option maxRecDepth 1000000

/-! ## brk (214) -/

/-- The `brk` (214) witness: the resolution that leaves the break where it
    is — `r = vm_brk h`.  That resolution is admissible on all three Linux
    paths keyed by the request (`brk_r_ok`'s query / invalid answer, the
    shrink's failure answer, and the grow's failure answer, where
    `brk_grow_ok` does not even gate it), so no gate has to be decided
    here. -/
def brk_witness (req : word) (m : Model) : Outcome SyscallEffect Model event :=
  let r := (m_vmmaps m).vm_brk
  .ok (SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
        (brk_unmaps r (m_vmmaps m).vm_brk) [] [])
     (with_brk_next m req r) []

/-- `brk_grow_ok` never refuses a resolution that does not move the break:
    the grow test is `vm_brk < r`, and `r = vm_brk`. -/
private theorem brk_grow_ok_vm_brk (req : word) (m : Model) :
    brk_grow_ok m req (m_vmmaps m).vm_brk = true := by
  unfold brk_grow_ok
  rw [ite_eq_right (by simp)]

/-- The tracked break is always an admissible `brk` resolution. -/
private theorem brk_r_ok_vm_brk (req : word) (m : Model) :
    brk_r_ok m req (m_vmmaps m).vm_brk = true := by
  unfold brk_r_ok
  have hbb : ((m_vmmaps m).vm_brk == (m_vmmaps m).vm_brk) = true := by simp
  by_cases h1 : (w_is0 req ||
      decide ((req.toNat : Int) < ((min_brk (m_vmmaps m)).toNat : Int))) = true
  · rw [ite_eq_left h1]
    exact hbb
  · rw [ite_eq_right h1]
    by_cases h2 : decide ((req.toNat : Int) < ((m_vmmaps m).vm_brk.toNat : Int)) = true
    · rw [ite_eq_left h2, hbb, Bool.or_true]
    · rw [ite_eq_right h2, hbb, Bool.or_true, Bool.true_and, brk_grow_ok_vm_brk]

theorem brk_witness_ok (req : word) (i : SyscallInput) (m : Model) :
    brk_spec req i m (brk_witness req m) := by
  unfold brk_spec brk_witness
  rw [bind_getModel]
  exact bind_step (choose (fun r => brk_r_ok m req r = true))
    (fun r => LinuxSem.LinuxProcessSem.bind
      (modify fun _ => with_brk_next m req r)
      (fun _ => LinuxSem.LinuxProcessSem.pure
        (SyscallEffect.mkEffectU r [] (brk_zeros req r (m_vmmaps m).vm_brk)
          (brk_unmaps r (m_vmmaps m).vm_brk) [] [])))
    i m ((m_vmmaps m).vm_brk) m _
    (choose_ok _ _ i m (brk_r_ok_vm_brk req m))
    (bind_step (modify fun _ => with_brk_next m req ((m_vmmaps m).vm_brk))
      (fun _ => LinuxSem.LinuxProcessSem.pure
        (SyscallEffect.mkEffectU (m_vmmaps m).vm_brk [] (brk_zeros req _ (m_vmmaps m).vm_brk)
          (brk_unmaps _ (m_vmmaps m).vm_brk) [] []))
      i m () _ _ (modify_ok _ i m) (pure_ok _ i _))

/-! ## mmap (222) / munmap (215) -/

section
set_option linter.unusedVariables false

/-- mmap witness: -EINVAL on a misaligned offset (with a length whose
    page-rounding does not wrap) or on a zero length in the plain
    anonymous shape, and -ENOMEM on a MAP_FIXED range whose page-rounded
    end leaves the address space; for the modeled shapes the
    environment-failure branch (errno 12), available regardless of the
    mapping ledger; `Unmodeled` on any unmodeled prot/flags/fd/off.  The
    MAP_FIXED branch admits three resolutions (see `Mmap.mmap_spec`); the
    witness keeps choosing the errno one that leaves the range in place,
    since it only has to be AN admissible outcome. -/
def mmap_witness (addr len prot flags fd off : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(mmap_off_aligned_b off) then
    (if mmap_pglen_ok_b len then ret_outcome (errno_ret EINVAL) m else .unmodeled)
  else if !(mmap_anon_b flags) then .unmodeled
  else if w_is0 len then
    (if mmap_plain_anon_b flags then ret_outcome (errno_ret EINVAL) m else .unmodeled)
  else if mmap_modeled_b prot flags off then
    ret_outcome (errno_ret witness_errno) m
  else if mmap_noaccess_b prot flags off then
    ret_outcome (errno_ret witness_errno) m
  else if mmap_fixed_noaccess_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then ret_outcome (errno_ret ENOMEM) m
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .unmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      ret_outcome (errno_ret EINVAL) m
    else if ¬ (0 < (addr.toNat : Int)) then .unmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n &&
          map_contains (m_vmmaps m).vm_maps addr n then
        ret_outcome (errno_ret witness_errno) m
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        ret_outcome (errno_ret witness_errno) m
      else if region_free (m_vmmaps m).vm_reserved addr n then
        ret_outcome (errno_ret witness_errno) m
      else .unmodeled
  else if mmap_fixed_rw_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then ret_outcome (errno_ret ENOMEM) m
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .unmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      ret_outcome (errno_ret EINVAL) m
    else if ¬ (0 < (addr.toNat : Int)) then .unmodeled
    else
      let n := BitVec.ofInt 64 nZ
      if region_free (m_vmmaps m).vm_reserved addr n &&
          map_contains (m_vmmaps m).vm_maps addr n then
        ret_outcome (errno_ret witness_errno) m
      else if region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) addr n then
        ret_outcome (errno_ret witness_errno) m
      else if region_free (m_vmmaps m).vm_reserved addr n then
        ret_outcome (errno_ret witness_errno) m
      else .unmodeled
  /- MAP_FIXED_NOREPLACE, either prot: past the MAP_FIXED argument gate
     BOTH ledger sub-cases carry the errno arm — the free range as an
     ordinary grant, the occupied one beside its -EEXIST — so the witness
     needs no ledger test at all. -/
  else if mmap_noreplace_noaccess_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then ret_outcome (errno_ret ENOMEM) m
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .unmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      ret_outcome (errno_ret EINVAL) m
    else if ¬ (0 < (addr.toNat : Int)) then .unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else if mmap_noreplace_rw_b prot flags off then
    let nZ := page_round_up_Z (len.toNat : Int)
    if two_pow_64 ≤ (addr.toNat : Int) + nZ then ret_outcome (errno_ret ENOMEM) m
    else if ¬ ((addr.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) then .unmodeled
    else if !(((addr.toNat : Int) % page_size) == 0) then
      ret_outcome (errno_ret EINVAL) m
    else if ¬ (0 < (addr.toNat : Int)) then .unmodeled
    else ret_outcome (errno_ret witness_errno) m
  else .unmodeled

end

/-- The environment errno the mmap witness exhibits is an admissible one:
    ENOMEM heads `mmap_errnos`. -/
private theorem mem_mmap_errnos : witness_errno ∈ mmap_errnos := by
  simp [mmap_errnos, witness_errno]

section

-- The witness's last arms are `match`-free `if` chains nested under long
-- `if` chains that the proof drives together with the spec's, exactly as
-- in `Checks/Sys/Mm/Mmap.lean`.
set_option maxRecDepth 1000000

theorem mmap_witness_ok (addr len prot flags fd off : word) (i : SyscallInput) (m : Model) :
    mmap_spec addr len prot flags fd off i m (mmap_witness addr len prot flags fd off m) := by
  unfold mmap_spec mmap_witness
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · repeat rw [ite_eq_left hoff]
    by_cases hpl : mmap_pglen_ok_b len = true
    · repeat rw [ite_eq_left hpl]
      exact pure_ok _ i m
    · repeat rw [ite_eq_right hpl]
      exact unmodeled_intro i m
  · repeat rw [ite_eq_right hoff]
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · repeat rw [ite_eq_left hanon]
      exact unmodeled_intro i m
    · repeat rw [ite_eq_right hanon]
      by_cases hzlen : w_is0 len = true
      · repeat rw [ite_eq_left hzlen]
        by_cases hpa : mmap_plain_anon_b flags = true
        · repeat rw [ite_eq_left hpa]
          exact pure_ok _ i m
        · repeat rw [ite_eq_right hpa]
          exact unmodeled_intro i m
      · repeat rw [ite_eq_right hzlen]
        by_cases hmod : mmap_modeled_b prot flags off = true
        · repeat rw [ite_eq_left hmod]
          exact alt_l _ _ i m _
            (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
              witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
              (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
              (pure_ok _ i m))
        · repeat rw [ite_eq_right hmod]
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · repeat rw [ite_eq_left hnoacc]
            exact alt_l _ _ i m _
              (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                (pure_ok _ i m))
          · repeat rw [ite_eq_right hnoacc]
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · repeat rw [ite_eq_left hfx]
              try try dsimp only
              by_cases hovf : two_pow_64 ≤
                  (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · repeat rw [ite_eq_left hovf]
                exact pure_ok _ i m
              · repeat rw [ite_eq_right hovf]
                rw [bind_getModel]
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · repeat rw [ite_eq_left hceil]
                  exact unmodeled_intro i m
                · repeat rw [ite_eq_right hceil]
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · repeat rw [ite_eq_left halign]
                    exact pure_ok _ i m
                  · repeat rw [ite_eq_right halign]
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · repeat rw [ite_eq_left hpos]
                      exact unmodeled_intro i m
                    · repeat rw [ite_eq_right hpos]
                      try try dsimp only
                      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · repeat rw [ite_eq_left hcont]
                        exact alt_l _ _ i m _
                          (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                            witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                            (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                            (pure_ok _ i m))
                      · repeat rw [ite_eq_right hcont]
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · repeat rw [ite_eq_left hfresh]
                          exact alt_l _ _ i m _
                            (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                              witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                              (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                              (pure_ok _ i m))
                        · repeat rw [ite_eq_right hfresh]
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · repeat rw [ite_eq_left hspan]
                            exact alt_l _ _ i m _
                              (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                (pure_ok _ i m))
                          · repeat rw [ite_eq_right hspan]
                            exact unmodeled_intro i m
            · repeat rw [ite_eq_right hfx]
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · repeat rw [ite_eq_left hfrw]
                try try dsimp only
                by_cases hovf : two_pow_64 ≤
                    (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · repeat rw [ite_eq_left hovf]
                  exact pure_ok _ i m
                · repeat rw [ite_eq_right hovf]
                  rw [bind_getModel]
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · repeat rw [ite_eq_left hceil]
                    exact unmodeled_intro i m
                  · repeat rw [ite_eq_right hceil]
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · repeat rw [ite_eq_left halign]
                      exact pure_ok _ i m
                    · repeat rw [ite_eq_right halign]
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · repeat rw [ite_eq_left hpos]
                        exact unmodeled_intro i m
                      · repeat rw [ite_eq_right hpos]
                        try try dsimp only
                        generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · repeat rw [ite_eq_left hcont]
                          exact alt_l _ _ i m _
                            (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                              witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                              (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                              (pure_ok _ i m))
                        · repeat rw [ite_eq_right hcont]
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · repeat rw [ite_eq_left hfresh]
                            exact alt_l _ _ i m _
                              (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                (pure_ok _ i m))
                          · repeat rw [ite_eq_right hfresh]
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · repeat rw [ite_eq_left hspan]
                              exact alt_l _ _ i m _
                                (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                  witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                  (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                  (pure_ok _ i m))
                            · repeat rw [ite_eq_right hspan]
                              exact unmodeled_intro i m
              · repeat rw [ite_eq_right hfrw]
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · repeat rw [ite_eq_left hnrn]
                  try try dsimp only
                  by_cases hovf : two_pow_64 ≤
                      (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · repeat rw [ite_eq_left hovf]
                    exact pure_ok _ i m
                  · repeat rw [ite_eq_right hovf]
                    rw [bind_getModel]
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · repeat rw [ite_eq_left hceil]
                      exact unmodeled_intro i m
                    · repeat rw [ite_eq_right hceil]
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · repeat rw [ite_eq_left halign]
                        exact pure_ok _ i m
                      · repeat rw [ite_eq_right halign]
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · repeat rw [ite_eq_left hpos]
                          exact unmodeled_intro i m
                        · repeat rw [ite_eq_right hpos]
                          try try dsimp only
                          generalize hn : BitVec.ofInt 64
                            (page_round_up_Z (len.toNat : Int)) = n
                          by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · repeat rw [ite_eq_left hfree]
                            exact alt_l _ _ i m _
                              (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                (pure_ok _ i m))
                          · repeat rw [ite_eq_right hfree]
                            exact alt_l _ _ i m _
                              (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                (pure_ok _ i m))
                · repeat rw [ite_eq_right hnrn]
                  by_cases hnrr : mmap_noreplace_rw_b prot flags off = true
                  · repeat rw [ite_eq_left hnrr]
                    try try dsimp only
                    by_cases hovf : two_pow_64 ≤
                        (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · repeat rw [ite_eq_left hovf]
                      exact pure_ok _ i m
                    · repeat rw [ite_eq_right hovf]
                      rw [bind_getModel]
                      by_cases hceil : ¬ ((addr.toNat : Int) +
                          page_round_up_Z (len.toNat : Int) ≤ alloc_top (m_vmmaps m))
                      · repeat rw [ite_eq_left hceil]
                        exact unmodeled_intro i m
                      · repeat rw [ite_eq_right hceil]
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · repeat rw [ite_eq_left halign]
                          exact pure_ok _ i m
                        · repeat rw [ite_eq_right halign]
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · repeat rw [ite_eq_left hpos]
                            exact unmodeled_intro i m
                          · repeat rw [ite_eq_right hpos]
                            try try dsimp only
                            generalize hn : BitVec.ofInt 64
                              (page_round_up_Z (len.toNat : Int)) = n
                            by_cases hfree : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · repeat rw [ite_eq_left hfree]
                              exact alt_l _ _ i m _
                                (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                  witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                  (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                  (pure_ok _ i m))
                            · repeat rw [ite_eq_right hfree]
                              exact alt_l _ _ i m _
                                (bind_step (errno_from mmap_errnos) (fun e => err_ret e) i m
                                  witness_errno m (.ok (mkEffect (errno_ret witness_errno) [] []) m [])
                                  (errno_from_witness mmap_errnos witness_errno i m mem_mmap_errnos)
                                  (pure_ok _ i m))
                  · repeat rw [ite_eq_right hnrr]
                    exact unmodeled_intro i m

end

/-- munmap witness: mirrors the spec's five-way split — -EINVAL on a bad
    argument or a range leaving the user address space, the removal (with
    its unmap effect) on an exact recorded mapping, the no-op 0 on a free
    range below the stack band, the cut (with its unmap effect) on a
    partial unmap below the band, and `Unmodeled` (fail closed) on a range
    touching the image or reaching into the band (see `Mmap.munmap_spec`). -/
def munmap_witness (addr len : word) (m : Model) : Outcome SyscallEffect Model event :=
  if !(((addr.toNat : Int) % page_size) == 0) || w_is0 len then
    ret_outcome (errno_ret EINVAL) m
  else
    let nZ := page_round_up_Z (len.toNat : Int)
    -- the range leaves the user address space: see `Mmap.munmap_spec`
    if TASK_SIZE < (addr.toNat : Int) + nZ then ret_outcome (errno_ret EINVAL) m
    else
      let n := BitVec.ofInt 64 nZ
      if map_has (m_vmmaps m).vm_maps addr n then
        .ok (SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] [] [(addr, n)] [] [])
           (with_mmap_destroyed addr n
             (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                (map_remove (m_vmmaps m).vm_maps addr)
                (maps_subtract (m_vmmaps m).vm_noaccess
                   (addr.toNat : Int)
                   ((addr.toNat : Int) + (n.toNat : Int)))
                (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                (m_vmmaps m).vm_init_sp) m) []
      else if munmap_free_ok (m_vmmaps m) addr nZ then
        ret_outcome (BitVec.ofInt 64 0) m
      else if munmap_cut_ok (m_vmmaps m) addr nZ then
        .ok (SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] [] [(addr, n)] [] [])
           (with_mmap_destroyed addr n
              (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m) []
      else .unmodeled

theorem munmap_witness_ok (addr len : word) (i : SyscallInput) (m : Model) :
    munmap_spec addr len i m (munmap_witness addr len m) := by
  unfold munmap_spec munmap_witness
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · repeat rw [ite_eq_left hi]
    exact pure_ok _ i m
  · repeat rw [ite_eq_right hi]
    try dsimp only
    rw [bind_getModel]
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · repeat rw [ite_eq_left hbig]
      exact pure_ok _ i m
    · repeat rw [ite_eq_right hbig]
      try dsimp only
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · repeat rw [ite_eq_left hhas]
        exact bind_step (modify fun m' =>
            vm_forget_range (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int))
              (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
                 (map_remove (m_vmmaps m).vm_maps addr)
                 (maps_subtract (m_vmmaps m).vm_noaccess
                    (addr.toNat : Int)
                    ((addr.toNat : Int) + (n.toNat : Int)))
                 (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk
                 (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
                 (m_vmmaps m).vm_init_sp) m')) (fun _ => pure (SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] [] [(addr, n)] [] []))
          i m () _ _ (modify_ok _ i m) (pure_ok _ i _)
      · repeat rw [ite_eq_right hhas]
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · repeat rw [ite_eq_left hfree]
          exact pure_ok _ i m
        · repeat rw [ite_eq_right hfree]
          by_cases hcut : munmap_cut_ok (m_vmmaps m) addr
              (page_round_up_Z (len.toNat : Int)) = true
          · repeat rw [ite_eq_left hcut]
            exact alt_r _ _ i m _
              (bind_step (modify fun _ =>
                  with_mmap_destroyed addr n
                    (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m)
                (fun _ => pure (SyscallEffect.mkEffectU (BitVec.ofInt 64 0) [] []
                  [(addr, n)] [] []))
                i m () _ _ (modify_ok _ i m) (pure_ok _ i _))
          · repeat rw [ite_eq_right hcut]
            exact unmodeled_intro i m

/- (** mremap witness: deterministic -EINVAL for the modeled flag shape's
       misaligned address and zero/wrapping new size, [Unmodeled] for
       unsupported flags, the clone shape, and non-exact/protected source
       mappings.  Past those, an equal-size call has no injectable failure at
       all (Linux cannot fail one for lack of memory — see [mremap_spec]), so
       the witness is its deterministic success; every resizing call still has
       the always-available ENOMEM branch. *) -/

/- (** mprotect witness: the argument gates first, in Linux's order — the
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

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the three
    witnesses and their proofs.  The check below is sanity checking: it pins
    the `brk` witness's resolution and the ledgers its effect carries. -/

/-- The `brk` witness answers the tracked break, and the effect carries the
    zero-fill and unmap ledgers of that (non-moving) resolution. -/
example (req : word) (m : Model) :
    (match brk_witness req m with
     | .ok e m' _ =>
         e.eff_ret = (m_vmmaps m).vm_brk ∧ m' = with_brk_next m req (m_vmmaps m).vm_brk
     | .unmodeled => False) := by
  simp [brk_witness]

end LinuxSem.Checks.Witness.Mm.Mmap
