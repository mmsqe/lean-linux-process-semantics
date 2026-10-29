/-
  * LinuxSem.Checks.Cases.Mm.Madvise — worked examples over madvise (233)

  Worked cases over `Sys.Mm.Madvise`, which answers to Linux
  [mm/madvise.c]: the examples for the syscall defined there, and no
  other.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the spec and checker of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have are supplied as local transparent `abbrev`s below,
  DEFINITIONALLY EQUAL to what they stand for, so every statement below
  denotes exactly the same claim:
  - `Z_to_bv n z` is `BitVec.ofInt n z` and `bv_unsigned w` is
    `(w.toNat : Int)`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`, and
    `negb` is `Bool.not`;
  - record projections are applied as functions by the prelude
    (vm_noaccess (m_vmmaps m)), so they are opened by name here; Lean's own projection on
    the structure is `⋯.vm_noaccess`.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  A conjunction of closed equations is
  `(repeat constructor) <;> rfl`, and the parentheses are load-bearing:
  without them the tactic parses as `repeat (constructor <;> rfl)` and
  leaves any ≥3-way conjunction untouched; `constructor <;> rfl` covers
  the two-way case.  A statement whose `let` has to be zeta-reduced first
  opens with `dsimp only`.
  `madvise_noaccess_remnant_decline_names_a_byte` is the one example here
  whose proof is a real argument rather than a computation; it runs over
  [Madvise.madvise_noaccess_decline_names_a_protected_byte] and
  [Mprotect.mprotect_model_next_noaccess_nonzero] step for step.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.StateVm

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Mm.Madvise

/-! ## The prelude's abbreviations, restored

    Each of these is a transparent alias, so it
    changes no statement's meaning. -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-- `Bool.negb`, under its short name. -/
abbrev negb (b : Bool) : Bool := !b

/-- `vm_maps` as a function. -/
abbrev vm_maps (h : VmMaps) : List (word × word) := h.vm_maps
/-- `vm_reserved` as a function. -/
abbrev vm_reserved (h : VmMaps) : List (word × word) := h.vm_reserved
/-- `vm_noaccess` as a function. -/
abbrev vm_noaccess (h : VmMaps) : List (word × word) := h.vm_noaccess

/-! * LinuxProcessSem.Checks.Cases.Mm.Madvise — worked examples over madvise (233)

    Worked cases over `Sys.Mm.Madvise`, which answers to Linux
    [mm/madvise.c]: the examples for the syscall defined there, and no
    other.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the spec and checker of the matching
    `Sys` module, without running a binary. -/


/-! The madvise input for [addr], [len] and [advice]; the three
    registers the kernel reads and nothing else. -/
def madvise_in (addr len advice : word) : SyscallInput :=
  SyscallInput.mkInput 233 [addr, len, advice, 0, 0, 0] (fun _ => none) (fun _ => none)

/- =========================================================================
   The argument gates, in the kernel's order
   ========================================================================= -/

/-! A misaligned address is -EINVAL ([is_valid_madvise]), and it is
    -EINVAL for EVERY advice value: the alignment test is one of four
    refusals that all answer the same errno, so the advice is never
    consulted. -/
theorem madvise_unaligned_einval :
  check_syscall (madvise_in 65537 4096 4)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckOk one_map_model []
:= by rfl

theorem madvise_unaligned_einval_for_any_advice :
  check_syscall (madvise_in 65537 4096 0)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckOk one_map_model []
  ∧ check_syscall (madvise_in 65537 4096 99)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckOk one_map_model []
:= by constructor <;> rfl

/-! A forged 0 on a misaligned address is rejected: the errno is the
    kernel's only answer there. -/
theorem madvise_unaligned_forged_success_rejected :
  check_syscall (madvise_in 65537 4096 4)
    (mkEffect 0 [] []) one_map_model
  = .CheckReject
:= by rfl

/-! Every advice value other than MADV_DONTNEED declines, including the
    ones Linux answers 0 with no effect (MADV_NORMAL) and the ones whose
    effect the model could not state (MADV_FREE).  A decline, never a
    guess: which values are even valid depends on the kernel
    configuration (see [Madvise.madvise_spec]). -/
theorem madvise_normal_is_unmodeled :
  check_syscall (madvise_in 65536 4096 0)
    (mkEffect 0 [] []) one_map_model
  = .CheckUnmodeled
:= by rfl

theorem madvise_free_is_unmodeled :
  check_syscall (madvise_in 65536 4096 8)
    (mkEffect 0 [] []) one_map_model
  = .CheckUnmodeled
:= by rfl

/-! The advice is read through [Syscall.int32]: garbage in the register's
    high half is discarded before the switch sees it, as the kernel's
    [int] parameter discards it. -/
theorem madvise_advice_is_read_as_int :
  check_syscall (madvise_in 65536 4096 (Z_to_bv 64 (2 ^ 32 + 4)))
    (mkEffect 0 [] [(65536, 4096)]) one_map_model
  = .CheckOk one_map_model []
:= by rfl

/-! [len = 0] is 0 at an aligned address ([madvise_should_skip]'s second
    exit), with no effect; an errno there is rejected. -/
theorem madvise_len_zero_is_zero :
  check_syscall (madvise_in 65536 0 4)
    (mkEffect 0 [] []) one_map_model
  = .CheckOk one_map_model []
:= by rfl

theorem madvise_len_zero_errno_rejected :
  check_syscall (madvise_in 65536 0 4)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckReject
:= by rfl

/-! THE ORDER OF THE TWO GATES is what this pins: the zero-length exit
    sits BEHIND the advice gate, so [len = 0] with any other advice value
    declines rather than answering 0.  Linux answers -EINVAL there for an
    invalid value ([is_valid_madvise] runs [madvise_behavior_valid]
    before [madvise_should_skip]'s zero-length exit) and 0 for a valid
    one, and which values are valid is a configuration question; a
    mutant that tests [w_is0 len] first answers 0 for every value and
    keeps every other example in this file green. -/
theorem madvise_len_zero_other_advice_is_unmodeled :
  check_syscall (madvise_in 65536 0 99)
    (mkEffect 0 [] []) one_map_model
  = .CheckUnmodeled
  ∧ check_syscall (madvise_in 65536 0 0)
    (mkEffect 0 [] []) one_map_model
  = .CheckUnmodeled
:= by constructor <;> rfl

/-! A range whose page-rounded end reaches 2^64 is -EINVAL
    ([is_valid_madvise]'s [start + len < start]), as is a [len] whose
    rounding wraps to zero ([len_in && !len]). -/
theorem madvise_wrapping_range_einval :
  check_syscall
    (madvise_in (Z_to_bv 64 (two_pow_64 - 4096)) 8192 4)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckOk one_map_model []
  ∧ check_syscall
    (madvise_in 65536 (Z_to_bv 64 (two_pow_64 - 1)) 4)
    (mkEffect (errno_ret EINVAL) [] []) one_map_model
  = .CheckOk one_map_model []
:= by constructor <;> rfl

/- =========================================================================
   The answered shape, and the three ways to leave it
   ========================================================================= -/

/-! Over a whole live rw grant: 0 and the zero-fill of the range.  With
    nothing lazy in the ledger the post-model is the pre-model. -/
theorem madvise_dontneed_whole_grant :
  check_syscall (madvise_in 65536 4096 4)
    (mkEffect 0 [] [(65536, 4096)]) one_map_model
  = .CheckOk one_map_model []
:= by rfl

/-! The zero-fill is load-bearing: a 0 that keeps the bytes is a kernel
    that did not zap the range, and is rejected. -/
theorem madvise_without_zeros_rejected :
  check_syscall (madvise_in 65536 4096 4)
    (mkEffect 0 [] []) one_map_model
  = .CheckReject
:= by rfl

/-! No errno is injectable on the answered shape, and no other return
    is admissible: -ENOMEM and 1 are both rejected. -/
theorem madvise_nonzero_return_rejected :
  check_syscall (madvise_in 65536 4096 4)
    (mkEffect (errno_ret ENOMEM) [] []) one_map_model
  = .CheckReject
  ∧ check_syscall (madvise_in 65536 4096 4)
    (mkEffect 1 [] [(65536, 4096)]) one_map_model
  = .CheckReject
:= by constructor <;> rfl

/-! A range with a page outside the grant declines.  Linux applies the
    advice to the mapped page and reports -ENOMEM for the hole
    ([madvise_walk_vmas]); the ledger cannot say which pages that is, so
    the model does not answer.  This is [map_contains]'s conjunct of
    [Madvise.madvise_dontneed_ok]. -/
theorem madvise_partial_grant_is_unmodeled :
  check_syscall (madvise_in 65536 8192 4)
    (mkEffect 0 [] [(65536, 8192)]) one_map_model
  = .CheckUnmodeled
:= by rfl

/-! A range the ledger holds nothing of declines, whether below the run's
    [State.alloc_top] (a hole, -ENOMEM on Linux) or inside the stack band
    above it (the stack Linux would zap and the ledger does not carry).
    Both conjuncts fall on the same [map_contains] test — the stack is in
    no ledger, so there is no separate stack-band gate to pin; the second
    is the same pin at the one address a reader would ask about. -/
theorem madvise_free_range_is_unmodeled :
  check_syscall (madvise_in 131072 4096 4)
    (mkEffect 0 [] []) one_map_model
  = .CheckUnmodeled
  ∧ check_syscall (madvise_in (Z_to_bv 64 demo_top) 4096 4)
    (mkEffect 0 [] [(Z_to_bv 64 demo_top, 4096)]) one_map_model
  = .CheckUnmodeled
:= by constructor <;> rfl

/-! The image's LOAD pages decline even on a ledger that also lists them
    in [vm_maps] — the [vm_reserved] conjunct.  No reachable state has
    such a ledger (grants are placed clear of the image), so this pins the
    conjunct on the one fixture that can reach it. -/
theorem madvise_image_range_is_unmodeled :
  check_syscall (madvise_in 4096 4096 4)
    (mkEffect 0 [] [(4096, 4096)]) noaccess_image_overlap
  = .CheckUnmodeled
:= by rfl

/-! A PROT_NONE range declines: Linux answers 0 there, but the machine
    overlay holds no bytes for a protected page to zap, and re-exposing
    one is [mprotect]'s zero-fill, not this arm's — the [vm_noaccess]
    conjunct. -/
theorem madvise_noaccess_range_is_unmodeled :
  check_syscall (madvise_in 65536 4096 4)
    (mkEffect 0 [] [(65536, 4096)]) noaccess_three_pages
  = .CheckUnmodeled
:= by rfl

/-! …and the same conjunct on a protected list that a SUBTRACTION left
    behind, which is the shape the conjunct's soundness turns on.
    [mprotect] exposes the MIDDLE page of the three, cutting the one
    recorded range into a remnant either side of it; the request below
    meets the upper remnant.

    What the example is for is not the decline — the line above already
    pins that — but why the decline is ATTRIBUTABLE.  [region_free] is
    closed by an entry that overlaps, and [State.iv_overlap] counts a
    ZERO-SIZE entry strictly inside the range as overlapping, so on the
    face of it a cut that left a vacuous remnant would decline a
    request over memory the process can read and write throughout.  The
    witness here comes out of
    [Madvise.madvise_noaccess_decline_names_a_protected_byte], and its
    invariant premise is discharged by
    [Mprotect.mprotect_model_next_noaccess_nonzero] rather than by
    reading the remnant list off this fixture: what the example shows is
    that the cut COULD NOT have manufactured a vacuous entry, not merely
    that this one did not.

    The two chained comparisons `a <= x < b` are read as
    `a <= x ∧ x < b`, so the `∧` below is the chain's own reading, not a
    strengthening of it. -/
def madvise_cut_addr : word := Z_to_bv 64 73728
def madvise_cut_n : word := Z_to_bv 64 4096

def madvise_noaccess_cut : Model :=
  mprotect_model_next noaccess_three_pages (Z_to_bv 64 69632) madvise_cut_n

theorem madvise_noaccess_remnant_decline_names_a_byte :
  check_syscall (madvise_in 73728 4096 4)
    (mkEffect 0 [] [(73728, 4096)]) madvise_noaccess_cut
  = .CheckUnmodeled
  ∧ region_free (vm_noaccess (m_vmmaps madvise_noaccess_cut))
       madvise_cut_addr madvise_cut_n = false
  ∧ ∃ a sz x,
       (a, sz) ∈ vm_noaccess (m_vmmaps madvise_noaccess_cut)
       ∧ 0 < bv_unsigned sz
       ∧ (bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned sz)
       ∧ (bv_unsigned madvise_cut_addr ≤ x ∧
          x < bv_unsigned madvise_cut_addr + bv_unsigned madvise_cut_n) := by
  have hdecl :
      check_syscall (madvise_in 73728 4096 4)
        (mkEffect 0 [] [(73728, 4096)]) madvise_noaccess_cut = .CheckUnmodeled := by
    rfl
  have hfree : region_free (vm_noaccess (m_vmmaps madvise_noaccess_cut))
      madvise_cut_addr madvise_cut_n = false := by
    rfl
  refine ⟨hdecl, hfree, ?_⟩
  refine madvise_noaccess_decline_names_a_protected_byte
    (m_vmmaps madvise_noaccess_cut) madvise_cut_addr madvise_cut_n ?_ ?_ hfree
  · apply mprotect_model_next_noaccess_nonzero
    unfold vm_noaccess_entries_nonzero
    apply entries_nonzero_forallb
    rfl
  · -- `vm_compute` takes `0 < 4096` down to `Lt = Lt`; `lia` never sees a
    -- comparison to solve.  In Lean the closed goal is decided outright.
    decide

/- =========================================================================
   What the arm is for: giving first-touch charges back
   ========================================================================= -/

/-! A two-page budget and a two-page MAP_NORESERVE grant.  Flags 16418
    is MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE. -/
def madvise_lazy_base : Model :=
  with_vmmaps (mkVmMaps [] [] 0 0 8192) noaccess_base

def madvise_lazy_granted : Model :=
  vm_add_lazy 65536 8192
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192) madvise_lazy_base)

theorem madvise_lazy_grant :
  check_syscall
    (SyscallInput.mkInput 222 [0, 8192, 3, 16418, mmap_fd_none, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 65536 [] [(65536, 8192)]) madvise_lazy_base
  = .CheckOk madvise_lazy_granted []
:= by rfl

/-! The same grant placed by MAP_FIXED_NOREPLACE at the address the
    runtime names (flags 1064994 = MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE
    |MAP_FIXED_NOREPLACE) lands in the ledger as the same anonymous lazy
    entry: the post-model IS [madvise_lazy_granted], so every madvise
    example below holds of a NOREPLACE-placed shadow mapping unchanged
    and the arm needs no case for it. -/
theorem madvise_lazy_grant_by_noreplace :
  check_syscall
    (SyscallInput.mkInput 222 [65536, 8192, 3, 1064994, mmap_fd_none, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 65536 [] [(65536, 8192)]) madvise_lazy_base
  = .CheckOk madvise_lazy_granted []
:= by rfl

/-! The grant costs nothing until a page is touched; the first touch
    charges that page and no other. -/
def madvise_lazy_touched : Model :=
  with_vm_backing (m_vm_lazy madvise_lazy_granted) [65536]
    madvise_lazy_granted

theorem madvise_lazy_first_touch_charges :
  vm_backing_used madvise_lazy_granted = 0
  ∧ materialize_model_accesses madvise_lazy_granted [(65536, 1)]
     = some madvise_lazy_touched
  ∧ vm_backing_used madvise_lazy_touched = 4096
:= by (repeat constructor) <;> rfl

/-! MADV_DONTNEED over the grant returns the charge: the post-model IS
    the pre-touch model — same mapping, same lazy provenance, no
    materialized page — so the budget is back to its pre-touch value
    and everything but the charge ledger is pinned equal by the
    equation itself. -/
theorem madvise_dontneed_returns_the_charge :
  check_syscall (madvise_in 65536 8192 4)
    (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_touched
  = .CheckOk madvise_lazy_granted []
:= by rfl

theorem madvise_dontneed_budget_back_to_pre_touch :
  let post := madvise_dontneed_next madvise_lazy_touched 65536 8192 ;
  vm_backing_used post = 0
  ∧ m_vm_lazy post = [(65536, 8192)]
  ∧ m_vm_materialized post = []
  ∧ m_vmmaps post = m_vmmaps madvise_lazy_touched
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The pages are lazy again, not free: the next touch charges the page
    exactly as the first one did.  Documentary rather than a pin —
    [materialize_model_accesses] is idempotent on a page still charged,
    so a mutant that never gave the page back passes this too; the pin
    is [madvise_dontneed_returns_the_charge] above. -/
theorem madvise_dontneed_next_touch_recharges :
  materialize_model_accesses
    (madvise_dontneed_next madvise_lazy_touched 65536 8192)
    [(65536, 1)]
  = some madvise_lazy_touched
:= by rfl

/-! Only the pages IN the range are given back.  Both pages touched,
    DONTNEED over the second: the first keeps its charge. -/
def madvise_lazy_both_touched : Model :=
  with_vm_backing (m_vm_lazy madvise_lazy_granted) [69632, 65536]
    madvise_lazy_granted

theorem madvise_dontneed_only_the_range :
  check_syscall (madvise_in 69632 4096 4)
    (mkEffect 0 [] [(69632, 4096)]) madvise_lazy_both_touched
  = .CheckOk madvise_lazy_touched []
  ∧ vm_backing_used madvise_lazy_both_touched = 8192
  ∧ vm_backing_used madvise_lazy_touched = 4096
:= by (repeat constructor) <;> rfl

/-! The scenario the arm is for, end to end.  Two pages granted lazily
    and both touched fill the two-page budget: a further one-page eager
    grant (flags 34 = MAP_PRIVATE|MAP_ANONYMOUS) cannot be admitted, only
    its -ENOMEM can.  After MADV_DONTNEED over the two pages the same
    grant fits.  Without the arm the model has no way back from the
    first state, and a program that recycles its pages runs out of the
    budget where Linux does not. -/
def madvise_scenario_grant : SyscallInput :=
  SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
    (fun _ => none) (fun _ => none)

theorem madvise_scenario_grant_refused_while_charged :
  check_syscall madvise_scenario_grant
    (mkEffect 131072 [] [(131072, 4096)]) madvise_lazy_both_touched
  = .CheckReject
  ∧ check_syscall madvise_scenario_grant
    (mkEffect (errno_ret ENOMEM) [] []) madvise_lazy_both_touched
  = .CheckOk madvise_lazy_both_touched []
:= by constructor <;> rfl

/-! After MADV_DONTNEED over both pages the model is the untouched grant
    again — stated as that independently written model, not as the
    arm's own post-state function, so the content is what is pinned. -/
theorem madvise_scenario_dontneed :
  check_syscall (madvise_in 65536 8192 4)
    (mkEffect 0 [] [(65536, 8192)]) madvise_lazy_both_touched
  = .CheckOk madvise_lazy_granted []
:= by rfl

theorem madvise_scenario_grant_fits_after_dontneed :
  check_syscall madvise_scenario_grant
    (mkEffect 131072 [] [(131072, 4096)]) madvise_lazy_granted
  = .CheckOk
      (with_vmmaps (mkVmMaps [] [(131072, 4096), (65536, 8192)] 0 0 8192)
        madvise_lazy_granted) []
:= by rfl

/-! An EAGERLY charged grant keeps its charge across the call, as Linux
    keeps the VMA's commit: the budget does not move. -/
theorem madvise_eager_grant_keeps_its_charge :
  vm_backing_used one_map_model = 4096
  ∧ vm_backing_used (madvise_dontneed_next one_map_model 65536 4096) = 4096
:= by constructor <;> rfl

end LinuxSem.Checks.Cases.Mm.Madvise
