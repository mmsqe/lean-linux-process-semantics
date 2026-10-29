/-
  * LinuxSem.Checks.Cases.Mm.Mprotect — worked examples over mprotect (226)

  Worked cases over `Sys.Mm.Mprotect`, which answers to Linux
  [mm/mprotect.c]: the examples for the syscalls defined there, and no
  others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have come from `LinuxSem.Common.RocqSpelling`, transparent
  `abbrev`s DEFINITIONALLY EQUAL to what they stand for, so every
  statement below denotes exactly the same claim:
  - `Z_to_bv n z` is `BitVec.ofInt n z` and `bv_unsigned w` is
    `(w.toNat : Int)`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`, and
    `negb` is `Bool.not`;
  - record projections are applied as functions by the prelude
    (vm_maps (m_vmmaps m)), so they are opened by name here; Lean's own projection on
    the structure is `⋯.vm_maps`.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  A conjunction of closed equations is
  `(repeat constructor) <;> rfl`, and the parentheses are load-bearing:
  without them the tactic parses as `repeat (constructor <;> rfl)` and
  leaves any ≥3-way conjunction untouched; `constructor <;> rfl` covers
  the two-way case.  A statement whose `let` has to be zeta-reduced first
  opens with `dsimp only`.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.Common.RocqSpelling

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
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Mm.Mprotect

open LinuxSem.Common.RocqSpelling

/-! Rocq spellings (`bv_unsigned`, `Z_to_bv`, `zeqb`/`zleb`/`zltb`) come from
    `LinuxSem.Common.RocqSpelling`, opened above. -/

/-- `Bool.negb`, under its short name. -/
abbrev negb (b : Bool) : Bool := !b

/-! * LinuxProcessSem.Checks.Cases.Mm.Mprotect — worked examples over mprotect (226)

    Worked cases over `Sys.Mm.Mprotect`, which answers to Linux
    [mm/mprotect.c]: the examples for the syscalls defined there, and no
    others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/


theorem mprotect_middle_splits_noaccess_and_zeros_exactly :
  check_syscall
    (SyscallInput.mkInput 226 [69632, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull [] [(65536, 12288)]
          [(65536, 4096), (73728, 4096)] 0 0 16384 0 demo_sp)
        noaccess_three_pages) []
:= by rfl

theorem mprotect_noaccess_errno_preserves_ledger :
  check_syscall
    (SyscallInput.mkInput 226 [69632, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

/-! Exposing a reserved page consumes backed capacity at the permission
    transition.  With a zero-byte budget the successful effect is rejected,
    while the modeled ENOMEM outcome remains available. -/
def noaccess_zero_backing : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(65536, 4096)] [(65536, 4096)] 0 0 0 0 demo_sp)
    noaccess_three_pages

theorem mprotect_over_backed_budget_rejects_success :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_zero_backing
  = .CheckReject
:= by rfl

theorem mprotect_over_backed_budget_allows_enomem :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_zero_backing
  = .CheckOk noaccess_zero_backing []
:= by rfl

theorem mprotect_unmapped_forged_success_is_unmodeled :
  check_syscall
    (SyscallInput.mkInput 226 [131072, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) noaccess_three_pages
  = .CheckUnmodeled
:= by rfl

theorem mprotect_already_rw_errno_is_rejected :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = .CheckReject
:= by rfl

theorem mprotect_noaccess_outside_vm_maps_is_unmodeled :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(65536, 4096)]) noaccess_unowned
  = .CheckUnmodeled
:= by rfl

theorem mprotect_wrapping_end_is_enomem :
  check_syscall
    (SyscallInput.mkInput 226 [9223372036854775808, 9223372036854775808, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

theorem mprotect_wrapping_end_success_is_rejected :
  check_syscall
    (SyscallInput.mkInput 226 [9223372036854775808, 9223372036854775808, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) noaccess_three_pages
  = .CheckReject
:= by rfl

theorem mprotect_wrapping_end_precedes_unsupported_prot :
  check_syscall
    (SyscallInput.mkInput 226 [9223372036854775808, 9223372036854775808, 4, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

theorem mprotect_unaligned_precedes_zero_length :
  check_syscall
    (SyscallInput.mkInput 226 [65537, 0, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

theorem mprotect_growsdown_alone_is_not_a_conflict :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 16777219, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

theorem mprotect_growsup_alone_is_not_a_conflict :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 33554435, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

theorem mprotect_growsdown_alone_einval_is_rejected :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 16777219, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = .CheckReject
:= by rfl

theorem mprotect_growsup_alone_einval_is_rejected :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 33554435, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = .CheckReject
:= by rfl

theorem mprotect_grows_conflict_is_einval :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 50331651, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) noaccess_three_pages
  = .CheckOk noaccess_three_pages []
:= by rfl

def mprotect_lazy_guard : Model :=
  with_vm_backing [(65536, 8192)] [65536]
    (with_vmmaps
      (VmMaps.mkVmMapsFull [] [(65536, 8192)] [(69632, 4096)] 0 0 4096 0 demo_sp)
      noaccess_base)

/-! Exposing a MAP_NORESERVE guard keeps its lazy provenance and the first
    page's existing first-touch charge; the second page is not charged until
    an instruction actually accesses it. -/
theorem mprotect_lazy_guard_preserves_backing_provenance :
  check_syscall
    (SyscallInput.mkInput 226 [69632, 4096, 3, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(69632, 4096)]) mprotect_lazy_guard
  = .CheckOk (mprotect_model_next mprotect_lazy_guard 69632 4096) []
:= by rfl

theorem mprotect_lazy_guard_does_not_eagerly_charge :
  let post := mprotect_model_next mprotect_lazy_guard 69632 4096 ;
  m_vm_lazy post = [(65536, 8192)] ∧
  m_vm_materialized post = [65536] ∧
  vm_backing_used post = 4096
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ** The read-only downgrade, pinned at the checker

    [mprotect(addr, len, PROT_READ)] over a live rw mapping is the shape
    an allocator reaches for after filling a buffer, and Linux answers it
    with 0 (mm/mprotect.c [do_mprotect_pkey] / [mprotect_fixup]: newflags
    loses VM_WRITE and the mapping stays live and readable).  The model
    declines it, and `Sys.Mm.Mprotect` argues why: anonymous memory has
    one representation, which is simultaneously the readable view and the
    writable one, so a readable-not-writable page cannot be encoded.

    These read the checker directly, and the first is the one that
    matters: offering the checker the answer the real kernel gives has
    to yield [CheckUnmodeled], not [CheckOk].
    A spec that widened [mprotect_modeled_b] to "prot is a subset of the
    permissions the range already has" would take that 0 and admit every
    later store to a page Linux has made read-only. -/
theorem mprotect_read_only_downgrade_is_unmodeled :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 1 /- PROT_READ -/, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = .CheckUnmodeled
:= by rfl

/-! The declining arm is reached on the ARGUMENT SHAPE, so no offered
    effect rescues it: a zero-fill range is refused for the same reason,
    rather than being rejected as the wrong effect for a modeled call. -/
theorem mprotect_read_only_downgrade_with_zeros_is_unmodeled :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 4096, 1 /- PROT_READ -/, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(65536, 4096)])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = .CheckUnmodeled
:= by rfl

/-! PROT_READ over a range that is still PROT_NONE is declined too, which
    is worth pinning separately: that range IS in [vm_noaccess], so the
    rw transition's own gate matches on everything but the prot word.  A
    spec that tested containment before the prot would expose the page
    and hand the effect's zero-fill to a program that may not write it. -/
theorem mprotect_read_only_over_noaccess_is_unmodeled :
  check_syscall
    (SyscallInput.mkInput 226 [69632, 4096, 1 /- PROT_READ -/, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [(69632, 4096)]) noaccess_three_pages
  = .CheckUnmodeled
:= by rfl

/-! The positive half at the same prot: the gates ahead of the prot test
    answer for PROT_READ exactly as they do for the modeled rw, because
    Linux takes its zero-length return before validating prot at all.
    Its negative twin is below — a zero-length call admits 0 and nothing
    else. -/
theorem mprotect_read_only_zero_length_is_zero :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 1 /- PROT_READ -/, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 0 [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = .CheckOk (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384)
               noaccess_base) []
:= by rfl

theorem mprotect_read_only_zero_length_errno_is_rejected :
  check_syscall
    (SyscallInput.mkInput 226 [65536, 0, 1 /- PROT_READ -/, 0, 0, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ENOMEM) [] [])
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 16384) noaccess_base)
  = .CheckReject
:= by rfl

end LinuxSem.Checks.Cases.Mm.Mprotect
