/-
  * LinuxSem.Checks.MemoryMaterialization — lazy backing checks

  These checks pin the access-to-accounting seam used by sparse anonymous
  mappings: page expansion deduplicates repeated touches, recorded syscall
  ranges are included, and a cross-page access either materializes every new
  page or none of them.  Instruction reporting itself is checked separately
  by [Checks.RiscvAccessReporting].

  Spelling.

  `Z` is [Int]; `bv_unsigned` is the local abbreviation the other [Checks]
  files declare (the unsigned value as an `Int`, see
  `Checks/VmMapsDisjoint/Core.lean`), and every closed computation
  here is `by decide` — every goal in this file is closed, so nothing else
  was needed.  `Some (CheckOk m _)` is `some (.CheckOk m _)`.

  The two `SyscallEffect`s are written with the [mkEffect] (ret, writes,
  zeros) and [mkEffectU] (all six fields) spellings.  [mkEffect] is an
  abbreviation of the three-argument shape and [mkEffectU] is
  [SyscallEffect]'s constructor, so both spellings read the same — the only
  visible difference is that `[0; 0]` is a `List byte`, written
  `[BitVec.ofInt 8 0, BitVec.ofInt 8 0]`.

  [write_input_at] takes the `mkInput sysno args mem wmem` shape, whose
  `sysno` is a `Z`.  [SyscallInput] takes the word itself, so the literal
  is the structure constructor with `BitVec.ofInt 64 64` in the first
  field; nothing else changes.
-/
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.StackLayout

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude (check_result)

namespace LinuxSem.Checks.MemoryMaterialization

/-- `bv_unsigned w` is `w`'s value as an integer, declared here as the other
    `Checks` files declare it so that the statements below read in one
    vocabulary. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

def page_numbers (pages : List word) : List Int :=
  pages.map bv_unsigned

def materialized_numbers (result : Option (List word)) : Option (List Int) :=
  match result with
  | some pages => some (page_numbers pages)
  | none => none

theorem cross_page_expansion_is_complete :
    page_numbers (access_pages (BitVec.ofInt 64 0xffc) 8) = [(0x1000 : Int), 0] := by
  decide

theorem repeated_page_is_charged_once :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
        (0 : Int) (0x2000 : Int)
        [(BitVec.ofInt 64 0x10, 8), (BitVec.ofInt 64 0x20, 8)]) = some [0] := by
  decide

theorem already_materialized_page_is_not_charged_twice :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)]
        [BitVec.ofInt 64 0] (0x1000 : Int) (0x1000 : Int)
        [(BitVec.ofInt 64 0x10, 8)]) = some [0] := by
  decide

theorem cross_page_access_materializes_both_pages :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
        (0 : Int) (0x2000 : Int)
        [(BitVec.ofInt 64 0xffc, 8)]) = some [(0x1000 : Int), 0] := by
  decide

theorem cross_page_access_fails_atomically_at_limit :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
        (0 : Int) (0x1000 : Int)
        [(BitVec.ofInt 64 0xffc, 8)]) = none := by
  decide

theorem ordinary_mapping_does_not_consume_lazy_budget :
    materialized_numbers
      (materialize_accesses [] [] (0 : Int) (0 : Int)
        [(BitVec.ofInt 64 0xffc, 8)]) = some [] := by
  decide

theorem syscall_copyout_reports_exact_byte_range :
    syscall_effect_accesses
      (mkEffect (BitVec.ofInt 64 0)
        [(BitVec.ofInt 64 0xfff, [BitVec.ofInt 8 0, BitVec.ofInt 8 0])] [])
    = [(BitVec.ofInt 64 0xfff, 2)] := by
  decide

theorem syscall_copyout_cross_page_is_atomic :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
        (0 : Int) (0x2000 : Int)
        (syscall_effect_accesses
          (mkEffect (BitVec.ofInt 64 0)
            [(BitVec.ofInt 64 0xfff, [BitVec.ofInt 8 0, BitVec.ofInt 8 0])] [])))
    = some [(0x1000 : Int), 0] := by
  decide

theorem syscall_copyout_cross_page_fails_without_partial_charge :
    materialized_numbers
      (materialize_accesses [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
        (0 : Int) (0x1000 : Int)
        (syscall_effect_accesses
          (mkEffect (BitVec.ofInt 64 0)
            [(BitVec.ofInt 64 0xfff, [BitVec.ofInt 8 0, BitVec.ofInt 8 0])] [])))
    = none := by
  decide

theorem demand_zero_grant_does_not_count_as_copyout :
    syscall_effect_accesses
      (mkEffect (BitVec.ofInt 64 0) []
        [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x100000)]) = [] :=
  rfl

theorem syscall_copyins_precede_copyouts :
    syscall_effect_accesses
      (SyscallEffect.mkEffectU (BitVec.ofInt 64 0)
        [(BitVec.ofInt 64 0x3000, [BitVec.ofInt 8 0, BitVec.ofInt 8 0])]
        [] [] [] [(BitVec.ofInt 64 0x1000, 4)])
    = [(BitVec.ofInt 64 0x1000, 4), (BitVec.ofInt 64 0x3000, 2)] := by
  decide

/-- The extracted public checker must thread the accounted post-model, not
    the raw syscall-body post-model.  These two writes touch distinct pages
    of one lazy reservation under a one-page backing limit.  The first call
    charges its page; the second sees that charge and takes the atomic
    materialization-fault result. -/
def accounted_write_model : Model :=
  with_vm_backing [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] []
    (init_model [] (BitVec.ofInt 64 0) (BitVec.ofInt 64 0)
      (BitVec.ofInt 64 sp_window_lo) (0x1000 : Int)
      (mkProcInput [] [] [] IEof (BitVec.ofInt 64 1000) (BitVec.ofInt 64 1002) []
                   net_silent default_nofile (BitVec.ofInt 64 0) hwcap_rv64gc false .Sv48))

def byte_at (wanted : word) : word → Option byte :=
  fun a => if bv_eqb a wanted then some (BitVec.ofInt 8 0) else none

def write_input_at (a : word) : SyscallInput :=
  ⟨BitVec.ofInt 64 64,
   [BitVec.ofInt 64 1, a, BitVec.ofInt 64 1, BitVec.ofInt 64 0, BitVec.ofInt 64 0,
    BitVec.ofInt 64 0],
   byte_at a, fun _ => none⟩

def write_effect_at (a : word) : SyscallEffect :=
  SyscallEffect.mkEffectU (BitVec.ofInt 64 1) [] [] [] [] [(a, 1)]

def first_accounted_write : Option check_result :=
  check_syscall_for_run (write_input_at (BitVec.ofInt 64 0))
    (write_effect_at (BitVec.ofInt 64 0)) accounted_write_model

theorem accounted_checker_threads_first_touch :
    match first_accounted_write with
    | some (.CheckOk m _) => page_numbers (m_vm_materialized m) = [0]
    | _ => False := by
  rfl

def second_accounted_write : Option check_result :=
  match first_accounted_write with
  | some (.CheckOk m _) =>
      check_syscall_for_run (write_input_at (BitVec.ofInt 64 0x1000))
        (write_effect_at (BitVec.ofInt 64 0x1000)) m
  | result => result

theorem accounted_checker_preserves_charge_between_syscalls :
    second_accounted_write = none := by
  rfl

end LinuxSem.Checks.MemoryMaterialization
