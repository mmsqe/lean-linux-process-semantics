/-
  * LinuxSem.Checks.Cases.Mm.Mremap — worked examples over mremap (216)

  Worked cases over `Sys.Mm.Mremap`, which answers to Linux
  [mm/mremap.c]: the examples for the syscalls defined there, and no
  others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
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
    (`vm_maps (m_vmmaps m)`), so they are opened by name here; Lean's own
    projection on the structure is `⋯.vm_maps`.

  The three statements that spell a comparison infix (`=?`, `<?`, `<=?`)
  carry it in the prefix form of those same shims, because Lean has no
  infix `Z.eqb`-style operator to hang them on; the operator each one
  stands for is named at the declaration.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  A conjunction of closed equations is
  `(repeat constructor) <;> rfl`, and the parentheses are load-bearing:
  without them the tactic parses as `repeat (constructor <;> rfl)` and
  leaves any ≥3-way conjunction untouched; `constructor <;> rfl` covers
  the two-way case.  A statement whose `let` has to be zeta-reduced first
  opens with `dsimp only`.

  The two declarations whose proofs are real arguments
  (`mremap_wrapping_old_size_cannot_pass_the_source_gate`,
  `mremap_move_gap_is_the_retained_source`) are argued on the `List`
  lemmas; see the notes at each.

  One statement needs its ASSOCIATIVITY restored rather than a spelling:
  in `mremap_move_gap_is_the_retained_source` the prefix
  `(old, old_n) :: vm_reserved h ++ vm_maps …` groups as
  `(old, old_n) :: (vm_reserved h ++ vm_maps …)` — both operators are
  level 60 and right associative — while Lean's `::` binds tighter than
  `++`, so the parentheses there are load-bearing and are called out
  again at the declaration.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
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
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Mm.Mmap

namespace LinuxSem.Checks.Cases.Mm.Mremap

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

/-- `ms_mem` as a function. -/
abbrev ms_mem (st : machine_state) : word → Option byte := st.ms_mem

/-- `vm_maps` as a function. -/
abbrev vm_maps (h : VmMaps) : List (word × word) := h.vm_maps
/-- `vm_reserved` as a function. -/
abbrev vm_reserved (h : VmMaps) : List (word × word) := h.vm_reserved
/-- `vm_noaccess` as a function. -/
abbrev vm_noaccess (h : VmMaps) : List (word × word) := h.vm_noaccess

/-! * LinuxProcessSem.Checks.Cases.Mm.Mremap — worked examples over mremap (216)

    Worked cases over `Sys.Mm.Mremap`, which answers to Linux
    [mm/mremap.c]: the examples for the syscalls defined there, and no
    others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/


def mremap_two_page_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

def mremap_in (old_size new_size : word) : SyscallInput :=
  /- a4 is deliberately nonzero: Linux ignores new_address without FIXED. -/
  SyscallInput.mkInput 216 [65536, old_size, new_size, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

theorem mremap_enomem_preserves_state :
  check_syscall (mremap_in 8192 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = .CheckOk mremap_two_page_model []
:= by rfl

def mremap_shrunk_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
    mremap_two_page_model

theorem mremap_shrink_refunds_tail :
  check_syscall (mremap_in 8192 4096)
    (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_two_page_model
  = .CheckOk mremap_shrunk_model []
:= by rfl

theorem mremap_refund_is_regrantable :
  check_syscall
    (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
      (fun _ => none) (fun _ => none))
    (mkEffect 131072 [] [(131072, 4096)]) mremap_shrunk_model
  = .CheckOk
      (with_vmmaps
        (mkVmMaps [] [(131072, 4096), (65536, 4096)] 0 0 8192)
        mremap_shrunk_model) []
:= by rfl

def mremap_budget_full_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
    (init_model [] 0 0 demo_sp 4096 (demo_input [] IEof))

theorem mremap_grow_beyond_budget_rejected :
  check_syscall (mremap_in 4096 8192)
    (mkEffect 65536 [] [(69632, 4096)]) mremap_budget_full_model
  = .CheckReject
:= by rfl

def mremap_occupied_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096), (131072, 8192)] 0 0 16384)
    (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof))

theorem mremap_move_to_occupied_range_rejected :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [MemCopy.mkCopy 65536 131072 4096] []) mremap_occupied_model
  = .CheckReject
:= by rfl

def mremap_snapshot_mem (a : word) : Option byte :=
  if bv_eqb a 65536 then some 90
  else if bv_eqb a 65537 then some 165
  else if bv_eqb a 196608 then some 51
  else none

def mremap_snapshot_ms : machine_state := {
  ms_regs := bvmap_empty, ms_fregs := bvmap_empty, ms_pc_val := 0,
  ms_svc_pending := none, ms_resv := none, ms_fcsr := 0,
  ms_mem := mremap_snapshot_mem, ms_rom := fun _ => none
}

def mremap_snapshot_effect : SyscallEffect :=
  SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
    [MemCopy.mkCopy 65536 131072 4096] []

theorem mremap_copy_reads_pre_effect_snapshot :
  let after := ms_mem (apply_effect mremap_snapshot_ms mremap_snapshot_effect) ;
  after 131072 = some 90 ∧
  after 131073 = some 165 ∧
  after 65536 = none ∧
  after 135168 = some 0 ∧
  after 196608 = some 51
:= by (try dsimp only); (repeat constructor) <;> rfl

theorem mremap_equal_size_accepts :
  check_syscall (mremap_in 8192 8192)
    (mkEffect 65536 [] []) mremap_two_page_model
  = .CheckOk mremap_two_page_model []
:= by rfl

theorem mremap_equal_size_enomem_rejected :
  check_syscall (mremap_in 8192 8192)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = .CheckReject
:= by rfl

def mremap_one_page_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem mremap_inplace_grow_accepts :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_one_page_model
  = .CheckOk
      (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
         mremap_one_page_model) []
:= by rfl

def mremap_crowded_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 4096), (69632, 4096)] 0 0 16384)
    (init_model [] 0 0 demo_sp 16384 (demo_input [] IEof))

theorem mremap_inplace_grow_into_neighbour_rejected :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_crowded_model
  = .CheckReject
:= by rfl

def mremap_below_image_model : Model :=
  with_vmmaps (mkVmMaps [(69632, 4096)] [(65536, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem mremap_inplace_grow_into_image_rejected :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_below_image_model
  = .CheckReject
:= by rfl

theorem mremap_move_out_of_the_image_accepts :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [MemCopy.mkCopy 65536 131072 4096] []) mremap_below_image_model
  = .CheckOk
      (with_vmmaps (mkVmMaps [(69632, 4096)] [(131072, 8192)] 0 0 8192)
         mremap_below_image_model) []
:= by rfl

def mremap_at_in (old_addr old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [old_addr, old_size, new_size, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

def mremap_grow_to_ceiling_model : Model :=
  with_vmmaps (mkVmMaps [] [(140735332474880, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem mremap_inplace_grow_to_ceiling_accepts :
  check_syscall (mremap_at_in 140735332474880 4096 8192)
    (SyscallEffect.mkEffectU 140735332474880 [] [(140735332478976, 4096)] [] [] [])
    mremap_grow_to_ceiling_model
  = .CheckOk
      (with_vmmaps (mkVmMaps [] [(140735332474880, 8192)] 0 0 8192)
         mremap_grow_to_ceiling_model) []
:= by rfl

def mremap_grow_past_ceiling_model : Model :=
  with_vmmaps (mkVmMaps [] [(140735332478976, 4096)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem mremap_inplace_grow_past_ceiling_rejected :
  check_syscall (mremap_at_in 140735332478976 4096 8192)
    (SyscallEffect.mkEffectU 140735332478976 [] [(140735332483072, 4096)] [] [] [])
    mremap_grow_past_ceiling_model
  = .CheckReject
:= by rfl

theorem mremap_move_down_from_ceiling_accepts :
  check_syscall (mremap_at_in 140735332478976 4096 8192)
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(140735332478976, 4096)]
      [MemCopy.mkCopy 140735332478976 65536 4096] []) mremap_grow_past_ceiling_model
  = .CheckOk
      (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
         mremap_grow_past_ceiling_model) []
:= by rfl

theorem mremap_wrapping_new_size_is_einval :
  check_syscall (mremap_in 8192 18446744073709551615)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = .CheckOk mremap_two_page_model []
:= by rfl

theorem mremap_wrapping_new_size_success_rejected :
  check_syscall (mremap_in 8192 18446744073709551615)
    (mkEffect 65536 [] []) mremap_two_page_model
  = .CheckReject
:= by rfl

theorem mremap_top_aligned_new_size_is_enomem :
  check_syscall (mremap_in 8192 18446744073709547520)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = .CheckOk mremap_two_page_model []
:= by rfl

theorem mremap_top_aligned_new_size_einval_rejected :
  check_syscall (mremap_in 8192 18446744073709547520)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = .CheckReject
:= by rfl

def mremap_misaligned_in (old_size new_size : word) : SyscallInput :=
  SyscallInput.mkInput 216 [65537, old_size, new_size, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

theorem mremap_old_size_zero_after_einval_gates :
  check_syscall (mremap_misaligned_in 0 4096)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = .CheckOk mremap_two_page_model []
:= by rfl

theorem mremap_old_size_zero_aligned_is_unmodeled :
  check_syscall (mremap_in 0 4096)
    (mkEffect (errno_ret EINVAL) [] []) mremap_two_page_model
  = .CheckUnmodeled
:= by rfl

def mremap_zero_entry_model : Model :=
  with_vmmaps (mkVmMaps [] [(65536, 0)] 0 0 8192)
    (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof))

theorem mremap_zero_entry_passes_the_source_gate :
  mremap_source_b (m_vmmaps mremap_zero_entry_model) 65536 0 0 = true
:= by rfl

theorem mremap_old_size_zero_gate_precedes_the_source_gate :
  check_syscall (mremap_in 0 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_zero_entry_model
  = .CheckUnmodeled
:= by rfl

theorem mremap_wrapping_old_size_cannot_pass_the_source_gate :
  ∀ h old old_n old_nZ,
    (two_pow_64 ≤ old_nZ) →
    mremap_source_b h old old_n old_nZ = false
:= by
  intro h old old_n old_nZ Hwrap
  -- The first conjunct is the one that fails: the sum wraps past 2^64, so it
  -- is above every ledger's `alloc_top`.
  have htop : alloc_top h < two_pow_64 := alloc_top_lt h
  have h0 : (0 : Int) ≤ (old.toNat : Int) := Int.natCast_nonneg _
  have hle : ¬ ((old.toNat : Int) + old_nZ ≤ alloc_top h) := by omega
  simp [mremap_source_b, decide_eq_false hle]

theorem mremap_wrapping_old_size_rounds_past_the_word :
  -- The `Z` comparison `two_pow_64 <= …`, in the prefix form of the shim.
  zleb two_pow_64 (page_round_up_Z (bv_unsigned (18446744073709551615 : word)))
  = true
:= by rfl

theorem mremap_wrapping_old_size_is_unmodeled :
  check_syscall (mremap_in 18446744073709551615 4096)
    (mkEffect (errno_ret ENOMEM) [] []) mremap_two_page_model
  = .CheckUnmodeled
:= by rfl

theorem mremap_move_gap_is_the_retained_source :
  ∀ h old dst old_n new_n,
    bv_eqb dst old = false →
    map_has (vm_maps (mremap_maps_next h old dst new_n)) old old_n = false
    ∧ ∀ r n,
         -- `::` and `++` are BOTH level 60 and right associative in the
         -- source spelling, so `(old, old_n) :: vm_reserved h ++ vm_maps …`
         -- groups as `(old, old_n) :: (vm_reserved h ++ vm_maps …)`.
         -- Lean's `::` binds tighter than `++`, so these parentheses are
         -- what keeps the statement the same one.
         region_free
           ((old, old_n) :: (vm_reserved h
              ++ vm_maps (mremap_maps_next h old dst new_n))) r n = true
         ↔
         iv_overlap r n old old_n = false
         ∧ region_free
              (vm_reserved h
                 ++ vm_maps (mremap_maps_next h old dst new_n)) r n = true
:= by
  intro h old dst old_n new_n Hdst
  constructor
  · -- `mremap_maps_next` replaced `old` with `dst`, and `dst <> old`, so no
    -- entry of the retained list is based at `old`.
    have hgap :
        (List.filter (fun p => !(p.1 == old)) h.vm_maps).any
          (fun p => p.1 == old && p.2 == old_n) = false := by
      rw [List.any_eq_false]
      intro p hp
      rw [List.mem_filter] at hp
      have hne : (p.1 == old) = false := by simpa using hp.2
      simp [hne]
    rw [show vm_maps (mremap_maps_next h old dst new_n)
          = (dst, new_n) :: List.filter (fun p => !(p.1 == old)) h.vm_maps from rfl]
    have hfst : (dst == old) = false := Hdst
    rw [map_has, List.any_cons]
    dsimp only
    rw [hfst, Bool.false_and, Bool.false_or]
    exact hgap
  · -- The prepended `(old, old_n)` is the ONLY difference between the two
    -- `region_free` arguments, so the two conjuncts line up one for one.
    intro r n
    have hstep : ∀ (rest : List (word × word)),
        region_free ((old, old_n) :: rest) r n
          = (!(iv_overlap r n old old_n) && region_free rest r n) := by
      intro rest
      rfl
    rw [hstep, Bool.and_eq_true, Bool.not_eq_true']

theorem apply_effect_zeros_run_after_unmaps :
  ms_mem (apply_effect mremap_snapshot_ms
            (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)] [] [])) 65536
  = some 0
:= by rfl

theorem apply_effect_copies_run_after_zeros :
  ms_mem (apply_effect mremap_snapshot_ms
            (SyscallEffect.mkEffectU 0 [] [(131072, 4096)] []
               [MemCopy.mkCopy 65536 131072 4096] [])) 131072
  = some 90
:= by rfl

theorem apply_effect_writes_run_after_copies :
  ms_mem (apply_effect mremap_snapshot_ms
            (SyscallEffect.mkEffectU 0 [(131072, [7])] [] []
               [MemCopy.mkCopy 65536 131072 4096] [])) 131072
  = some 7
:= by rfl

theorem apply_effect_copy_source_survives_unmap_and_zero :
  let after := ms_mem (apply_effect mremap_snapshot_ms
                 (SyscallEffect.mkEffectU 0 [] [(65536, 4096)] [(65536, 4096)]
                    [MemCopy.mkCopy 65536 131072 4096] [])) ;
  after 131072 = some 90 ∧ after 65536 = some 0
:= by (try dsimp only); (repeat constructor) <;> rfl

def mremap_orphan_in : SyscallInput :=
  /- a4 is deliberately nonzero: Linux ignores new_address without FIXED. -/
  SyscallInput.mkInput 216 [131072, 4096, 8192, 1, 0x12345000, 0]
    (fun _ => none) (fun _ => none)

theorem mremap_move_onto_brk_orphan_page_rejected :
  check_syscall mremap_orphan_in
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
      [MemCopy.mkCopy 131072 65536 4096] []) m_brk_orphan_with_source
  = .CheckReject
:= by rfl

theorem mremap_move_above_brk_orphan_accepts :
  check_syscall mremap_orphan_in
    (SyscallEffect.mkEffectU 69632 [] [(73728, 4096)] [(131072, 4096)]
      [MemCopy.mkCopy 131072 69632 4096] []) m_brk_orphan_with_source
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull brk_reserved [(69632, 8192), (65536, 4084)]
          [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
        m_brk_orphan_with_source) []
:= by rfl

theorem mremap_move_onto_orphan_without_residual_accepts :
  check_syscall mremap_orphan_in
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [(131072, 4096)]
      [MemCopy.mkCopy 131072 65536 4096] []) m_brk_orphan_without_residual
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull brk_reserved [(65536, 8192)]
          [(65536, 4096)] 65536 69620 demo_limit 0 demo_sp)
        m_brk_orphan_without_residual) []
:= by rfl

def mremap_lazy_two_pages : Model :=
  with_vm_backing [(65536, 8192)] [65536, 69632]
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
      (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)))

theorem mremap_lazy_shrink_drops_tail_charge :
  check_syscall (mremap_in 8192 4096)
    (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_lazy_two_pages
  = .CheckOk
      (mremap_model_next mremap_lazy_two_pages 65536 8192 65536 4096) []
:= by rfl

theorem mremap_lazy_shrink_ledgers_are_exact :
  let post := mremap_model_next mremap_lazy_two_pages
                65536 8192 65536 4096 ;
  m_vm_lazy post = [(65536, 4096)] ∧
  m_vm_materialized post = [65536] ∧
  vm_backing_used post = 4096
:= by (try dsimp only); (repeat constructor) <;> rfl

def mremap_lazy_one_page : Model :=
  with_vm_backing [(65536, 4096)] [65536]
    (with_vmmaps (mkVmMaps [] [(65536, 4096)] 0 0 4096)
      (init_model [] 0 0 demo_sp 4096 (demo_input [] IEof)))

/-! A lazy grow succeeds at a full backed budget because its new tail is a
    reservation, not an eager charge. -/
theorem mremap_lazy_grow_bypasses_eager_delta :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 65536 [] [(69632, 4096)] [] [] []) mremap_lazy_one_page
  = .CheckOk
      (mremap_model_next mremap_lazy_one_page 65536 4096 65536 8192) []
:= by rfl

theorem mremap_lazy_grow_preserves_only_old_charge :
  let post := mremap_model_next mremap_lazy_one_page
                65536 4096 65536 8192 ;
  m_vm_lazy post = [(65536, 8192)] ∧
  m_vm_materialized post = [65536] ∧
  vm_backing_used post = 4096
:= by (try dsimp only); (repeat constructor) <;> rfl

theorem mremap_lazy_move_relocates_materialized_pages :
  check_syscall (mremap_in 4096 8192)
    (SyscallEffect.mkEffectU 131072 [] [(135168, 4096)] [(65536, 4096)]
      [MemCopy.mkCopy 65536 131072 4096] []) mremap_lazy_one_page
  = .CheckOk
      (mremap_model_next mremap_lazy_one_page 65536 4096 131072 8192) []
:= by rfl

theorem mremap_lazy_move_ledgers_follow_contents :
  let post := mremap_model_next mremap_lazy_one_page
                65536 4096 131072 8192 ;
  m_vm_lazy post = [(131072, 8192)] ∧
  m_vm_materialized post = [131072] ∧
  vm_backing_used post = 4096
:= by (try dsimp only); (repeat constructor) <;> rfl

def mremap_mixed_backing : Model :=
  with_vm_backing [(65536, 4096)] []
    (with_vmmaps (mkVmMaps [] [(65536, 8192)] 0 0 8192)
      (init_model [] 0 0 demo_sp 8192 (demo_input [] IEof)))

theorem mremap_mixed_backing_fails_closed :
  check_syscall (mremap_in 8192 4096)
    (SyscallEffect.mkEffectU 65536 [] [] [(69632, 4096)] [] []) mremap_mixed_backing
  = .CheckUnmodeled
:= by rfl

/- -------------------------------------------------------------------------
   Moved destinations are preference-free placements

   Linux picks a MAYMOVE destination with [get_unmapped_area] at
   [addr = 0] (mm/mremap.c:1170, cited on [Mremap.mremap_fresh_b]), so
   whatever the spec is entitled to say about a preference-free mmap
   placement it is entitled to say here, and no more.  That is three
   conditions — page-aligned, inside the user range, disjoint from every
   recorded mapping — and these cases pin both halves of it on a move.

   The spec does not pin the search as well: that would exclude
   placements Linux makes (see the placement section in
   `Sys.Mm.Mmap`), so the low destination is admissible here for
   exactly the reason it is admissible for a fresh grant.

   Reason 4 for all of them: the kernel's allocator descends from an
   [mmap_base] just under the stack (mm/util.c [mmap_base], v6.18.46) and
   never produces a destination this low, so only these cases can say
   what the spec does with one.
   ------------------------------------------------------------------------- -/

def mremap_placed_in (old_addr old_size new_size : word)
    : SyscallInput :=
  SyscallInput.mkInput 216 [old_addr, old_size, new_size, 1, 0, 0]
    (fun _ => none) (fun _ => none)

def mremap_placement_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaab000, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) demo_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp 8192 (demo_input [] IEof))

/-! A growing move to a low destination, admitted: 0x80000000 is
    page-aligned, positive, below the ceiling and free, which is
    everything the spec asks of a preference-free placement. -/
theorem mremap_move_low_destination_admitted :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000000) []
       [(Z_to_bv 64 0x80001000, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000000) 4096] [])
    mremap_placement_model
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x80000000, 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) demo_sp) mremap_placement_model) []
:= by rfl

/-! NEGATIVE: the conditions that DO refuse a move still refuse it.  An
    unaligned destination is rejected… -/
theorem mremap_move_unaligned_destination_rejected :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 0x80000001) []
       [(Z_to_bv 64 0x80001001, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x80000001) 4096] [])
    mremap_placement_model
  = .CheckReject
:= by rfl

/-! …and so is one that OVERLAPS the source, which is the disjointness
    condition doing the work a move most needs it for: Linux runs the
    destination search while the source VMA is still live (it is not
    unmapped until [move_vma] reaches [unmap_source_vma], mm/mremap.c,
    Linux v6.18.46 — the search is over before any of it runs), so the
    destination cannot be a range the source still holds, and the model
    gets that exclusion from [old] still being in [vm_maps] when
    [region_free] runs.

    THE ADDRESS IS CHOSEN SO THAT ONLY [region_free] REFUSES IT.  The
    destination starts one page BELOW the source and is two pages long,
    so it covers the source's page without starting on it: [dst <> old]
    holds, the alignment, positivity and ceiling conjuncts hold, and the
    budget holds.  Landing exactly ON the source would not test this —
    [mremap_fresh_b]'s first conjunct is [negb (bv_eqb dst old)], which
    refuses [dst = old] before [region_free] is ever consulted, so such
    a case stays [CheckReject] with the disjointness conjunct deleted
    and pins nothing.  This one does not: deleting [region_free] from
    [mremap_fresh_b] turns it into a [CheckOk]. -/

/-! The source and the overlapping destination are NAMED, and the case
    below and its witness both use the names.  Spelling the addresses
    twice would let the witness drift off the case it is evidence for —
    an edit to one set of literals leaves the other proving something
    true about an address nobody tests — and a witness that can drift is
    a witness nobody should trust. -/
def mremap_src : word := Z_to_bv 64 0x2aaaaab000
def mremap_src_n : word := Z_to_bv 64 4096
def mremap_overlapping_dst : word := Z_to_bv 64 0x2aaaaaa000
def mremap_overlapping_dst_n : word := Z_to_bv 64 8192

theorem mremap_move_onto_source_rejected :
  check_syscall (mremap_placed_in mremap_src 4096 8192)
    (SyscallEffect.mkEffectU mremap_overlapping_dst []
       [(mremap_src, 4096)]
       [(mremap_src, 4096)]
       [MemCopy.mkCopy mremap_src mremap_overlapping_dst 4096] [])
    mremap_placement_model
  = .CheckReject
:= by rfl

/-! …and the uniqueness is CHECKED rather than asserted, since a
    negative that fails for the wrong reason pins nothing.  At this
    destination every other conjunct of [Mremap.mremap_fresh_b] holds
    and only [region_free] fails; at [dst = old] the FIRST conjunct
    fails and [region_free] is never reached, which is why that
    spelling would have been vacuous.

    Each conjunct below is the guard's, at the same arguments the case
    above passes: [mremap_overlapping_dst] for [dst],
    [mremap_overlapping_dst_n] for [new_n], [mremap_src] for [old].  That
    the six are ALL of them is pinned separately, by
    [mremap_fresh_b_conjuncts] below. -/
theorem mremap_move_onto_source_only_region_free_fails :
  region_free (vm_reserved (m_vmmaps mremap_placement_model)
               ++ vm_maps (m_vmmaps mremap_placement_model))
    mremap_overlapping_dst mremap_overlapping_dst_n = false
  ∧ negb (bv_eqb mremap_overlapping_dst mremap_src) = true
  -- The three `Z` comparisons spelled infix in the source, in the prefix
  -- form of the same shims (`=?` is `zeqb`, `<?` is `zltb`, `<=?` is `zleb`).
  ∧ zeqb (bv_unsigned mremap_overlapping_dst % page_size) 0 = true
  ∧ zltb 0 (bv_unsigned mremap_overlapping_dst) = true
  ∧ zleb (bv_unsigned mremap_overlapping_dst
            + bv_unsigned mremap_overlapping_dst_n)
         (alloc_top (m_vmmaps mremap_placement_model)) = true
  ∧ mremap_final_budget_b mremap_placement_model
       mremap_src mremap_src_n
       mremap_overlapping_dst mremap_overlapping_dst_n = true
:= by (repeat constructor) <;> rfl

/-! …and the spelling that would NOT have bitten, recorded so the choice
    above reads as forced rather than arbitrary: at [dst = old] the
    guard's first conjunct is already false.  This one is documentary
    rather than a test — it is [reflexivity] on a ground term — and is
    kept for what it explains, not for what it checks. -/
theorem mremap_move_dst_eq_old_is_refused_before_region_free :
  negb (bv_eqb mremap_src mremap_src) = false
:= by rfl

/-! THE ENUMERATION IS PINNED BY THE BUILD, which is the other half of
    making that witness trustworthy.  It lists the guard's conjuncts,
    but nothing in it says the list is COMPLETE: add a seventh conjunct
    to [Mremap.mremap_fresh_b] and the witness keeps passing while
    quietly ceasing to be the uniqueness argument its name claims.  This
    states the guard's shape, so that edit breaks the build instead.

    STATED AT ABSTRACT ARGUMENTS ON PURPOSE.  At the concrete ones the
    case uses, [vm_compute] reduces BOTH sides to [false] and the
    equation holds for reasons having nothing to do with the shape —
    which is precisely the vacuity these cases guard against, and
    would have hidden a seventh conjunct rather than exposing it.
    Quantified, neither side computes and [reflexivity] is the
    definitional unfolding. -/
theorem mremap_fresh_b_conjuncts :
  ∀ m old_nZ new_nZ old old_n dst new_n,
    mremap_fresh_b m old_nZ new_nZ old old_n dst new_n
    -- Again the infix `Z` comparisons of the statement, in the prefix
    -- form of the same shims.
    = (negb (bv_eqb dst old)
       && zeqb (bv_unsigned dst % page_size) 0
       && zltb 0 (bv_unsigned dst)
       && zleb (bv_unsigned dst + new_nZ) (alloc_top (m_vmmaps m))
       && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
            dst new_n
       && mremap_final_budget_b m old old_n dst new_n)
:= by
  intro m old_nZ new_nZ old old_n dst new_n
  rfl

/-! …and the ordinary move, one page above the source, is admitted. -/
theorem mremap_move_just_above_source_accepts :
  check_syscall (mremap_placed_in (Z_to_bv 64 0x2aaaaab000) 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 0x2aaaaac000) []
       [(Z_to_bv 64 0x2aaaaad000, 4096)]
       [(Z_to_bv 64 0x2aaaaab000, 4096)]
       [MemCopy.mkCopy (Z_to_bv 64 0x2aaaaab000) (Z_to_bv 64 0x2aaaaac000) 4096] [])
    mremap_placement_model
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 0x2aaaaac000, 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) demo_sp) mremap_placement_model) []
:= by rfl


/- -------------------------------------------------------------------------
   THE BOUND IS READ FROM THE LEDGER, for mremap's two placing arms.  The
   same two effects [mremap_inplace_grow_past_ceiling_rejected] and the
   moved-destination case refuse under [demo_sp] are admitted once the
   ledger's stack pointer is [hi_sp] (see the twin block at the end of
   `Cases.Mm.Mmap` for the argument).
   ------------------------------------------------------------------------- -/

def mremap_grow_past_top_hi_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) hi_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp 8192 (demo_input [] IEof))

theorem mremap_inplace_grow_past_demo_top_admitted_under_high_sp :
  check_syscall (mremap_at_in (Z_to_bv 64 (demo_top - 4096)) 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)] [] [] [])
    mremap_grow_past_top_hi_model
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) hi_sp) mremap_grow_past_top_hi_model) []
:= by rfl

def mremap_move_source_lo_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) demo_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) demo_sp 8192 (demo_input [] IEof))
def mremap_move_source_hi_model : Model :=
  with_vmmaps
    (VmMaps.mkVmMapsFull [] [(65536, 4096)] [] 0 0 8192
      (Z_to_bv 64 mmap_base_max) hi_sp)
    (init_model [] 0 (Z_to_bv 64 mmap_base_max) hi_sp 8192 (demo_input [] IEof))

/-! A move whose destination ends one page past [demo_top]. -/
theorem mremap_move_past_demo_top_rejected_under_low_sp :
  check_syscall (mremap_at_in 65536 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
       [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
    mremap_move_source_lo_model
  = .CheckReject
:= by rfl

theorem mremap_move_past_demo_top_admitted_under_high_sp :
  check_syscall (mremap_at_in 65536 4096 8192)
    (SyscallEffect.mkEffectU (Z_to_bv 64 (demo_top - 4096)) [] [(Z_to_bv 64 demo_top, 4096)]
       [(65536, 4096)] [MemCopy.mkCopy 65536 (Z_to_bv 64 (demo_top - 4096)) 4096] [])
    mremap_move_source_hi_model
  = .CheckOk
      (with_vmmaps
        (VmMaps.mkVmMapsFull [] [(Z_to_bv 64 (demo_top - 4096), 8192)] [] 0 0 8192
          (Z_to_bv 64 mmap_base_max) hi_sp) mremap_move_source_hi_model) []
:= by rfl

end LinuxSem.Checks.Cases.Mm.Mremap
