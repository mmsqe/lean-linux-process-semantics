/-
  * Common.AllocIface — image-INDEPENDENT abstract allocator interface.

    Every binary-specific constant (mallocng entry PCs, the globals
    window, the loaded segments, alloc_ceiling, the libc env facts) is a
    field of [AllocLayout]; [AllocIface] states the allocator laws and the
    weak/strong malloc + free CPS rules over an opaque allocator state.

    Vocabulary:
    - [AS]            abstract allocator state (opaque to clients)
    - [ainv A m vm]   A describes the allocator data in memory [m] with
                      vm ledger [vm]; nothing else of the model matters.
    - [live A p]      = Some n iff the client owns block [p, p+n).
    - [owned A a]     address [a] belongs to the allocator (heap regions
                      including client blocks + headers, and its globals).
    Clients may write inside live blocks and anywhere not [owned];
    everything else owned must be left alone ([ai_frame]).

    The toy instance in [AllocIfaceToy] witnesses that the class is
    instantiable (consistency); it is NOT a usable allocator model — a
    real instance is a per-binary refinement proof (e.g. mallocng).
 The Lean
  port imports the mirrored modules; they already export everything this
  file mentions (`PropExec.mkst`/`getr`/`FPState`,
  `Hoare.at_`, `ShapeAlg.TSet`/`t_alt2`/`realizes`, `Run.config`,
  `Run.valid_brk`, `State.VmMaps`, `MemImageType.Segment`).
Context {AL :
  AllocLayout}` becomes `section WithLayout / variable [AL : AllocLayout]`,
  and since Lean has no "class declared inside another class's implicit
  argument context", [AllocIface] carries [AL] as its instance-implicit
  parameter; its fields mention it as `AL.al_…`.
  `Z` is `Int`, `N` is `Nat`; `bv_unsigned w` is
  `(w.toNat : Int)` (as everywhere in this tree), so the chained
  comparisons of the (`0 <= i < round16 n`, `18 <= bv_unsigned r
  <= 27`, `bv_unsigned p <= bv_unsigned a < bv_unsigned p + n`, …) become
  conjunctions inside the same position and keep their polarity — the
  ones under a `~` stay under a `¬`.  `Z_to_bv 64 n` is `BitVec.ofInt 64
  n`, `None`/`Some` are `none`/`some`, `<>` is `≠`, `~` is `¬`.
 `vm_limit` is
  a field of `VmMaps`, hence a Lean structure projection and written
  `vm'.vm_limit` / `(m_vmmaps md).vm_limit` (the deviation `StateVm.lean`
  records for every former `State` accessor of that shape).
   quantifies `(fx : FPState)` first in
  each CPS rule and then lets `mkst` pick it up as an implicit instance
  argument.  The explicit binder is kept here (the allocator does not
  touch FP registers, so the rule is polymorphic in the FP state) and
  `mkst` is applied as `mkst (fx := fx)`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.Hoare
import LinuxSem.Common.ShapeAlg

set_option autoImplicit false

namespace LinuxSem.Common.AllocIface

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.Hoare
open LinuxSem.Common.ShapeAlg

/-- `round16 n` — `n` rounded up to a multiple of 16, the allocator's
block granularity. -/
def round16 (n : Int) : Int := 16 * ((n + 15) / 16)

/-- Callee-saved registers of the RV64 psABI (+ gp, tp). -/
def callee_saved (r : reg) : Prop :=
  r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 8 ∨ r = 9 ∨ (18 ≤ r.toNat ∧ r.toNat ≤ 27)

/-- Stack budget (bytes below sp) sufficient for one malloc or free call. -/
def ALLOC_STACK : Int := 1024

/-- Everything binary-specific the interface mentions. -/
class AllocLayout where
  al_segs : List Segment               -- the binary's LOAD segments
  al_rom : word → Option byte          -- the mkst rom component
  al_malloc_pc : word                  -- malloc entry point
  al_free_pc : word                    -- free entry point
  al_gp : word                         -- the ABI gp value at call sites
  al_globals : word → Prop             -- allocator-private globals
  al_errno_slot : word → Prop          -- errno slot: writable, not owned
  al_grantable : word → Prop           -- where mmap may grant
  al_ceiling : Int                     -- top of the heap address space
  al_image_hi : Int                    -- end of the loaded image
  al_in_ro : word → Prop               -- read-only image bytes
  al_in_rw : word → Prop               -- live-data image bytes
  al_ret_ok : word → Prop              -- admissible return addresses
  -- the call-boundary environment facts (libc globals the allocator
  -- reads, the pristine region above sp0, argv/envp validity)
  al_env : word → List (List byte) → List (List byte) → (word → Option byte) → Prop
  -- the initial vm ledger as a function of the initial brk
  al_init_vm : word → VmMaps
  -- mmap-vs-brk threshold of the modelled allocator
  al_mmap_threshold : Int

section WithLayout

variable [AL : AllocLayout]

class AllocIface where
  AS : Type
  ainv : AS → (word → Option byte) → VmMaps → Prop
  live : AS → word → Option Int
  owned : AS → word → Prop

  ai_globals_owned : ∀ (A : AS) (a : word), AL.al_globals a → owned A a
  ai_live_hull : ∀ (A : AS) (m : word → Option byte) (vm : VmMaps) (p : word) (n : Int),
    ainv A m vm → live A p = some n →
    0 ≤ n ∧ (p.toNat : Int) % 16 = 0 ∧
    (p.toNat : Int) + round16 n ≤ AL.al_ceiling ∧
    ∀ (i : Int), 0 ≤ i ∧ i < round16 n →
      owned A (at_ p i) ∧ m (at_ p i) ≠ none ∧
      ¬ AL.al_in_ro (at_ p i) ∧ ¬ AL.al_in_rw (at_ p i)
  ai_live_disjoint : ∀ (A : AS) (m : word → Option byte) (vm : VmMaps) (p : word) (n : Int)
      (q : word) (k : Int),
    ainv A m vm → live A p = some n → live A q = some k → p ≠ q →
    (p.toNat : Int) + round16 n ≤ (q.toNat : Int) ∨
    (q.toNat : Int) + round16 k ≤ (p.toNat : Int)
  ai_live_not_globals : ∀ (A : AS) (m : word → Option byte) (vm : VmMaps) (p : word) (n : Int)
      (i : Int),
    ainv A m vm → live A p = some n → 0 ≤ i ∧ i < round16 n → ¬ AL.al_globals (at_ p i)
  ai_owned_where : ∀ (A : AS) (m : word → Option byte) (vm : VmMaps) (a : word),
    ainv A m vm → owned A a → AL.al_globals a ∨ (AL.al_grantable a ∧ m a ≠ none)
  ai_frame : ∀ (A : AS) (m m' : word → Option byte) (vm : VmMaps),
    ainv A m vm →
    (∀ (a : word), owned A a →
       (∀ (p : word) (n : Int), live A p = some n →
          ¬ ((p.toNat : Int) ≤ (a.toNat : Int) ∧ (a.toNat : Int) < (p.toNat : Int) + n)) →
       m' a = m a) →
    (∀ (a : word), owned A a → m a ≠ none → m' a ≠ none) →
    (∀ (a : word), AL.al_grantable a → m' a ≠ none → m a ≠ none) →
    ainv A m' vm

  A0 : AS
  ai_init_live : ∀ (p : word), live A0 p = none
  ai_init_owned : ∀ (a : word), owned A0 a ↔ AL.al_globals a
  ai_init : ∀ (m : word → Option byte) (brk : word),
    (∀ (a : word), AL.al_globals a → m a = none) →
    (∀ (a : word), AL.al_grantable a → m a = none) →
    valid_brk AL.al_segs brk →
    ainv A0 m (AL.al_init_vm brk)

  -- fresh_small carries the number k of metas in use; a small bound
  -- guarantees no meta-area growth in the next malloc
  fresh_small : AS → Int → Prop
  ai_init_fresh : fresh_small A0 0
  ai_fresh_mono : ∀ (A : AS) (k k' : Int), fresh_small A k → k ≤ k' → fresh_small A k'

  ai_malloc :
    ∀ (fx : FPState) (A : AS) (m : word → Option byte) (md : Model) (regs : BvMap word)
      (n : Int) (ret sp0 : word) (argv envp : List (List byte)) (S : TSet),
      ainv A m (m_vmmaps md) → m_halted md = none →
      AL.al_env sp0 argv envp m →
      getr regs 10 = BitVec.ofInt 64 n → 0 ≤ n ∧ n < 2 ^ 63 →
      getr regs 1 = ret → AL.al_ret_ok ret → getr regs 4 = AL.al_gp →
      ((getr regs 2).toNat : Int) % 16 = 0 →
      AL.al_ceiling + 8192 ≤ ((getr regs 2).toNat : Int) →
      ((getr regs 2).toNat : Int) ≤ (sp0.toNat : Int) →
      (∀ (a : word), ((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) →
          (a.toNat : Int) < ((getr regs 2).toNat : Int) →
          m a ≠ none ∧ ¬ owned A a ∧ ¬ AL.al_in_ro a ∧ ¬ AL.al_in_rw a) →
      (∀ (A' : AS) (m' : word → Option byte) (vm' : VmMaps) (regs' : BvMap word) (res : word),
          ainv A' m' vm' →
          getr regs' 10 = res → (∀ (r : reg), callee_saved r → getr regs' r = getr regs r) →
          ((res = BitVec.ofInt 64 0 ∧ (∀ (q : word), live A' q = live A q) ∧
             (∀ (k : Int), fresh_small A k → k ≤ 80 → fresh_small A' k)) ∨
           ((res.toNat : Int) ≠ 0 ∧ live A res = none ∧ live A' res = some n ∧
             (∀ (q : word), q ≠ res → live A' q = live A q) ∧
             (∀ (i : Int), 0 ≤ i ∧ i < round16 n →
                owned A (at_ res i) ∨ m (at_ res i) = none))) →
          (∀ (a : word), ¬ owned A a → ¬ owned A' a → ¬ AL.al_errno_slot a →
             ¬ (((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) ∧
                (a.toNat : Int) < ((getr regs 2).toNat : Int)) →
             m' a = m a) →
          (∀ (q : word) (k : Int) (i : Int), live A q = some k → 0 ≤ i ∧ i < k →
             m' (at_ q i) = m (at_ q i)) →
          (∀ (a : word), m a ≠ none →
             (a.toNat : Int) < AL.al_image_hi ∨ owned A a ∨ m' a ≠ none) →
          vm'.vm_limit = (m_vmmaps md).vm_limit →
          realizes AL.al_segs ⟨mkst (fx := fx) regs' ret m' AL.al_rom, with_vmmaps vm' md⟩ S) →
      realizes AL.al_segs ⟨mkst (fx := fx) regs AL.al_malloc_pc m AL.al_rom, md⟩ S

  ai_malloc_strong :
    ∀ (fx : FPState) (A : AS) (m : word → Option byte) (md : Model) (regs : BvMap word)
      (n k : Int) (ret sp0 : word) (argv envp : List (List byte)) (Snull Sok : TSet),
      ainv A m (m_vmmaps md) → m_halted md = none →
      AL.al_env sp0 argv envp m →
      fresh_small A k → k ≤ 80 →
      getr regs 10 = BitVec.ofInt 64 n → 0 < n ∧ n < 2 ^ 40 →
      vm_live_bytes (m_vmmaps md) + n + 2 ^ 24 ≤ (m_vmmaps md).vm_limit →
      getr regs 1 = ret → AL.al_ret_ok ret → getr regs 4 = AL.al_gp →
      ((getr regs 2).toNat : Int) % 16 = 0 →
      AL.al_ceiling + 8192 ≤ ((getr regs 2).toNat : Int) →
      ((getr regs 2).toNat : Int) ≤ (sp0.toNat : Int) →
      (∀ (a : word), ((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) →
          (a.toNat : Int) < ((getr regs 2).toNat : Int) →
          m a ≠ none ∧ ¬ owned A a ∧ ¬ AL.al_in_ro a ∧ ¬ AL.al_in_rw a) →
      (∀ (A' : AS) (m' : word → Option byte) (vm' : VmMaps) (regs' : BvMap word),
          ainv A' m' vm' →
          getr regs' 10 = BitVec.ofInt 64 0 →
          (∀ (r : reg), callee_saved r → getr regs' r = getr regs r) →
          (∀ (q : word), live A' q = live A q) → fresh_small A' k →
          (∀ (a : word), ¬ owned A a → ¬ owned A' a → ¬ AL.al_errno_slot a →
             ¬ (((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) ∧
                (a.toNat : Int) < ((getr regs 2).toNat : Int)) →
             m' a = m a) →
          (∀ (q : word) (k' : Int) (i : Int), live A q = some k' → 0 ≤ i ∧ i < k' →
             m' (at_ q i) = m (at_ q i)) →
          (∀ (a : word), m a ≠ none →
             (a.toNat : Int) < AL.al_image_hi ∨ owned A a ∨ m' a ≠ none) →
          vm'.vm_limit = (m_vmmaps md).vm_limit →
          vm_live_bytes vm' ≤ vm_live_bytes (m_vmmaps md) + n + 2 ^ 23 →
          realizes AL.al_segs ⟨mkst (fx := fx) regs' ret m' AL.al_rom, with_vmmaps vm' md⟩
            Snull) →
      (∀ (A' : AS) (m' : word → Option byte) (vm' : VmMaps) (regs' : BvMap word) (res : word),
          ainv A' m' vm' →
          getr regs' 10 = res → (res.toNat : Int) ≠ 0 →
          (∀ (r : reg), callee_saved r → getr regs' r = getr regs r) →
          live A res = none → live A' res = some n →
          (∀ (q : word), q ≠ res → live A' q = live A q) →
          ((AL.al_mmap_threshold ≤ n ∨ (n = 65536 ∧ ∀ (q : word), live A q = none)) →
             fresh_small A' (k + 1)) →
          (∀ (i : Int), 0 ≤ i ∧ i < round16 n →
             owned A (at_ res i) ∨ m (at_ res i) = none) →
          (∀ (a : word), ¬ owned A a → ¬ owned A' a → ¬ AL.al_errno_slot a →
             ¬ (((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) ∧
                (a.toNat : Int) < ((getr regs 2).toNat : Int)) →
             m' a = m a) →
          (∀ (q : word) (k' : Int) (i : Int), live A q = some k' → 0 ≤ i ∧ i < k' →
             m' (at_ q i) = m (at_ q i)) →
          (∀ (a : word), m a ≠ none →
             (a.toNat : Int) < AL.al_image_hi ∨ owned A a ∨ m' a ≠ none) →
          vm'.vm_limit = (m_vmmaps md).vm_limit →
          vm_live_bytes vm' ≤ vm_live_bytes (m_vmmaps md) + n + 2 ^ 23 →
          realizes AL.al_segs ⟨mkst (fx := fx) regs' ret m' AL.al_rom, with_vmmaps vm' md⟩
            Sok) →
      realizes AL.al_segs ⟨mkst (fx := fx) regs AL.al_malloc_pc m AL.al_rom, md⟩
        (t_alt2 Snull Sok)

  ai_free :
    ∀ (fx : FPState) (A : AS) (m : word → Option byte) (md : Model) (regs : BvMap word)
      (p ret sp0 : word) (argv envp : List (List byte)) (S : TSet),
      ainv A m (m_vmmaps md) → m_halted md = none →
      AL.al_env sp0 argv envp m →
      getr regs 10 = p → (p = BitVec.ofInt 64 0 ∨ ∃ (n : Int), live A p = some n) →
      getr regs 1 = ret → AL.al_ret_ok ret → getr regs 4 = AL.al_gp →
      ((getr regs 2).toNat : Int) % 16 = 0 →
      AL.al_ceiling + 8192 ≤ ((getr regs 2).toNat : Int) →
      ((getr regs 2).toNat : Int) ≤ (sp0.toNat : Int) →
      (∀ (a : word), ((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) →
          (a.toNat : Int) < ((getr regs 2).toNat : Int) →
          m a ≠ none ∧ ¬ owned A a ∧ ¬ AL.al_in_ro a ∧ ¬ AL.al_in_rw a) →
      (∀ (A' : AS) (m' : word → Option byte) (vm' : VmMaps) (regs' : BvMap word),
          ainv A' m' vm' →
          (∀ (r : reg), callee_saved r → getr regs' r = getr regs r) →
          live A' p = none → (∀ (q : word), q ≠ p → live A' q = live A q) →
          ((∀ (n : Int), live A p = some n → AL.al_mmap_threshold ≤ n ∨ n = 65536) →
             ∀ (k : Int), fresh_small A k → fresh_small A' k) →
          (∀ (a : word), ¬ owned A a → ¬ owned A' a → ¬ AL.al_errno_slot a →
             ¬ (((getr regs 2).toNat : Int) - ALLOC_STACK ≤ (a.toNat : Int) ∧
                (a.toNat : Int) < ((getr regs 2).toNat : Int)) →
             m' a = m a) →
          (∀ (q : word) (k : Int) (i : Int), live A' q = some k → 0 ≤ i ∧ i < k →
             m' (at_ q i) = m (at_ q i)) →
          (∀ (a : word), m a ≠ none → owned A a ∨ m' a ≠ none) →
          vm'.vm_limit = (m_vmmaps md).vm_limit →
          vm_live_bytes vm' ≤ vm_live_bytes (m_vmmaps md) →
          realizes AL.al_segs ⟨mkst (fx := fx) regs' ret m' AL.al_rom, with_vmmaps vm' md⟩ S) →
      realizes AL.al_segs ⟨mkst (fx := fx) regs AL.al_free_pc m AL.al_rom, md⟩ S

end WithLayout

/-! -/

example : ALLOC_STACK = 1024 := rfl

example : round16 0 = 0 := by decide

example : round16 1 = 16 := by decide

example : round16 16 = 16 := by decide

example : round16 17 = 32 := by decide

example : round16 100 = 112 := by decide

example : callee_saved (2 : reg) := by unfold callee_saved; decide

example : callee_saved (9 : reg) := by unfold callee_saved; decide

example : callee_saved (18 : reg) := by unfold callee_saved; decide

example : callee_saved (27 : reg) := by unfold callee_saved; decide

example : ¬ callee_saved (0 : reg) := by unfold callee_saved; decide

example : ¬ callee_saved (5 : reg) := by unfold callee_saved; decide

example : ¬ callee_saved (10 : reg) := by unfold callee_saved; decide

example : ¬ callee_saved (28 : reg) := by unfold callee_saved; decide

end LinuxSem.Common.AllocIface
