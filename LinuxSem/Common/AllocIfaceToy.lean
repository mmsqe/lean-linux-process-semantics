/-
  * Common.AllocIfaceToy — the planted positive for [AllocIface].

  A degenerate layout and instance that DISCHARGES every field of
  [AllocIface], proving the class is consistent and instantiable against our
  spec.  It is deliberately NOT a usable allocator model: [toy_env] is False,
  so the three CPS rules hold vacuously, and [live] is empty.  What this file
  certifies is exactly (and only) that the interface's law set has a model —
  an inconsistent class would let a proof derive False from
  `Context {AI : AllocIface}`, and this file is what rules that out.  A usable
  instance is a per-binary refinement proof (for example of mallocng); this
  library does not contain one.

  ENCODING NOTES.

  - `Class AllocLayout` / `Class AllocIface` are Lean `class`es (see
    `Common/AllocIface.lean`), so the layout is a `local instance` and the
    instance itself is a plain instance whose fields are given with `where`;
    `@AllocIface toy_layout` is applied with explicit `@`.
  - Values are `Int`, and `BitVec.ofInt 64 0` is the zero word;
    `none`/`some` replace option constructors, `False` stays `False`, and
    `Unit` is written `()`.  Each class obligation is discharged by an
    explicit proof rather than a blanket tactic: every obligation is either
    `True`, a `none = some _` absurdity, or the `al_env … = False` hypothesis
    of a CPS rule.
  - `mkVmMaps [] [] brk brk 0`: the two `[]`s are `List (word × word)` (the
    ledger's reserved/mapped interval lists).
-/
import LinuxSem.Common.AllocIface

set_option autoImplicit false

namespace LinuxSem.Common.AllocIfaceToy

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Common.AllocIface

/-- The degenerate layout: no segments, no ROM, the null pointer for every
    code address, an empty globals/errno/grantable set, zero bounds, and an
    empty initial vm ledger. -/
local instance toy_layout : AllocLayout where
  al_segs := []
  al_rom := fun _ => none
  al_malloc_pc := BitVec.ofInt 64 0
  al_free_pc := BitVec.ofInt 64 0
  al_gp := BitVec.ofInt 64 0
  al_globals := fun _ => False
  al_errno_slot := fun _ => False
  al_grantable := fun _ => False
  al_ceiling := 0
  al_image_hi := 0
  al_in_ro := fun _ => False
  al_in_rw := fun _ => False
  al_ret_ok := fun _ => False
  al_env := fun _ _ _ _ => False
  al_init_vm := fun brk => mkVmMaps ([] : List (word × word)) [] brk brk 0
  al_mmap_threshold := 0

/-- The degenerate allocator state: the unit state, the always-true
    invariant, no live block, nothing owned, and the vacuous
    [fresh_small].  Every law is discharged below. -/
local instance toy_alloc : @AllocIface toy_layout where
  AS := Unit
  ainv := fun _ _ _ => True
  live := fun _ _ => none
  owned := fun _ _ => False
  ai_globals_owned := by
    intro A a h
    exact h
  ai_live_hull := by
    intro A m vm p n _ hlive
    exact absurd hlive (by simp)
  ai_live_disjoint := by
    intro A m vm p n q k _ hlive _ _
    exact absurd hlive (by simp)
  ai_live_not_globals := by
    intro A m vm p n i _ hlive _
    exact absurd hlive (by simp)
  ai_owned_where := by
    intro A m vm a _ hown
    exact False.elim hown
  ai_frame := by
    intro A m m' vm _ _ _ _
    trivial
  A0 := ()
  ai_init_live := by
    intro p
    rfl
  ai_init_owned := by
    intro a
    exact Iff.rfl
  ai_init := by
    intro m brk _ _ _
    trivial
  fresh_small := fun _ _ => True
  ai_init_fresh := trivial
  ai_fresh_mono := by
    intro A k k' _ _
    trivial
  ai_malloc := by
    intro fx A m md regs n ret sp0 argv envp S _ _ henv
    exact False.elim henv
  ai_malloc_strong := by
    intro fx A m md regs n k ret sp0 argv envp Snull Sok _ _ henv
    exact False.elim henv
  ai_free := by
    intro fx A m md regs p ret sp0 argv envp S _ _ henv
    exact False.elim henv

/-! ### Sanity checks

The obligation that the class is INHABITED is the whole content of the
file.  These pin that, and the computable parts of the two instances. -/

example : Nonempty (@AllocIface toy_layout) := ⟨toy_alloc⟩

example : @AllocIface.AS toy_layout toy_alloc = Unit := rfl

example : @AllocIface.A0 toy_layout toy_alloc = () := rfl

example : @AllocIface.live toy_layout toy_alloc () (BitVec.ofInt 64 0) = none := rfl

example : ¬ @AllocIface.owned toy_layout toy_alloc () (BitVec.ofInt 64 0) := by
  intro h
  exact h

example : @AllocIface.ainv toy_layout toy_alloc () (fun _ => none)
    (mkVmMaps ([] : List (word × word)) [] (BitVec.ofInt 64 0)
      (BitVec.ofInt 64 0) 0) := trivial

end LinuxSem.Common.AllocIfaceToy
