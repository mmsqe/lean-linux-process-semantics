/-
  * LinuxProcessSem.Specs — the dispatched syscall surface.

  TRUST BOUNDARY: this file is part of the trusted specification.

  `syscall_spec` is the arm for the input's syscall number, or `unmodeled`
  (fail closed).  Both it and `modeled_sysnos` are read off
  `Sys.SyscallTable.spec_table`, so they cannot drift from the table or from
  each other — that tie is DEFINITIONAL, since both are `spec_table`
  unfolded, and this file states it by construction rather than by proof.

  WHAT THIS FILE DOES.  Two definitions, no theorem — but the theorems
  that matter are now in the tree, in `Checks/DispatchSurface.lean`
  (24 of 24 declarations).  `modeled_sysnos` is **not** merely documented:
  `Checks.DispatchSurface.modeled_sysnos_exact` proves

      n ∈ modeled_sysnos ↔ ∃ i m o,
        (i.in_sysno.toNat : Int) = n ∧ syscall_spec i m o ∧ o ≠ .unmodeled

  i.e. the list is EXACTLY the dispatched set.  Its two halves say
  different things, and the asymmetry is worth knowing:

  - `syscall_spec_number_modeled` — the EXCLUSION.  Any `.ok` outcome
    forces membership.  It is the only bridge from the dispatcher back to
    the list, and it is generic over the table, because
    `Dispatch.dispatch_unmodeled` is stated over `lookup_arm t n = None`
    and never mentions `arm_numbers`.
  - `modeled_sysnos_dispatched` — the CONVERSE, which the shared table
    does NOT give: every listed number is answered on SOME input, by
    running `Progress.syscall_spec_witness` on a probe.  Read it as a
    floor on coverage, not as coverage — a listed number still declines
    the argument shapes its own spec rejects.

  Two further facts this file relied on as prose and no longer does:

  - `syscall_spec_unmodeled_outside` — the fail-closed corollary the
    coverage arguments want: outside the list, the only admissible
    outcome is `.unmodeled`;
  - `modeled_sysnos_nodup` — no number is listed twice.  This one is not
    decoration: `lookup_arm` is first-match-wins, so a duplicated arm is
    DEAD, and an `In`-shaped exactness statement cannot see that.

  Is caught here, by theorem, and `lake env lean` is not the only thing standing
  between the list and a silent shadowing.

  The `by decide` checks below pin the list's shape (90 entries, no
  duplicates by `eraseDups`, membership of the four numbers spot-checked)
  and nothing about what the dispatcher does with it.
-/
import LinuxSem.LinuxProcessSem.Sys.SyscallTable

namespace LinuxSem.LinuxProcessSem.Specs

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable

/-- The syscall numbers this model covers, as unsigned values.  The trace
    semantics does not consult this list — an ecall whose number is not in
    it simply falls through the dispatcher to `unmodeled` (fail closed).
    The list documents the modeled surface. -/
def modeled_sysnos : List Int := arm_numbers spec_table

/-- Dispatch on the unsigned syscall number.  The final `unmodeled` arm is
    the fail-closed fallback for every number outside `modeled_sysnos`. -/
def syscall_spec : SysSpec SyscallEffect := dispatch spec_table

/-! ## Sanity checks -/

example : 17 ∈ modeled_sysnos := by decide
example : 63 ∈ modeled_sysnos := by decide
example : 222 ∈ modeled_sysnos := by decide
example : 439 ∈ modeled_sysnos := by decide
example : 1 ∉ modeled_sysnos := by decide
example : modeled_sysnos.length = 90 := by decide
example : modeled_sysnos = modeled_sysnos.eraseDups := by decide


/-- …and one whose test has become `false = true` is its ELSE arm. -/
theorem ite_false_cond {α : Sort _} (a b : α) :
    (if (false = true) then a else b) = b := by
  rw [ite_eq_right (show ¬(false = true) by decide)]


/-- An `if` whose test `cases` has already rewritten to the literal `true`
    — `if true = true then a else b` — is its THEN arm. -/
theorem ite_true_cond {α : Sort _} (a b : α) :
    (if (true = true) then a else b) = a := by
  rw [ite_eq_left rfl]

end LinuxSem.LinuxProcessSem.Specs
