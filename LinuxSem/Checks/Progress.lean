/-
  * LinuxSem.Checks.Progress — receptiveness: the model is never stuck

  For every syscall input (number, register arguments, pre-syscall
  memory) and every model state, `syscall_spec` admits SOME outcome —
  an `ok` effect or an explicit `unmodeled`.  Together with the machine step
  being total-or-illegal, this validates that the trace semantics has
  no stuck-and-not-halted configurations (see the note in `Run.lean`).

  WHAT IT DOES AND DOES NOT CERTIFY, because the difference is easy to
  over-read.  `receptive` exhibits ONE admissible outcome for every
  input and model state — the witness — so what it certifies is that
  no spec is STUCK.  It does not certify that any particular ARM is
  inhabited.  The only way to write a non-receptive spec in this DSL
  is a `choose` with an unsatisfiable predicate, but one to the RIGHT
  of an `alt` whose left branch always answers is invisible here: the
  witness takes the left branch, the right is never evaluated, and
  this theorem still proves.  That is not hypothetical, it is how
  `openat` is built — `Witness/Fs/Open.lean`'s `openat_core_witness`
  answers from `openat_errnos` on every path it reaches, so
  `Fs.File.lowest_fd`'s `choose` on the success side is never shown
  inhabited.  `Sys/Fs/Open.lean` says the same thing from the other
  direction, noting that EMFILE and ENFILE are in that set partly to
  "keep the spec receptive when no free fd < 2^31 exists".

  Syscall arguments and returns are `word = BitVec 64`, errnos are `Int`,
  and the brk/word choices follow the `Int`-side predicates of `Specs.lean`.

  The witnesses are EXPLICIT DEFINITIONS, not existentials buried in
  proof scripts: each `<sys>_witness` is a computable function from the
  syscall's inputs and the model to a concrete outcome (the one-byte
  delivery — or, at end of input, the 0 return — for channel reads,
  the ENOMEM failure branch for mmap/openat, …),
  and `<sys>_witness_ok` proves the spec admits it.  `receptive` then
  states `syscall_spec i m (syscall_spec_witness i m)` — so the chosen
  outcome is readable here rather than recoverable only by stepping
  through the proof.

  Placement.  `Checks/Sys/Dispatch.lean` §3 proves both declarations over
  an ARBITRARY table (`receptive t ht`, with `ht` the table/spec-surface
  agreement), and §4 holds the `checked_table` instances in
  `namespace CheckedTable`, under the same names.  That placement is
  forced by the direction of the dependencies: this file takes
  `Dispatch.lean` for the table and the generic proofs, so the reverse
  dependency is impossible, and the §3 versions already hold the
  unqualified names.

  This file therefore restates both declarations under the plain names
  and the plain statements, in the `Progress` namespace (which is
  distinct from `CheckedTable`, so nothing clashes):
  `syscall_spec_witness` is the `CheckedTable` definition and each proof
  is one line handing over to the `CheckedTable` result.  Nothing is
  reproved and nothing here grows when a syscall is added.

  Spelling.  `outcome SyscallEffect` is
  `Outcome SyscallEffect Model event`, `Ok` / `Unmodeled` are
  `.ok` / `.unmodeled`, `syscall_spec` is `Specs.syscall_spec`, and
  `bv_unsigned (in_sysno i)` is `(i.in_sysno.toNat : Int)` — the very
  term `Dispatch.check_syscall` dispatches on, so the witness and the
  spec read the same number out of the same `SyscallInput`.  The
  witness modules come in transitively through `Checks.Sys.Dispatch`,
  which names exactly that set.
-/
import LinuxSem.Checks.Sys.Dispatch

namespace LinuxSem.Checks.Progress

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs (syscall_spec)
-- The checked table, and, as a prefix, `CheckedTable.*`.  Every use below
-- is written with the `CheckedTable.` prefix: the generic §3 names
-- (`receptive`, `syscall_spec_witness`, …) come along with this `open`, and
-- the restatements in this file must not be confused with them.
open LinuxSem.Checks.Sys.Dispatch

/- =========================================================================
   Proof kit
   ========================================================================= -/

/-- The witness for this input's syscall, from the same table the spec and
    the checker dispatch over.  A number with no arm has no witness and is
    `unmodeled` — which is what `receptive` then has to show, once.

    The body is the arm match itself; it is `CheckedTable`'s
    definition, which is `Dispatch.syscall_spec_witness checked_table`:

      `match lookup_ca checked_table (i.in_sysno.toNat : Int) with`
      `| some c => c.ca_witness i m`
      `| none   => .unmodeled`

    Restated here so the name reads at this module. -/
def syscall_spec_witness (i : SyscallInput) (m : Model) :
    Outcome SyscallEffect Model event :=
  CheckedTable.syscall_spec_witness i m

/-- The dispatcher is receptive: `syscall_spec_witness i m` is an
    admissible outcome for every input and model state.

    Receptivity in one lookup: the spec dispatches over `spec_table`, the
    witness over `checked_table`, and `checked_table_arms` says those are
    the same surface — so the arm that answers is the arm whose
    `ca_receptive` field is exactly this goal.  No case analysis over the
    numbers, and nothing here grows when a syscall is added. -/
theorem receptive (i : SyscallInput) (m : Model) :
    syscall_spec i m (syscall_spec_witness i m) :=
  CheckedTable.receptive i m

/-- Receptivity, existentially: no input leaves the spec stuck. -/
theorem receptive_ex (i : SyscallInput) (m : Model) :
    ∃ o, syscall_spec i m o :=
  CheckedTable.receptive_ex i m

/-! ## Sanity checks

    Beyond the minimum: both results are already proved by
    `CheckedTable`.  These pin the restatement —
    the two names really are the `checked_table` dispatch, so what
    `receptive` talks about is the same witness the dispatcher hands out. -/

/-- The witness here is the checked table's, arm match and all. -/
example : syscall_spec_witness = CheckedTable.syscall_spec_witness := rfl

/-- And that is the dispatcher's, at the concrete table. -/
example : syscall_spec_witness
    = LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness checked_table := rfl

end LinuxSem.Checks.Progress
