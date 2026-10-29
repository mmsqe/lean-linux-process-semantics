# Lean 4 Linux process semantics

Ported from [theorem-labs/rocq-linux-process-semantics#f1006fe](https://github.com/theorem-labs/rocq-linux-process-semantics/tree/f1006fe)

A Lean 4 formalisation of the Linux process model and the syscall surface a
process actually observes: a RISC-V machine model, an executable specification of
the modelled syscalls, equivalence notions between images, and a verification
layer that checks concrete states against those specifications.

Zero dependencies beyond Lean itself. Toolchain pinned in `lean-toolchain`.

## Layout

| directory | contents |
| --- | --- |
| `Riscv/` | the ISA: decode, step, the register/memory helpers, alignment and access reporting |
| `LinuxProcessSem/` | the machine model (`State*`), the syscall specs (`Sys/`), and `Run` — the trace semantics |
| `EquivalenceDefinition/` | what it means for two images to agree: the equivalence, the measures, the classifier surfaces |
| `Checks/` | checkers, witnesses, and the verification layer; `Capstone` is the audit surface |
| `Common/` | shared machinery: the symbolic-execution tower, the ASan plan checker and its soundness proof, the tactic library |
| `Examples/` | three worked demonstrations, each with a sealed specification and a proof that it is met |

## Building

```
lake build          # the library and the decoder executable
./scripts/check.sh  # build + hygiene guards (see below)
```

`scripts/check.sh` runs four guards and prints `OK`:

1. `lake build` succeeds;
2. no escape hatches — the tree contains no `sorry` and no added axioms;
3. the axiom audit (`scripts/AxiomAudit.lean`) confirms nothing depends on
   `sorryAx`;
4. the decoder's smoke test succeeds.

## What is proved

`LinuxSem/Checks/Capstone.lean` is the verification surface: it
states every headline claim of this repository in one place, each paired with a
concrete witness that makes it non-vacuous. It typechecks or the claims are not
usable. Among them:

- `check_syscall_preserves_vm_wf` — an accepted syscall preserves page-granularity
  disjointness of the mapping ledger. Unconditional: an unmodelled syscall number
  makes the hypothesis impossible, so there is no coverage premise.
- `coexec_progress_iff` — the two co-execution judgments agree.
- `modeled_sysnos_exact` — the modelled syscall list is exactly the dispatched
  set, in both directions.
- `abrt_refutes_error_free_abort` — a concrete image whose run dies by SIGABRT,
  firing the error-free abort refutation rather than merely stating it.
- `check_sound` — the ASan plan checker is sound against the abstract semantics.
- `DemoSealed`, `omni_strong_universal` — the worked demonstrations' sealed
  specifications, and proofs that their images meet them.

## Documentation

- `NOTES.md` — Lean 4.31 tactics, reduction behaviour, and build latency, with
  the measurements behind each entry. Read it before fighting a proof.
- `AGENTS.md` — the working conventions (one module per file, comments are part
  of the artifact, no proof holes, verify with `lake env lean`).
