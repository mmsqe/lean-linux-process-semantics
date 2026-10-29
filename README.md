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
| `Checks/` | checkers, witnesses, and the verification layer |
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
   `sorryAx`, and that every headline claim listed there still resolves;
4. the decoder's smoke test succeeds.

## What is proved

The claims below are the repository's headline results. Each is proved, and
shown non-vacuous by a witness, in the module named in the last column; the
first column is the name `scripts/AxiomAudit.lean` pins.

| claim | what it says | where |
| --- | --- | --- |
| `brk_grant_wf` → `check_syscall_preserves_vm_wf` | an accepted syscall preserves page-granularity disjointness of the mapping ledger. Unconditional: an unmodelled syscall number makes the hypothesis impossible, so there is no coverage premise. `brk` is the case it hinges on; `base_entry_unique` is the payoff. | `Checks/VmMapsDisjoint/` |
| `coexec_progress_iff` | the two co-execution judgments agree, so a claim stated in one currency transfers. | `Checks/Omni.lean` |
| `modeled_sysnos_exact` | the modelled syscall list is exactly the dispatched set, in both directions, and is duplicate-free and non-empty (`Specs.lean`, `modeled_sysnos.length = 90`, by `decide`). | `Checks/DispatchSurface.lean` |
| `abrt_refutes_error_free_abort` | a concrete image whose run dies by SIGABRT, firing the error-free abort refutation rather than merely stating it; `abrt_dies_by_signal` discharges the premise at every limit. | `Checks/AbortWitness.lean` |
| `exits_c_must_exit_at`, `exit0_image_must_exit_zero` | a successful `exits_c` walk forces an exit — for the concrete exit-0 image the walk is closed by `decide`. | `Checks/Examples.lean` |
| `check_sound` | the ASan plan checker is sound against the abstract semantics, over a concrete `LIMIT` kept as an explicit parameter. | `Common/AsanPlanSound.lean` |
| `gate_exit0_accepts`, `gate_exit1_rejects` | the accept/reject gate is decided on both demo verdicts. | `Checks/GatedSize.lean` |
| `DemoSealed`, `omni_strong_universal` | the worked demonstrations' sealed specifications (a full `SPEC_PATCH_CLASSIFY` instance, so the classifier surface is inhabited), and proofs that their images meet them. | `Examples/` |

## Documentation

- `NOTES.md` — Lean 4.31 tactics, reduction behaviour, and build latency, with
  the measurements behind each entry. Read it before fighting a proof.
- `AGENTS.md` — the working conventions (one module per file, comments are part
  of the artifact, no proof holes, verify with `lake env lean`).
