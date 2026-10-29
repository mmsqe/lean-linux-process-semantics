/-
  * Common.SimInv — generic path-invariant / no-error combinator.

  TRUST BOUNDARY: this file is part of the shared proof library, not the
  trusted specification.  Nothing here knows about any particular
  binary.

  Every "sim" file in `Common/` (ExitSim, CatSim, StreamSim, AllocSim,
  MmapSim, FileSim, DrainSim) closes the `~ reaches_error` obligation the
  same way: it defines a per-file configuration invariant `Inv`, proves
  that `Inv` is preserved by every `sstep` to a `SNext` successor, proves
  that `Inv` excludes the `SError` transition, and then lifts these two
  facts along `star` to conclude that no reachable configuration errors.

  The `star`-lifting induction and the final `reaches_error` closure are
  byte-identical across all those files, so they are factored here once:

    - `star_inv`              : `Inv` is preserved along `star`
    - `inv_no_reaches_error`  : `Inv c -> ~ reaches_error segs c`

  Each sim file supplies only its two genuinely per-file hypotheses (the
  step-preservation and no-error lemmas) and instantiates these two
  combinators; its `star_X`/`X_no_error` lemmas become thin corollaries.

  This file is also where the shared ABI-boundary normalization tactics
  live (`norm_fd32`, `fd32_ok`): every "sim" file and every per-binary
  proof imports it (directly or through CatSim/StreamSim/FileSim), and
  proof automation shaped by particular example proofs has no business
  sitting in the trusted `LinuxProcessSem.Specs`.

  Those two `Ltac`s are documented, not transliterated, in the
  proof-kit section below; the stated identity lemmas
  `Syscall.fd32_id`/`fd32_lt31` plus `decide` on concrete `BitVec` words
  supply the same discharge.  Nothing in THIS file uses either kit.
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
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence

namespace LinuxSem.Common.SimInv

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

/- =========================================================================
   ABI-boundary truncation (`Syscall.fd32`) — proof kit
   =========================================================================

    two `Ltac`s are not transliterated .
   The kit they provide already exists in this module in the shape the Lean
   proofs consume:
     - the identity side is `Syscall.fd32_id` / `Syscall.fd32_lt31`, both
       stated with `Syscall.fd32` itself;
     - the "by conversion" normalisation of a CONCRETE fd is a closed
       `BitVec` computation in Lean — `decide`/`simp` discharge it, so no
       side condition is needed here either (`fd32` of a symbolic register
       is likewise left alone: the rewrite simply does not fire).
    text, kept for reference:
     (** Proof kit for the per-binary proofs: the fds they step through are
         concrete ([Z_to_bv 64 1], AT_FDCWD, …), and on those [fd32] is the
         identity BY CONVERSION — so normalizing it away wherever it blocks a
         rewrite needs no side condition.  ([fd32] of a symbolic register is
         left alone; the match simply stops there.) *)
     Ltac norm_fd32 :=
       repeat match goal with
              | |- context [fd32 AT_FDCWD] =>
                  change (fd32 AT_FDCWD) with AT_FDCWD32
              | H : context [fd32 AT_FDCWD] |- _ =>
                  change (fd32 AT_FDCWD) with AT_FDCWD32 in H
              | |- context [fd32 ?x] => change (fd32 x) with x
              | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
              end.
     (** Discharge an [fd32 fd = fd] premise: by conversion for a concrete
         fd, otherwise from the [< 2^31] / [< 2^32] bound the caller carries
         for the fd it holds. *)
     Ltac fd32_ok :=
       solve [ reflexivity
             | assumption
             | apply fd32_lt31; assumption
             | apply fd32_id; assumption
             | apply fd32_lt31; lia
             | apply fd32_id; lia ].
   ========================================================================= -/

/-- `Inv` is preserved along any `star` run, given that it is preserved by
    every single `sstep` to a `SNext` successor. -/
theorem star_inv (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c') :
    ∀ c tr c', Inv c → star segs c tr c' → Inv c' := by
  intro c tr c' HInv Hstar
  revert HInv
  induction Hstar with
  | refl => intro HInv; exact HInv
  | step c1 evs c2 tr c3 h1 h2 ih =>
      intro HInv
      exact ih (Hstep c1 evs c2 HInv h1)

/-- If `Inv` is preserved by `sstep`-to-`SNext` and excludes the `SError`
    transition, then any configuration satisfying `Inv` never reaches the
    explicit error step. -/
theorem inv_no_reaches_error (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs .SError) :
    ∀ c, Inv c → ¬ reaches_error segs c := by
  intro c HInv h
  obtain ⟨tr, c', evs, Hstar, Hss⟩ := h
  exact Hnoerr c' evs (star_inv segs Inv Hstep c tr c' HInv Hstar) Hss

/-- The same invariant delivers the omni safety judgment directly: an
    invariant that excludes the error transition is a proof of
    `OmniRun.coexec … never_errors`, by coinduction along the
    preservation clause — no `Run.star` in sight.
    `OmniRun.coexec` is the finite-unrolling *definition* (see its notes), so
    the same statement is obtained from
    `no_error_coexec` and the two hypotheses (which do go through
    `star_inv` internally); the conclusion is unchanged. -/
theorem inv_coexec (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs .SError) :
    ∀ c, Inv c → coexec segs c never_errors := by
  intro c HInv
  exact no_error_coexec segs c
    (inv_no_reaches_error segs Inv Hstep Hnoerr c HInv)

/-- ... and the bridge from the library's `~ reaches_error` shape to it,
    for combinators that already have the negative fact in hand.
-/
theorem no_error_run_corun (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) →
    omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp never_errors := by
  intro H
  simpa [omni_corun, mkImage] using
    no_error_coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) H

/- =========================================================================
   The `Equivalence.modeled` conjunct, once
   ========================================================================= -/

/-- Turn a source `~ reaches_error` proof into the source-coverage
    conjunct of `Equivalence.strong_equiv`.  Every combinator below
    (`AllocSim`, `AllocSim2`, `CatSim`, `DrainSim`, `ExitSim`, `FileSim`,
    `MmapSim`, `StreamSim`) discharges `modeled` this way — the run never
    errors at all, so a fortiori it never reaches a configuration the
    model declined to interpret (`Run.no_error_no_unmodeled`).  It lives
    here, applied uniformly, so that the ten combinators cannot drift:
    the argument `~ reaches_error` must be about the SOURCE image, pc, sp
    and brk that `run` is applied to, and stating it once makes the
    unifier check that rather than leaving it to a copy-pasted script.

    The combinators whose source is EXPECTED to error need a direct proof
    instead: `ErrEscape.err_escape_modeled` (a deterministic
    `MachineFault`) and `AllocMixSim.tom_no_unmodeled` (a may-faulting
    brk mix). -/
theorem no_error_run_modeled (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) →
    modeled (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) := by
  intro H
  exact (modeled_iff (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp).mpr
    (coexec_conseq segs _ never_errors (covered segs)
      (no_error_run_corun segs pc ph sp brk0 mb rnd lim inp H)
      (never_errors_covered segs))

end LinuxSem.Common.SimInv
