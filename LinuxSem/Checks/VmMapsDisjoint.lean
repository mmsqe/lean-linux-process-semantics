/-
  * LinuxSem.Checks.VmMapsDisjoint — what [vm_maps] really guarantees

    Not part of the trusted specification: QA on the definitions, in the
    style of [Checks/Examples], plus the ledger invariant those
    definitions DO maintain.

    One might expect the [vm_maps] intervals to be "pairwise disjoint
    by construction ([region_free] gates every grant)".  PART 1 below is
    a machine-checked execution that refutes that: six modeled syscalls
    from an [execve]-shaped [init_model] state leave the ledger holding
    two OVERLAPPING entries, and eight leave it holding two entries with
    the SAME BASE and different sizes.  So neither byte-level pairwise
    disjointness nor byte-level base uniqueness is an invariant of
    reachable states, and no proof of either can exist.

    PART 2 states and proves what IS invariant, which is the property
    every consumer of the ledger actually needs: no PAGE-ALIGNED address
    is owned by two entries.  Every address a syscall can name as a
    mapping base is page aligned ([munmap], [mremap] and [mprotect]
    answer -EINVAL otherwise, and [mmap] only ever places on a page
    boundary), so this yields base uniqueness exactly where it is used,
    and in particular makes [munmap]'s [map_has]/[map_remove] pair agree.

    WHY THE WEAKER PROPERTY IS THE RIGHT ONE.  The gap Part 1 exploits is
    real Linux behaviour, not a modelling slip: [SYSCALL_DEFINE1(brk)]
    (mm/mmap.c) rounds both breaks and takes

      newbrk = PAGE_ALIGN(brk);
      oldbrk = PAGE_ALIGN(mm->brk);
      if (oldbrk == newbrk) {
              mm->brk = brk;
              goto success;
      }

    BEFORE any VMA is consulted — the shrink block's [vma_find], the
    grow path's [check_brk_limits], its stack-guard-gap [vma_find] and
    [do_brk_flags] are all BELOW this exit.  Read at the kernel of
    record, stable v6.18.46 (commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5): [SYSCALL_DEFINE1(brk)] is
    still in mm/mmap.c — the v6.12-era VMA split moved [do_brk_flags] out
    to mm/vma.c but left the syscall and this exit where they were — and
    no statement between function entry and [goto success] reads the VMA
    tree.  The exit block quoted above is byte-identical from v5.18
    through v6.18.46.  The PROLOGUE is not byte-identical that far:
    commit e001ef9652c2 ("mm: simplify min_brk handling in brk()", first
    released in v6.17) hoisted [min_brk = mm->start_brk] above the
    [CONFIG_COMPAT_BRK] ifdef and inverted the test inside it, holding
    the prologue text constant only over v6.5-v6.16.  That is a
    no-functional-change refactor of a gate already above the exit and
    already not an address-space test, so nothing argued here moves with
    it; and neither does the v6.12 change of the shrink call from
    [do_vma_munmap] to [do_vmi_align_munmap], which is below the exit.
    Window figures sample mainline tags; the v6.18.46 statement is read
    from that commit itself.  A brk move
    within one page therefore reaches [mm->brk = brk] with NO
    ADDRESS-SPACE TEST APPLIED,
    even when the bytes it walks over belong to some other mapping — a
    state a real process reaches by unmapping the brk VMA and mapping
    over it.  Not unconditionally, though: three gates sit ABOVE the
    exit, none of them about the address space — the killable
    [mmap_write_lock], the [brk < min_brk] floor, and
    [check_data_rlimit(rlimit(RLIMIT_DATA), brk, ...)], which is passed
    the RAW unaligned break precisely so a non-page-aligned limit cannot
    be escaped by a within-page grow.  Each returns [origbrk], the break
    unchanged.  The model does not carry [RLIMIT_DATA], and does not need
    to: [brk_r_ok] admits [r = vm_brk h] on every grow, which is that
    same unchanged break, so a refusal it does not model is already an
    admissible outcome.  The model reproduces
    that faithfully with [brk_grow_ok]'s [else true], and a gate that
    required the unrounded range [[old, r)] to be [region_free] would
    make the model REJECT a call Linux serves.  [brk_r_ok] evaluates the
    gate at the resolution it is shown, so the tightening would decline
    the SUCCESS resolution [r = req] — the break Linux hands back —
    while leaving the no-op resolution [r = old] admissible, its outer
    guard having degenerated to [old < old].  The byte-level overlap is
    the honest ledger reading of a real kernel state; page-granular
    ownership is what survives it.

  SPELLING.  As in the neighbouring `Checks/Cases/Mm/` files,
  the statements keep one vocabulary and the few
  spellings Lean does not have are supplied as local transparent
  `abbrev`s below, DEFINITIONALLY EQUAL to what they stand for, so no
  statement below changes meaning:
  - `Z_to_bv n z` is `BitVec.ofInt n z` and `bv_unsigned w` is
    `(w.toNat : Int)`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`;
  - `negb` does not exist in Lean and is shimmed;
  - the record PROJECTIONS are opened under their bare names, because
    a projection can be applied as a function (`vm_maps (m_vmmaps m)`)
    while Lean's projections live in the structure's namespace
    (`⋯.vm_maps`), and `machine_state`'s fields are reachable only by dot
    notation.

  PROOFS.  The concrete examples are compiled reductions:
  `repeat first [reflexivity | (apply bv_eq; reflexivity) |
  progress f_equal]` over a closed goal evaluates in the VM, and its
  counterpart here is `rfl` (kernel reduction of a closed goal), which
  closes every concrete example — the same
  treatment `Checks/Cases/Mm/Mmap.lean` gives the identical idiom.  The
  universally quantified lemmas carry ordinary tactic proofs.

  THE FRAME HALF.  The frame argument is a LOOP: case-split a hypothesis
  that contains an `if` or a `match` until it reads
  `CheckOk m [] = CheckOk m' evs`, then `rfl`.  PART 3 carries that loop,
  and records the route that works and the one that does not:

  * `split at *` / `split at H` on the UN-destructed checker body is not
    the route.  Splitting the `match eff with | ⟨r, [], zs, us, [], []⟩ =>
    … | _ => .CheckReject` shape makes Lean GENERALISE `eff` and case on the
    wildcard, which leaves goals the `repeat` loop cannot close (a previous
    session reported the symptom as "Missing cases: _"; on this toolchain
    the split itself succeeds and the damage shows up downstream).
  * The route that works is to DESTROY the effect
    (`obtain` its six components `⟨r, ws, zs, us, cs, ci⟩`, then `cases`
    on the five fields — the spelling of a `destruct ws as [|? ?]` chain),
    so the checker's `match eff with` is a match on a CONSTRUCTOR
    application that `simp only [check_X, <its helpers>]` reduces.

  The `vm_frame` macro is section-local to this file on purpose: it is not
  general (it assumes the six-field `SyscallEffect` and a `CheckOk`-shaped
  checker result), so it does not belong in `Checks/Cases/CheckToolkit.lean`.

  Seven arms — `bind`, `clock_gettime`, `connect`, `nanosleep`, `openat`,
  `socket`, `write` — each had a MEASURED obstacle rather than a missing
  proof idea: bitvector guards that `split` cannot decide, `openat`'s
  `split`-hostile `check_copyins_after`/`check_openat_body` nest, a
  descriptor dispatch whose NESTED constructor patterns `split` refuses, and
  a `check_ret_only_copyins` leaf whose `let copied` binding (a `sint32
  addrlen == 0` test) makes the `*_model` inversion blow `maxRecDepth` at
  1,000,000 during unification.  The obstacles, and the route that moves
  each, are recorded in the block at the end of this file.

  The four routes, all of them this tree's own: the `cases h : <Bool guard>`
  walk (`vm_close`, for the `private`-helper arms); the plain `vm_frame` for
  the arms whose guards are all cheap; `vm_frame_m` for the arms whose
  accepting branch ends in a `check_ret_only`-family COPY-IN WRAPPER (see
  the note on that macro; `split` generalises such a wrapper's stuck `match`
  and destroys the hypothesis); and the written-out `generalize`/`cases`
  walk with the `vm_ret_only` leaf closer (five arms, see its own note) —
  plus the arms that walk their own dispatch and then hand the accepting
  branch to a helper's PUBLIC frame (`readv` →
  `Fs.ReadWrite.check_readv_imported_frame`, `sendto`/`sendmsg` →
  `Net.Socket.check_send_on_socket_frame`).  One more is not a loop at all:
  the `rt_sigprocmask` arm CHANGES the model, so its VM half is proved
  beside the checker in `Checks/Sys/Kernel/Signal.lean` and this file cites
  it.

  `arm_preserves_vm`, `checked_table_preserves_vm` and the dispatcher
  corollaries (`check_syscall_preserves_vm_wf`,
  `syscall_spec_preserves_vm_wf`, `base_unique_after_syscall`) follow from
  the frame lemmas in `VmMapsDisjoint/Chain.lean`, on top of
  `Chain/Arms.lean` (86 frame arms, `brk` included) and
  `Chain/Writers.lean` (the four ledger-rebuilding writers).  The `brk`
  preservation is `Core`'s `check_brk_preserves`.
-/

/-
  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moved).

  This file used to BE the whole thing: 3,185 lines, 92.8 s of
  `lake env lean`.  Five frame arms were ~80 s of that (`prlimit64` 28 s,
  `writev` 26 s, `pwrite64` 22 s, `setresgid` 20.7 s, `futex` 12.1 s),
  while a full incremental `lake build` with nothing changed is 0.26 s —
  so the cost was never the build, it was this one module's elaboration.
  Lean elaborates a module as a unit and lake parallelises only ACROSS
  modules, so the file is now a pyramid that a 16-core machine checks
  concurrently, and an edit to one arm no longer costs a check of every
  wide one:

    VmMapsDisjoint/Core.lean              PART 1, PART 2, PART 2b, the
                                          writers' `*_preserves` lemmas,
                                          `bvnorm`, `lookup_ca_In`,
                                          `init_model_vm_wf`
    VmMapsDisjoint.lean                   this file, the aggregator: a pure
                                          import shim — no declaration, just
                                          the imports and the PART 3
                                          narrative and the frame-half record
    VmMapsDisjoint/Tactics.lean           the frame tactics and the five
                                          `*_model` inversions every arm
                                          loop ends in
    VmMapsDisjoint/Frames.lean            the bulk of PART 3's cheap arms
    VmMapsDisjoint/Frames/Wide.lean       the five wide-dispatch, cheap-guard
                                          arms (`accept4` … `tgkill`)
    VmMapsDisjoint/Frames/CostlyA.lean    getsockopt, newfstatat, futex
    VmMapsDisjoint/Frames/CostlyB.lean    setresid (setresuid / setresgid)
    VmMapsDisjoint/Frames/CostlyC.lean    writev
    VmMapsDisjoint/Frames/CostlyD.lean    pwrite64
    VmMapsDisjoint/Frames/CostlyE.lean    prlimit64
    VmMapsDisjoint/Frames/CostlyF.lean    sched_setscheduler
    VmMapsDisjoint/Chain/Arms.lean        `arm_preserves_vm` and its 86
                                          frame-arm instances
    VmMapsDisjoint/Chain/Writers.lean     the four ledger-REBUILDING
                                          writers' preservations
    VmMapsDisjoint/Chain.lean             the 90-arm table and the four
                                          dispatcher corollaries

  The split is by COST, not by size, and the measured cost table is the
  whole argument for the boundaries.  `lake env lean <module>`, warm
  oleans, one module at a time:

    Tactics        1.0 s     Frames       17.5 s     Wide        23.8 s
    CostlyA       14.3 s     CostlyB      23.2 s     CostlyC     32.1 s
    CostlyD       24.4 s     CostlyE      31.2 s     CostlyF      3.4 s
    Core           8.8 s     this file     0.25 s

  A cold `lake build` of the eleven (the nine arm modules in parallel with
  `Core`, then this file, then the root module and its `Capstone` leaf) is
  41.3 s to 46.0 s wall on this 16-core machine, measured by deleting those
  eleven oleans, the leaf's and the root module's; the same protocol on the
  ten-module layout, which elaborated PART 1/2 here, gives 51.0 s to
  53.2 s.  (Those runs predate the deletion of `Checks/Capstone.lean`.  It
  held nothing but `#check`s — no declaration, no dependency edge above this
  file — so the numbers below stand; only a file that is no longer compiled
  is missing from the protocol.)  (The machine's load drifted from ~9 to ~21
  during these runs, so the ranges are wider than the effect.)  A warm
  `lake build` with nothing changed is ~0.2 s either way.  The two 32 s arms
  (`writev`, `prlimit64`) are SINGLE declarations, so they are the floor on
  any wall time for this subtree and everything else is arranged to finish
  before them — `CostlyC` and `CostlyE` are alone in their modules for
  exactly that reason.

  What an edit costs depends on which module it lands in.  Each number
  below is a measured `lake build` after the edited module's olean (and
  this aggregator's and the root module's) was removed, so it
  includes the re-elaboration of everything downstream of the edit:

    a cheap arm (`Frames.lean`)      19.4–20.5 s  (was 28.6–31.3 s)
    a wide-guard arm (`Wide.lean`)   25.6–27.9 s  (was 34.8 s)
    an expensive arm (`CostlyC`)     32.9–36.5 s  (was 43.0 s)
    PART 1/2 (`Core.lean`)           10.3–10.7 s  (was 10.7 s — unchanged)

  So the common case — a proof in a cheap arm — drops from ~29 s to ~20 s:
  the ~9 s this file used to spend re-elaborating PART 1/2 now runs in
  PARALLEL with the frame modules instead of after them.  A PART 1/2 proof
  is unchanged rather than worse: `Core`'s 8.8 s replaces the old
  aggregator's 8.8 s, and the shim itself costs only 0.25 s.  The `writev`
  / `prlimit64` case improves with the rest (~43 s to ~33–37 s) because
  the aggregator's 9 s leaves its path too; those two declarations are
  still ~32 s of elaboration each, and no module split can divide one
  declaration.

  Every declaration keeps the fully qualified name it had, because every
  module uses this file's own namespace; nothing that was `private` moved
  (the moved declarations were all public), and no statement, proof term,
  hypothesis or tactic call changed — the bodies were copied byte for byte,
  and the file boundaries are the only edit.  `git diff` against the state
  before the two splits shows exactly that: the removed lines all reappear,
  unchanged, in the new modules.

  `bvnorm` moved WITH `bv_unsigned` and `vm_wf`, not above them: a macro
  quotation resolves its identifiers at the MACRO'S DEFINITION SITE
  so a `bvnorm` defined before those names exist would
  expand to `bv_unsigned✝` / `vm_wf✝`, and the surrounding `try` would make
  it a silent no-op.  `Core` defines `bv_unsigned` (the prelude) and
  `vm_wf` (PART 2), so `bvnorm` lives there.  Verified after the move:
  `Core` checks clean — the 24 `omega` failures the first attempt produced
  do not recur — and a probe that needs the normalisation still closes.

  The narrative comments stay here, in front of the reader: PART 3's
  "what replaces it" note (the effect-destruct route, the three obstacles)
  is the map for the arm modules, and the block at the end records what the
  last seven arms cost and which two helper frames are still absent,
  whether the arm lives in
  `Frames`, in `Wide` or in one of the `Costly` siblings.  `lookup_ca_In`
  and `init_model_vm_wf` sit at the end of `Core`, beside the PART 2
  invariant they are the base case of.
-/

import LinuxSem.Checks.VmMapsDisjoint.Core
import LinuxSem.Checks.VmMapsDisjoint.Tactics
import LinuxSem.Checks.VmMapsDisjoint.Frames
import LinuxSem.Checks.VmMapsDisjoint.Frames.Wide
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyA
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyB
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyC
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyD
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyE
import LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyF
import LinuxSem.Checks.VmMapsDisjoint.Chain

/- =========================================================================
   PART 3 — the FRAME half: what one syscall arm leaves [vm_maps] alone

   The argument is a LOOP over the checker's body — case-split a
   hypothesis that contains an [if] or a [match] until it reads
   `CheckOk m [] = CheckOk m' evs`, then `rfl` — and each lemma is one line
   of the `vm_frame` macro below.  The shape it splits is

     check_X ... = CheckOk m' evs
       with the checker's body ending in
     match eff with | ⟨r, [], zs, us, [], []⟩ => ... | _ => .CheckReject

   Lean's closest primitive, `split at H`, is not equivalent to a destruct:
   on that shape it GENERALISES `eff` and cases on the wildcard.  (An
   earlier note here recorded "Missing cases: _" as the symptom; on this
   toolchain the split SUCCEEDS, and the damage shows up downstream as
   goals the loop cannot close.  The obstruction is that the split is
   unproductive, not that it is refused.)  It is a tactic-level obstruction
   all the same: the same checkers are perfectly well-founded (three
   probes closed with `split at *`).

   WHAT REPLACES IT (the `vm_frame` macro below).  Do not split the match
   on [eff] — DESTROY [eff] instead, doing to the fields what a
   `destruct ws as [|? ?]` chain does:

     1. `obtain ⟨r, ws, zs, us, cs, ci⟩ := eff` — replace the effect by
        its six components, so the checker's `match eff with` is a match
        on a CONSTRUCTOR application;
     2. `cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci` —
        the 32 constructor shapes.  With the lists constructor-shaped,
        `simp only [check_X, <the helpers it calls>]` reduces the match
        to `.CheckReject` in 31 of them;
     3. then a loop that repeats the same steps:
          `cases H; rfl`  — the hypothesis has become
                            `CheckOk m [] = CheckOk m' evs`, so `cases`
                            substitutes and the goal is `rfl`;
          `cases H`       — the hypothesis is `CheckReject = CheckOk …`;
          `split at H`    — split an `if`/`match` that is left (the
                            checker's STATE dispatch: `fd_lookup`,
                            `m_stdin`, `read_bytes_map`, …);
          `simp only [check_X, helpers] at H` — unfold the next layer.

   `simp only` and `split` both refuse to be no-ops, so they double as the
   loop's progress test: the loop stops exactly when nothing applies, which
   is when `cases H` has made the goal `rfl`-true.

   The helper list is per-checker (the transitive closure of the
   `check_*` names its body mentions), NOT the whole `Checks.Sys` tree:
   passing all 67 helpers to every lemma costs more than it saves.

   COST OF THE ROUTE.  TWO causes, both measured, neither of them
   soundness — the record is kept because the hard arms were closed
   against it:

   (a) `private` checker helpers.  `check_ftruncate` calls
       `Open.check_ftruncate_file_arm`, which is `private def`, so its
       equation lemmas are not nameable from THIS module and `simp only`
       cannot unfold it: the accepting branch stays opaque and the goal
       `m_vmmaps m' = m_vmmaps m` never becomes `rfl`.  The same holds for
       `check_unlinkat` (`check_unlinkat_body`, `check_unlink_found`,
       `check_unlinkat_tmp`), `check_faccessat` / `check_faccessat2`
       (`check_faccessat_body`) and `check_openat` (via the public
       `check_openat_body`, which calls the private `check_open_devnull` /
       `check_open_urandom`).  Both `Open.lean` and `Namei.lean` already
       carry a private `*_sound_ok` that unfolds its helper, so the natural
       fix is a private `*_frame` beside it — that is their file to change,
       not this one.

   (b) `split` cost on the wide MODEL-state dispatch.  For a checker that
       dispatches first on model state with a wide match (`check_read`'s
       `fd_lookup` × `m_stdin` × two `read_bytes_map` tree), step 3's
       `split at H` produces that whole tree of leaves and every leaf's
       `cases H` does `isDefEq` on the fully instantiated checker body: the
       33 arm lemmas still open at the time cost >1,000,000 heartbeats each
       (measured: 4 min 20 s for the 33 at `maxHeartbeats 1000000`, 28 of
       them still timing out).  The fix is a `*_frame` lemma for the
       model-state helpers so the loop never has to split them, not a
       bigger budget.

   Both causes are cleared by the routes the block at the end records — the
   public `*_frame` helpers in `Open.lean` / `Namei.lean` for (a), the
   `cases h : <Bool guard>` walk for (b).

   COST OF THE FRAME LEMMAS THEMSELVES: they took the pre-split module from
   8.4 s to ~20 s of `lake env lean` (32 effect shapes × a per-lemma helper
   unfold — no `simp`-all, no `decide`).
   ========================================================================= -/

/-! ### The frame lemmas, the writer preservations, and the dispatcher chain

    The frame half is `Frames.lean` / `Frames/Wide.lean` /
    `Frames/Costly*.lean` (the effect-destruct route), with the two base
    lemmas `lookup_ca_In` and `init_model_vm_wf` at the end of `Core`,
    beside the PART 2 invariant they are the base case of.

    (1) THE OBSTACLES, one by one.  Each cost a round, and each is a fact
        about Lean's tactics rather than about the checkers:

        A BITVECTOR GUARD MUST REDUCE.  `check_read_frame` — the widest
        dispatch in the module (`fd_lookup` × `m_stdin` × two
        `read_bytes_map` trees × the socket protocol) — closes in 1.1 s, and
        so do `pread64`, `accept4`, `rt_sigaction` and `tgkill`, because
        every guard on the way down is a `Bool` test on the arguments
        (`errno_ret_in`, `bv_eqb`, `access_okb`) or a `match` on model
        state.  The blocker is the guard that is a BITVECTOR COMPUTATION:
        `decide (len.toInt < 0)`, `!(z_ldiff … == 0)`,
        `!(sint32 domain == …)`, `!(modeled_access_mode mode)`.  To case
        such an `if`, `split at H` (and `simp only [check_X] at H`) has to
        REDUCE the guard, and `BitVec.toInt` / `z_land` / `z_ldiff` on a
        SYMBOLIC word do not reduce.  Measured on `check_socket`: `split at
        H` spends ~250,000 `Nat.rec` unfoldings before the
        `maxRecDepth 1000000` ceiling, and on
        `check_write`/`readv`/`sendto`/`sendmsg`/`connect`/`bind` the same
        attempt instead exhausts `maxHeartbeats 1000000` inside `whnf` —
        or, for `connect`, `maxRecDepth 1000000` as well.  Crucially, BOTH
        limits are UNRECOVERABLE exceptions — `first` cannot catch them —
        so one such guard aborts the whole proof, which is why a bigger
        budget is not the answer and why the loop cannot simply try it and
        fall back.

        THE ROUTE THAT WORKS: a one-`destruct`-per-guard walk, with the
        guard cased as a BOOLEAN — `cases h1 : decide (len.toInt < 0)`,
        never `split`, then
        `simp only [h1, Bool.false_eq_true, ite_true, ite_false] at H`.
        `cases` on a `Bool` term only generalises and splits it; it never
        reduces it.  That is exactly the idiom
        `Checks/Sys/Net/Socket/Socket.lean` already uses for
        `check_socket_sound_ok`.  The `vm_close` macro runs the ordinary
        loop once the guards are gone.  Measured per arm: `ftruncate` 2.0 s,
        `faccessat` 1.4 s, `faccessat2` 1.9 s, `unlinkat` 1.3 s — all four
        in a probe file with warm oleans.

        A PROBE FILE MEASURES THE OLEAN, NOT THE SOURCE.  `lake env lean
        probe.lean` with a probe that imports this module resolves every
        name from `.lake/build/lib/lean` first, so while the module under
        edit is red — or has not been rebuilt — the probe silently sees an
        older `VmMapsDisjoint`.  One probe here answered "unknown tactic"
        for a macro that was in the source and not in the olean, and an
        earlier batch of "passing" probes had never run the loop at all.
        Either probe in a file that copies the `*_model` helpers it needs,
        or verify inside the real file; the per-arm numbers above are worth
        only as much as the freshness of the olean behind them.

        THE `private`-HELPER HALF.  Four arms (`ftruncate`, `faccessat`,
        `faccessat2`, `unlinkat`) also need the accepting branch of a
        `private def` helper unfolded, which a sibling module cannot do.
        `Checks/Sys/Fs/Open.lean` and `Checks/Sys/Fs/Namei.lean` carry
        PUBLIC frames for them — `Open.check_ftruncate_file_arm_frame`,
        `Open.check_faccessat_body_frame`, `Open.check_open_devnull_frame`,
        `Open.check_open_urandom_frame`,
        `Namei.check_unlinkat_body_frame`, `Namei.check_unlink_found_frame`,
        `Namei.check_unlinkat_tmp_frame` — and the loop cites them as a
        TERM (`vm_close H [exact …_frame _ _ _ _ H] …`), FIRST in the
        `first` chain: `cases H` on a private helper application succeeds
        but is unproductive, so it must not get the first word.

        `openat`: a SPLIT-HOSTILE NEST.  Its accepting branch is
        `check_copyins_after reads eff (check_openat_body …)`, and
        `check_openat_body`'s own `match read_cstr i.in_mem pathp` /
        `match clear_copyins eff` nest is split UNPRODUCTIVELY by
        `split at H`: the split succeeds and leaves
        `x✝ : (match …) = .CheckUnmodeled → False` goals the loop cannot
        close.  The route taken is to walk `check_openat_body`'s `read_cstr`
        match by hand (`cases hc : read_cstr i.in_mem pathp`, the idiom
        `Open.check_faccessat_body_frame` already uses internally), so
        `check_openat_frame` needs no public `check_openat_body_frame`.

        A DESCRIPTOR DISPATCH ON NESTED CONSTRUCTOR PATTERNS (`none`,
        `some (.FdChannel _)`, … `some .FdDir`) is not splittable:
        `split at H` answers "Missing cases: _" and leaves the goal
        untouched, so the dispatch must be `generalize hq : fd_lookup
        (m_fds m) fd = q` + `cases q` + `cases e` + `dsimp only at H`
        (`unfold` alone leaves `match none with …` UNREDUCED — the iota
        step is `dsimp`'s).

        `exact nomatch H` ON A STUCK `if` EMITS "Missing cases: _", WHICH IS
        NOT BACKTRACKABLE, so it cannot be the first arm of a `first` chain
        that also has to handle the stuck case — one such arm aborts the
        whole proof.  `contradiction` fails cleanly on the `if` and closes
        the `CheckReject = CheckOk` leaves; that is what the `vm_ret_only`
        closer uses.  (`Checks/Sys/Fs/ReadWrite.lean`'s header records the
        same footgun from the `check_read` proofs.)

        A COPY-IN WRAPPER'S STUCK `match`.  `check_ret_only`,
        `check_ret_only_copyins`, `check_write_oset_copyins` and friends end
        in a `match check_ret_only (clear_copyins eff) r mm evs0 with
        | .CheckOk m'' evs' => … | result => result`.  Once
        `simp only [check_X, <helpers>] at H` has unfolded the wrapper, the
        `match` scrutinee is `if bv_eqb ret r` — undecidable — so the loop's
        next `split at H` GENERALISES it, introducing `x✝` and `heq✝` and
        losing the hypothesis the loop names.  The fix is `vm_frame_m`,
        which keeps those wrappers OUT of the `simp only` list and closes
        the terminal call with the `*_model` inversions
        (`check_ret_only_model`, `check_ret_only_copyins_model`,
        `check_copyins_model`, `check_copyin_prefix_model`,
        `check_copyins_after_model`): `rw [<lemma> … H]` replaces `m'` by
        the model the wrapper hands back, and `rfl` then closes
        `m_vmmaps (with_fds …) = m_vmmaps m`, because a projection of a
        structure update reduces definitionally.

        THE KERNEL-DEPTH WALL.  `bind` and `connect` first looked like a
        size problem in `H`, and that diagnosis was measured WRONG: the wall
        is the `rw [ite_eq_left h] at H` STEP.  `ite_eq_left`'s statement embeds BOTH
        branches of the `if`, so each rewrite copies the surviving tail into
        the proof term, and chained once per guard the TERM's depth exceeds
        the kernel's own budget — which `set_option maxRecDepth` does not
        reach (a different budget from the tactic-level one above).  That is
        why seven factoring attempts — tail lemmas, a named arm body, a
        generic peel lemma — all reproduced it: the cost is in the rewrite's
        shape, not in what it rewrote.

        `bind` uses `check_bind_sound_ok`'s own idiom: `generalize` the
        addrlen truncation, then `by_cases h : <guard> = true` +
        `simp only [h, ite_true] at H` — that rewrites the guard in the
        CONDITION, a one-hole motive, and then iota-reduces the `if`.  0.4 s.

        `connect` cannot use that: every hypothesis-level transformation of
        its UNFOLDED body reproduces the wall (measured individually — zeta,
        `generalize`, the `fd_lookup` `cases` each alone).  It is proved
        with the checker FOLDED in `H` and the 11 arm equations as the leaf
        opener (`Check.Connect`'s own `connect_chk_*` design), each a
        one-hole motive; those are public in that module, so this tree cites
        them directly and the restatements it used to carry are gone.  An external mirror
        is not defeq-checkable either: `check_bind … = bind_full …` by
        `rfl`, and by `unfold … ; dsimp only ; rfl`, both give the kernel
        error after ~31 s, while staged tail lemmas each check in 0.4 s and
        still cannot cross into stage 1 without the same two-sided defeq.
        `check_errno_or_success_model` was added beside the other `*_model`
        inversions.

        **Rule**: cross a boundary with a TERM-level equation, never with
        definitional equality.

        A SIX-WAY SIMULTANEOUS `match` ON OPTIONS.  `sendmsg`'s `read_u64`
        `msghdr` read is that shape, so `split` cannot do it: each of the
        six scrutinees must be `generalize`d and `cases`d (64 leaves, one
        live), and the live leaf's guards name the bound fields (`name`,
        `iov`, `iovlen`, `ctllen`), which is why the `cases` must name the
        `some` patterns with `cases … with | some x =>` instead of
        `cases … <;>` — the `case`-bound variables are otherwise
        inaccessible (`val✝³`).  `simp only [check_ret_only] at H` while
        `H` still holds the 11-arm descriptor match is what burns
        `maxRecDepth`; dispatch the descriptor FIRST and it is instant.

        THE THREE HELPER FRAMES THOSE ARMS NEEDED:
        `Fs.ReadWrite.check_readv_imported_frame` and
        `Net.Socket.check_send_on_socket_frame` /
        `check_recv_fd_answer_frame`, PUBLIC and stated beside their
        checker exactly as `Open.lean`'s `check_ftruncate_file_arm_frame`
        is; `readv`, `sendto` and `sendmsg` cite the first two as TERMS.
        `check_recv_fd_answer_frame` is cited nowhere only because
        `recvfrom` / `recvmsg` close without it (`simp only
        [check_recv_fd_answer]` suffices there).

    (2) NO HELPER FRAMES ARE MISSING.  Two were formerly listed here, and
        neither is a gap.  `Checks.Sys.Uaccess.check_efault_or` is
        called by no checker — only by its own soundness and completeness
        lemmas — so a `check_efault_or_frame` would have no site; and
        `Checks.Sys.Fs.ReadWrite.check_readv_gap` is by definition
        `.CheckUnmodeled`, so a hypothesis `check_readv_gap = .CheckOk m' evs`
        is unsatisfiable and a frame over it would be vacuous.  The readv
        arm's frame is `check_readv_frame`, which cites the public
        `check_readv_imported_frame` for the body that can accept.

    (3) THE DISPATCHER CHAIN lives in `VmMapsDisjoint/Chain.lean`:
        `arm_preserves_vm`, the table statement `checked_table_preserves_vm`,
        and the corollaries `check_syscall_preserves_vm_wf`,
        `syscall_spec_preserves_vm_wf`, `base_unique_after_syscall` — on top
        of `Chain/Arms.lean` (the 86 frame-backed arms, `brk` included, each
        `simp only [arm_X] at H` + the arm's frame + `exact Hwf`) and the
        four writer arm lemmas.  The table induction is 90 named
        applications, one per `checked_table` entry, so no arm can be
        dropped silently.  `checked_table_preserves_vm` is stated with the
        two-constructor `Forall` that module declares: Lean's core list
        library has none (see `Checks/Cases/Net/Socket.lean`), and the
        `∀ c ∈ checked_table, …` form the dispatcher reads is derived from
        it once.

    (4) THE FOUR NON-BRK WRITER PRESERVATIONS
        `check_munmap_preserves` / `check_mprotect_preserves` /
        `check_mmap_preserves` / `check_mremap_preserves` live in
        `VmMapsDisjoint/Chain/Writers.lean`.  These are NOT frames: each
        writer rebuilds the ledger, so each proof follows its checker's own
        `*_sound_ok` walk and closes the accepting leaf with PART 2's
        algebra — `maps_wf_filter` for `map_remove`,
        `maps_wf_subtract`/`maps_wf_cons_free` for the `mmap` destroyed and
        spanning shapes (`maps_subtract_region_free` is what makes the
        spanning cons safe), `maps_wf_cons_sub` for `mremap`'s shrink (the
        source entry reappears shorter at the same base), and
        `region_free_app_r`/`region_free_filter` to move a gate's
        `region_free (vm_reserved ++ …)` fact onto the list the invariant
        reads.  `mprotect` is the one writer whose `vm_maps` is untouched,
        so its proof ends in `vm_wf_of_vm_maps`.

    (5) THE PART 2b `owned_bytes` EXAMPLES, above.  Four are still open, and
        the reason is the interpreter rather than the statement: a
        4,196-byte `owned_bytes` walk is ≈20k kernel recursion levels and
        overflows the stack.  Do not raise `maxRecDepth` hoping to fix a
        stack overflow.  The fifth —
        `live_bytes_over_counts_the_duplicate_base` — is proved: it is a
        named `theorem` beside the block in `Core.lean` and `rfl` closes
        both conjuncts, so the stack limit is not universal on this shape.
        Read the block in `Core.lean`, not this list, as the current state.

    (6) WHAT THE FINAL LAYER RESTS ON.  `brk_grant_wf` — the heart of
        PART 2 — is proved, together with `brk_r_ok_grow`,
        `brk_model_next_wf` and `check_brk_preserves`, and the whole
        `maps_subtract` algebra it rests on (`iv_subtract_ok`,
        `maps_subtract_ok`, `maps_wf_subtract`, `maps_wf_cons_free`).  So
        the page-granularity invariant is PRESERVED BY `brk` — the one
        syscall whose grant can overlap a live mapping (PART 1 exhibits
        exactly that) — and `base_entry_unique`/`map_has_pins_size`/
        `munmap_returns_matched_bytes` give the payoff munmap needs.

        The frame lemmas cover 85 of the 90 arms (11 arms reuse a sibling's
        frame: `accept`/`exit_group`/`fdatasync` and the eight
        `setid`/`setresid`/`getid` arms), `check_brk_preserves` is the
        86th, and `Chain/Writers.lean` proves the four ledger-rebuilding
        writers (`munmap`, `mremap`, `mmap`, and `mprotect` — which keeps
        `vm_maps` but rebuilds `vm_noaccess`); `init_model_vm_wf` gives the
        invariant its base case.  The dispatcher chain in
        `VmMapsDisjoint/Chain.lean` closes the surface:
        `checked_table_preserves_vm` covers all 90 arms and
        `check_syscall_preserves_vm_wf` turns that into "an ACCEPTED syscall
        preserves `vm_wf`", which is the result
        `LinuxProcessSem/StateLedger.lean` cites — so "every modelled
        syscall preserves page-granularity disjointness" is a claim about
        the checker, not a hypothesis, and `syscall_spec_preserves_vm_wf` is
        the same claim on the relational spec (through the completeness
        direction).
-/
