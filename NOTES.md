# Notes — Lean 4 tactics, reduction, and build latency

Engineering notes for this repository. They record the Lean 4.31 (and toolchain)
behaviour that the proofs here have had to work around, with the measurements
that established each one. They are written to be useful on their own: none of
them requires knowing anything about another codebase.

Three themes recur, and most entries are an instance of one of them:

> **A tactic that fails silently is worse than one that fails.**
> `try`, `first`, `nomatch`, and macro hygiene can all turn a hard failure into
> something that looks like success. Several entries below are that shape.
>
> **When a proof "closes every goal and then fails", suspect the term it
> elaborated, not the tactic.** Tactics can finish in milliseconds and leave a
> proof term the kernel refuses.
>
> **A measured characterisation can still name the wrong cause.** Correlations
> across a handful of failures can be real and point at the wrong mechanism;
> the entries note where an earlier explanation had to be retracted.

## Contents

1. `omega` reasons over syntactic atoms
2. The `.lake` olean can shadow a newer source
3. Interpreted vs compiled reduction
4. Do not build while another process is verifying
5. Macro and tactic traps
6. Reduction walls: four distinct obstacles
7. Build latency

### ### 5.7 `omega` reasons over syntactic atoms

Nearly every stalled proof in this tree has had the same root cause. Each of
the following is a *distinct* atom to `omega`, even when the terms are
definitionally equal: `bv_unsigned x`, `↑(x.toNat)`, `two64`, `2 ^ 64 : Nat`,
`↑(2^64) : Int`, the numeral `18446744073709551616`, `estart E (SA b k)`,
`estart E {a_base := b, a_off := k}`, any projection (`HC.co_totsz`), any
`def` abbreviation (`page_size`, `estart`, `elenZ`), and any `let`-bound
variable. It also **silently drops hypotheses containing a `Nat` `2^64`** and
saturates on numerals above it. And it cannot see through a `let x := <e>`,
so `x.toNat` and `<e>.toNat` become unrelated.

The working discipline is therefore: pick one spelling per term, normalise
**both** sides the same way (`simp only [bv_unsigned] at H ⊢`,
`unfold two64 at *`), materialise projections into `have`s, and avoid
introducing `let` for anything that reaches `omega`.
- **`simp only [bv_unsigned] at *` does NOT unify the two spellings for
  `omega`** — normalising both sides does not make `bv_unsigned brk` and
  `↑brk.toNat` the same atom. What works is to **materialise the bound in the
  goal's own spelling** (`have h0 : 0 ≤ bv_unsigned … := (u64_range _).1`) and,
  when a naked numeral / `two64` / `page_size` / `KHI` sits in context, to
  `clear` the junk hypotheses in that subgoal. (This corrects an earlier,
  too-simple version of this note.)
- **`decide` refuses goals with free variables even when the projection would
  reduce to `true`** (e.g. `(ACS …).a_tidset = true`) — use `by simp` instead.

### ### 5.8 The `.lake` olean can shadow a *newer* source

`lake env` does not honour an exported `LEAN_PATH`; it **prepends** the
package's build directory. Measured:

```
$ LEAN_PATH=/tmp/x/lib:$TC lake env sh -c 'echo $LEAN_PATH'
…/.lake/build/lib/lean:<toolchain>/lib/lean:/tmp/x/lib:<toolchain>/lib/lean
```

So `lake env lean Foo.lean` resolves every `import` from `.lake/build/lib/lean`
**first**. In a shared worktree those oleans can be *newer* than the sources,
and then **"silent under `lake env lean`" can mean "a newer, foreign olean for
this module was found"** — a red source can look green. This is the mirror
image of the stale-olean trap (§ above): there the olean is too old, here it
is too new.

Observed concretely: `Obligations.lean` compiled silently against a `.lake`
`Traces.olean` that contained six `*_traces` theorems its own source did not
yet have.

**Remedy — verify from source, bypassing lake:**

```bash
TC=<toolchain>/lib/lean ; LEAN=<toolchain>/bin/lean
# 1. private module root: symlink all of .lake/build/lib/lean EXCEPT the
#    directory under test (the mirror must be COMPLETE — a partial root makes
#    Lean report "object file … does not exist" instead of falling through)
# 2. compile in dependency order, writing oleans yourself:
LEAN_PATH=/tmp/x/lib:$TC $LEAN -o /tmp/x/lib/<mod>/F.olean <path>/F.lean
```

Then a non-zero exit or any stderr is the source speaking. (`lake env lean`
also writes no olean at all, so it can never refresh the artifact that is
shadowing it.)

- **`split at H` is NOT reliable for `Bool` guards built from `==` on `Int`** — it
  descends into `Int.beq`'s internal `match` and either fails with "Dependent
  elimination failed" or splits the wrong thing (the `h_1`/`h_2` naming is the
  tell-tale). The uniform recipe for every guard in such a proof is:

  ```
  cases hg : <the Bool expression>        -- false branch first, then true
  · rw [hg] at Hn; simp only [Bool.false_eq_true, ite_false] at Hn
  · rw [hg] at Hn; simp only [ite_true] at Hn
  ```

  (`ite_true` alone handles `(true = true)`; the false side needs
  `Bool.false_eq_true`. For a `!(x == e)` / `!decide p` guard add
  `Bool.not_false`/`Bool.not_true` on the corresponding side.) `split at H`
  *is* right for a genuine outer `match` such as
  `match (if … then some k else …) with | none => … | some k0 => …`.
- **`cases`/`simp` do not close `Hn : none = some cs'`** — the goal does not
  depend on it, so `cases` merely clears it. Use `exact absurd Hn (by simp)`.
- `Z_to_bv 64 (bv_unsigned w) = w` is not reached by `rw [ofInt_toNat]` on the
  `bv_unsigned` spelling; wrap it.
- **A structure literal's continuation lines must be indented to at least the
  first field's column.** `Lean.Parser.Term.structInst` uses `sepByIndent`, so
  `exact { a := 1,\n    b := 2, c := 3 }` stops after the fields already
  accepted and reports "unexpected identifier; expected '}'" plus
  "Fields missing: …". Reproducible with a bare three-field `structure`. Either
  keep the literal on one line or align every continuation to the first field.
  This is a general toolchain trap, not specific to any proof.
- Passing a **tactic block as an argument** to a large lemma
  (`(by rw [h]; exact H)`) can stack-overflow; pre-prove the premises as `have`s
  and pass the names.
- `rw [e]` where `e` relates two `vis … model` terms fails with "motive is not
  type correct" (the enclosing `if`'s `Decidable` instance depends on the
  rewritten term) — `simp only [e]` works.
- `cases h : e` on a `Bool` substitutes in the **goal** but not in the
  hypotheses, so the equation you `obtain` may no longer match the goal.
- `if (3 : Int) = 0` does not reduce definitionally — `rw [ite_eq_right (by decide : ¬((3:Int) = 0))]`.
- **A large local context makes elaboration flaky, not just `omega` slow.** In a
  node theorem carrying many hypotheses, `rw`/`congrArg`/`Eq.mp`/`simpa` on
  `bv_unsigned (edenot E ne) ↦ page_round_up_Z …` conversions intermittently hit
  `maxRecDepth` (1,000,000) or **abort the file with exit 134 while swallowing
  printed errors**. `clear`-ing unused hypotheses only moves the failure.
  **The reliable cure is structural: prove big sub-parts as standalone lemmas
  with a narrow context and apply them.** A 488-line destroyed-child lemma proved
  in isolation in ~1 s, where the same steps inside the node theorem were
  unusable. When elaboration becomes flaky, factor out a lemma — do not tune the
  context.
- **Do NOT write a `match` on a section variable inside a `have`'s type.** It
  generalises over every arm-dependent hypothesis (`H12`, `H13`, `HFA`, `Hn`) and
  stops unifying with the equation you have. Introduce a plain `def` that
  pattern-matches (defeq to the `match`) and state the arm-specific equation from
  it. Same root cause as the statement-level `match` trap above.
- **`||` and `&&` bind LOOSER than `=` in this toolchain.** `a || b = true`
  parses as `a || decide (b = true)` — confirmed by
  `#check (fun (a b : Bool) => a || b = true)`. Always parenthesise
  `(A || B) = true`. (Same family as the `!a = !b` trap below.)
- **Lean SKIPS the bullets of a rejected `refine`.** If `refine know_ok_unhide …`
  fails to apply, the three `·` bullets that follow are silently skipped rather
  than reported — so a block can *look* green while never being checked. This is
  the same shape as the `elab`-drops-goals hazard ((see NOTES)): a tactic failing leaves
  no textual trace, and here it also swallows the sub-proof. Always confirm a
  `refine` actually fired (e.g. by `case`-naming or by checking the goal count)
  before trusting its bullets.
- **`abbrev` constants do NOT expand at elaboration.** `bv_unsigned w`,
  `Z_to_bv n z`, `elenZ`, `uE` are real constants (an `abbrev` is a *reducible
  def*, not a macro), so `rw`/`omega` distinguish `bv_unsigned x` from
  `↑x.toNat` even though they are definitionally equal. **State every helper
  `have` in the spelling the goal uses, and switch with `show`.** Goals produced
  by lemmas from *other* files often print in the opposite spelling — hence a
  `show` before each `rw`. One agent measured this as ~80% of its debugging time.
- **`generalize` yields a PROPOSITIONAL equality, not a definitional one**, so
  `omega`'s atoms split, and a `let b := …` abbreviation cannot be
  reproduced by it. Spell the definitional term out instead.
- **`by decide` fails with "free variables" on `is_fog`/`is_hole` of a concrete
  `AM … .KRW`** — `by rfl` works.
- `rw [h, h]` **errors on the second pass** when the first removes every
  occurrence; one `rw [h]` rewrites all occurrences.
- `rw [HC.co_limit]` / `rw [Un]` cannot see through a `def` — ascribe a `have`
  in the goal's own spelling first, then `rw` that.
- **`++` on `List` is LEFT-associative, unlike the original's `app`.** `a ++ b ++ c` is
  `(a ++ b) ++ c`, so `List.mem_append.mp` splits off the **last** chunk first.
  This matters for every `Forall_app` port with three or more chunks (the original's
  `app` associates right in the notation readers expect). Check associativity
  before porting a `Forall_app` chain, not after.
- **`rcases h with h1 | h2 | h3` can die on a `List.Mem` disjunct** — if the
  third hypothesis is `x ∈ (k.map …).flatten`, `rcases`'s internal `cases` fails
  with "Dependent elimination failed … at case List.Mem.head". Bind it instead:
  `have hsp := List.mem_append.mp hKe`, and use
  `have hKe' : Ke = <entry> := by simpa using hKe` rather than
  `mem_singleton` + `subst`.
- **A `match args with | [.ELit K], … | _,_,_,_,_ => none` tree is stuck on the
  *expr* discriminator, not the list shape** — `cases ha : a` must come before
  `cases hr : rest`, or the cons case never reduces.
- `↑(4 * k)` and `4 * ↑(k)` are different terms; state and prove
  `((4 * k : Nat) : Int) = 4 * (nn - i)` via `Int.natCast_mul` +
  `Int.toNat_of_nonneg`. There is no `norm_num`/`ring` — core Lean only.
- `Z_to_bv5_ten` is in the `(10 : Int)` spelling and does **not** match `↑10`;
  `show getr regs' (Z_to_bv 5 (10 : Int)) = …` first. `ridx (10 : reg) = 10` is
  not `rfl` — `by decide` closes it.
- **A unification-side stack overflow exits with code 134 *and swallows
  already-printed errors*** — so a run whose output looks green can be an
  illusion. Observed when passing `GM.2 x hx` with `hx` spelled
  `nZ = page_round_up_Z …` against a bounds hypothesis spelled
  `bv_unsigned (Z_to_bv 64 nZ)`: the two are equal, the check still overflows.
  Fix: `have hx' := hx; rw [← Un] at hx'` and pass `hx'` (`simp only [← Un]`
  loops, because `nZ` occurs inside `Z_to_bv 64 nZ`). **This is the strongest
  argument for checking exit codes rather than reading output** — (see NOTES) has the
  matching hazard for stale oleans, and both produce a false green.
- `vis_add_slice_ok` (not `vis_add_sound` + `know_ok_unhide`) is the entry point
  for fixed-hint visible arms: it is stated for exactly the
  `.KWr (SA b off) ne :: .KZero (SA b off) ne :: kn cs1` shape and takes a
  four-conjunct `NEW`. Reading a landed lemma's *premise shape* (§ above) pays
  off repeatedly.
- **`split at H` is breadth-first over *every* `ite` in the hypothesis**, not
  just the outermost one. On a nested guard such as
  `match (if off_image_x … then some k else match dst with …)`, `split` also
  splits the residue of already-eliminated `!(…)` guards, so the bullets get
  consumed by junk `hk : false = true` goals. Peel the components explicitly
  with `cases h : …` instead, and in junk arms use full `simp at H` — note
  `simp only [] at H` **errors** ("simp made no progress") when `H` is already
  fully reduced.
- **A "reusable" lemma can be shape-specific in a way that matters.** |
  `grant_vis_add` looked like a drop-in replacement for
  `vis_add_sound'` + `know_ok_unhide'`, but its `vis_add` premise **hardcodes**
  `[KWr (SA base 0) ne, KZero (SA base 0) ne]`, whereas `mmap_fixed_grant`
  builds `[KWr (SA b off) ne, KZero (SA b off) ne]` with
  `split_lit (reg cs 10) = (b, off)`. Those are **not interchangeable** —
  `vis_add`'s guard is syntactic — so the fixed-hint arms must use the same
  route instead. Before reusing a landed lemma as a shortcut, read its
  *premise's* spelling, not just its conclusion.
- **`omega` can STACK-OVERFLOW and abort the whole file** — not merely fail.
  With `% 4096`-style hypotheses in context (as in `slice_args`), `omega` aborts
  elaboration entirely rather than reporting a goal. Every arithmetic step in
  that neighbourhood must be done by hand: `Int.le_trans`,
  `Int.add_le_add_left`, `Int.lt_of_le_of_lt`. Some `simpa` calls blow up the
  same way. This is the most severe form of the poisoning problem in (see NOTES) —
  the others cost a round, this one loses the file.
- **A `match` written directly in a theorem *statement* is generalized over every
  hypothesis whose type mentions the scrutinee** — it becomes
  `match s, SH, Hbudget with …` and then fails to be defeq to the plain match.
  Introduce a `def` for it instead (this is the `have`-opacity hazard in another
  guise, and it is why `AsanNodesMmLib` gained `slMaps`). Inside a *proof*,
  `cases s` first and compute afterwards; `subst s` / `rw [Hs] at *` produce the
  generalized match and then nothing reduces.
- **`Bool.or_eq_true` / `Bool.and_eq_true` are Prop *equalities*, not `↔`** — use
  `rw [Bool.or_eq_true] at h`, not `.mp`. `Bool.not_eq_true` is the ¬-version;
  the `!`-version is `Bool.not_eq_true'`.
- `List.mem_of_mem_filter` and `List.Nodup.filter` do not exist — use
  `(List.mem_filter.mp h).1` and `List.Sublist.nodup List.filter_sublist h`.
- `cases h : f x` substitutes in the **goal** but not in other hypotheses — follow
  with `rw [h] at <the hyp>`.
- **Passing a hypothesis by NAME into a big lemma can cost minutes of `whnf`,
  where passing it as a tactic costs nothing.** With `Hknew : know_ok … knew` fed
  directly to `grant_cs1_ok`, elaboration spent >10 min in `isDefEq` on the two
  `know_ok`/`ite`/`flatMap` terms — *even though the two applications were
  syntactically identical*. Passing `(by intro K HK; exact Hknew K HK)` instead
  drives unification goal-first and brought the whole file back to **5.9 s**
  from >10 min. When an elaboration hangs on an argument of that shape, replace
  the term with its tactic form before trying anything else.
- **Hardcoding a value can break defeq.** `fixed_cs1`'s shadow
  list is `[AM (reg cs 10) ne kd]`; `shadow_facts_new_ok` states its
  result for `KRWLAZY`. Passing `[… ne KRWLAZY]` as `grant_cs1_ok`'s knowledge
  is **not** defeq (the `if` condition is stuck on `kd`), so the final `exact`
  fails. State it with `kd` and `subst kd` inside the `KRWLAZY` branch before
  calling the shape-adapted lemma.
- **A `have`-bound VALUE is completely opaque to elaboration.** `have x : Nat :=
  f 3` followed by `have hx : P x := h` fails with "h has type `P (f 3)` but
  expected `P x`", and **even `rfl : x = f 3` fails**. Only a real `def`
  unfolds. So `let E' := …` / `let base := …` abbreviations cannot be
  rendered as `have`s — they must become top-level `def`s (this is why
  `AsanNodesMmLib` gained `mmEnv` and `mmBase`). Note this is the *opposite* of
  the `let`-in-a-*definition* case, where `omega` treats a `let`-bound variable
  as opaque but `dsimp only` zeta-reduces it.
- **`obtain` DOES zeta-reduce a lemma's `let` prefix** (e.g.
  `mmap_len_sound`'s `let len := page_round_up_Z …`), so the facts arrive in the
  unfolded spelling — a caller's equation for that quantity must match that
  spelling, not a `let`-introduced name.
- **`min` + `%` in one `omega` context defeats it.** Rewrite `Int.min_eq_left/right`
  into **both** the hypothesis and the goal, and `clear` the `%` /
  `page_round_up_Z` hypotheses first.
- `List.mem_append.mp HK` works where `rw [List.mem_append] at HK` cannot see
  through `HAppend`.
- `split at HK` on a `match m.am_base with | .ELit _ => [] | mb => …` yields
  exactly two goals while **keeping** `m.am_base` in the singleton — so a
  nine-constructor `cases` and its dependent elimination are both avoidable.
- **`subst` on a state variable inlines the successor term into every statement
  about it.** In `node_munmap_sound` the successor is an ~8-line `ACS …`
  literal; with two statements about `cs'` in the *shared* context, elaboration
  went from 6 s to **2 m 28 s** and hit "4,000,000 heartbeats exceeded" inside a
  field that had compiled fine before. Keep successor-sized `have`s **out of the
  shared context**, or better: `generalize` the successor's big fields (the
  `foldl`, the `a_maps` filter) **before** the `subst`, so every downstream
  statement stays small. This is a performance wall, not a correctness one, and
  it is silent until it times out.
- **`!a = !b` does NOT parse as `(Bool.not a) = (Bool.not b)`** — `!` binds
  looser than `=`, so it becomes `!(a = b)`, a `Not`. This bites in *goals*, not
  just hypothesis types. Write `Bool.not` explicitly.
- **`(u64_range x).1` is `0 ≤ ↑x.toNat`, a different `omega` atom from
  `0 ≤ bv_unsigned x`** — re-ascribe it (`have h : 0 ≤ bv_unsigned x :=
  (u64_range x).1`) or `omega` fails.
- The successor's `cs_ok` projections **do** reduce (`(ACS …).a_maps` is the
  filter), but only at `exact`/`show` transparency — `rw` will not see through
  them. Use `show`/`change`.
- **A projection of a `let`-bound literal is defeq but does not reduce** for
  `omega`/`simp` — only `rfl`/`exact` see through it. Recipe: `change` the goal
  to the `let`, then state the component equations with `:= rfl`
  (`have Ha_totsz : cs1.a_totsz = cs.a_totsz + nhi := rfl`) and rewrite with
  them before any arithmetic.
- **`if eager then … else …` on a `Bool` displays as `if eager = true then …`**;
  `dsimp only` refuses to reduce it (and *errors* "made no progress" here) while
  `omega` treats it as opaque. `cases eager`, then
  `rw [ite_eq_left (rfl : (true:Bool) = true)]` /
  `rw [ite_eq_right (by decide : ¬((false:Bool) = true))]` on **both** the goal and
  any `(!eager)` appearing in a hypothesis.
- **An implication hypothesis (`Hbudget : eager = true → …`) is invisible to
  `omega`** — `have hb := Hbudget rfl` inside the branch is required.
- **`Int.lt_of_lt_of_le`'s implicit `c` is inferred from the SECOND argument**,
  so nested applications pick the wrong `c`; split into two `have`s.

### ### 5.10 Interpreted vs compiled reduction — a hard limit on `vm_compute` ports

Coq's `vm_compute` is a **compiled** evaluator; Lean's `decide`/`rfl` reduce in
the **kernel interpreter**. For most goals the difference is invisible, but it
is decisive when a computation is super-linear in the data.

Observed: `Checks/Cases/Prelude.v`'s `every_byte_of_the_entry_page_is_mapped`
asks for a `forallb` over the 3,880-element `entry_slack_len`, each element
doing a `stack_to_mem` walk to its own index — roughly **7.5 million kernel
steps**. It does not finish in any sane heartbeat budget, and it is deferred for
that reason alone. Every other check in that 857-line file (all 16-byte
AT_RANDOM/auxv read-backs, entry-page ends, hwcap, refutations) closes by
`decide`/`rfl` in ~2 s total.

`native_decide` would close it but adds a postulate, which this project forbids
(§2.0's guarantees). So the honest options are: defer the individual check with
its statement quoted, or restructure it into per-byte lemmas with a proved
indexing argument.

**Practical rule for the `Checks/Cases/` tree**: expect `decide`-provable
examples everywhere *except* where a `forallb`/`existsb` ranges over a whole
page — those need the restructuring treatment, not a bigger heartbeat budget.

### ### 5.11 Do not run `lake build` while another agent is verifying

`lake env lean` can fail with "object file … does not exist" when a concurrent
`lake build` is rewriting `.lake/build/lib/lean`. These are **transient and not
source errors** (the same layer as the (see NOTES) olean-shadowing hazard). If a file
that compiled a minute ago suddenly reports a missing dependency olean, re-run
it before treating it as a regression — and if you must build, do it when no
other agent is verifying.

### ### 5.14 Three more macro/tactic traps (v4.31.0)

- **A `(tactic| …)` quotation parses exactly ONE tactic.** `(tactic|⏎ tac1⏎ tac2)`
  is a parse error ("unexpected identifier; expected ')'"). Multi-tactic macro
  bodies must be parenthesised and `;`-separated: `(tactic| (tac1; tac2; tac3))`.
- **`$x` antiquotation does not parse inside a `rw [ … ]` bracket**, but does
  inside a `have h : … := …` type — bind the fact with `have`, then `rw [h]`.
- **`rw [ite_eq_left h]` / `ite_eq_right h` on a `Bool` condition needs `h : c = true`**
  (or `h : ¬(c = true)`), because the `if` is `ite (c = true)`. And `dsimp only`
  *errors* on "made no progress", so a uniform macro cannot carry unconditional
  `dsimp`s.

#### `Checks/ProcessCreation.v` — 71 of 71, COMPLETE

`Checks/ProcessCreation.lean` landed with **51 of 71 proved**. The names that
the declarations this tree provides are:
`clone_sharing_bits`, `clone_sharing_flags_unmodeled`,
`prctl_modeled_options_are` (which is `rfl`: this tree's list is literally
`[PR_CAPBSET_READ]`), `prctl_option_unmodeled`,
`prctl_tagged_addr_ctrl_unmodeled`, `ptrace_unmodeled`,
`setrlimit_unmodeled`, `getrlimit_unmodeled`, `execve_unmodeled`,
`execveat_unmodeled`, plus the three full per-number characterizations
(`clone_is_clone_spec`, `clone3_is_clone3_spec`, `setsid_is_setsid_spec`) and
the run-section lemmas (`unmodeled_at_syscall`, `reaches_unmodeled_syscall`,
`execve_refutes_coverage`).

**The 20 that were hypotheses are now proved.**  The route was not a
hand-inversion of `alt`/`choose`: the `Ok`-inversion already existed as
`Checks/Sys/Kernel/Fork.lean`'s `check_clone_resolve_complete_ok` (and siblings),
so the work was **unpacking a checker-completeness lemma**, not building a chain
walk.  `check_clone_answer`'s `if errno_ret_in … else if clone_pid_ok_b …` *is*
the `alt` collapsed to a function of the return, which is why `choose` never had
to be inverted by hand.  Same shape for `clone3_spec` and `wait4`.

**General lesson**: before writing a staged evaluator for a relational spec, check
whether a `*_complete_ok` / `*_complete_unmodeled` lemma already states the
inversion you want at the checker layer.  In this tree that is where the
inversion usually lives.
 instead" is now true of a landed file, but each `Common/` file's own
statement is still best cited by its local restatement — `DispatchCompute`
supplies only the checker-side twin.

### ### 5.15 `cbn` does not exist here — and every deferred the original block uses it

**`cbn` is Mathlib's, not Lean core's.** Core `Lean`/`Std` has no `cbn` tactic, so a
transcribed `cbn [a b c]` fails as an unknown tactic. The translation is

    cbn [a b c]   ->   simp only [a, b, c]        (COMMAS, not spaces)

This silently cost a compile round on `Checks/Omni.lean`. It matters beyond one
file because **every deferred the original block in this tree quotes proof scripts**, and
most of them contain `cbn` — so an agent picking up a deferral inherits a script
that will not run as written even after the statement is fixed.

### ### 5.16 Two facts about `cases` on `sstep`, and a ready-made inversion

- **`cases` at a LITERAL config binds fewer names than at `⟨ms, model⟩`**: the
  config's fields are indices, so `| syscall ms model x8 …` shifts and later
  names become "unknown identifier". State the inversion over variables instead.
- **`Common/LibWritev.lean`'s `sstep_svc_inv`** is a ready checker-phrased
  inversion of a syscall transition (three `CheckOk` shapes plus
  `CheckUnmodeled`). Use it rather than re-deriving; it is what closed
  `Omni.wloop_syscall_only`.

**The reusable staged-evaluator stack** for spec-side `Ok` inversion at a
concrete input (an `inv_ok` analogue at one input, *not* a general tactic):

1. `Checks.Sys.DispatchCompute.check_syscall_<name>` — checker to `check_<arm>`;
2. `Checks.ExecutableSpecs.check_syscall_ok_iff` / `check_syscall_complete_ok` /
   `check_syscall_complete_unmodeled` — checker to and from `syscall_spec`;
3. per-arm walk: `simp [check_<arm>, <by-decide guard facts>]` leaves the
   claimed-effect test, then `cases eff` + `split` reads it.

`Omni.check_write_wloop_walk` / `_inv` is a 40-line worked template of the whole
thing. This is the route for `ProcessCreation`'s 20 `Ok`-inversion deferrals.

**Concrete instruction steps under `with_mem`**: `simp only [RiscvSemantics.step,
step_accesses, with_mem_ms_pc]; rfl` — packaged as `Omni`'s `istep` macro plus
the `with_mem_ms_pc` lemma. `by decide` cannot do these: `machine_state` has no
`DecidableEq`, and `decide` needs a CLOSED goal (no free `mem`).

### ### 5.17 The frame-tactic: what worked, and two things I had wrong

`Checks/VmMapsDisjoint.lean` closed **44 of 77** `check_*_frame` lemmas with one
section-local `macro vm_frame`:

1. `obtain ⟨r, ws, zs, us, cs, ci⟩ := eff` — destruct `eff` **first**;
2. `cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci` — 32 shapes,
   which is what the original's `destruct ws as [|? ?]` chain does;
3. `all_goals (repeat' (first | cases H; rfl | cases H | split at H |
   simp only [checker, helpers] at H | (simp only [m_vmmaps]; rfl)))` —
   a `repeat` over the same step. `simp only`/`split` double as the progress test
   because both refuse no-ops.

Pass the **transitive closure** of the checker's own helper names, not the whole
tree — handing all 67 to every lemma costs more than it saves.

**Two corrections to the earlier brief, both measured:**

- **`split at *` / `split at H` does NOT reproduce "Missing cases: _" on
  v4.31.0.** It *succeeds* on `check_munmap`/`check_getcwd` — generalising
  `eff` and casing the wildcard — and the damage shows up downstream as goals
  the loop cannot close. The error string was misattributed: the split is not
  refused, it is **unproductive**.
- **`split at H` is still needed in the loop**, but for the checker's
  *model-state* dispatch (`fd_lookup`, `m_stdin`, `read_bytes_map`) rather than
  for the `eff` match.

**The remaining blocker is `private def` helpers.** Five arms
(`ftruncate`, `faccessat`, `faccessat2`, `openat`, `unlinkat`) cannot be framed
because their accepting branch lives in a **private** helper
(`Open.check_ftruncate_file_arm`, `Namei.check_unlinkat_body`, …): a private
helper's equation lemmas are not nameable from another module, so `simp only`
cannot unfold it and the goal never becomes `rfl`. **A private `*_frame` beside
each private `*_sound_ok` — which already unfolds the helper — is the fix**, and
it belongs in `Checks/Sys/Fs/{Open,Namei}.lean`.

The other 28 need `*_frame` lemmas for the *state* helpers so the loop never
splits the wide model-state dispatch: measured, they cost >1,000,000 heartbeats
each (4 min 20 s for 33 at `maxHeartbeats 1000000`, 28 still timing out), so a
larger budget is not the answer.

### ### 5.18 Free variables block kernel reduction — `vm_compute` with a symbolic state does not port

**`vm_compute` with free variables does NOT port to `rfl`/`decide`.** With a
symbolic `sp`, or even with only `ms_mem` abstracted, `RiscvSemantics.step … =
.MachineOk …` is not `rfl`: **a free variable inside the state blocks kernel
reduction of the whole chain.** So a concrete-looking `vm_compute`
whose state still contains a variable cannot be replayed as `decide`.

The fix is to **assemble** the computation instead of reducing it: discharge the
abstract pieces by `rfl` at the point they are concrete, and use the generic
step lemmas (`Verdicts.step_addi_a7`, `step_ecall`, … — all quantified over
`segs` and the state) for the rest. `Checks/Omni.lean`'s `exit0_exits_c` is 30
lines that way and the whole file runs in 0.3 s; as a `decide` it does not
terminate.

### ### 5.19 `obtain rfl` / `subst` in a `cases` branch can kill the OUTER variable

In a `cases hss` branch, `obtain rfl : x8' = x8` or `subst hx` where
`hx : x8' = x8` will sometimes eliminate the **older** `x8` (the one from the
enclosing proof) rather than the branch-local `x8'` — yielding "unknown
identifier x8" and a lost context. Use a **targeted rewrite** instead:
`rw [hx] at hspec`.

Related: passing `_` for an `sstep` constructor argument that unifies with an
outer variable (e.g. `evs` in the `syscall` arm) makes that outer variable
unknown in the branch. **Name it.**

### ### 5.21 `unfold a, b` is a parse error

Lean's `unfold` takes **space-separated** names. `unfold a, b` fails; it is
`unfold a b`. This bites when a transcribed `cbn [a b]` list is converted to
`unfold` rather than to `simp only [a, b]` ((see NOTES)).

### ### 5.24 (see NOTES)'s diagnosis for the 28 "cost" frames was WRONG

(see NOTES) said the remaining `check_*_frame` lemmas needed >1,000,000 heartbeats
because `split at H` walks the wide model-state dispatch. **Measured, that is
false**: `check_read` — `fd_lookup` × `m_stdin` × two `read_bytes_map` trees ×
the socket protocol, the widest dispatch in the file — closes in **1.1 s** with
the plain macro.

What the 24 survivors actually share is a **guard that is a bitvector
computation**: `decide (len.toInt < 0)`, `!(z_ldiff … == 0)`, `!(sint32 domain
== …)`, `!(modeled_access_mode mode)`. To case such an `if`, `split`/`simp` must
**reduce** the guard, and `BitVec.toInt` / `z_land` / `z_ldiff` on a *symbolic*
word do not reduce: `check_socket` burns ~250,000 `Nat.rec` unfoldings into
`maxRecDepth`; others exhaust `maxHeartbeats` in `whnf`.

**And both limits are unrecoverable exceptions — `first` cannot catch them.** So
one such guard aborts the whole proof and no fallback arm can rescue it. That is
why per-helper state frames (the (see NOTES) prescription) could not have helped.

**The route that works is to case the guard as a **Bool**,

    cases h : decide (len.toInt < 0)
    simp only [h, Bool.false_eq_true, ite_true, ite_false] at H

then the ordinary loop. `cases` on a `Bool` term only generalises/splits — it
never reduces. This is exactly `Checks/Sys/Net/Socket/Socket.lean`'s
`check_socket_sound_ok` idiom. `check_ftruncate_frame` is the worked template.

**Dead end recorded**: a generic meta-tactic (`vm_guard`) that finds the `Bool`
guard in a hypothesis and cases it. Reading a hypothesis's type via
`(← getLCtx).findFromUserName?` sees the **pre-`unfold`** type (use
`withMainContext` + `getFVarFromUserName` + `inferType`); and once fixed, the
meta route took **>600 s on one effect shape** versus 3.4 s for the hand walk.
Do not re-attempt it without a much better reason.

**General lesson**: `first`-based tactic chains are the wrong tool when a
sub-tactic can die on an *unrecoverable* limit rather than fail. Reach for
`cases h : <the guard>` — a `cases` that generalises cannot blow a budget.

### ### 5.25 The THIRD obstacle: `split` generalises a copy-in wrapper's stuck `match`

(see NOTES)'s `cases h : <Bool guard>` route is necessary but not sufficient. Nine
of the 24 `VmMapsDisjoint` frames moved this session, and six of them
(`getsockopt`, `newfstatat`, `writev`, `pwrite64`, `prlimit64`,
`sched_setscheduler`) were blocked by something else:

> `check_ret_only`, `check_ret_only_copyins`, `check_write_oset_copyins`
> and friends end in
> `match check_ret_only (clear_copyins eff) r mm evs0 with | .CheckOk m'' evs' => … | result => result`.
> Once `simp only [check_X, <helpers>] at H` has unfolded the wrapper, the
> `match` scrutinee is `if bv_eqb ret r` — undecidable — so the loop's next
> `split at H` **generalises it**: it introduces `x✝ : check_result` plus
> `heq✝`, and the hypothesis `H` the loop names is GONE. `repeat'` then
> stops and the goal is unreachable. It is the failure mode `openat` already
> had recorded for `check_copyins_after`, one layer up.

The fix is a THIRD loop, `vm_frame_m` (in the file, next to `vm_frame` /
`vm_close`), which keeps those wrappers OUT of the `simp only` list and
closes the terminal call with the `*_model` inversions that are already in
the file (`check_ret_only_model`, `check_ret_only_copyins_model`,
`check_copyins_model`, `check_copyin_prefix_model`,
`check_copyins_after_model`): `rw [<lemma> … H]` replaces `m'` by the model
the wrapper hands back, and `rfl` then closes `m_vmmaps (with_fds …) =
m_vmmaps m`, because a projection of a structure update reduces
definitionally. `rfl` is also an explicit loop arm so a goal that has become
reflexive closes at once.

Two more findings worth carrying forward:

* `rt_sigprocmask` is not a `vm_frame` arm at all: it CHANGES the model
  (`with_sigmask`, and `with_killed` over it), so `Checks/Sys/Kernel/Signal.lean`
  proves `check_rt_sigprocmask_frame` beside the checker. The DEFERRED entry
  in `VmMapsDisjoint` was stale; that arm is now one line that cites it.
* `setresuid`/`setresgid` share `check_setresid`, so one
  `check_setresid_frame` (not `check_setresgid_frame`) is the name the audit
  looks for; it covers both arms.

**Still deferred (15, after 62 of the 77 frames):** `bind clock_gettime connect getdents64 getgroups
madvise nanosleep openat readv sendmsg sendto setsockopt sigaltstack socket
write`. `readv` and `sendmsg` additionally need a PUBLIC
`check_readv_imported_frame` (in `Checks/Sys/Fs/ReadWrite.lean`) and
`check_send_on_socket_frame` (in `Checks/Sys/Net/Socket.lean`), beside the
existing `*_sound_ok` proofs there — the `Open.lean`/`Namei.lean`
precedent. The rest are the `decide (sint32 … )` / `z_ldiff` guards of
(see NOTES), one written-out `cases h : <guard>` per gate.

**Measurement warning.** `lake env lean probe.lean` with a probe that does
`import …VmMapsDisjoint` loads the OLEAN, not the source. While the file
under edit is red, or has not been re-`lake build`-ed, such a probe silently
sees an older `VmMapsDisjoint` (one probe here failed with "unknown tactic"
for a macro that was in the source and not in the olean, and an earlier
batch of "passing" probes had in fact never run the loop). Either probe in a
file that copies the `*_model` helper lemmas it needs, or verify inside the
real file. This is the (see NOTES) hazard in a new place.

### ### 5.26 Four more frame-tactic facts (each cost a round)

1. **`split at H` REFUSES a descriptor dispatch on nested constructor patterns**
   (`none`, `some (.FdChannel _)`, …, `some .FdDir`) with `Missing cases: _`, and
   leaves `H` untouched. Use
   `generalize hq : fd_lookup (m_fds m) fd = q at H`, then `cases q`, then `cases e`.
2. **`exact nomatch H` on a stuck `if … = .CheckOk …` emits `Missing cases: _`,
   which is NOT backtrackable** — so one such arm aborts a whole `first` chain,
   including the alternative that would have worked. `contradiction` fails
   *cleanly* on the `if` and closes the `CheckReject = CheckOk` leaves. Use it.
3. **After `unfold check_X at H` the iota step is NOT done** (`match none with …`
   stays in `H`). `dsimp only at H` performs it — and must be `try`-guarded,
   because in the `none`/single-arm branches there is nothing to reduce and it
   errors.
4. **A six-way SIMULTANEOUS `match` on options** (sendmsg's `read_u64` `msghdr`
   import) **has no `split`**: each of the six scrutinees must be `generalize`d and
   `cases`d (64 leaves), and the live leaf's guards name the bound fields, so the
   `cases` must use named `some x` patterns — `cases … <;>` leaves them as
   `val✝³`.

Also confirmed: `simp only [check_ret_only] at H` **while `H` still holds the
11-arm descriptor match** is what burns `maxRecDepth`. Dispatch the descriptor
FIRST, then it is instant.

### ### 5.27 The three obstacles are finally separated

`Checks/VmMapsDisjoint.lean`'s frame half hit three *distinct* walls, and each
needs its own tool. Conflating them cost several rounds:

| wall | symptom | tool |
| --- | --- | --- |
| bitvector guard must reduce | `maxHeartbeats`/`maxRecDepth` in `whnf` on a symbolic `BitVec.toInt`/`z_land`/`z_ldiff` | `cases h : decide (guard)` + `simp only [h, …]` — `cases` generalises, never reduces ((see NOTES)) |
| wrapper `match` on an undecidable scrutinee | `split at H` generalises and **destroys `H`**, leaving `repeat'` on an unreachable goal | keep wrappers out of the simp set; close with the `*_model` inversion + `rfl` (`vm_frame_m`, (see NOTES)) |
| private helper unnameable across modules — **only a private `DEF`**, not a private `ABBREV` | `simp only` cannot unfold a private `def`'s accepting branch. A private **`abbrev` is transparent**, so writing the gate as its public body lets `by_cases` + `rw [ite_eq_left]` unify through the defeq and find the occurrence from another module | a **public** `*_frame` beside the private `*_sound_ok` ((see NOTES)) — but for an `abbrev`, nothing is needed |
| **chained `rw [ite_eq_left h] at H` builds a motive too deep** | the tactics finish in 0.04 s and then the **KERNEL** reports "(kernel) deep recursion detected" — after 108 s of work | state the terminal `if` as its **own lemma** with `p` a Prop *variable*, where `split at H` is cheap |

### ### 5.28 Splitting a slow module: what works, and the hard floor

`Checks/VmMapsDisjoint.lean` took **92.8 s** to check as one file, so every edit
cost 93 s. It was split into ten modules (`Tactics`, `Frames`, `Frames/Wide`,
`CostlyA`–`CostlyF`, plus the aggregator). Measured result:

| | before | after |
| --- | ---: | ---: |
| cold parallel `lake build` (all ten) | 92.8 s | **47.6 s** |
| edit a cheap arm | 94.3 s | **28.1 s** |
| edit PART 1/2 | 94.3 s | **10.7 s** |
| warm `lake build` | 0.26 s | 0.16 s |

**The mechanism is per-module parallelism, not smaller files.** Lean elaborates a
module as a unit and lake parallelises *across* modules; on 16 cores the five
expensive arms then build concurrently. Total elaboration work is unchanged
(~391 s CPU).

**Two hard limits, both measured:**

- **The box saturates at ~8.2 effective cores** — each `lean` process is itself
  multi-threaded, so "16 modules in parallel" is not 16× throughput.
- **The floor is the largest SINGLE declaration.** `writev` (32 s) and `prlimit64`
  (32 s) are single proofs; no module split can divide one declaration. 47.6 s ≈
  (contending max module 37 s) + (aggregator 8.4 s).

So the realistic gain from splitting is **~2×**, not the module count. Plan for
that.

**Split by COST, not by size.** The 70 arms were: five expensive (12–28 s), five
middling (22–24 s as a module), sixty cheap (~1 s). Putting the cheap sixty in one
module and each expensive arm in its own is what produced the numbers above.
Merging `writev`+`pwrite64` into one module would exceed 45 s and *raise* the wall.

**The shim was then done, and it paid.** The aggregator was made a pure import
shim with the elaborated body in `VmMapsDisjoint/Core.lean` (563 lines of imports
+ comments, 0 declarations):

| measurement | before shim | after shim |
| --- | ---: | ---: |
| `lake env lean` aggregator | 8.8–9.0 s | **0.25–0.28 s** |
| cheap-arm edit → full build | 28.6–31.3 s | **19.4–20.5 s** |
| PART 1/2 edit → full build | 10.7 s | 10.3–11.2 s (unchanged) |
| wide arm edit | 34.8 s | 25.6–27.9 s |
| expensive arm edit | 43.0 s | 32.9–36.5 s |
| cold parallel build | 51.0–53.2 s | **41.3–46.0 s** |

The ~9 s win is exactly the old aggregator cost, now off the critical path — and
the **cold** build also improved, because `Core` now elaborates concurrently with
the frame modules instead of after them. Making the aggregator a shim is worth
doing whenever a long-lived module imports a fan-out.

**The lesson underneath both splits**: a build-latency fix has two separable parts
— *split the work* (parallelism) and *get the long pole off the edit path*
(the shim). The first bought 2×; the second bought another 1.5× on the common
edit.

### ### 5.29 A macro quotation resolves identifiers at MACRO-DEFINITION time

Splitting exposed this, and it failed **silently**:

`bvnorm` — a macro whose body is a `dsimp only [bv_unsigned, vm_wf, …]` — could
not move to the **`Tactics`** module (it lives in `Core`, below them), because a macro quotation resolves its
identifiers **at the macro's definition site**. In `Tactics` the names did not
exist, became `bv_unsigned✝` / `vm_wf✝`, and **`try` swallowed the failure** →
a silent no-op → 24 downstream `omega` failures with no error at the macro.

After the shim, `bvnorm` lives in `Core` at line 521 — **after** `bv_unsigned`
(85) and `vm_wf` (437), same namespace. It was verified rather than assumed: a
positive probe (an `omega` goal needing the normalisation) closes, and a negative
control — a copy of `Core` with `bvnorm`'s body replaced by `skip` — gives **22
errors**, essentially all `omega` failures. So the macro is load-bearing, and the
silent-no-op mode would reproduce exactly there.

Two lessons:
- **A macro can only see what is in scope where it is DEFINED**, not where it is
  used. Moving a macro above the declarations it names breaks it.
- **`try` around a macro invocation converts a hard failure into a silent no-op.**
  The same shape as (see NOTES)'s `first` and (see NOTES)'s `nomatch`: `try`/`first` are only
  safe when the wrapped tactic fails *cleanly and detectably*.

#### What the kernel-depth wall actually tracks

`bind` and `connect` remain, and seven attempts were measured against them:

| attempt | result |
| --- | --- |
| `by_cases h : <guard> = true` + `rw [ite_eq_left]` (the (see NOTES) route) | closes, kernel wall |
| generic peel lemma `(if p then a else b) = .CheckOk → a = … ∨ b = …` (`split` is cheap in the lemma: `p` is a variable) | closes, kernel wall |
| `cases h : decide (…)` (the `ftruncate` idiom) | `maxRecDepth` **during elaboration** — generalising a two-`decide` disjunction inside `H` is itself expensive |
| `generalize hal : sint32 addrlen = al at H` | guards opaque as intended, **wall unchanged** |
| factoring the whole `FdSocket` arm body into its own lemma | the **factored** lemma still hits the wall, so **`H`-size alone is not the trigger** |
| factoring the innermost `check_errno_or_success` acceptance | no change |
| substituting `connect`'s `copied` `let`-`if` by hand | wall remains — so the recorded "`sint32` through the `reads` argument" diagnosis is **wrong** |

**Diagnostic that bounds it**: a synthetic `H` with the same two `Int`-comparison
disjunctions plus an equality closes in 0.33 s, so the **guard shape is fine**.
The wall tracks **(size of `H`) × (number of nested `if`-rewrites)**.

**Suggested route for the next session**: split each arm's guard chain into 2–3
**tail lemmas**, each with its own transcribed sub-body, so that no single proof
term carries more than ~2 nested `if`-rewrites over a large hypothesis. Or give
`check_bind` / `check_connect`'s socket arm a named `def` in `Socket.lean` (a
semantic no-op) so its frame's hypothesis is one compact application.

### ### 5.30 The FOURTH wall: kernel deep recursion from chained `ite_eq_left`

`clock_gettime` and `nanosleep` could not use (see NOTES)'s `cases h : <guard> = true` +
`rw [ite_eq_left h] at H` recipe. It **closes every goal and then dies in the kernel**.

Measured, and the measurements matter because they rule out the obvious fixes:

| observation | value |
| --- | --- |
| `check_clock_gettime` with the guards cased at the call site | **108 s**, then `(kernel) deep recursion detected` |
| same, with one guard leaf replaced by `skip` | **0.35 s** |
| the tactics themselves (`set_option profiler true`) | **0.04 s** |
| `set_option maxRecDepth 100` | **still the same kernel error** |

So the tactics are instant and the *elaborated term* is the problem: each
`rw [ite_eq_left h] at H` inside the enlarged checker body **builds a motive over the
whole surviving body**, and chained they exceed the kernel's recursion limit.
**`maxRecDepth` does not reach the kernel's limit**, so raising the budget is not
a route — this is a different budget from (see NOTES)'s.

**The fix**: state the terminal `if` as its own lemma —

    theorem <name> (p : Prop) [Decidable p] (k : check_result) (m' : Model) (evs : List event)
        (H : (if p then .CheckOk k evs else .CheckReject) = .CheckOk m' evs) : m' = k

— where **`p` is a VARIABLE of type `Prop`**, so `split at H` is cheap. The arm leaf
then becomes a lemma *application* and the kernel never puts the `if` into a
motive. `check_ok_if_model` / `check_ok_if2_model` are the two instances in
`Frames.lean`.

**This is what also blocks `bind`/`connect`** — their guard chains are longer
(six guards + `fd_lookup` dispatch + `SockState` dispatch), so the same motive
depth is reached.

**Pattern**: the wall moved from tactics ((see NOTES)) to packaging ((see NOTES)) to
visibility ((see NOTES)) to **the kernel's own term depth**. When a proof "closes every
goal and then fails", suspect the *term it elaborated*, not the tactic.

And the meta-lesson from all three: **`first`-based loops are fragile against
tactics that die on unrecoverable limits or emit non-backtrackable errors.**
Whenever a loop arm can fail that way, restructure to an explicit `cases`/`rw`
that cannot.

### ### 5.31 The kernel wall was the `rw`, not the body — (see NOTES) was wrong in its last link

(see NOTES) concluded the wall tracked `(size of H) × (nested if-rewrites)` and suggested
"split into tail lemmas, or give the arm a named `def`". **Both were tried and both
are dead ends.** What the wall actually is:

> **`rw [ite_eq_left h] at H` is the trigger.** `ite_eq_left`/`ite_eq_right` are equations whose
> *statement* embeds **both branches** of the `if`, so every such rewrite copies
> the surviving tail of the checker body into the proof term. Chained once per
> guard, the term's **depth** exceeds the kernel's budget — which `maxRecDepth`
> cannot reach.

That explains why all seven body-factoring attempts failed: **the cost was in the
rewrite's shape, not in what it rewrote.**

**The fix** (and it is not new machinery — it is the checker's own soundness idiom):

```lean
generalize hal : sint32 addrlen = av at H
by_cases hp : <guard> = true
· simp only [hp, ite_true] at H      -- NOT rw [ite_eq_left hp]
```

`simp only [h, ite_true]` rewrites the guard **inside the condition** — a one-hole
motive over the guard rather than over the `if` — and then iota-reduces. Nothing
ever embeds the tail. Measured: `check_bind_frame` **0.4 s**.

**When even that is too big**: `check_connect`'s body is the widest in the module
(10 `FdEntry` × 5 `SockState`), and *every* hypothesis-level transformation of its
**unfolded** body reproduces the wall on its own — zeta (`simp only [] at H`),
`generalize`, and `cases` over the `fd_lookup` dispatch, measured individually at
~31 s each. It is proved with the checker **folded** in `H` (a one-line
application) and each leaf opened by a pre-proved **arm equation** — a one-hole
motive. That is `Connect.lean`'s own design.

**Two negative results worth not repeating:**

- **An external mirror is not defeq-checkable.** `check_bind … = bind_full …` by
  `rfl`, and by `unfold … ; dsimp only ; rfl`, both give the kernel error after
  ~31 s. So `change`-based retyping across that boundary is unavailable.
- **Staged tail lemmas are necessary but not sufficient**: the six stages each
  check in 0.4 s, but crossing from the checker's own body into stage 1 needs the
  same two-sided defeq.

**The rule**: **cross a boundary with a TERM-level equation, never with
definitional equality.**

And the meta-lesson, which is the third time this has bitten: a *measured
characterisation* of a wall ("it tracks X × Y") can still name the wrong
mechanism. (see NOTES)'s correlation was real; the cause was one layer lower.


### ### 5.32 Toolchain v4.35: four walls moved, and one budget changed hands

Bumping `lean-toolchain` from v4.31 to v4.35 broke eighteen modules — three
under `LinuxProcessSem`, twelve under `Common`, three under `Checks`.  Every
failure was one of the following, and each was re-measured on both toolchains at
the site that broke.

**1. The `Int`-comparison divergence spread from `rfl` into `simp`/`rw`.**

The shape is `let u : Int := ((abi_low32 w).toNat : Int); if u < 2 ^ 31 then u
else u - 2 ^ 32` — the old body of `Sys.Syscall.sint32`, and `Int.decLt` on an
`Int.ofNat` of a `BitVec.toNat` cannot be unwound by a unifier ((see NOTES)).
What changed is *who* trips on it:

| goal, `f` the shape above | v4.31 | v4.35 |
| --- | --- | --- |
| `example : f 23 = 23 := by simp [f]` | **closes** | "maximum recursion depth" |
| `example : f 23 = 23 := by rw [f]` | rewrites, leaves the goal | "maximum recursion depth" |

`maxRecDepth` 1e5 does not rescue either — they take 0.9 s and then fail, so
this is a loop, not a budget.  (The `rfl`/kernel form of the same wall, at the
`abi_low32` spelling, is what (see NOTES) already recorded; this is that wall
reaching the *rewrite* machinery.)  **The cure is at the definition**: compare the
`Nat` first —

```lean
def sint32 (w : word) : Int :=
  let n : Nat := (abi_low32 w).toNat
  if n < 2 ^ 31 then (n : Int) else (n : Int) - 2 ^ 32
```

— the same function, and `simp`/`rw`/`rfl` all reach it again, which is what
restored the `Checks/Cases` evaluators (`eval_check`'s third `simp` had simply
stopped making progress).  `StateVm.lazy_interior` and `Sys.Syscall.nfds_signed`
keep the old shape, and pay for it where a projection is peeled through them:
`rfl` on `m_vm_lazy (vm_add_lazy a n m) = …` now dies in the kernel, so
`- m_vm_lazy_vm_add_lazy` goes through the existing
`m_vm_lazy_with_vm_backing` — `unfold vm_add_lazy` then `rw` — which stops at
the projection instead of forcing the `List.append` above the guard.

**2. `rw` elaborates its argument BEFORE it looks for the pattern.**

So `rw [ite_eq_left (by decide)]` / `rw [ite_eq_left (by omega)]` hand the block a
*metavariable* to prove, and `omega`/`rw` inside it answer "did not find an
occurrence of the pattern"; where the block did produce a term, the rewrite
itself can still abort in `simp` with "maximum recursion depth" (that is what
`Kernel/Sys`'s `setresid` check did).  Hoist the fact into a `have` whose
statement is spelled out, and rewrite with the name:

```lean
have hg : (decide (-(2 : Int) ^ 63 ≤ k) && decide (k < (2 : Int) ^ 63)) = true := by
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨h1, h2⟩
refine (ite_eq_left hg).trans ?_
```

Note the second line: even with the guard *named*, `rw [ite_eq_left hg]` fails to
match on v4.35 in several goals (the pattern prints fully instantiated and the
occurrence is plainly there), while `ite_eq_left hg` — or `exact`, or
`(ite_eq_right hg).symm` — unifies the same equation.  Same story for
`rw [e]` where `e` relates two `vis … model` terms: "motive is not type
correct", because the rewritten term sits under an `if`'s instance;
`simp only [e]` does it.

**3. `simp only`/`simpa` rewriting an `ite`'s condition leaves the `Decidable`
instance at the OLD spelling**, and the goal stops type-checking.  v4.35 prints
the mismatch rather than repairing it:

```
Application type mismatch: The argument (2 ^ 63).decLe (k % two64z)
has type Decidable (2 ^ 63 ≤ k % two64z)
but is expected to have type Decidable (2 ^ 63 ≤ k % 2 ^ 64)
```

Three sites, three shapes of the cure, all *"do not rewrite the condition under
the `if`"*: leave the `rfl`-equal abbreviation alone (`snorm_hi`/`snorm_lo` and
`two64z` in `AxSymExec3Sound`); state the lemma's conclusion at the goal's own
spelling (`elen w` rather than `expr.ELit ↑w` in `AxSymExec3B`); or apply the
equation to the guard `Bool` in its own step and `by_cases` on *each* guard, so
each `ite` gets a canonical instance (`sl_MR_out`/`d_MR_out` in
`AsanNodesMmLib`).

**4. `rw` no longer `whnf`s the target.**  A `match` on
`with_copyins … (mkEffect … (rmtp, rem) …)` therefore stays stuck, and the
`bv_eqb rmtp rmtp` the next rewrite wants is not in the goal yet (`simp only
[with_copyins]` performs the unfolding).  Relatedly, `simp`'s closing step can
fail where `rfl`/`exact` succeed: after `simp` normalises a goal to
`if c then 1#64 else 0#64 = if c then 1#64 else 0#64`, the instances are still
two, and `rfl` is what closes it (`Common/PropExec`, `Common/MmapSim`).

**5. The KERNEL's recursion budget now follows `maxRecDepth`.**  v4.31 said
"(kernel) deep recursion detected"; v4.35 appends "use `set_option maxRecDepth
<num>` to increase the limit", and it is true: `Common/AsanPlacement`'s `omega`
proofs over `(w.toNat : Int)` sums are *finite* but deeper than the default
1000, so `set_option maxRecDepth 4096` admits them (1024 is the first value that
works; 4096 is headroom).  On a *divergent* term the same option only buys a
slower failure — the two are not interchangeable, which is why item 1 had to be
fixed at the definition.

**6. The `if_*` family is renamed.**  `if_pos` → `ite_eq_left`, `if_neg` →
`ite_eq_right`, `if_true` → `ite_true`, `if_false` → `ite_false`.  The old names
are deprecated aliases with unchanged statements, so the rename is textual; every
use in the tree now takes the new spelling (10,503 occurrences over 168 files),
and the sections above are written that way too.  The build is warning-free
besides: 28 Prop-valued `def`s became `theorem`s (`linter.defProp`), 7 unused
`simp` arguments removed, and one binder that only `omega` reads renamed `_Hz`.
