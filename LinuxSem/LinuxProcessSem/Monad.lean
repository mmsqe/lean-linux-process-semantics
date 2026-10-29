/-
  * Monad — the non-determinism monad for syscall specs.

  TRUST BOUNDARY: this file is part of the trusted specification.

  A `Sys A` spec is a RELATION: given the syscall's `SyscallInput`
  (read-only) and the current `Model`, it relates them to the set of
  admissible `Outcome`s.  An outcome is either

  - `ok x m' evs` — the syscall may return `x`, leaving the model in `m'`
    and emitting the observable events `evs`; or
  - `unmodeled` — the program did something the model does not cover (an
    unmodeled syscall, an unreadable user buffer, unmodeled flags...).
    `unmodeled` is a POSITIVE outcome, not an empty relation: it drives the
    explicit error transition in `Run.sstep` (fail closed), rather than
    leaving the semantics stuck.

  (Standard input is NOT part of this non-determinism: the bytes stdin
  delivers come from the run's `InputStream` parameter, threaded in the
  model's `m_stdin` field; only HOW MANY of them a given read delivers
  — short reads — is chosen here.)

  Non-determinism is set-valued: `choose P` has one `ok` outcome per value
  satisfying `P`, and `alt` unions two outcome sets.  Specs must be
  RECEPTIVE — every input and model state admits at least one outcome
  (possibly `unmodeled`); this is validated by `Progress.receptive`.  The
  one way to write a non-receptive spec is `choose` with an unsatisfiable
  predicate, so `choose` should always be guarded by an obviously
  inhabited predicate or an `alt`ernative branch.

  The spec GENERATES admissible effects.  It does not take the observed
  result as an input and accept or reject it: that would tie the spec's
  shape to what a particular tester could observe and need erased `Prop`
  side-conditions for memory framing.  The executable acceptor is derived
  separately and verified against this relation (see `ExecutableSpecs.v`).

  ** What kind of monad is this?

  `Sys` is a single monad that stacks five classic effects:

  - READER over `SyscallInput`: `input`, `sysno` and `arg`.
  - STATE over `Model`: `getModel` and `modify`.
  - WRITER over `List Event`: each `ok` carries the events emitted by that
    step; `bind` concatenates them in chronological order.
  - EXCEPTION with a unit payload: the `unmodeled` outcome.  `bind`
    short-circuits on `unmodeled` — no later step runs — and an
    `unmodeled` carries NO model and NO events.
  - NON-DETERMINISM: `Sys A` is set-valued.

  The transformer order is load-bearing: `ExceptT` sits innermost, BELOW
  both `StateT` and `WriterT`, so an `unmodeled` discards the state and the
  events.

  The concrete `Model`, `SyscallInput` and `event` come from `State.lean`.
  This module is PARAMETERIZED by them (`Sys M I E A`), because
  `State.lean` — a 8197-line file with the full fd/VmMaps/fs/net state and
  its rewrite matrix — is the layer below, and a spec should not have to
  name the concrete types.  The construction, the laws and the lemmas are
  identical; instantiating `M := Model`, `I := SyscallInput`,
  `E := event` gives the definition up to the order of the type
  parameters.  `LinuxProcessSem.MonadInstances` is exactly that thin
  module: it fixes the three parameters, so the parameterization is a
  convenience for reuse.

  ** Monad laws

  Because `Sys A` is a RELATION, two specs are "equal" when they relate
  exactly the same outcomes.  We spell that out as `sysEquiv` and prove
  the three monad laws (left identity, right identity, associativity) up
  to it below, so `pure`/`bind` really do form a monad.
-/
import LinuxSem.Riscv.Prelude

namespace LinuxSem.LinuxProcessSem

/-- One admissible outcome of a syscall spec. -/
inductive Outcome (A : Type) (M : Type) (E : Type) : Type where
  /-- May return `x`, leaving the model in `m` and emitting `evs`. -/
  | ok (x : A) (m : M) (evs : List E)
  /-- The model does not cover this call (fail closed). -/
  | unmodeled

/-- The specification monad: a relation from input and model to outcomes. -/
abbrev Sys (M I E A : Type) : Type := I → M → Outcome A M E → Prop

variable {M I E : Type}

/-- The computation that returns `x`, leaves the model alone and emits
    nothing. -/
def pure {A : Type} (x : A) : Sys M I E A := fun _ m o => o = .ok x m []

/-- Sequencing: an `unmodeled` anywhere in the chain is an `unmodeled` of
    the whole program; event lists concatenate in chronological order. -/
def bind {A B : Type} (c : Sys M I E A) (k : A → Sys M I E B) : Sys M I E B :=
  fun i m o =>
    match o with
    | .unmodeled =>
        c i m .unmodeled ∨
        (∃ x m1 evs1, c i m (.ok x m1 evs1) ∧ k x i m1 .unmodeled)
    | .ok y m2 evs =>
        ∃ x m1 evs1 evs2,
          c i m (.ok x m1 evs1) ∧ k x i m1 (.ok y m2 evs2) ∧ evs = evs1 ++ evs2

scoped infixr:100 " >>= " => bind

/-! ### Monad laws

`Sys A` is a relation, so equality of specs is extensional: two specs are
equivalent when they admit exactly the same outcomes for every input and
starting model.  We do not assume functional/propositional extensionality,
so the laws are stated up to this `sysEquiv` rather than Lean's `=`. -/

/-- Extensional equality of specs. -/
def sysEquiv {A : Type} (c1 c2 : Sys M I E A) : Prop :=
  ∀ i m o, c1 i m o ↔ c2 i m o

/-- `sysEquiv` is an equivalence relation (this is what lets us read the
    laws below as genuine equations). -/
theorem sysEquiv_refl {A : Type} (c : Sys M I E A) : sysEquiv c c := by
  intro i m o; rfl

theorem sysEquiv_sym {A : Type} {c1 c2 : Sys M I E A} (h : sysEquiv c1 c2) :
    sysEquiv c2 c1 := by
  intro i m o; exact (h i m o).symm

theorem sysEquiv_trans {A : Type} {c1 c2 c3 : Sys M I E A}
    (h1 : sysEquiv c1 c2) (h2 : sysEquiv c2 c3) : sysEquiv c1 c3 := by
  intro i m o; exact (h1 i m o).trans (h2 i m o)

/-- Left identity: `pure` is a left unit for `bind`. -/
theorem bind_pure_l {A B : Type} (a : A) (k : A → Sys M I E B) :
    sysEquiv (bind (pure a) k) (k a) := by
  intro i m o
  cases o with
  | ok x m' evs =>
      simp only [bind, pure]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [Outcome.ok.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp at h3
        subst h3
        exact h2
      · intro h
        exact ⟨a, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
      simp only [bind, pure]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact absurd h (by simp)
        · simp only [Outcome.ok.injEq] at h1
          obtain ⟨rfl, rfl, rfl⟩ := h1
          exact h2
      · intro h
        exact Or.inr ⟨a, m, [], rfl, h⟩

/-- Right identity: `pure` is a right unit for `bind`. -/
theorem bind_pure_r {A : Type} (c : Sys M I E A) : sysEquiv (bind c pure) c := by
  intro i m o
  cases o with
  | ok x m' evs =>
      simp only [bind, pure]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [Outcome.ok.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        simp only [List.append_nil] at h3
        subst h3
        exact h1
      · intro h
        exact ⟨x, m', evs, [], h, rfl, by simp⟩
  | unmodeled =>
      simp only [bind, pure]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact h
        · exact absurd h2 (by simp)
      · intro h
        exact Or.inl h

/-- Associativity of `bind`.  Both sides run `c`, then `k`, then `h`; they
    differ only in how the three event lists are parenthesized, so the
    proof is a pile of existentials closed by `List.append_assoc`. -/
theorem bind_assoc {A B C : Type} (c : Sys M I E A) (k : A → Sys M I E B)
    (h : B → Sys M I E C) :
    sysEquiv (bind (bind c k) h) (bind c (fun x => bind (k x) h)) := by
  intro i m o
  cases o with
  | ok z m3 evs =>
      simp only [bind]
      constructor
      · rintro ⟨y, m2, evsA, evsB, ⟨x, m1, evs1, evs2, Hc, Hk, HevsA⟩, Hh, Hevs⟩
        subst HevsA Hevs
        exact ⟨x, m1, evs1, evs2 ++ evsB, Hc, ⟨y, m2, evs2, evsB, Hk, Hh, rfl⟩,
          List.append_assoc _ _ _⟩
      · rintro ⟨x, m1, evs1, evsBC, Hc, ⟨y, m2, evs2, evsB, Hk, Hh, HevsBC⟩, Hevs⟩
        subst HevsBC Hevs
        exact ⟨y, m2, evs1 ++ evs2, evsB, ⟨x, m1, evs1, evs2, Hc, Hk, rfl⟩, Hh,
          (List.append_assoc _ _ _).symm⟩
  | unmodeled =>
      simp only [bind]
      constructor
      · intro hh
        rcases hh with (Hc | ⟨x, m1, evs1, Hc, Hk⟩) | ⟨y, m2, evsA, ⟨x, m1, evs1, evs2, Hc, Hk, _⟩, Hh⟩
        · exact Or.inl Hc
        · exact Or.inr ⟨x, m1, evs1, Hc, Or.inl Hk⟩
        · exact Or.inr ⟨x, m1, evs1, Hc, Or.inr ⟨y, m2, evs2, Hk, Hh⟩⟩
      · intro hh
        rcases hh with Hc | ⟨x, m1, evs1, Hc, Hk_or⟩
        · exact Or.inl (Or.inl Hc)
        · rcases Hk_or with Hk | ⟨y, m2, evs2, Hk, Hh⟩
          · exact Or.inl (Or.inr ⟨x, m1, evs1, Hc, Hk⟩)
          · exact Or.inr ⟨y, m2, evs1 ++ evs2, ⟨x, m1, evs1, evs2, Hc, Hk, rfl⟩, Hh⟩

/-! ### Core effects -/

/-- The outcome that says THE MODEL DOES NOT COVER THIS CALL (fail closed).

    NOT a kernel failure.  A syscall that fails on real Linux — `-ENOENT`,
    `-EBADF`, a short read — is an ordinary `ok` carrying the negative
    errno, because a real process observes exactly that and runs on.  The
    program leaves the modeled surface only via `unmodeled`, and that is
    what `Run.unmodeled_at` reads and `Equivalence.modeled` forbids of a
    source binary. -/
def unmodeled {A : Type} : Sys M I E A := fun _ _ o => o = .unmodeled

/-- Environment choice: any `x` satisfying `P` may be returned. -/
def choose {A : Type} (P : A → Prop) : Sys M I E A :=
  fun _ m o => ∃ x, P x ∧ o = .ok x m []

/-- Union of two admissible-outcome sets. -/
def alt {A : Type} (c1 c2 : Sys M I E A) : Sys M I E A :=
  fun i m o => c1 i m o ∨ c2 i m o

/-- Emit observable events. -/
def emit (evs : List E) : Sys M I E Unit := fun _ m o => o = .ok () m evs

/-! ### Readers (the syscall input) and state accessors (the model) -/

/-- The current syscall input. -/
def input : Sys M I E I := fun i m o => o = .ok i m []

/-- Allocate a fresh model state (the state effect's `get`). -/
def getModel : Sys M I E M := fun _ m o => o = .ok m m []

/-- Update the model state (the state effect's `modify`). -/
def modify (f : M → M) : Sys M I E Unit := fun _ m o => o = .ok () (f m) []

/-- Reading the model is pure: a `getModel` at the head of a chain binds the
    model the chain starts in and changes nothing, so the whole chain is
    the continuation at that model. -/
theorem bind_getModel {A : Type} (k : M → Sys M I E A) : ∀ (i : I) m o,
    bind getModel k i m o ↔ k m i m o := by
  intro i m o
  cases o with
  | ok x m2 evs =>
      simp only [bind, getModel]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [Outcome.ok.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp at h3
        subst h3
        exact h2
      · intro h
        exact ⟨m, m, [], evs, rfl, h, rfl⟩
  | unmodeled =>
      simp only [bind, getModel]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact absurd h (by simp)
        · simp only [Outcome.ok.injEq] at h1
          obtain ⟨rfl, rfl, rfl⟩ := h1
          exact h2
      · intro h
        exact Or.inr ⟨m, m, [], rfl, h⟩

/-! ### Introduction lemmas — building admissible outcomes compositionally.
Used by the receptiveness proof (`Progress.v`), the checker verification
(`ExecutableSpecs.v`), and target equivalence proofs. -/

theorem bind_ok {A B : Type} (c : Sys M I E A) (k : A → Sys M I E B)
    (i : I) (m : M) (x : A) (m1 : M) (evs1 : List E) (y : B) (m2 : M) (evs2 : List E)
    (hc : c i m (.ok x m1 evs1)) (hk : k x i m1 (.ok y m2 evs2)) :
    bind c k i m (.ok y m2 (evs1 ++ evs2)) :=
  ⟨x, m1, evs1, evs2, hc, hk, rfl⟩

theorem bind_unmodeled1 {A B : Type} (c : Sys M I E A) (k : A → Sys M I E B)
    (i : I) (m : M) (hc : c i m .unmodeled) : bind c k i m .unmodeled :=
  Or.inl hc

theorem bind_unmodeled2 {A B : Type} (c : Sys M I E A) (k : A → Sys M I E B)
    (i : I) (m : M) (x : A) (m1 : M) (evs1 : List E)
    (hc : c i m (.ok x m1 evs1)) (hk : k x i m1 .unmodeled) :
    bind c k i m .unmodeled :=
  Or.inr ⟨x, m1, evs1, hc, hk⟩

theorem pure_ok {A : Type} (x : A) (i : I) (m : M) :
    pure (M := M) (I := I) (E := E) x i m (.ok x m ([] : List E)) := rfl

theorem choose_ok {A : Type} (P : A → Prop) (x : A) (i : I) (m : M) (h : P x) :
    choose (M := M) (I := I) (E := E) P i m (.ok x m ([] : List E)) := ⟨x, h, rfl⟩

theorem unmodeled_intro {A : Type} (i : I) (m : M) :
    unmodeled (M := M) (I := I) (E := E) (A := A) i m .unmodeled := rfl

theorem alt_l {A : Type} (c1 c2 : Sys M I E A) (i : I) (m : M) (o : Outcome A M E)
    (h : c1 i m o) : alt c1 c2 i m o := Or.inl h

theorem alt_r {A : Type} (c1 c2 : Sys M I E A) (i : I) (m : M) (o : Outcome A M E)
    (h : c2 i m o) : alt c1 c2 i m o := Or.inr h

theorem emit_ok (evs : List E) (i : I) (m : M) :
    emit (M := M) (I := I) (E := E) evs i m (.ok () m evs) := rfl

theorem input_ok (i : I) (m : M) :
    input (M := M) (I := I) (E := E) i m (.ok i m ([] : List E)) := rfl

theorem getModel_ok (i : I) (m : M) :
    getModel (M := M) (I := I) (E := E) i m (.ok m m ([] : List E)) := rfl

theorem modify_ok (f : M → M) (i : I) (m : M) :
    modify (M := M) (I := I) (E := E) f i m (.ok () (f m) ([] : List E)) := rfl

end LinuxSem.LinuxProcessSem
