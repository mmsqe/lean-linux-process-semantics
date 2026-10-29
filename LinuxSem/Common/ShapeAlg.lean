/-
  * Common.ShapeAlg — a COMPOSITIONAL behavior-shape algebra (prototype)

    TRUST BOUNDARY: image-INDEPENDENT proof library, like every other file
    in [Common/].  Nothing here is part of the trusted specification, and
    [EquivalenceDefinition/Equivalence] is NOT touched.

    ** The problem

    Each existing shape file ([CatSim], [StreamSim], [DrainSim],
    [AllocSim], [MmapSim], [FileSim], ...) defines its OWN inductive
    characterization of reachable behavior and hand-proves its own trio
    ([*_obs_iff], [*_no_error], [*_strong_equiv]).  Those relations do not
    compose: putting an allocation prologue in front of a write-list tail
    requires a NEW file gluing two relations together ([AllocSim2] is
    exactly that, for one combination).

    ** The design

    Two layers, connected by one generic theorem.

    - LAYER 1 (semantics of shapes).  A shape denotes a [TSet], a
      PREFIX-CLOSED set of finite event traces — the same object
      [Run.obs_trace] is, and the same object [Equivalence.trace_equiv]
      compares.  Prefix closure is baked into the denotation rather than
      applied as a closure operator on a set of maximal traces, so a
      never-terminating behavior (an unbounded stdin stream, which has no
      maximal trace) is still an ordinary inhabitant of the type.
      Combinators: [t_nil], [t_emit] (emit a block, then continue),
      [t_alt] (indexed nondeterministic choice).  Everything else
      ([t_exit], [t_writes_pick], [t_alt2]) is derived.

    - LAYER 2 (realization).  ONE reachability relation, [realizes c T],
      "configuration [c] realizes shape [T]", replacing every per-shape
      inductive.  It has exactly three constructors:

        [rz_node]   — an I-indexed syscall/instruction node whose
                      admissible transitions are EXACTLY
                      { (evs i, nx i) | i : I }, with a continuation
                      shape per resolution;
        [rz_halt]   — the model is halted; nothing more happens;
        [rz_conseq] — replace the shape by an extensionally equal one.

      The node interface is [node_ok]: a soundness half (every [sstep]
      from here is one of the resolutions) and a completeness half (every
      resolution is an admissible [sstep]).  That is PRECISELY the
      [sstep_*_inv] / [*_ok] lemma pair each existing shape file already
      proves per syscall.  An ordinary instruction step is the [unit]-
      indexed silent node; an [exit] is the [unit]-indexed node emitting
      one [ExitEv] into a halted config; [mmap] is the two-summand node.

    ** The master theorem

    Proved ONCE, by induction on [realizes] (never on a shape):

      [realizes_obs_iff]  : obs_trace segs c tr <-> T tr     (both directions)
      [realizes_no_error] : realizes c T -> ~ reaches_error segs c
      [shape_strong_equiv]: source and target realizing the SAME [T]
                            gives [Equivalence.modeled] + [Equivalence.equiv]

    Note that [realizes_obs_iff] is a plain [iff] with no closure operator
    on either side: because [T] is already prefix-closed, shape equality
    IS trace-prefix-set equality.

    ** Composition

    Every combinator is a CONTINUATION-POLYMORPHIC introduction lemma for
    [realizes] — "given [realizes c' T] for the continuation, [realizes c
    (t_emit evs T)]" — so blocks compose by plugging derivations into each
    other, with no glue file and no new master theorem.  [rz_alloc_writes]
    at the bottom of this file is the #1 corpus unlock ("silent
    nondeterministic allocation prologue, then a deterministic
    write-list-then-exit tail") derived in four lines from the mmap node
    combinator and the [CatSim] bridge.

    ** Sanity: the existing shapes are instances

    [cat_realizes] and [twm_realizes]/[tmw_realizes] translate [CatSim]'s
    [to_wexit] and [MmapSim]'s [twm]/[tmw] into [realizes], and
    [cat_strong_equiv_alg] / [mmap_strong_equiv_alg] re-derive
    [CatSim.cat_strong_equiv_te] and [MmapSim.mmap_strong_equiv_te] from
    the single master theorem.  Nothing is deleted: the originals stay.

    ** NOTES

    COVERAGE.  [AllocSim] and
    [AllocSim2] do not import this file, so the dependency is acyclic.
    [t_alt_emit_nil] sits inside the same  block but needs nothing
    from either module (the composition lemmas of the
    [SpinAlg]/[DrainAlg] family use it).
    [rz_wall1_mut] and [wall_realizes] USED to be deferred too, waiting for
    `Common/WallSim`.  `Common/WallSim.lean` now
    supplies [to_wall], [to_wall_tail], [to_wallexit] and the combined
    eliminator [to_wall_mutind], so both are present here.
    CONSTRUCTOR NAMES.  Consumers that apply them at the
    FLAT name, as the section lets them (`apply (rz_node segs ...)`,
    `eapply rz_conseq`), use the dotted form.  NOTE for the integrator:
    `LibWritev.lean`'s temporary PREREQUISITES copy spells the same three
    constructors [realizes.node] / [realizes.halt] / [realizes.conseq], so
    its proofs need that three-name rename when its section is deleted;
    `SpinAlg.lean`'s scaffold already uses the spelling and needs
    only the section deleted plus `open Common.ShapeAlg`.
    AXIOMS.  Every theorem here depends on at most `propext`,
    `Classical.choice` and `Quot.sound` (no `sorryAx`); the file carries no
    proof hole, no `admit`, no extra postulate and no `unsafe`, and it typechecks with
    Lean's `unusedVariables` linter ON .
-/

import LinuxSem.Common.AllocSim
import LinuxSem.Common.AllocSim2
import LinuxSem.Common.CatSim
import LinuxSem.Common.ExitSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.WallSim
import LinuxSem.EquivalenceDefinition.OmniEquivalence

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.Common.AllocSim
open LinuxSem.Common.AllocSim2
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.MmapSim
open LinuxSem.Common.WallSim
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

namespace LinuxSem.Common.ShapeAlg

/-- The FP state at process entry, so that the [MmapSim]/[CatSim] lemmas
    (whose proofs go through [PropExec.mkst]) elaborate.  Same local
    instance `SpinAlg.lean` declares. -/
local instance shapealg_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   Prefix lemmas
   ========================================================================= -/

theorem is_prefix_app_r {A : Type} (l m a : List A) (H : is_prefix a l) :
    is_prefix a (l ++ m) := by
  induction l generalizing a with
  | nil =>
    cases a with
    | nil => exact is_prefix_nil _
    | cons _ _ => exact False.elim H
  | cons x l ih =>
    cases a with
    | nil => exact is_prefix_nil _
    | cons y a =>
      obtain ⟨rfl, H'⟩ := H
      exact ⟨rfl, ih a H'⟩

theorem is_prefix_app_split {A : Type} :
    ∀ (l a b : List A), is_prefix b (l ++ a) →
      is_prefix b l ∨ ∃ b', b = l ++ b' ∧ is_prefix b' a := by
  intro l
  induction l with
  | nil => intro a b H; exact Or.inr ⟨b, rfl, H⟩
  | cons x l ih =>
    intro a b H
    cases b with
    | nil => exact Or.inl (is_prefix_nil _)
    | cons y b =>
      obtain ⟨rfl, H'⟩ := H
      rcases ih a b H' with Hp | ⟨b', rfl, Hp⟩
      · exact Or.inl ⟨rfl, Hp⟩
      · exact Or.inr ⟨b', rfl, Hp⟩

theorem is_prefix_nil_r {A : Type} (a : List A) (H : is_prefix a []) : a = [] := by
  cases a with
  | nil => rfl
  | cons _ _ => exact False.elim H

/- =========================================================================
   LAYER 1 — shapes: prefix-closed trace sets and their combinators
   ========================================================================= -/

/-- A shape.  Intended invariant (established for every shape a
    configuration realizes, see [realizes_nonempty] / [realizes_pclosed]):
    nonempty and prefix-closed. -/
def TSet : Type := List event → Prop

/-- Extensional equality of shapes. -/
def t_eq (T T' : TSet) : Prop := ∀ tr, T tr ↔ T' tr

theorem t_eq_refl (T : TSet) : t_eq T T := fun _ => Iff.rfl

theorem t_eq_sym {T T' : TSet} (H : t_eq T T') : t_eq T' T := fun tr => (H tr).symm

theorem t_eq_trans {T1 T2 T3 : TSet} (H12 : t_eq T1 T2) (H23 : t_eq T2 T3) :
    t_eq T1 T3 := fun tr => (H12 tr).trans (H23 tr)

/-- The terminated shape: only the empty trace. -/
def t_nil : TSet := fun tr => tr = []

/-- Emit a fixed block of events, then continue as [T].  The left
    disjunct is what keeps the result prefix-closed: a run may be
    observed part-way through the block. -/
def t_emit (evs : List event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs ∨ ∃ tr', tr = evs ++ tr' ∧ T tr'

/-- Indexed nondeterministic choice. -/
def t_alt {I : Type} (f : I → TSet) : TSet := fun tr => ∃ i, f i tr

/-- Binary choice. -/
def t_alt2 (A B : TSet) : TSet := fun tr => A tr ∨ B tr

/-- Terminating leaf: exit with [code], final file system [fs]. -/
def t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [event.ExitEv code fs] t_nil

/-- The index type of a single channel write's resolutions: the
    delivered length, any nonempty prefix of the buffer.  (For an empty
    buffer the type is EMPTY — the model EFAULTs an empty readable
    prefix, so no realized shape ever contains one.) -/
def wr_index (buf : List byte) : Type :=
  { n : Nat // 1 ≤ n ∧ n ≤ buf.length }

/-- The full-delivery resolution. -/
def wr_full (buf : List byte) (Hnb : 1 ≤ buf.length) : wr_index buf :=
  ⟨buf.length, Hnb, Nat.le_refl _⟩

/-- A single [write(ch, ...)] of buffer [buf]: the environment delivers
    a chosen nonempty prefix, then the continuation. -/
def t_write_ch (ch : word) (buf : List byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf => t_emit ((buf.take i.1).map (event.WriteEv ch)) T)

/-- A list of [write(1, ...)] buffers, then the continuation. -/
def t_writes_pick (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (t_write_ch (BitVec.ofInt 64 1)) T

/-- A shape prefixed by no events is that shape (given nonemptiness, which
    every realized shape has). -/
theorem t_emit_nil_eq (T : TSet) (H0 : T []) : t_eq (t_emit [] T) T := by
  intro tr
  constructor
  · rintro (Hp | ⟨tr', he, HT⟩)
    · rw [is_prefix_nil_r tr Hp]; exact H0
    · obtain rfl : tr = tr' := by simpa using he
      exact HT
  · intro HT
    exact Or.inr ⟨tr, rfl, HT⟩

theorem t_writes_pick_nil (T : TSet) : t_writes_pick [] T = T := rfl

theorem t_writes_pick_cons (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes_pick (buf :: bufs) T
      = t_write_ch (BitVec.ofInt 64 1) buf (t_writes_pick bufs T) := rfl

/- -------------------------------------------------------------------------
   The FULL-DELIVERY write combinators: the shape of a write realized
   through a put-style retry loop, whose trace contribution is the whole
   buffer regardless of the environment's chunking (WallSim's nodes).
   ------------------------------------------------------------------------- -/

def t_writes_ch (ch : word) (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (fun buf acc => t_emit (buf.map (event.WriteEv ch)) acc) T

def t_writes (bufs : List (List byte)) (T : TSet) : TSet :=
  t_writes_ch (BitVec.ofInt 64 1) bufs T

theorem t_writes_nil (T : TSet) : t_writes [] T = T := rfl

theorem t_writes_cons (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes (buf :: bufs) T
      = t_emit (buf.map (event.WriteEv (BitVec.ofInt 64 1))) (t_writes bufs T) := rfl

theorem t_writes_ch_cons (ch : word) (buf : List byte) (bufs : List (List byte)) (T : TSet) :
    t_writes_ch ch (buf :: bufs) T
      = t_emit (buf.map (event.WriteEv ch)) (t_writes_ch ch bufs T) := rfl

/-- Every emit-chain shape contains the empty trace. -/
theorem t_emit_has_nil (e : List event) (T : TSet) : t_emit e T [] :=
  Or.inl (is_prefix_nil e)

theorem t_writes_ch_exit_has_nil (ch : word) (bufs : List (List byte)) (code : word)
    (fs : Fs.Fs) : t_writes_ch ch bufs (t_exit code fs) [] := by
  cases bufs with
  | nil => exact t_emit_has_nil _ _
  | cons b bs => exact t_emit_has_nil _ _

/-- The bridge to the hand-written shapes' spelling of the same set:
    [CatSim]'s "prefixes of [wevents bufs ++ [ExitEv code fs]]". -/
theorem t_writes_ch_exit_iff (ch : word) (bufs : List (List byte)) (code : word)
    (fs : Fs.Fs) (tr : List event) :
    t_writes_ch ch bufs (t_exit code fs) tr ↔
      is_prefix tr (wevents_ch ch bufs ++ [event.ExitEv code fs]) := by
  revert tr
  induction bufs with
  | nil =>
    intro tr
    unfold t_writes_ch t_exit t_emit t_nil
    simp only [wevents_ch, List.nil_append]
    constructor
    · rintro (H | ⟨tr', he, hnil⟩)
      · exact H
      · subst hnil
        subst he
        exact is_prefix_refl _
    · intro H
      exact Or.inl H
  | cons buf bufs ih =>
    intro tr
    rw [t_writes_ch_cons]
    simp only [wevents_ch, List.append_assoc]
    constructor
    · rintro (H | ⟨tr', he, Hc⟩)
      · exact is_prefix_app_r _ _ _ H
      · subst he
        exact is_prefix_app_mono _ _ _ ((ih tr').1 Hc)
    · intro H
      rcases is_prefix_app_split _ _ _ H with Hp | ⟨tr', he, Hp⟩
      · exact Or.inl Hp
      · exact Or.inr ⟨tr', he, (ih tr').2 Hp⟩

theorem t_writes_exit_iff (bufs : List (List byte)) (code : word) (fs : Fs.Fs)
    (tr : List event) :
    t_writes bufs (t_exit code fs) tr ↔
      is_prefix tr (wevents bufs ++ [event.ExitEv code fs]) := by
  unfold t_writes
  rw [t_writes_ch_exit_iff, wevents_ch_1]

/-- A single retry-loop write node collapses to one [t_emit] of the
    whole buffer: the per-delivery alternatives denote the same set. -/
theorem t_alt_wall (ch : word) (rest : List byte) (T : TSet)
    (_HT : T []) (Hnb : 1 ≤ rest.length) :
    t_eq (t_alt (fun i : wr_index rest =>
            t_emit ((rest.take i.1).map (event.WriteEv ch))
                   (t_emit ((rest.drop i.1).map (event.WriteEv ch)) T)))
         (t_emit (rest.map (event.WriteEv ch)) T) := by
  intro tr
  constructor
  · rintro ⟨⟨n, hn1, hn2⟩, Hi⟩
    rcases Hi with Hp | ⟨tr1, he, Hi⟩
    · refine Or.inl ?_
      have hsplit : rest.map (event.WriteEv ch)
          = (rest.take n).map (event.WriteEv ch) ++ (rest.drop n).map (event.WriteEv ch) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact is_prefix_app_r _ _ _ Hp
    · subst he
      rcases Hi with Hp | ⟨tr2, he2, Ht⟩
      · refine Or.inl ?_
        have hsplit : rest.map (event.WriteEv ch)
            = (rest.take n).map (event.WriteEv ch) ++ (rest.drop n).map (event.WriteEv ch) := by
          rw [← List.map_append, List.take_append_drop]
        rw [hsplit]
        exact is_prefix_app_mono _ _ _ Hp
      · subst he2
        refine Or.inr ⟨tr2, ?_, Ht⟩
        simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · rintro (Hp | ⟨tr', he, Ht⟩)
    · refine ⟨wr_full rest Hnb, ?_⟩
      simp only [wr_full, List.take_length]
      exact Or.inl Hp
    · subst he
      refine ⟨wr_full rest Hnb, ?_⟩
      simp only [wr_full, List.take_length, List.drop_length, List.map_nil]
      exact Or.inr ⟨tr', rfl, Or.inr ⟨tr', rfl, Ht⟩⟩

/-- The bridge to the hand-written shapes' spelling of the same set:
    [CatSim]'s "prefixes of [full ++ [ExitEv code fs]] over the delivery
    choices [wpick ch bufs full]".  Nonemptiness of every buffer (which
    every realized shape has, [CatSim.to_wexit_bufs_nonempty]) is what
    makes the two spellings agree: an empty buffer empties BOTH sides
    from that point on.

    This is what [t_writes_ch_pick] DENOTES, and it is the per-delivery
    twin of [t_writes_ch_exit_iff] above.  It has no proof caller — the
    example developments reach the same set through [realizes_obs_iff]
    — and it is kept anyway, for the same reason [t_writes_ch_exit_iff]
    is: the shape algebra states what each of its shapes means, and
    [t_writes_ch_pick] is the shape this development added.  Deleting it
    would leave the algebra characterizing the full-delivery shape that
    short writes replaced and saying nothing about the one that replaced
    it. -/
theorem t_writes_ch_pick_exit_iff (ch : word) (bufs : List (List byte))
    (code : word) (fs : Fs.Fs) (tr : List event)
    (Hall : ∀ b ∈ bufs, 1 ≤ b.length) :
    bufs.foldr (t_write_ch ch) (t_exit code fs) tr ↔
      ∃ full, wpick ch bufs full ∧ is_prefix tr (full ++ [event.ExitEv code fs]) := by
  revert Hall tr
  induction bufs with
  | nil =>
    intro tr Hall
    unfold t_exit t_emit t_nil
    constructor
    · rintro (h | ⟨tr', rfl, rfl⟩)
      · exact ⟨[], wpick.wp_nil, by simpa using h⟩
      · exact ⟨[], wpick.wp_nil, by simpa using is_prefix_refl [event.ExitEv code fs]⟩
    · rintro ⟨full, hw, hp⟩
      cases hw with
      | wp_nil => exact Or.inl (by simpa using hp)
  | cons b bs ih =>
    intro tr Hall
    have hb : 1 ≤ b.length := Hall b (by simp)
    have hbs : ∀ x ∈ bs, 1 ≤ x.length := fun x hx => Hall x (by simp [hx])
    unfold t_write_ch
    simp only [List.foldr_cons]
    unfold t_alt
    constructor
    · rintro ⟨⟨n, hn1, hn2⟩, h | ⟨tr', rfl, hT⟩⟩
      · refine ⟨List.map (event.WriteEv ch) (b.take n) ++ wevents_ch ch bs,
          wpick.wp_cons b bs n (wevents_ch ch bs) hn1 hn2 (wpick_wevents ch bs hbs), ?_⟩
        simpa only [List.append_assoc] using
          is_prefix_trans h
            (is_prefix_app (List.map (event.WriteEv ch) (b.take n))
              (wevents_ch ch bs ++ [event.ExitEv code fs]))
      · obtain ⟨full, hw, hp⟩ := (ih tr' hbs).1 hT
        refine ⟨List.map (event.WriteEv ch) (b.take n) ++ full,
          wpick.wp_cons b bs n full hn1 hn2 hw, ?_⟩
        simpa only [List.append_assoc] using
          is_prefix_app_mono (List.map (event.WriteEv ch) (b.take n)) tr'
            (full ++ [event.ExitEv code fs]) hp
    · rintro ⟨full, hw, hp⟩
      cases hw with
      | wp_cons b' bs' n tr0 hn1 hn2 hpick =>
        have hp' : is_prefix tr
            (List.map (event.WriteEv ch) (b.take n) ++ (tr0 ++ [event.ExitEv code fs])) := by
          simpa only [List.append_assoc] using hp
        rcases is_prefix_app_split (List.map (event.WriteEv ch) (b.take n))
          (tr0 ++ [event.ExitEv code fs]) tr hp' with hp'' | ⟨tr', rfl, hp''⟩
        · exact ⟨⟨n, hn1, hn2⟩, Or.inl hp''⟩
        · exact ⟨⟨n, hn1, hn2⟩, Or.inr ⟨tr', rfl,
            (ih tr' hbs).2 ⟨tr0, hpick, hp''⟩⟩⟩

theorem t_writes_pick_exit_iff (bufs : List (List byte)) (code : word) (fs : Fs.Fs)
    (tr : List event) (Hall : ∀ b ∈ bufs, 1 ≤ b.length) :
    t_writes_pick bufs (t_exit code fs) tr ↔
      ∃ full, wpick (BitVec.ofInt 64 1) bufs full ∧
        is_prefix tr (full ++ [event.ExitEv code fs]) :=
  t_writes_ch_pick_exit_iff _ bufs code fs tr Hall

/-- [MmapSim.two_traces] is the binary alternative of two write-then-exit
    shapes (on all-nonempty buffer lists). -/
theorem two_traces_t_alt2 (bf : List (List byte)) (cf : word) (bs : List (List byte))
    (cs : word) (fs : Fs.Fs) (tr : List event) :
    t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs)) tr
      ↔ MmapSim.two_traces bf cf bs cs fs tr := by
  unfold t_alt2 MmapSim.two_traces
  rw [t_writes_exit_iff, t_writes_exit_iff]

/- =========================================================================
   LAYER 2 — realization
   ========================================================================= -/

/-- A configuration from its two halves . -/
abbrev mkCfg (ms : machine_state) (model : Model) : config := ⟨ms, model⟩

/-- The syscall/step boundary interface.  A node at configuration [c] is
    characterized by an index type [I] of RESOLUTIONS, the events each
    resolution emits, and the successor configuration each resolution
    reaches.  [node_ok] says the set of admissible transitions is EXACTLY
    that — which in particular rules out [SError], and hence rules out
    both faults and unmodeled configurations, at this node.

    This is the ONLY thing a per-binary proof (symbolic executor, Hoare
    logic, hand-written [step_*] chain) must supply about a syscall: the
    [*_ok] lemma is clause 1, the [sstep_*_inv] lemma is clause 2. -/
def node_ok (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) : Prop :=
  (∀ i, sstep segs c (evs i) (.SNext (nx i)))
  ∧ (∀ (e : List event) (st : step_to), sstep segs c e st →
      ∃ i, e = evs i ∧ st = .SNext (nx i))

/-- The one reachability relation. -/
inductive realizes (segs : List Segment) : config → TSet → Prop where
  | rz_node (c : config) (I : Type) (evs : I → List event) (nx : I → config)
      (T : I → TSet) (i0 : I)
      (hnode : node_ok segs c I evs nx)
      (hcont : ∀ i, realizes segs (nx i) (T i)) :
      realizes segs c (t_alt (fun i => t_emit (evs i) (T i)))
  | rz_halt (c : config) (Hh : m_halted c.cfg_model ≠ none) :
      realizes segs c t_nil
  | rz_conseq (c : config) (T T' : TSet)
      (h : realizes segs c T) (heq : t_eq T T') :
      realizes segs c T'

/- -------------------------------------------------------------------------
   Structural facts: every realized shape is nonempty and prefix-closed.
   ------------------------------------------------------------------------- -/

theorem realizes_nonempty (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : T [] := by
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
  | rz_halt c Hh => rfl
  | rz_conseq c T T' h heq ih => exact (heq []).1 ih

theorem realizes_pclosed (segs : List Segment) (c : config) (T : TSet) :
    realizes segs c T →
      ∀ (tr tr' : List event), T tr → is_prefix tr' tr → T tr' := by
  intro H
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    intro tr tr' HT Hp
    rcases HT with ⟨i, Hpre | ⟨tr0, htr, HT0⟩⟩
    · exact ⟨i, Or.inl (is_prefix_trans Hp Hpre)⟩
    · subst htr
      rcases is_prefix_app_split (evs i) tr0 tr' Hp with Hp' | ⟨tr0', htr', Hp'⟩
      · exact ⟨i, Or.inl Hp'⟩
      · subst htr'
        exact ⟨i, Or.inr ⟨tr0', rfl, ih i tr0 tr0' HT0 Hp'⟩⟩
  | rz_halt c Hh =>
    intro tr tr' HT Hp
    simp only [t_nil] at HT
    subst HT
    exact is_prefix_nil_r tr' Hp
  | rz_conseq c T T' h heq ih =>
    intro tr tr' HT Hp
    exact (heq tr').1 (ih tr tr' ((heq tr).2 HT) Hp)

/- -------------------------------------------------------------------------
   Soundness: every reachable trace is in the shape.
   ------------------------------------------------------------------------- -/

theorem realizes_star_only (segs : List Segment) (c : config) (T : TSet) :
    realizes segs c T →
      ∀ (tr : List event) (c' : config), star segs c tr c' → T tr := by
  intro H
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    intro tr c' hstar
    cases hstar with
    | refl => exact ⟨i0, Or.inl (is_prefix_nil (evs i0))⟩
    | step c1 e c2 tr2 c3 hss htail =>
      obtain ⟨i, he, hst⟩ := hnode.2 e (.SNext c2) hss
      subst he
      cases hst
      exact ⟨i, Or.inr ⟨tr2, rfl, ih i tr2 _ htail⟩⟩
  | rz_halt c Hh =>
    intro tr c' hstar
    obtain ⟨rfl, -⟩ := star_halted_nil segs c tr c' Hh hstar
    rfl
  | rz_conseq c T T' h heq ih =>
    intro tr c' hstar
    exact (heq tr).1 (ih tr c' hstar)

/- -------------------------------------------------------------------------
   Completeness: every trace in the shape is admitted.
   ------------------------------------------------------------------------- -/

theorem realizes_admits (segs : List Segment) (c : config) (T : TSet) :
    realizes segs c T → ∀ tr, T tr → obs_trace segs c tr := by
  intro H
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    intro tr HT
    rcases HT with ⟨i, Hpre | ⟨tr0, htr, HT0⟩⟩
    · exact ⟨evs i, nx i, star_one segs c (evs i) (nx i) (hnode.1 i), Hpre⟩
    · subst htr
      obtain ⟨tr'', c'', hstar, hp⟩ := ih i tr0 HT0
      exact ⟨evs i ++ tr'', c'',
        star.step c (evs i) (nx i) tr'' c'' (hnode.1 i) hstar,
        is_prefix_app_mono (evs i) tr0 tr'' hp⟩
  | rz_halt c Hh =>
    intro tr HT
    cases HT
    exact obs_trace_nil segs c
  | rz_conseq c T T' h heq ih =>
    intro tr HT
    exact ih tr ((heq tr).2 HT)

/-- The master observation theorem: shape membership IS trace-prefix-set
    membership, with no closure operator on either side. -/
theorem realizes_obs_iff (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) (tr : List event) :
    obs_trace segs c tr ↔ T tr := by
  constructor
  · rintro ⟨tr', c', hstar, hp⟩
    exact realizes_pclosed segs c T H tr' tr (realizes_star_only segs c T H tr' c' hstar) hp
  · exact realizes_admits segs c T H tr

/- -------------------------------------------------------------------------
   No error.
   ------------------------------------------------------------------------- -/

theorem sstep_halted_none (segs : List Segment) (c : config) (e : List event)
    (st : step_to) (H : sstep segs c e st) : m_halted c.cfg_model = none := by
  cases H <;> assumption

theorem realizes_step (segs : List Segment) (c : config) (T : TSet) :
    realizes segs c T → ∀ (e : List event) (c' : config),
      sstep segs c e (.SNext c') → ∃ T', realizes segs c' T' := by
  intro H
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    intro e c' hss
    obtain ⟨i, he, hst⟩ := hnode.2 e (.SNext c') hss
    subst he
    cases hst
    exact ⟨T i, hcont i⟩
  | rz_halt c Hh =>
    intro e c' hss
    exact absurd (sstep_halted_none segs c e (.SNext c') hss) Hh
  | rz_conseq c T T' h heq ih =>
    intro e c' hss
    exact ih e c' hss

theorem realizes_no_sserror (segs : List Segment) (c : config) (T : TSet) :
    realizes segs c T → ∀ e, ¬ sstep segs c e .SError := by
  intro H
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    intro e hss
    obtain ⟨i, -, hbad⟩ := hnode.2 e .SError hss
    exact nomatch hbad
  | rz_halt c Hh =>
    intro e hss
    exact Hh (sstep_halted_none segs c e .SError hss)
  | rz_conseq c T T' h heq ih =>
    intro e hss
    exact ih e hss

/-- "Configuration [c] realizes some shape". -/
def rz_path (segs : List Segment) (c : config) : Prop := ∃ T, realizes segs c T

/- -------------------------------------------------------------------------
   The omni reading of [realizes]
   ------------------------------------------------------------------------- -/

/-- [realizes] is already an exact omni judgment — [node_ok] says the
    admissible transitions are EXACTLY the indexed family — so both
    coinductive judgments of [OmniRun] fall out of one induction over
    the shape: every finite prefix is in the shape ([cosafe], from
    [realizes_star_only] through [OmniRun.star_cosafe]) and every
    execution that ends halts with its trace in the shape ([coexec],
    by induction over the shape).  The "admits" half,
    [realizes_admits], is the existential one and stays as it is. -/
theorem realizes_cosafe (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : cosafe segs c T :=
  star_cosafe segs c T (fun tr c' hstar => realizes_star_only segs c T H tr c' hstar)

theorem realizes_coexec (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) :
    OmniRun.coexec segs c (fun tr o => T tr ∧ ¬ is_error o) := by
  induction H with
  | rz_node c I evs nx T i0 hnode hcont ih =>
    refine coexec_step segs c _ (sstep_halted_none segs c (evs i0) (.SNext (nx i0)) (hnode.1 i0)) ?_ ?_
    · intro e hss
      obtain ⟨i, -, hbad⟩ := hnode.2 e .SError hss
      exact nomatch hbad
    · intro e c' hss
      obtain ⟨i, he, hst⟩ := hnode.2 e (.SNext c') hss
      subst he
      cases hst
      refine coexec_conseq segs _ _ _ (ih i) ?_
      rintro tr o ⟨HT, Hno⟩
      exact ⟨⟨i, Or.inr ⟨tr, rfl, HT⟩⟩, Hno⟩
  | rz_halt c Hh =>
    exact coexec_halt segs c _ Hh ⟨rfl, fun h => h⟩
  | rz_conseq c T T' h heq ih =>
    refine coexec_conseq segs c _ _ ih ?_
    rintro tr o ⟨HT, Hno⟩
    exact ⟨(heq tr).1 HT, Hno⟩

theorem realizes_no_error (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ¬ reaches_error segs c := by
  refine coexec_no_error segs c ?_
  refine coexec_conseq segs c _ _ (realizes_coexec segs c T H) ?_
  rintro tr o ⟨-, Hno⟩
  exact Hno

/-- Bites.  A realised shape never takes the escape: [OmniRun.exec … errors]
    is refuted, because the one execution it would be realised by
    ([OmniRun.exec_realizes]) ends in an error and [realizes_coexec] says
    no ending execution does. -/
theorem realizes_not_errors (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : ¬ OmniRun.exec segs c errors := by
  intro Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs c errors Hex
  exact (coexec_sound segs c tr o Hm _
    (realizes_coexec segs c T H)).2 Herr

/-- ... and every trace of the shape is really produced, so a prefix
    postcondition that excludes one of them — prefix-closed, hence a
    candidate for [OmniEquivalence.omni_trace_equiv] — is refuted. -/
theorem realizes_refutes_excluding (segs : List Segment) (c : config) (T : TSet)
    (tr : List event) (H : realizes segs c T) (HT : T tr) :
    ¬ cosafe segs c (fun tr' => ¬ is_prefix tr tr') := by
  intro Hc
  obtain ⟨tr', c', Hstar, Hp⟩ := realizes_admits segs c T H tr HT
  exact (cosafe_star segs c _ tr' c' Hc Hstar) Hp

/- =========================================================================
   Combinators — every one is continuation-polymorphic
   ========================================================================= -/

/-- A [Unit]-indexed alternative is its own only branch. -/
theorem t_alt_unit (f : Unit → TSet) : t_eq (t_alt f) (f ()) := by
  intro tr
  constructor
  · rintro ⟨i, H⟩
    cases i
    exact H
  · intro H
    exact ⟨(), H⟩

/-- A silent [unit]-indexed node collapses to its continuation. -/
theorem rz_silent1 (segs : List Segment) (c c' : config) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => []) (fun _ => c'))
    (Hc : realizes segs c' T) : realizes segs c T := by
  refine .rz_conseq c (t_alt (fun _ : Unit => t_emit [] T)) T ?_ ?_
  · exact .rz_node c Unit (fun _ => []) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_eq_trans (t_alt_unit (fun _ : Unit => t_emit [] T))
      (t_emit_nil_eq T (realizes_nonempty segs c' T Hc))

/-- A [unit]-indexed node emitting a block. -/
theorem rz_emit1 (segs : List Segment) (c c' : config) (e : List event) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => e) (fun _ => c'))
    (Hc : realizes segs c' T) : realizes segs c (t_emit e T) := by
  refine .rz_conseq c (t_alt (fun _ : Unit => t_emit e T)) (t_emit e T) ?_ ?_
  · exact .rz_node c Unit (fun _ => e) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · exact t_alt_unit (fun _ : Unit => t_emit e T)

/-- A SILENT two-way nondeterministic node: the resolutions split into two
    groups, each group's members all continuing as the same shape.  This is
    the mmap/brk pattern. -/
theorem rz_alt2 (segs : List Segment) (c : config) (IA IB : Type)
    (nx : IA ⊕ IB → config) (A B : TSet) (a0 : IA) (b0 : IB)
    (Hnode : node_ok segs c (IA ⊕ IB) (fun _ => []) nx)
    (HA : ∀ i, realizes segs (nx (.inl i)) A)
    (HB : ∀ i, realizes segs (nx (.inr i)) B) :
    realizes segs c (t_alt2 A B) := by
  have HA0 : A [] := realizes_nonempty segs (nx (.inl a0)) A (HA a0)
  have HB0 : B [] := realizes_nonempty segs (nx (.inr b0)) B (HB b0)
  refine .rz_conseq c
    (t_alt (fun i : IA ⊕ IB => t_emit [] (match i with | .inl _ => A | .inr _ => B)))
    (t_alt2 A B) ?_ ?_
  · exact .rz_node c (IA ⊕ IB) (fun _ => []) nx
      (fun i => match i with | .inl _ => A | .inr _ => B) (.inl a0) Hnode
      (fun i => by cases i with | inl i => exact HA i | inr i => exact HB i)
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i with
      | inl i => exact Or.inl ((t_emit_nil_eq A HA0 tr).1 Hi)
      | inr i => exact Or.inr ((t_emit_nil_eq B HB0 tr).1 Hi)
    · rintro (H | H)
      · exact ⟨.inl a0, (t_emit_nil_eq A HA0 tr).2 H⟩
      · exact ⟨.inr b0, (t_emit_nil_eq B HB0 tr).2 H⟩

/- -------------------------------------------------------------------------
   Concrete nodes: instruction step, write(1), exit, munmap, mmap.
   ------------------------------------------------------------------------- -/

theorem node_instr (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    node_ok segs (mkCfg ms model) Unit (fun _ => []) (fun _ => mkCfg ms' model) := by
  constructor
  · intro i
    cases i
    exact sstep.instr ms model ms' model Hh Hsvc
      (by rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep])
  · intro e st Hss
    obtain ⟨he, hst⟩ := sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss
    exact ⟨(), he, hst⟩

theorem rz_step (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hc : realizes segs (mkCfg ms' model) T) : realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep) Hc

theorem rz_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hms : msteps segs ms ms') (Hc : realizes segs (mkCfg ms' model) T) :
    realizes segs (mkCfg ms model) T := by
  revert Hc
  induction Hms with
  | mst_refl ms => intro Hc; exact Hc
  | mst_step ms ms1 ms2 hsvc hstep hms ih =>
    intro Hc
    exact rz_step segs ms model ms1 T Hh Hlazy hsvc hstep (ih Hc)

/-- The [write(1, buf, len)] node: one resolution per delivered length
    (any nonempty prefix of the buffer). -/
theorem node_write1 (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    node_ok segs (mkCfg ms model) (wr_index buf)
      (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model) := by
  constructor
  · rintro ⟨n, hn1, hn2⟩
    exact sstep.syscall ms model x8
      (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))
      model model ((buf.take n).map (event.WriteEv (BitVec.ofInt 64 1)))
      Hh Hsvc (write1_ok_n segs ms x8 model buf n Hfd Hno Hg Hr Hbm hn1 hn2) Hh
      (materialize_model_accesses_no_lazy model _ Hlazy)
  · intro e st Hss
    obtain ⟨n, hn1, hn2, he, hst⟩ :=
      sstep_write_inv segs ms model x8 buf e st Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss
    exact ⟨⟨n, hn1, hn2⟩, he, hst⟩

theorem rz_write1 (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    realizes segs (mkCfg ms model) (t_write_ch (BitVec.ofInt 64 1) buf T) := by
  unfold t_write_ch
  exact .rz_node (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T) (wr_full buf Hnb)
    (node_write1 segs ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

/-- The [exit] leaf. -/
theorem rz_exit (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hx8 : is_exit_no x8) :
    realizes segs (mkCfg ms model)
      (t_exit (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)) := by
  have hspec : Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []) := by
    simpa [sys_input, in_arg, syscall_args]
      using exit_dispatch_ok (sys_input segs ms x8) model Hx8
  have hnode : node_ok segs (mkCfg ms model) Unit
      (fun _ => [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)])
      (fun _ => mkCfg ms (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model)) := by
    constructor
    · intro i
      cases i
      have hs := sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh Hsvc hspec (by simp) (by simp)
      simpa using hs
    · intro e st Hss
      obtain ⟨he, hst⟩ := sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss
      exact ⟨(), he, hst⟩
  unfold t_exit
  exact rz_emit1 segs _ _ _ _ hnode (realizes.rz_halt _ (by simp))

/-- The [munmap] node (silent, model-changing). -/
theorem rz_munmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (T : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 215)
    (Hargs : munmap_args_ok ms model)
    (Hc : realizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T) :
    realizes segs (mkCfg ms model) T := by
  refine rz_silent1 segs _ _ T ?_ Hc
  constructor
  · intro i
    cases i
    exact sstep.syscall ms model x8 (munmap_eff ms)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
      (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
      Hh Hsvc (munmap_ok segs ms x8 model Hno Hargs)
      (by rw [munmap_model_halted]; exact Hh)
      (materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy))
  · intro e st Hss
    obtain ⟨he, hst⟩ :=
      sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
    exact ⟨(), he, hst⟩

/-- The [mmap] node: the two-resolution silent nondeterministic node.
    Failure resolutions (an errno from [mmap_errnos]) continue as [A];
    success resolutions (a grantable address) continue as [B]. -/
theorem rz_mmap (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (A B : TSet) (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (HA : ∀ e, e ∈ mmap_errnos →
      realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A)
    (HB : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      realizes segs (mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true) :
    realizes segs (mkCfg ms model) (t_alt2 A B) := by
  obtain ⟨a0, Ha0⟩ := Hex
  let IA := { e : Int // e ∈ mmap_errnos }
  let IB := { a : word // grant_ok (ms_gpr ms 0) model a
                (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true }
  let nx : IA ⊕ IB → config := fun i =>
    match i with
    | .inl e => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e.1))) model
    | .inr a => mkCfg (advance_past_svc
        (apply_effect ms (mkEffect a.1 [] [(a.1, page_round_up (ms_gpr ms 1))])))
        (mmap_model a.1 (page_round_up (ms_gpr ms 1)) model)
  have Hnode : node_ok segs (mkCfg ms model) (IA ⊕ IB) (fun _ => []) nx := by
    constructor
    · rintro (⟨e, He⟩ | ⟨a, Ha⟩)
      · exact sstep.syscall ms model x8 (mkEffect (errno_ret e) [] []) model model []
          Hh Hsvc (mmap_fail_ok segs ms x8 model e Hno Hargs He) Hh
          (materialize_model_accesses_no_lazy _ _ Hlazy)
      · exact sstep.syscall ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
          (mmap_model a (page_round_up (ms_gpr ms 1)) model)
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) []
          Hh Hsvc (mmap_succ_ok segs ms x8 model a Hno Hargs Ha)
          (by rw [mmap_model_halted]; exact Hh)
          (materialize_model_accesses_no_lazy _ _ (by rw [mmap_model_lazy]; exact Hlazy))
    · intro e st Hss
      obtain ⟨he, hst⟩ := sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss
      rcases hst with ⟨er, Her, hst⟩ | ⟨a, Ha, hst⟩
      · exact ⟨.inl ⟨er, Her⟩, he, hst⟩
      · exact ⟨.inr ⟨a, Ha⟩, he, hst⟩
  exact rz_alt2 segs (mkCfg ms model) IA IB nx A B ⟨ENOMEM, ENOMEM_in_mmap_errnos⟩ ⟨a0, Ha0⟩
    Hnode
    (fun i => HA i.1 i.2)
    (fun i => HB i.1 i.2)

/- =========================================================================
   The master equivalence theorem
   ========================================================================= -/

/- A source and a target realizing the SAME shape are equivalent, and the
   source is covered by the model.  This replaces every
   [*_strong_equiv] lemma in [Common/]: there is one theorem, and the
   shape is the only thing the two per-binary proofs must agree on. -/

/-- The omni ingredients of the master theorem, one per conjunct. -/
theorem shape_omni_corun (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (T : TSet) (inp : ProcInput)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (fun tr o => T tr ∧ ¬ is_error o) := by
  show coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (fun tr o => T tr ∧ ¬ is_error o)
  exact realizes_coexec segs _ T H

theorem shape_omni_cosafe (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (T : TSet) (inp : ProcInput)
    (H : realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T) :
    omni_cosafe (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp T := by
  show cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp) T
  exact realizes_cosafe segs _ T H

/-- Two realisations of the same shape agree on every prefix-closed
    postcondition: the refinement pair, each side's trace set being the
    shape. -/
theorem shape_omni_trace_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    omni_trace_equiv (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩
      (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp := by
  refine (omni_trace_equiv_refinement (mkImage source_segs rpc rph) rlim
    ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) alim
    ⟨asp, abrk, amb, arnd⟩ inp).2 ⟨?_, ?_⟩
  · show cosafe source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
      ((run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp).bh_traces)
    rw [show (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp).bh_traces
        = obs_trace target_segs
            (init_config target_segs apc aph asp abrk amb arnd alim inp) from rfl]
    refine (cosafe_obs_iff source_segs _ _ (obs_trace_is_prefix_closed target_segs _)).2 ?_
    intro tr Hobs
    exact (realizes_obs_iff target_segs _ T Htarget tr).2
      ((realizes_obs_iff source_segs _ T Hsource tr).1 Hobs)
  · show cosafe target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp)
      ((run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp).bh_traces)
    rw [show (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp).bh_traces
        = obs_trace source_segs
            (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) from rfl]
    refine (cosafe_obs_iff target_segs _ _ (obs_trace_is_prefix_closed source_segs _)).2 ?_
    intro tr Hobs
    exact (realizes_obs_iff source_segs _ T Hsource tr).2
      ((realizes_obs_iff target_segs _ T Htarget tr).1 Hobs)

theorem shape_omni_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    omni_equiv (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩
      (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp := by
  refine Or.inr ⟨?_, ?_⟩
  · exact shape_omni_trace_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
      target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget
  · show coexec target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) never_errors
    have hco : coexec target_segs
        (init_config target_segs apc aph asp abrk amb arnd alim inp)
        (fun tr o => T tr ∧ ¬ is_error o) :=
      shape_omni_corun target_segs apc aph asp abrk amb arnd alim T inp Htarget
    exact coexec_conseq target_segs _ _ _ hco (fun _ _ h => h.2)

/-- The master theorem in omni shape: at the two role budgets, a source
    and a target realizing the SAME shape satisfy
    [OmniEquivalence.omni_strong_equiv]. -/
theorem shape_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  refine ⟨?_, ?_⟩
  · show coexec source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (covered source_segs)
    have hco : coexec source_segs
        (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
        (fun tr o => T tr ∧ ¬ is_error o) :=
      shape_omni_corun source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit T inp Hsource
    exact coexec_conseq source_segs _ _ _ hco
      (fun tr o h => never_errors_covered source_segs tr o h.2)
  · exact shape_omni_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
      target_segs apc aph asp abrk amb arnd target_alloc_limit T inp Hsource Htarget

/-- A source and a target realizing the SAME shape are equivalent, and the
    source is covered by the model.  This replaces every
    [*_strong_equiv] lemma in [Common/]: there is one theorem, and the
    shape is the only thing the two per-binary proofs must agree on.
    From the omni ingredients above through the compat [iff]s. -/
theorem shape_strong_equiv (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (T : TSet) (inp : ProcInput)
    (Hsource : realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T)
    (Htarget : realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp) T) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine ⟨?_, ?_⟩
  · refine (modeled_iff (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp).mpr ?_
    show coexec source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) (covered source_segs)
    have hco : coexec source_segs
        (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
        (fun tr o => T tr ∧ ¬ is_error o) :=
      shape_omni_corun source_segs rpc rph rsp rbrk rmb rrnd rlim T inp Hsource
    exact coexec_conseq source_segs _ _ _ hco
      (fun tr o h => never_errors_covered source_segs tr o h.2)
  · refine (equiv_iff (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩
      (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp).mpr ?_
    exact shape_omni_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
      target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget

/- =========================================================================
   Sanity: the existing shapes are instances
   ========================================================================= -/

/-- [CatSim.to_wexit] realizes [t_writes_pick bufs (t_exit code fs)]. -/
theorem cat_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hte : to_wexit segs ms bufs code)
    (Hbm : bufs_modeled bufs) :
    realizes segs (mkCfg ms model) (t_writes_pick bufs (t_exit code (m_fs model))) := by
  revert Hfd Hlazy Hh Hbm
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro Hh Hlazy Hfd Hbm
    rw [t_writes_pick_nil]
    exact rz_exit segs ms model x8 Hh hsvc hx8
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro Hh Hlazy Hfd Hbm
    have hb : buf_modeled buf := Hbm buf (by simp)
    have hbs : bufs_modeled bufs := fun b hmem => Hbm b (by simp [hmem])
    rw [t_writes_pick_cons]
    refine rz_write1 segs ms model x8 buf _ Hh Hlazy Hfd hsvc hno hg hr hb hnb ?_
    intro n hn1 hn2
    exact ih n hn1 hn2 Hh Hlazy Hfd hbs
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    intro Hh Hlazy Hfd Hbm
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih Hh Hlazy Hfd Hbm)

/-- The exit straight line realizes the exit leaf (no fd needed). -/
theorem exitline_realizes_aux (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (model : Model)
    (Hte : to_wexit segs ms bufs code) (Hbufs : bufs = [])
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (mkCfg ms model) (t_exit code (m_fs model)) := by
  revert Hlazy Hh Hbufs
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro Hbufs Hh Hlazy
    exact rz_exit segs ms model x8 Hh hsvc hx8
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro Hbufs Hh Hlazy
    exact nomatch Hbufs
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    intro Hbufs Hh Hlazy
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih Hbufs Hh Hlazy)

theorem exitline_realizes (segs : List Segment) (ms : machine_state) (code : word)
    (model : Model) (Hte : to_wexit segs ms [] code)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (mkCfg ms model) (t_exit code (m_fs model)) :=
  exitline_realizes_aux segs ms [] code model Hte rfl Hh Hlazy

/- -------------------------------------------------------------------------
   Wall nodes

   [WallSim]'s put-style retry loop delivers exactly the buffer it offers,
   however the environment chunks it, so its trace contribution is one
   [t_emit] of the WHOLE buffer — the FULL-DELIVERY shape [t_writes] of the
   section above, not the ret-oblivious [t_writes_pick].  [rz_wall1_mut] is
   the mutual induction over the two wall members ([to_wall] and its
   between-syscalls form [to_wall_tail]), through [to_wall_mutind];
   [wall_realizes] is the run-level corollary for [to_wallexit].
   ------------------------------------------------------------------------- -/

/-- One retry-loop write realizes [t_emit (rest.map (WriteEv 1)) T]: the
    per-delivery alternatives ([t_alt_wall]) all denote the same set as the
    single full-delivery block.  Mutual over [to_wall] / [to_wall_tail],
    which is the shape [to_wall_mutind] eliminates. -/
theorem rz_wall1_mut (segs : List Segment) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) :
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs (BitVec.ofInt 64 1) ms rest k → buf_modeled rest →
      ∀ T : TSet, T [] → (∀ ms', k ms' → realizes segs (mkCfg ms' model) T) →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1))) T))
    ∧ (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs (BitVec.ofInt 64 1) ms rest k → buf_modeled rest →
      ∀ T : TSet, T [] → (∀ ms', k ms' → realizes segs (mkCfg ms' model) T) →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1))) T)) := by
  refine to_wall_mutind segs (BitVec.ofInt 64 1)
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (mkCfg ms' model) T) →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1))) T))
    (fun ms rest k => buf_modeled rest → ∀ T : TSet, T [] →
      (∀ ms', k ms' → realizes segs (mkCfg ms' model) T) →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1))) T)) ?_ ?_ ?_ ?_
  · -- twl_write: the write node, then the per-delivery collapse
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hbm T hT hk
    refine .rz_conseq _ _ _ ?_ (t_alt_wall (BitVec.ofInt 64 1) rest T hT hnb)
    exact .rz_node (mkCfg ms model) (wr_index rest)
      (fun i => (rest.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take i.1)))) model)
      (fun i => t_emit ((rest.drop i.1).map (event.WriteEv (BitVec.ofInt 64 1))) T)
      (wr_full rest hnb)
      (node_write1 segs ms model x8 rest Hh Hlazy Hfd hsvc hno hg hr hbm hnb)
      (fun i => by
        obtain ⟨n, hn1, hn2⟩ := i
        exact ih n hn1 hn2 (buf_modeled_skipn n rest hbm) T hT hk)
  · -- twt_done: nothing left to deliver; the prefix is empty
    intro ms k hk hbm T hT hkcont
    refine .rz_conseq _ _ _ (hkcont ms hk) ?_
    exact t_eq_sym (t_emit_nil_eq T hT)
  · -- twt_more: hand the nonempty remainder back to [to_wall]
    intro ms rest k hnb hw ih hbm T hT hk
    exact ih hbm T hT hk
  · -- twt_step: one instruction step, then the tail
    intro ms ms' rest k hsvc hstep ht ih hbm T hT hk
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih hbm T hT hk)

/-- [WallSim.to_wallexit] realizes the FULL-DELIVERY write-list shape:
    the original [t_writes]. -/
theorem wall_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model)
    (Hw : to_wallexit segs (BitVec.ofInt 64 1) bufs code ms)
    (Hbm : bufs_modeled bufs) :
    realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) := by
  revert ms Hw Hbm
  induction bufs with
  | nil =>
    -- the exit straight line, exactly [CatSim.to_wexit]
    intro ms Hw Hbm
    exact exitline_realizes segs ms code model Hw Hh Hlazy
  | cons buf rest ih =>
    intro ms Hw Hbm
    obtain ⟨Hnb, Ht⟩ := Hw
    have Hb : buf_modeled buf := Hbm buf (by simp)
    have Hbs : bufs_modeled rest := fun b hb => Hbm b (by simp [hb])
    rw [t_writes_cons]
    exact (rz_wall1_mut segs model Hh Hlazy Hfd).2 ms buf
      (to_wallexit segs (BitVec.ofInt 64 1) rest code) Ht Hb
      (t_writes rest (t_exit code (m_fs model)))
      (t_writes_ch_exit_has_nil _ _ _ _)
      (fun ms' hk => ih ms' hk Hbs)

/-- [MmapSim.twm] (retry-loop writes / munmap / exit) realizes the same
    FULL-DELIVERY shape.  The wall structure here is [twm]'s own mutual
    pend/tail pair, so the collapse is replayed over [twm]'s recursor. -/
theorem twm_realizes_mut (segs : List Segment) :
    (∀ (ms : machine_state) (model : Model) (bufs : List (List byte)) (code : word),
      MmapSim.twm segs ms model bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    ∧ (∀ (ms : machine_state) (model : Model) (rest : List byte) (bufs : List (List byte))
        (code : word),
      MmapSim.twm_pend segs ms model rest bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))))
    ∧ (∀ (ms : machine_state) (model : Model) (rest : List byte) (bufs : List (List byte))
        (code : word),
      MmapSim.twm_tail segs ms model rest bufs code →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model))))) := by
  have c_exit : ∀ (ms : machine_state) (model : Model) (x8 : word)
      (hsvc : ms.ms_svc_pending = some x8) (hx8 : is_exit_no x8),
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled [] →
      realizes segs (mkCfg ms model)
        (t_writes [] (t_exit (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model))) := by
    intro ms model x8 hsvc hx8 hh hlazy hfd hbm
    exact rz_exit segs ms model x8 hh hsvc hx8
  have c_write : ∀ (ms : machine_state) (model : Model) (buf : List byte)
      (bufs : List (List byte)) (code : word) (hne : 1 ≤ buf.length)
      (hp : MmapSim.twm_pend segs ms model buf bufs code),
      (m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled buf → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (buf.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model))))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      bufs_modeled (buf :: bufs) →
      realizes segs (mkCfg ms model) (t_writes (buf :: bufs) (t_exit code (m_fs model))) := by
    intro ms model buf bufs code hne hp ih hh hlazy hfd hbm
    have hb : buf_modeled buf := hbm buf (by simp)
    have hbs : bufs_modeled bufs := fun b hmem => hbm b (by simp [hmem])
    exact ih hh hlazy hfd hb hbs
  have c_munmap : ∀ (ms : machine_state) (model : Model) (x8 : word)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 215) (hargs : munmap_args_ok ms model)
      (hte : MmapSim.twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code),
      (m_halted (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = none →
        m_vm_lazy (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = [] →
        fd1chan (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) →
        bufs_modeled bufs →
        realizes segs
          (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
            (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
          (t_writes bufs
            (t_exit code
              (m_fs (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) := by
    intro ms model x8 bufs code hsvc hno hargs hte ih hh hlazy hfd hbm
    refine rz_munmap segs ms model x8 _ hh hlazy hsvc hno hargs ?_
    rw [← munmap_model_fs]
    exact ih (by rw [munmap_model_halted]; exact hh) (munmap_model_no_lazy _ _ _ hlazy)
      (munmap_model_fd1chan _ _ _ hfd) hbm
  have c_step : ∀ (ms ms' : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hte : MmapSim.twm segs ms' model bufs code),
      (m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        realizes segs (mkCfg ms' model) (t_writes bufs (t_exit code (m_fs model)))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) := by
    intro ms ms' model bufs code hsvc hstep hte ih hh hlazy hfd hbm
    exact rz_step segs ms model ms' _ hh hlazy hsvc hstep (ih hh hlazy hfd hbm)
  have c_pend : ∀ (ms : machine_state) (model : Model) (x8 : word) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 64) (h0 : ms_gpr ms 0 = BitVec.ofInt 64 1)
      (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest)
      (hne : 1 ≤ rest.length)
      (hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
        MmapSim.twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model
          (rest.drop n) bufs code),
      (∀ (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ rest.length),
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled (rest.drop n) → bufs_modeled bufs →
        realizes segs
          (mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model)
          (t_emit ((rest.drop n).map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model))))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms model x8 rest bufs code hsvc hno h0 hr hne hcont ih hh hlazy hfd hbr hbm
    refine .rz_conseq _ _ _ ?_
      (t_alt_wall (BitVec.ofInt 64 1) rest
        (t_writes bufs (t_exit code (m_fs model)))
        (t_writes_ch_exit_has_nil _ _ _ _) hne)
    exact .rz_node (mkCfg ms model) (wr_index rest)
      (fun i => (rest.take i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (rest.take i.1)))) model)
      (fun i => t_emit ((rest.drop i.1).map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model))))
      (wr_full rest hne)
      (node_write1 segs ms model x8 rest hh hlazy hfd hsvc hno h0 hr hbr hne)
      (fun i => by
        obtain ⟨n, hn1, hn2⟩ := i
        exact ih n hn1 hn2 hh hlazy hfd (buf_modeled_skipn n rest hbr) hbm)
  have c_done : ∀ (ms : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (hte : MmapSim.twm segs ms model bufs code),
      (m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model)))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled [] → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit ([].map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms model bufs code hte ih hh hlazy hfd hbn hbm
    refine .rz_conseq _ _ _ (ih hh hlazy hfd hbm) ?_
    exact t_eq_sym (t_emit_nil_eq (t_writes bufs (t_exit code (m_fs model)))
      (t_writes_ch_exit_has_nil _ _ _ _))
  have c_more : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hne : 1 ≤ rest.length)
      (hp : MmapSim.twm_pend segs ms model rest bufs code),
      (m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model))))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms model rest bufs code hne hp ih hh hlazy hfd hbr hbm
    exact ih hh hlazy hfd hbr hbm
  have c_tstep : ∀ (ms ms' : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word) (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (ht : MmapSim.twm_tail segs ms' model rest bufs code),
      (m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms' model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model))))) →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms ms' model rest bufs code hsvc hstep ht ih hh hlazy hfd hbr hbm
    exact rz_step segs ms model ms' _ hh hlazy hsvc hstep (ih hh hlazy hfd hbr hbm)
  have rec1 : ∀ (ms : machine_state) (model : Model) (bufs : List (List byte))
      (code : word) (d : MmapSim.twm segs ms model bufs code),
      m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
      realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) := by
    intro ms model bufs code d
    exact MmapSim.twm.rec
      (motive_1 := fun ms model bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
      (motive_2 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      (motive_3 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  have rec2 : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word)
      (d : MmapSim.twm_pend segs ms model rest bufs code),
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms model rest bufs code d
    exact MmapSim.twm_pend.rec
      (motive_1 := fun ms model bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
      (motive_2 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      (motive_3 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  have rec3 : ∀ (ms : machine_state) (model : Model) (rest : List byte)
      (bufs : List (List byte)) (code : word)
      (d : MmapSim.twm_tail segs ms model rest bufs code),
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      buf_modeled rest → bufs_modeled bufs →
      realizes segs (mkCfg ms model)
        (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                (t_writes bufs (t_exit code (m_fs model)))) := by
    intro ms model rest bufs code d
    exact MmapSim.twm_tail.rec
      (motive_1 := fun ms model bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
      (motive_2 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      (motive_3 := fun ms model rest bufs code _ =>
        m_halted model = none → m_vm_lazy model = [] → fd1chan model →
        buf_modeled rest → bufs_modeled bufs →
        realizes segs (mkCfg ms model)
          (t_emit (rest.map (event.WriteEv (BitVec.ofInt 64 1)))
                  (t_writes bufs (t_exit code (m_fs model)))))
      c_exit c_write c_munmap c_step c_pend c_done c_more c_tstep d
  exact ⟨rec1, rec2, rec3⟩

theorem twm_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hte : MmapSim.twm segs ms model bufs code)
    (Hbm : bufs_modeled bufs) :
    realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))) :=
  (twm_realizes_mut segs).1 ms model bufs code Hte Hh Hlazy Hfd Hbm

/-- [MmapSim.tmw] (deterministic prefix, then the branching mmap) realizes
    the binary alternative of two write-then-exit shapes. -/
theorem tmw_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model) (Hte : MmapSim.tmw segs ms model bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    realizes segs (mkCfg ms model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
              (t_writes bs (t_exit cs (m_fs model)))) := by
  revert Hfd Hlazy Hh Hbs Hbf
  induction Hte with
  | mmap ms model x8 bf cf bs cs hsvc hno hargs hfail hsucc hex =>
    intro Hh Hlazy Hfd Hbf Hbs
    refine rz_mmap segs ms model x8 _ _ Hh Hlazy hsvc hno hargs ?_ ?_ hex
    · intro e He
      exact twm_realizes segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model
        bf cf Hh Hlazy Hfd (hfail e He) Hbf
    · intro a Ha
      rw [← mmap_model_fs]
      exact twm_realizes segs _ (mmap_model a (page_round_up (ms_gpr ms 1)) model)
        bs cs (by rw [mmap_model_halted]; exact Hh)
        (by rw [mmap_model_lazy]; exact Hlazy)
        (mmap_model_fd1chan _ _ _ Hfd) (hsucc a Ha) Hbs
  | step ms ms' model bf cf bs cs hsvc hstep hte ih =>
    intro Hh Hlazy Hfd Hbf Hbs
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih Hh Hlazy Hfd Hbf Hbs)

/-- [CatSim.cat_strong_equiv_te], re-derived from the single master
    theorem. -/
theorem cat_strong_equiv_alg (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hs : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Ht : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Hbm : bufs_modeled bufs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim
    (t_writes_pick bufs (t_exit code (in_fs inp))) inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
      (t_writes_pick bufs (t_exit code (in_fs inp)))
    exact cat_realizes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      bufs code rfl rfl rfl Hs Hbm
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
      (t_writes_pick bufs (t_exit code (in_fs inp)))
    exact cat_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp)
      bufs code rfl rfl rfl Ht Hbm

/-- The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. -/
theorem cat_omni_strong_equiv_alg (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hs : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Ht : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Hbm : bufs_modeled bufs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  refine shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
    target_segs apc aph asp abrk amb arnd
    (t_writes_pick bufs (t_exit code (in_fs inp))) inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (t_writes_pick bufs (t_exit code (in_fs inp)))
    exact cat_realizes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bufs code rfl rfl rfl Hs Hbm
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp)
      (t_writes_pick bufs (t_exit code (in_fs inp)))
    exact cat_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bufs code rfl rfl rfl Ht Hbm

/-- [MmapSim.mmap_strong_equiv_te], re-derived from the same theorem. -/
theorem mmap_strong_equiv_alg (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hs : MmapSim.tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs)
    (Ht : MmapSim.tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim
    (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      bf cf bs cs rfl rfl rfl Hs Hbf Hbs
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp)
      bf cf bs cs rfl rfl rfl Ht Hbf Hbs

/-- The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. -/
theorem mmap_omni_strong_equiv_alg (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hs : MmapSim.tmw source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bf cf bs cs)
    (Ht : MmapSim.tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  refine shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
    target_segs apc aph asp abrk amb arnd
    (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bf cf bs cs rfl rfl rfl Hs Hbf Hbs
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs rfl rfl rfl Ht Hbf Hbs

/- =========================================================================
   The allocation-prologue composition, DERIVED
   ========================================================================= -/

/-- "Silent nondeterministic allocation prologue, then a deterministic
    write-list-then-exit tail."

    Without this lemma, this composition needs a new hand-written shape
    file per allocator/tail combination.  Here it is four lines: the mmap node
    combinator with the [CatSim] tail bridge plugged into both
    continuations.  Nothing about it is specific to [to_wexit] — any
    [realizes] derivation may be plugged in, including one produced by a
    reflective symbolic executor. -/
theorem rz_alloc_writes (segs : List Segment) (ms0 ms : machine_state) (model : Model)
    (x8 : word) (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (Hfail : ∀ e, e ∈ mmap_errnos →
      to_wexit segs (advance_past_svc (set_gpr0 ms (errno_ret e))) bf cf)
    (Hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      MmapSim.twm segs
        (advance_past_svc
          (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs)
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    realizes segs (mkCfg ms0 model)
      (t_alt2 (t_writes_pick bf (t_exit cf (m_fs model)))
              (t_writes bs (t_exit cs (m_fs model)))) := by
  refine rz_msteps segs ms0 ms model _ Hh Hlazy Hms ?_
  refine rz_mmap segs ms model x8 _ _ Hh Hlazy Hsvc Hno Hargs ?_ ?_ Hex
  · intro e He
    exact cat_realizes segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf
      Hh Hlazy Hfd (Hfail e He) Hbf
  · intro a Ha
    rw [← mmap_model_fs]
    exact twm_realizes segs _ (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs
      (by rw [mmap_model_halted]; exact Hh) (by rw [mmap_model_lazy]; exact Hlazy)
      (mmap_model_fd1chan _ _ _ Hfd) (Hsucc a Ha) Hbs

/- =========================================================================
   Bridge: AllocSim's brk-branching shape
   ========================================================================= -/

/-- The trace set an [AllocSim.to_outcomes] outcome SET denotes: the
    prefixes of the candidate traces of each outcome.  This is exactly the
    right-hand side of [AllocSim.alloc_obs_iff]. -/
def t_outcomes (fs : Fs.Fs) (U : (List (List byte) × word) → Prop) : TSet :=
  fun tr => ∃ o, U o ∧ is_prefix tr (AllocSim.outcome_trace fs o)

/-- A [t_emit]-chain over a family of shapes, each containing the empty
    trace, denotes the same set as the family itself. -/
theorem t_alt_emit_nil {I : Type} (f : I → TSet) (H : ∀ i, f i []) :
    t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f) := by
  intro tr
  constructor
  · rintro ⟨i, Hi⟩
    exact ⟨i, (t_emit_nil_eq (f i) (H i) tr).1 Hi⟩
  · rintro ⟨i, Hi⟩
    exact ⟨i, (t_emit_nil_eq (f i) (H i) tr).2 Hi⟩

/-- [AllocSim.to_outcomes] realizes [t_outcomes].  The brk node is an
    [rz_node] indexed by the admissible syscall resolutions; receptivity
    ([AllocSim.brk_receptive]) supplies the inhabitant [rz_node] needs. -/
theorem outcomes_realizes (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : AllocSim.to_outcomes segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    realizes segs (mkCfg ms model) (t_outcomes (m_fs model) U) := by
  revert Hh Hlazy
  refine AllocSim.to_outcomes.rec (segs := segs) (motive := fun ms model U _ =>
    m_halted model = none → m_vm_lazy model = [] →
      realizes segs (mkCfg ms model) (t_outcomes (m_fs model) U)) ?_ ?_ ?_ Hto
  · -- tou_wexit: the retry-loop write-list tail
    intro ms model bufs code U hfd hte hbm hU Hh Hlazy
    refine .rz_conseq _ _ _ (wall_realizes segs ms model bufs code Hh Hlazy hfd hte hbm) ?_
    intro tr
    rw [t_writes_exit_iff]
    unfold t_outcomes AllocSim.outcome_trace
    constructor
    · intro Hp
      exact ⟨(bufs, code), (hU _).mpr rfl, Hp⟩
    · rintro ⟨o, Ho, Hp⟩
      obtain rfl : o = (bufs, code) := (hU o).mp Ho
      exact Hp
  · -- tou_step: one silent instruction step, then the tail
    intro ms ms' model U hsvc hstep hto ih Hh Hlazy
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih Hh Hlazy)
  · -- tou_brk: the indexed nondeterministic node
    intro ms model x8 T U hsvc hno hcont hU hcont_ih Hh Hlazy
    let IX := { p : SyscallEffect × Model //
      syscall_spec (sys_input segs ms x8) model (.ok p.1 p.2 []) }
    let nx : IX → config := fun i =>
      mkCfg (advance_past_svc (apply_effect ms i.1.1)) i.1.2
    let Ti : IX → TSet := fun i => t_outcomes (m_fs model) (T i.1.1 i.1.2)
    obtain ⟨eff0, model0, Hspec0⟩ := brk_receptive segs ms x8 model hno
    have Hcont' : ∀ i : IX, realizes segs (nx i) (Ti i) := by
      rintro ⟨⟨eff, model'⟩, Hspec⟩
      show realizes segs (mkCfg (advance_past_svc (apply_effect ms eff)) model')
        (t_outcomes (m_fs model) (T eff model'))
      obtain ⟨-, hhalt, hfs, -, hlazy⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno Hspec
      rw [← hfs]
      exact hcont_ih eff model' [] Hspec hhalt (by rw [hlazy]; exact Hlazy)
    have Hnode : node_ok segs (mkCfg ms model) IX (fun _ => []) nx := by
      constructor
      · rintro ⟨⟨eff, model'⟩, Hspec⟩
        obtain ⟨-, hhalt, -, -, hlazy⟩ :=
          brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno Hspec
        exact sstep.syscall ms model x8 eff model' model' [] Hh hsvc Hspec hhalt
          (by rw [materialize_model_accesses_no_lazy model' _
            (by rw [hlazy]; exact Hlazy)])
      · intro e st Hss
        obtain ⟨eff, model', Hspec, he, hst⟩ :=
          sstep_brk_inv segs ms model x8 e st Hh Hlazy hsvc hno Hss
        exact ⟨⟨(eff, model'), Hspec⟩, he, hst⟩
    refine .rz_conseq _ _ _
      (.rz_node (mkCfg ms model) IX (fun _ => []) nx Ti ⟨(eff0, model0), Hspec0⟩
        Hnode Hcont') ?_
    refine t_eq_trans (t_alt_emit_nil Ti (fun i =>
      realizes_nonempty segs (nx i) (Ti i) (Hcont' i))) ?_
    intro tr
    constructor
    · rintro ⟨i, o, Ho, Hp⟩
      exact ⟨o, (hU o).mpr ⟨i.1.1, i.1.2, [], i.2, Ho⟩, Hp⟩
    · rintro ⟨o, Ho, Hp⟩
      obtain ⟨eff, model', evs, Hspec, Ht⟩ := (hU o).mp Ho
      obtain ⟨hevs, -, -, -, -⟩ :=
        brk_step_shape segs ms x8 model eff model' evs Hh Hlazy hno Hspec
      subst hevs
      exact ⟨⟨(eff, model'), Hspec⟩, o, Ht, Hp⟩

/-- The two-element outcome set of [AllocSim2] is the binary alternative
    of two write-then-exit shapes — the SAME [TSet] a [tmw] target lands
    on.  That equality is the whole content of the mixed-allocator glue. -/
theorem t_outcomes_two_alt2 (fs : Fs.Fs) (bf : List (List byte)) (cf : word)
    (bs : List (List byte)) (cs : word) :
    t_eq (t_outcomes fs (AllocSim2.two_outcomes bf cf bs cs))
      (t_alt2 (t_writes bf (t_exit cf fs)) (t_writes bs (t_exit cs fs))) := by
  intro tr
  unfold t_outcomes AllocSim2.two_outcomes AllocSim.outcome_trace t_alt2
  rw [t_writes_exit_iff, t_writes_exit_iff]
  constructor
  · rintro ⟨o, (ho | ho), Hp⟩
    · subst ho; exact Or.inl (by simpa using Hp)
    · subst ho; exact Or.inr (by simpa using Hp)
  · rintro (Hp | Hp)
    · exact ⟨(bf, cf), Or.inl rfl, by simpa using Hp⟩
    · exact ⟨(bs, cs), Or.inr rfl, by simpa using Hp⟩

/-- [AllocSim2.alloc_mmap_strong_equiv], re-derived from the master
    theorem: a brk-allocating source and an mmap-allocating target that
    realize the SAME shape. -/
theorem alloc_mmap_strong_equiv_alg
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hs : AllocSim.to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      (AllocSim2.two_outcomes bf cf bs cs))
    (Ht : MmapSim.tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim
    (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    refine .rz_conseq _ _ _
      (outcomes_realizes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
          (inp.in_uid) (inp.in_hwcap))
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
        (AllocSim2.two_outcomes bf cf bs cs) Hs rfl rfl) ?_
    exact t_outcomes_two_alt2 (in_fs inp) bf cf bs cs
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp)
      bf cf bs cs rfl rfl rfl Ht Hbf Hbs

/-- The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. -/
theorem alloc_mmap_omni_strong_equiv_alg
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word)
    (inp : ProcInput)
    (Hs : AllocSim.to_outcomes source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      (AllocSim2.two_outcomes bf cf bs cs))
    (Ht : MmapSim.tmw target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs)
    (Hbf : bufs_modeled bf) (Hbs : bufs_modeled bs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  refine shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
    target_segs apc aph asp abrk amb arnd
    (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    refine .rz_conseq _ _ _
      (outcomes_realizes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
          (inp.in_uid) (inp.in_hwcap))
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
        (AllocSim2.two_outcomes bf cf bs cs) Hs rfl rfl) ?_
    exact t_outcomes_two_alt2 (in_fs inp) bf cf bs cs
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp)
      (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
    exact tmw_realizes target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bf cf bs cs rfl rfl rfl Ht Hbf Hbs

/- =========================================================================
   CHANNEL-PARAMETRIC SHAPE

   [t_writes_pick] and [cat_realizes] above are hardwired to channel 1.  These
   are their (fd, channel)-parametric twins, built on [CatSim]'s
   [to_wexit_ch]; [t_writes_ch_pick_1] and [cat_strong_equiv_alg] exhibit the
   channel-1 development as the instance.  A stderr-reporting binary uses
   [cat_ch_strong_equiv_alg] at [fd = ch = 2].
   ========================================================================= -/

def t_writes_ch_pick (ch : word) (bufs : List (List byte)) (T : TSet) : TSet :=
  bufs.foldr (t_write_ch ch) T

theorem t_writes_ch_pick_1 (bufs : List (List byte)) (T : TSet) :
    t_writes_ch_pick (BitVec.ofInt 64 1) bufs T = t_writes_pick bufs T := rfl

theorem t_writes_ch_pick_cons (ch : word) (buf : List byte)
    (bufs : List (List byte)) (T : TSet) :
    t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T) := rfl

theorem node_write_ch (segs : List Segment) (ms : machine_state) (model : Model)
    (fd ch x8 : word) (buf : List byte)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : fd32 fd = fd)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = fd)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length) :
    node_ok segs (mkCfg ms model) (wr_index buf)
      (fun i => (buf.take i.1).map (event.WriteEv ch))
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model) := by
  constructor
  · rintro ⟨n, hn1, hn2⟩
    exact sstep.syscall ms model x8
      (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))
      model model ((buf.take n).map (event.WriteEv ch))
      Hh Hsvc (write_ch_ok_n segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hbm hn1 hn2) Hh
      (materialize_model_accesses_no_lazy model _ Hlazy)
  · intro e st Hss
    obtain ⟨n, hn1, hn2, he, hst⟩ :=
      sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm
        Hnb Hss
    exact ⟨⟨n, hn1, hn2⟩, he, hst⟩

theorem rz_write_ch (segs : List Segment) (ms : machine_state) (model : Model)
    (fd ch x8 : word) (buf : List byte) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : fd32 fd = fd)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 64) (Hg : ms_gpr ms 0 = fd)
    (Hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf)
    (Hbm : buf_modeled buf) (Hnb : 1 ≤ buf.length)
    (Hc : ∀ n, 1 ≤ n → n ≤ buf.length →
      realizes segs
        (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) T) :
    realizes segs (mkCfg ms model) (t_write_ch ch buf T) := by
  unfold t_write_ch
  exact .rz_node (mkCfg ms model) (wr_index buf)
    (fun i => (buf.take i.1).map (event.WriteEv ch))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take i.1)))) model)
    (fun _ => T) (wr_full buf Hnb)
    (node_write_ch segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb)
    (fun i => by
      obtain ⟨n, hn1, hn2⟩ := i
      exact Hc n hn1 hn2)

theorem cat_realizes_ch (segs : List Segment) (fd ch : word) (ms : machine_state)
    (model : Model) (bufs : List (List byte)) (code : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfdc : fdchan fd ch model) (H32 : fd32 fd = fd)
    (Hte : to_wexit_ch segs fd ms bufs code)
    (Hbm : bufs_modeled bufs) :
    realizes segs (mkCfg ms model) (t_writes_ch_pick ch bufs (t_exit code (m_fs model))) := by
  revert Hfdc Hlazy Hh Hbm
  induction Hte with
  | twc_exit ms x8 hsvc hx8 =>
    intro Hh Hlazy Hfdc Hbm
    exact rz_exit segs ms model x8 Hh hsvc hx8
  | twc_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro Hh Hlazy Hfdc Hbm
    have hb : buf_modeled buf := Hbm buf (by simp)
    have hbs : bufs_modeled bufs := fun b hmem => Hbm b (by simp [hmem])
    rw [t_writes_ch_pick_cons]
    refine rz_write_ch segs ms model fd ch x8 buf _ Hh Hlazy Hfdc H32 hsvc hno hg hr hb hnb ?_
    intro n hn1 hn2
    exact ih n hn1 hn2 Hh Hlazy Hfdc hbs
  | twc_step ms ms' bufs code hsvc hstep hte ih =>
    intro Hh Hlazy Hfdc Hbm
    exact rz_step segs ms model ms' _ Hh Hlazy hsvc hstep (ih Hh Hlazy Hfdc Hbm)

/-- The channel-parametric [cat_strong_equiv_alg]. -/
theorem cat_ch_strong_equiv_alg (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (fd ch : word) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (H32 : fd32 fd = fd)
    (Hinit : ∀ (reserved : List (word × word)) (brk0 mb1 sp1 : word) (lim1 : Int)
      (inp1 : ProcInput), fdchan fd ch (init_model reserved brk0 mb1 sp1 lim1 inp1))
    (Hs : to_wexit_ch source_segs fd
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Ht : to_wexit_ch target_segs fd
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Hbm : bufs_modeled bufs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim
    (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp)
      (t_writes_ch_pick ch bufs (t_exit code (in_fs inp)))
    exact cat_realizes_ch source_segs fd ch
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
      bufs code rfl rfl (Hinit _ _ _ _ _ _) H32 Hs Hbm
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd alim inp)
      (t_writes_ch_pick ch bufs (t_exit code (in_fs inp)))
    exact cat_realizes_ch target_segs fd ch
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp alim inp)
      bufs code rfl rfl (Hinit _ _ _ _ _ _) H32 Ht Hbm

/-- The same, in the shape of [OmniEquivalence.omni_strong_equiv], at the
    two role budgets. -/
theorem cat_ch_omni_strong_equiv_alg (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (fd ch : word) (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (H32 : fd32 fd = fd)
    (Hinit : ∀ (reserved : List (word × word)) (brk0 mb1 sp1 : word) (lim1 : Int)
      (inp1 : ProcInput), fdchan fd ch (init_model reserved brk0 mb1 sp1 lim1 inp1))
    (Hs : to_wexit_ch source_segs fd
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Ht : to_wexit_ch target_segs fd
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Hbm : bufs_modeled bufs) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  refine shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
    target_segs apc aph asp abrk amb arnd
    (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp ?_ ?_
  · show realizes source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (t_writes_ch_pick ch bufs (t_exit code (in_fs inp)))
    exact cat_realizes_ch source_segs fd ch
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
      bufs code rfl rfl (Hinit _ _ _ _ _ _) H32 Hs Hbm
  · show realizes target_segs
      (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp)
      (t_writes_ch_pick ch bufs (t_exit code (in_fs inp)))
    exact cat_realizes_ch target_segs fd ch
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap))
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
      bufs code rfl rfl (Hinit _ _ _ _ _ _) H32 Ht Hbm

/-- ... and the fd-1 theorem is its instance. -/
theorem cat_strong_equiv_alg_via_ch (source_segs : List Segment) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bufs : List (List byte)) (code : word) (inp : ProcInput)
    (Hs : to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Ht : to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd (inp.in_argv) (inp.in_envp)
        (inp.in_uid) (inp.in_hwcap)) bufs code)
    (Hbm : bufs_modeled bufs) :
    Equivalence.modeled (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim
        ⟨rsp, rbrk, rmb, rrnd⟩ inp)
      (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) :=
  cat_ch_strong_equiv_alg source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim
    (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) bufs code inp rfl
    (fun _ _ _ _ _ _ => fd1chan_fdchan _ (init_model_fd1chan _ _ _ _ _ _))
    (to_wexit_ch_1 source_segs _ bufs code Hs)
    (to_wexit_ch_1 target_segs _ bufs code Ht) Hbm

end LinuxSem.Common.ShapeAlg
