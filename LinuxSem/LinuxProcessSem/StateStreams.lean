/-
  * LinuxProcessSem.StateStreams — standard input: taking bytes, endless streams

  Standard input: taking bytes off the stream, and streams that never end.

  THE TYPE ITSELF IS NOT HERE.  `InputStream` (`IEof`, `ICons`) lives in
  `LinuxProcessSem.State`, together with the long comment explaining why
  the run's input is an explicit parameter rather than an internal choice,
  and why EOF is sticky by construction.  This file imports that type and
  never redefines it.

  TRUST BOUNDARY: this file is part of the trusted specification.

  THE ENCODING.  Lean 4 has neither coinductive types nor corecursion
  without `partial`/`unsafe`, both banned by `AGENTS.md`.  So `InputStream`
  is the total function `Nat → Option byte`
  (`s n = some b` means byte `n` is `b`; `s n = none` means the stream ended
  at or before `n`) and:

  - `stream_take` never destructs the stream.  It OBSERVES `s 0` and
    recurses on the shift `fun n => s (n + 1)`, structurally on the count
  `k`.  Coinduction and `destruct s` steps therefore become inductions
  on `k` and case splits on `s 0` — strictly easier, and no corecursion
  appears anywhere;
  - `stream_infinite` is the predicate `∀ n, (s n).isSome` instead of a
  corecursive `Prop`, and the constructor `stream_infinite_cons` is a
  lemma;
  - `stream_const` is `fun _ => some b`, and `stream_const_unfold` is the
  one-level case analysis the "frob" comment describes (here: `funext`
  plus `cases n`, because the match on the encoding's head is stuck on a
  variable);
  - `stream_take_pos` recurses on the binary digits of a `Nat`.  The
    binary recursion is cheap over `Nat`, so both it and its bridge
  `stream_take_pos_eq` are here.  One deliberate simplification: the
  `IEof` short-circuits inside the two binary branches are omitted — they
  are an extraction-cost optimization, and over `Nat` the cost is already
  `O(bytes taken + log n)`.  A chunk that observes an already-ended
  stream returns `([], IEof)` by `stream_take` itself, so the omitted
  tests change nothing (`stream_take_pos_eq` proves the result is exactly
  `stream_take`);
  - `stream_take_z` is `stream_take s n.toNat`: the same value `n`'s sign
  case would return for every `n`, without a unary numeral, and still
  kernel-reducible (a well-founded `stream_take_pos` is not), which is
  what downstream `by decide` checks and extracted checkers need.

  THE ONE LEMMA THAT NEEDS A HYPOTHESIS.  `stream_take_rest_self` is
  unconditional when a stream is built from `IEof`/`ICons`, because `IEof`
  has no successor.  The function encoding is total: a value of the type can
  be `none` at 0 and `some _` at 1, which no `ICons`/`IEof`-built stream ever
  is.  The unconditional lemma is FALSE for such junk streams (take 1 byte:
  the remainder is `IEof`, whereas taking 0 bytes leaves the stream itself),
  so it is stated with the explicit invariant `stream_sticky` — an ended
  stream stays ended — which every stream the model builds satisfies.  The
  unconditional form has no other use anywhere in the tree, so no downstream
  statement inherits the hypothesis.
-/
import LinuxSem.LinuxProcessSem.State

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/- =========================================================================
   Standard input: taking bytes off the stream

  The `InputStream` type — its long COLIST comment and its declaration —
  lives in `LinuxProcessSem.State`; see the `InputStream` docstring there.
   ========================================================================= -/

/-- Take up to `k` bytes off the front of `s`: the bytes actually
    available (fewer than `k` when the input ends first) together with
    the REMAINING stream.  This is the whole of what a read consumes;
    `ReadWrite.read_spec` chooses how many bytes a given read delivers
    (short reads are real) but not WHICH — those come from here.

    Indexed by a `Nat` rather than a `word`: the index is always the
    length of a delivered byte list, never guest arithmetic, so no
    wrapping is possible.

  The stream is read by observation rather than by destructing it: a
  stream here is a function, so the two cases become `s 0 = none` (the
  input ends: nothing is delivered and the remainder is `IEof`) and
  `s 0 = some b` (deliver `b` and continue with the shift
  `fun n => s (n + 1)`).  Recursion is structural on `k` — the stream is
  never an inductive argument — which is why every proof below is an
  induction on the count. -/
def stream_take (s : InputStream) : Nat → List byte × InputStream
  | 0 => ([], s)
  | k + 1 =>
      match s 0 with
      | none => ([], IEof)
      | some b =>
          let r := stream_take (fun n => s (n + 1)) k
          (b :: r.1, r.2)

/-- The bytes a read of at most `k` delivers. -/
def stream_bytes (s : InputStream) (k : Nat) : List byte :=
  (stream_take s k).1

/-- What is left after such a read. -/
def stream_rest (s : InputStream) (k : Nat) : InputStream :=
  (stream_take s k).2

/-! ### Unfolding `stream_take` (the encoding's `destruct s`)

  The function encoding reads the stream as a case split on `s 0`
  rather than by destructuring it.  These three equations are exactly
  what those case splits produce; everything else
    in the file rewrites with them (or with `stream_take_eof` /
    `stream_take_cons` below) instead of unfolding `stream_take` again. -/

theorem stream_take_zero (s : InputStream) : stream_take s 0 = ([], s) := rfl

theorem stream_take_none {s : InputStream} (h : s 0 = none) (k : Nat) :
    stream_take s (k + 1) = ([], IEof) := by
  simp [stream_take, h]

theorem stream_take_some {s : InputStream} {b : byte} (h : s 0 = some b) (k : Nat) :
    stream_take s (k + 1)
      = (b :: (stream_take (fun n => s (n + 1)) k).1,
         (stream_take (fun n => s (n + 1)) k).2) := by
  simp [stream_take, h]

theorem stream_take_eof : ∀ k, stream_take IEof k = ([], IEof)
  | 0 => rfl
  | k + 1 => stream_take_none rfl k

theorem stream_take_cons (b : byte) (s : InputStream) (k : Nat) :
    stream_take (ICons b s) (k + 1) = (b :: (stream_take s k).1, (stream_take s k).2) := rfl

/-- A read never delivers more than it was asked for. -/
theorem stream_take_length (k : Nat) : ∀ s, (stream_take s k).1.length ≤ k := by
  induction k with
  | zero => intro s; exact Nat.zero_le _
  | succ k ih =>
      intro s
      cases h : s 0 with
      | none => rw [stream_take_none h k]; exact Nat.zero_le _
      | some b =>
          rw [stream_take_some h k]
          simp only [List.length_cons]
          exact Nat.succ_le_succ (ih _)

/-- Taking exactly as many bytes as were delivered is idempotent: the
    delivered list is the stream's prefix of its own length.  (Used to
    read the choice condition of `ReadWrite.read_spec` both ways.) -/
theorem stream_take_bytes_self (k : Nat) : ∀ s,
    (stream_take s (stream_take s k).1.length).1 = (stream_take s k).1 := by
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      cases h : s 0 with
      | none => rw [stream_take_none h k]; rfl
      | some b =>
          rw [stream_take_some h k]
          simp only [List.length_cons]
          rw [stream_take_some h (stream_take (fun n => s (n + 1)) k).1.length]
          simp only [List.cons.injEq, true_and]
          exact ih _

/-- A stream that has ended STAYS ended: `s n = none` implies
    `s (n + 1) = none`.

  This is free for a stream built from `IEof`/`ICons` — `IEof` has no
  successor, so no such stream can resume after it.  But the function
  encoding in `State.lean` is total, so a value of the type may be junk
  after its first `none`.  Every stream the model BUILDS is sticky
  (`IEof`, `ICons` and `stream_const` all are), and this is the
  hypothesis that lets `stream_take_rest_self` be stated at all. -/
def stream_sticky (s : InputStream) : Prop := ∀ n, s n = none → s (n + 1) = none

/-- A sticky stream that has already ended at 0 is `IEof`, all the way out:
    the encoding's replacement for "`IEof` has no successor". -/
theorem stream_sticky_eof {s : InputStream} (hs : stream_sticky s) (h0 : s 0 = none) :
    s = IEof := by
  funext n
  induction n with
  | zero => simpa [IEof] using h0
  | succ n ih => exact hs n ih

/-- Stickiness is preserved by the shift, so it survives a read. -/
theorem stream_sticky_tail {s : InputStream} (hs : stream_sticky s) :
    stream_sticky (fun n => s (n + 1)) := by
  intro n h
  exact hs (n + 1) h

/-- `stream_take_rest_self`, with the encoding's `stream_sticky`
    hypothesis: the remainder after taking the delivered prefix is the
    remainder after taking the whole read.  (See the module header: the
    unconditional form is false for a junk stream that ends at 0 and
  resumes at 1, and the statement is unconditional over `IEof`/`ICons`
  only because `IEof` cannot resume.) -/
theorem stream_take_rest_self (k : Nat) : ∀ s, stream_sticky s →
    (stream_take s (stream_take s k).1.length).2 = (stream_take s k).2 := by
  induction k with
  | zero => intro s _; rfl
  | succ k ih =>
      intro s hs
      cases h : s 0 with
      | none =>
          have hsE : s = IEof := stream_sticky_eof hs h
          subst hsE
          simp [stream_take_eof]
      | some b =>
          rw [stream_take_some h k]
          simp only [List.length_cons]
          rw [stream_take_some h (stream_take (fun n => s (n + 1)) k).1.length]
          exact ih _ (stream_sticky_tail hs)

/-- A nonempty delivery is only possible from a nonempty stream. -/
theorem stream_take_nil_of_eof (k : Nat) : (stream_take IEof k).1 = [] := by
  rw [stream_take_eof]

/-- Taking `a + b` bytes is taking `a`, then `b` from what is left. -/
theorem stream_take_add (a : Nat) : ∀ b s,
    stream_take s (a + b)
      = ((stream_take s a).1 ++ (stream_take (stream_take s a).2 b).1,
         (stream_take (stream_take s a).2 b).2) := by
  induction a with
  | zero =>
      intro b s
      simp [stream_take]
  | succ a ih =>
      intro b s
      rw [Nat.add_right_comm]
      cases h : s 0 with
      | none =>
          rw [stream_take_none h (a + b), stream_take_none h a]
          exact (stream_take_eof b).symm
      | some c =>
          rw [stream_take_some h (a + b), stream_take_some h a]
          dsimp only
          rw [ih b (fun n => s (n + 1))]
          simp [List.cons_append]

/-! ### `stream_take` indexed by a `Z` count

  This is the one place the count is the kernel's aggregate rather than
  the length of a delivered list: the bytes the source could supply to a
  read of `n`, which decides whether a partially writable destination is
  declined (`ReadWrite.read_spec`, `ReadWrite.readv_imported`).  `n`
  there can be `MAX_RW_COUNT`, and `stream_take s n.toNat` would build
  that many unary successors in the extracted checker before looking at
  the stream.  This recurses on the BINARY digits of `n` instead — each
  digit takes two halves, stopping as soon as the stream ends — so the
  cost is the bytes actually taken plus one step per digit, and no unary
  numeral is ever built.  `stream_take_z_eq` says it computes exactly
  `stream_take` at `n.toNat`; the spec uses this spelling so that the
  checker, which is the same term, can run it.

  The recursion is on the binary digits of a `Nat` (`n / 2`, `n % 2`),
  because Lean's `Nat` is a machine word and there is no `positive` type.
  The digit structure — and therefore the cost argument above — is the
  same: `0` and `1` are the base cases (a 1 digit is `take 1`), and each
  larger count takes `p = n / 2` twice, plus one more byte for an odd
  count. -/
def stream_take_pos (s : InputStream) : Nat → List byte × InputStream
  | 0 => ([], s)
  | 1 => stream_take s 1
  | n + 2 =>
      let p := (n + 2) / 2
      let r1 := stream_take_pos s p
      let r2 := stream_take_pos r1.2 p
      if (n + 2) % 2 = 0 then
        (r1.1 ++ r2.1, r2.2)
      else
        let r3 := stream_take r2.2 1
        (r1.1 ++ r2.1 ++ r3.1, r3.2)
termination_by n => n
decreasing_by all_goals exact Nat.div_lt_self (by omega) (by decide)

/-- The binary-count version computes exactly `stream_take`, by
    `stream_take_add` at `p + p` and `p + p + 1`). -/
theorem stream_take_pos_eq (n : Nat) : ∀ s, stream_take_pos s n = stream_take s n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro s
      rcases n with _ | _ | m
      · simp [stream_take_pos, stream_take]
      · simp [stream_take_pos]
      · have hp : (m + 2) / 2 < m + 2 := Nat.div_lt_self (by omega) (by decide)
        have h1 : stream_take_pos s ((m + 2) / 2) = stream_take s ((m + 2) / 2) := ih _ hp s
        have h2 : stream_take_pos (stream_take_pos s ((m + 2) / 2)).2 ((m + 2) / 2)
            = stream_take (stream_take_pos s ((m + 2) / 2)).2 ((m + 2) / 2) := ih _ hp _
        rw [h1] at h2
        have hmod : (m + 2) % 2 = 0 ∨ (m + 2) % 2 = 1 := by omega
        rw [stream_take_pos]
        rcases hmod with hmod | hmod
        · rw [ite_eq_left hmod]
          simp only [h1, h2]
          have hm : m + 2 = (m + 2) / 2 + (m + 2) / 2 := by
            have := Nat.div_add_mod (m + 2) 2
            omega
          conv => rhs; rw [hm]
          rw [stream_take_add]
        · rw [ite_eq_right (by omega)]
          simp only [h1, h2]
          have hm : m + 2 = (m + 2) / 2 + (m + 2) / 2 + 1 := by
            have := Nat.div_add_mod (m + 2) 2
            omega
          conv => rhs; rw [hm]
          rw [stream_take_add, stream_take_add ((m + 2) / 2) ((m + 2) / 2) s]

/-- The `Z`-indexed spelling `read_urandom` uses.

  A sign case on `n` (positive: recurse on the binary count; otherwise
  `([], s)`) would keep the extracted checker from building a unary
  `nat`.  Lean's `Nat` is a machine word and `stream_take_pos` is
  well-founded (hence not kernel-reducible), so the wrapper is written
  directly as `stream_take s n.toNat`, which returns the same value for
  EVERY `n`: for `n < 0`, `n.toNat = 0` and `stream_take s 0 = ([], s)`,
  the `([], s)` branch, and for `n >= 0` it is the count itself.  The
  binary-count version stays above with `stream_take_pos_eq` as the
  bridge, for any chunk that wants the digit-recursive term itself. -/
def stream_take_z (s : InputStream) (n : Int) : List byte × InputStream :=
  stream_take s n.toNat

/-- `stream_take_z` is `stream_take` at `n.toNat`.  Over the function
  encoding this is definitional, and it is kept as the rewrite rule
  `read_urandom` and the rest of the tree expect. -/
theorem stream_take_z_eq (s : InputStream) (n : Int) :
    stream_take_z s n = stream_take s (Int.toNat n) := rfl

/- -------------------------------------------------------------------------
   A stream that never ends
   ------------------------------------------------------------------------- -/

/-- A STREAM THAT NEVER REACHES `IEof`.

  THIS IS THE COINDUCTIVE-LOOKING ONE, AND THE LOOK IS FORCED rather than
  stylistic.  It is the exact dual of
  `EquivalenceDefinition.FinInput.finite_stream`, which is inductive
  because a derivation there must reach `IEof` in a bounded number of
  steps.  Here nothing is ever reached, so a derivation would be a
  productive corecursion.

  A Lean `Prop` cannot be corecursive, and the encoding needs none:
  `InputStream` is `Nat → Option byte`, so "the stream never ends" is the
  pointwise predicate `∀ n, (s n).isSome`.  That is the same predicate as
  "never `IEof`" (a stream is never `IEof` iff every observation is a
  byte), and every proof below is an induction on the count rather than a
  corecursive argument.

    WHAT IT IS FOR.  `in_stdin` and `in_net` carry no validity clause
    and should not: a pipe that ends is a real pipe, and a program has
    to survive it.  The RANDOM DEVICE is not like that.
    `Sys.Fs.ReadWrite.read_urandom` takes the whole clamped count from
    the declared stream and DECLINES if fewer bytes come back, because a
    short read from this device is not something Linux does:
    `urandom_read_iter` is `get_random_bytes_user` over the imported
    iterator, and that loops until the iterator is drained, stopping
    early only where `copy_to_iter` copies short or a signal is pending
    at a page boundary (drivers/char/random.c, Linux v6.18.46; both
    functions are the same in v6.12.1).  The pool is never empty once
    initialised, and `urandom_read_iter` does not wait for it to be.  So a
    finite declaration does not describe a device at all, and a clause
    ruling one out narrows nothing a real /dev/urandom can do.

    IT IS NOT A CLAIM THAT THE STREAM IS UNIFORM, or unpredictable, or
    anything else about its contents.  It says only that reading it
    always yields as many bytes as were asked for, which is what the
    arm needs and the whole of what this predicate says. -/
def stream_infinite (s : InputStream) : Prop := ∀ n, (s n).isSome = true

/-- A stream whose head is a byte and whose tail is endless is endless. -/
theorem stream_infinite_cons (b : byte) (s : InputStream) (hs : stream_infinite s) :
    stream_infinite (ICons b s) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact hs n

theorem stream_infinite_not_eof : ¬ stream_infinite IEof := by
  intro h
  exact absurd (h 0) (by decide)

/-- THE ONE FACT EVERY CONSUMER WANTS: a take off an endless stream
    delivers exactly as many bytes as it asked for. -/
theorem stream_take_infinite_length (k : Nat) : ∀ s, stream_infinite s → (stream_take s k).1.length = k := by
  induction k with
  | zero => intro s _; rfl
  | succ k ih =>
      intro s hs
      cases h : s 0 with
      | none => exact absurd (hs 0) (by simp [h])
      | some b =>
          rw [stream_take_some h k]
          simp only [List.length_cons]
          rw [ih (fun n => s (n + 1)) (fun n => hs (n + 1))]

/-- ...AND THE INVARIANT SURVIVES THE READ, which is what makes the
    clause an input clause rather than one that has to be re-established
    at every step: the remainder of an endless stream is endless, so a
    model whose `m_urandom` started endless stays endless however many
    reads it serves. -/
theorem stream_infinite_rest (k : Nat) : ∀ s, stream_infinite s → stream_infinite (stream_take s k).2 := by
  induction k with
  | zero => intro s hs; exact hs
  | succ k ih =>
      intro s hs
      cases h : s 0 with
      | none => exact absurd (hs 0) (by simp [h])
      | some b =>
          rw [stream_take_some h k]
          exact ih (fun n => s (n + 1)) (fun n => hs (n + 1))

/-- The same two, in the `Z`-indexed spelling `read_urandom` uses. -/
theorem stream_take_z_infinite_length (s : InputStream) (n : Int) (hs : stream_infinite s)
    (hn : 0 ≤ n) : Int.ofNat (stream_take_z s n).1.length = n := by
  rw [stream_take_z_eq, stream_take_infinite_length _ _ hs]
  exact Int.toNat_of_nonneg hn

theorem stream_take_z_infinite_rest (s : InputStream) (n : Int) (hs : stream_infinite s) :
    stream_infinite (stream_take_z s n).2 := by
  rw [stream_take_z_eq]
  exact stream_infinite_rest _ _ hs

/-- THE WITNESS, so the clause is not one nothing satisfies: the
    constant stream.  A launch really can declare it — it is a
    perfectly good description of a device that happened to hand out one
    byte value — and it is the fixtures' declaration.

  Over the function encoding the constant stream is literally
  `fun _ => some b`; no corecursion is needed. -/
def stream_const (b : byte) : InputStream := fun _ => some b

/-- A constant stream does not reduce as a bare function value; it has to
  be applied (or matched on) first.  This one-level case analysis puts
  it in that position — the same "frob" step
  `EquivalenceDefinition.FinInput.stream_decompose` makes, restated here
  because `State` is a lower layer than that file.

  The match is on the INDEX (`cases n`), which is the function-encoding
  form of the same one-level case analysis; after `funext` each side is
  `some b`. -/
theorem stream_const_unfold (b : byte) : stream_const b = ICons b (stream_const b) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem stream_const_infinite (b : byte) : stream_infinite (stream_const b) := by
  intro n
  rfl

/-- THE RANDOM STREAM A FIXTURE GETS WHEN IT DOES NOT SAY.  It is a
    FIXTURE DEFAULT and appears in no theorem: it is what `mkProcInput`
    fills `in_urandom` with, for positional literals that do not
    give the field.

    IT IS NOT `IEof`, and that is not cosmetic.
    `Run.valid_urandom` asks that a launch's declared random stream
    never end, so `IEof` is not a declaration any valid input can
    carry, and a fixture that used it would fail its own validity pin.
    Zero bytes forever is the shortest thing that does satisfy the
    clause; the VALUE is arbitrary and nothing reads it.

  The zero byte is spelled `BitVec.ofInt 8 0`. -/
def default_urandom : InputStream := stream_const (BitVec.ofInt 8 0)

theorem default_urandom_infinite : stream_infinite default_urandom :=
  stream_const_infinite _

/-! ## Sanity checks

    `by decide` wherever the compared type is decidable.  `InputStream` is
  a function, so it has no `DecidableEq`; a whole `stream_take` result is
  a pair whose second component is a stream, so those equalities are
  checked by `rfl` (kernel computation), and every decidable projection
  (the byte list, a single observation of the remainder) is checked `by
  decide`. -/

example : stream_take IEof 3 = ([], IEof) := rfl
example : stream_take (ICons 7 IEof) 3 = ([7], IEof) := rfl
example : stream_take (ICons 1 (ICons 2 IEof)) 3 = ([1, 2], IEof) := rfl
example : stream_bytes IEof 3 = [] := by decide
example : stream_bytes (ICons 7 IEof) 3 = [7] := by decide
example : stream_bytes (ICons 1 (ICons 2 IEof)) 5 = [1, 2] := by decide
example : stream_rest IEof 3 = IEof := rfl
example : stream_rest (ICons 7 IEof) 3 = IEof := rfl
example : stream_rest (ICons 1 (ICons 2 IEof)) 1 = ICons 2 IEof := rfl
example : (stream_rest (ICons 1 (ICons 2 IEof)) 1) 0 = some 2 := by decide
example : stream_bytes (stream_const 7) 3 = [7, 7, 7] := by decide
example : stream_infinite (stream_const 7) := stream_const_infinite 7
example : stream_infinite default_urandom := default_urandom_infinite
example : (stream_const 7 100).isSome = true := by decide
example : default_urandom 3 = some (BitVec.ofInt 8 0) := by decide
example : stream_take_z (ICons 1 IEof) (-1) = ([], ICons 1 IEof) := rfl
example : (stream_take_z (ICons 1 IEof) (-1)).1 = [] := by decide
example : (stream_take_z (ICons 1 (ICons 2 IEof)) 2).1 = [1, 2] := by decide
example : (stream_take_pos (ICons 1 (ICons 2 IEof)) 5).1 = [1, 2] := by
  rw [stream_take_pos_eq]; decide
example : (stream_take_pos IEof 8).1 = [] := by
  rw [stream_take_pos_eq]; decide

end LinuxSem.LinuxProcessSem
