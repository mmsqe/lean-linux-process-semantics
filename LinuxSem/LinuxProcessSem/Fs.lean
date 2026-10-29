/-
  * LinuxProcessSem.Fs — the interpreted file-system model

  TRUST BOUNDARY: this file is part of the trusted specification.

  Paths and file contents are `byte = BitVec 8` lists; offsets and counts
  arrive from registers as `word = BitVec 64` and are bridged to `Nat`
  for the list operations.  Well-formedness clauses bounding bytes
  are unnecessary — `BitVec 8` enforces them by type.

  The file system has an INTERNAL, INTERPRETED model (unlike channels,
  whose contents are supplied non-deterministically by the environment):
  it is a finite map from paths to byte contents, threaded through the
  syscall model.  The initial file-system image is an input to the
  program (quantified in `Equivalence.strong_universal_T`, like argv/envp),
  and the file system is OBSERVED ONLY AT EXIT: `ExitEv` carries the
  final map, and no file operation emits a trace event.

  CANONICAL FORM: because the final map appears inside a trace event
  (compared with `=`), the representation must not depend on the order
  in which files were written.  We keep the association list strictly
  sorted by path (`fs_sorted`); `fs_set` preserves sortedness, so two
  runs that create the same files with the same contents produce equal
  `Fs` values.  `valid_fs` requires the initial image to be sorted as
  well.

  `firstn`/`skipn`/`repeat` are Lean's
  `List.take`/`List.drop`/`List.replicate`; `Forall P l` is
  spelled `∀ x ∈ l, P x` throughout (the Lean 4.31 core library has no
  `List.Forall`), which is the same predicate at the same places.
-/
import LinuxSem.LinuxProcessSem.BvBase

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Fs

/-! ## Paths -/

/-- A path is the raw byte string the program passed to the kernel (no
    NUL terminator).  Paths are uninterpreted: there is no directory
    structure, no normalization ("./x" and "x" are different files), and
    no symlinks.

    That is a statement about this MAP, and it is NOT the same as a
    statement about what the model admits.  A spec that would have to
    walk a path in order to answer correctly is expected to decline
    rather than read the map as if it had walked one; which specs
    currently do is not written here, because a list of them is a claim
    nothing checks and it goes stale silently.  Grep for
    `Sys.Fs.Namei.path_has_slash` to see the current set.

    What is worth writing down is the consequence: the only spec that
    CREATES a key is `Open.create_wronly`, and it is behind that guard,
    so no program can make "./x" and "x" two keys.  Where a spec answers
    off the map instead of declining, it can diverge from Linux:
    `newfstatat` on the flat namespace can reject a path Linux accepts.

  `abbrev` rather than `def`, so that instance search
    (`Membership`, `DecidableEq`, the `List` lemmas) sees through the
    synonym.  A `def` would be a new constant that search has to be told
    about; an `abbrev` is transparent, so `List byte`'s instances apply
    directly. -/
abbrev path : Type := List byte

/-- Boolean equality on paths. -/
def path_eqb : path → path → Bool
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && path_eqb p' q'
  | _, _ => false

theorem bv_eqb_eq {n : Nat} (a b : BitVec n) : bv_eqb a b = true ↔ a = b := by
  simp [bv_eqb]

theorem path_eqb_eq : ∀ (p q : path), path_eqb p q = true ↔ p = q := by
  intro p
  induction p with
  | nil =>
    intro q
    cases q with
    | nil => simp [path_eqb]
    | cons b q => simp [path_eqb]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [path_eqb]
    | cons b q =>
      simp only [path_eqb, Bool.and_eq_true, bv_eqb_eq, ih]
      constructor
      · rintro ⟨rfl, rfl⟩
        rfl
      · intro h
        exact List.cons.inj h

theorem path_eqb_refl : ∀ (p : path), path_eqb p p = true := by
  intro p
  exact (path_eqb_eq p p).mpr rfl

/-- Strict lexicographic order on paths (shorter prefixes first);
    bytes compare unsigned. -/
def path_ltb : path → path → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_ltu a b || (bv_eqb a b && path_ltb p' q')

/-- The file system: a path-to-contents association list, kept strictly
    sorted by `path_ltb` (see the canonical-form note above).

  `abbrev`, for the same reason as `path`. -/
abbrev Fs : Type := List (path × List byte)

def fs_lookup : Fs → path → Option (List byte)
  | [], _ => none
  | (q, data) :: r, p => if path_eqb p q then some data else fs_lookup r p

/-- Insert-or-replace, preserving strict sortedness of the keys. -/
def fs_set : Fs → path → List byte → Fs
  | [], p, data => [(p, data)]
  | (q, d) :: r, p, data =>
      if path_ltb p q then (p, data) :: (q, d) :: r
      else if path_eqb p q then (p, data) :: r
      else (q, d) :: fs_set r p data

/-- `path_ltb` is transitive.  This is what makes "drop one entry"
    preserve the canonical form: the neighbours either side of a removed
    key were separated only through it. -/
theorem path_ltb_trans : ∀ (a b c : path),
    path_ltb a b = true → path_ltb b c = true → path_ltb a c = true := by
  intro a
  induction a with
  | nil =>
    intro b c h1 h2
    cases b with
    | nil => simp only [path_ltb] at h1; exact absurd h1 (by simp)
    | cons y b =>
      cases c with
      | nil => simp only [path_ltb] at h2; exact absurd h2 (by simp)
      | cons z c => simp only [path_ltb]
  | cons x a ih =>
    intro b c h1 h2
    cases b with
    | nil => simp only [path_ltb] at h1; exact absurd h1 (by simp)
    | cons y b =>
      cases c with
      | nil => simp only [path_ltb] at h2; exact absurd h2 (by simp)
      | cons z c =>
        simp only [path_ltb] at h1 h2 ⊢
        rw [Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
        rcases h1 with h1 | ⟨h1e, h1r⟩
        · rcases h2 with h2 | ⟨h2e, _⟩
          · exact Or.inl (by simp only [bv_ltu, decide_eq_true_eq] at h1 h2 ⊢; omega)
          · have hyz : y = z := (bv_eqb_eq y z).mp h2e
            exact Or.inl (by simp only [hyz] at h1 ⊢; exact h1)
        · rcases h2 with h2 | ⟨h2e, h2r⟩
          · have hxy : x = y := (bv_eqb_eq x y).mp h1e
            exact Or.inl (by simp only [hxy] at h2 ⊢; exact h2)
          · have hxy : x = y := (bv_eqb_eq x y).mp h1e
            have hyz : y = z := (bv_eqb_eq y z).mp h2e
            exact Or.inr ⟨by rw [bv_eqb_eq]; exact hxy.trans hyz, ih b c h1r h2r⟩

/-- Remove a path.  A path absent from the map leaves it unchanged, so a
    caller that has already decided the path is present (unlink) and one
    that has not both get the same function. -/
def fs_remove : Fs → path → Fs
  | [], _ => []
  | (q, d) :: r, p => if path_eqb p q then r else (q, d) :: fs_remove r p

/-- Keys strictly increasing — the canonical form. -/
def fs_sorted : Fs → Bool
  | [] => true
  | (p, _) :: r =>
      match r with
      | [] => true
      | (q, _) :: _ => path_ltb p q && fs_sorted r

/-- The head-key clause of `fs_sorted`, named so the two lemmas below
    can talk about it. -/
def fs_lt_head (a : path) (fs : Fs) : Bool :=
  match fs with
  | [] => true
  | (q, _) :: _ => path_ltb a q

theorem fs_sorted_cons : ∀ (p : path) (d : List byte) (r : Fs),
    fs_sorted ((p, d) :: r) = (fs_lt_head p r && fs_sorted r) := by
  intro p d r
  rcases r with _ | ⟨⟨q, e⟩, r'⟩ <;> rfl

/-- A `Bool` that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  simpa using h

theorem fs_remove_lt_head : ∀ (fs : Fs) (a p : path),
    fs_sorted fs = true → fs_lt_head a fs = true → fs_lt_head a (fs_remove fs p) = true := by
  intro fs
  induction fs with
  | nil => intro a p _ hh; exact hh
  | cons qd r ih =>
    intro a p hs hh
    obtain ⟨q, d⟩ := qd
    have hs' := hs
    rw [fs_sorted_cons, Bool.and_eq_true] at hs'
    obtain ⟨hq, _hr⟩ := hs'
    have hh' : path_ltb a q = true := by simpa only [fs_lt_head] using hh
    simp only [fs_remove]
    by_cases hpq : path_eqb p q = true
    · rw [ite_eq_left hpq]
      rcases r with _ | ⟨⟨q', d'⟩, r'⟩
      · rfl
      · exact path_ltb_trans a q q' hh' (by simpa only [fs_lt_head] using hq)
    · rw [ite_eq_right hpq]
      exact hh'

/-- Dropping an entry preserves the canonical form, so a modeled unlink
    keeps the final `Fs` comparable with `=` (see the CANONICAL FORM note
    above). -/
theorem fs_remove_sorted : ∀ (fs : Fs) (p : path),
    fs_sorted fs = true → fs_sorted (fs_remove fs p) = true := by
  intro fs
  induction fs with
  | nil => intro p _; rfl
  | cons qd r ih =>
    intro p hs
    obtain ⟨q, d⟩ := qd
    have hs' := hs
    rw [fs_sorted_cons, Bool.and_eq_true] at hs'
    obtain ⟨hq, hr⟩ := hs'
    simp only [fs_remove]
    by_cases hpq : path_eqb p q = true
    · rw [ite_eq_left hpq]
      exact hr
    · rw [ite_eq_right hpq]
      rw [fs_sorted_cons, Bool.and_eq_true]
      exact ⟨fs_remove_lt_head r q p hr hq, ih p hr⟩

/-- `path_ltb` is TOTAL against `path_eqb`: two paths that are neither
    equal nor in that order are in the opposite one.  This is what lets
    an insertion that has ruled out both of `fs_set`'s first two
    branches conclude that the key it is walking PAST is strictly below
    the key it is carrying. -/
theorem path_ltb_total : ∀ (p q : path),
    path_ltb p q = false → path_eqb p q = false → path_ltb q p = true := by
  intro p
  induction p with
  | nil =>
    intro q
    cases q with
    | nil =>
      intro hlt hpe
      simp only [path_ltb, path_eqb] at hlt hpe
      exact absurd hpe (by simp)
    | cons b q =>
      intro hlt _
      simp only [path_ltb] at hlt
      exact absurd hlt (by simp)
  | cons a p ih =>
    intro q
    cases q with
    | nil => intro _ _; simp only [path_ltb]
    | cons b q =>
      intro hlt heq
      simp only [path_ltb, path_eqb] at hlt heq ⊢
      rw [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hlt
      obtain ⟨hlt1, hlt2⟩ := hlt
      rw [Bool.and_eq_false_iff] at heq
      by_cases he : bv_eqb a b = true
      · have hba : bv_eqb b a = true := by
          rw [bv_eqb_eq] at he ⊢
          exact he.symm
        have hp : path_ltb p q = false := by
          rcases hlt2 with h | h
          · rw [he] at h; exact absurd h (by simp)
          · exact h
        have hpe : path_eqb p q = false := by
          rcases heq with h | h
          · rw [he] at h; exact absurd h (by simp)
          · exact h
        have hqp : path_ltb q p = true := ih q hp hpe
        simp only [hba, hqp, Bool.true_and, Bool.or_true]
      · have hle : b.toNat ≤ a.toNat := by
          simp only [bv_ltu, decide_eq_false_iff_not] at hlt1
          omega
        have hne : a.toNat ≠ b.toNat := by
          intro h
          exact he (by rw [bv_eqb_eq]; exact BitVec.eq_of_toNat_eq h)
        have hlt' : b.toNat < a.toNat := by omega
        have hltu : bv_ltu b a = true := by
          simp only [bv_ltu, decide_eq_true_eq]
          exact hlt'
        simp only [hltu, Bool.true_or]

/-- Inserting a key strictly above `a` cannot put anything at or below
    `a` at the head: the insertion either lands at the head (and the key
    is above `a` by hypothesis) or leaves the old head in place. -/
theorem fs_set_lt_head : ∀ (fs : Fs) (a p : path) (d : List byte),
    path_ltb a p = true → fs_lt_head a fs = true → fs_lt_head a (fs_set fs p d) = true := by
  intro fs
  induction fs with
  | nil => intro a p d hap _; exact hap
  | cons qd r ih =>
    intro a p d hap hh
    obtain ⟨q, e⟩ := qd
    simp only [fs_set]
    by_cases h1 : path_ltb p q = true
    · rw [ite_eq_left h1]
      exact hap
    · rw [ite_eq_right h1]
      by_cases h2 : path_eqb p q = true
      · rw [ite_eq_left h2]
        exact hap
      · rw [ite_eq_right h2]
        simpa only [fs_lt_head] using hh

/-- Insert-or-replace preserves the canonical form.  This is the fact
    the header's "`fs_set` preserves sortedness" claims and the one
    `State.fs_seed_tmp` rests on: an initial image assembled by
    repeated insertion is canonical WHATEVER list it was assembled
    from, which is why the run's declared private /tmp needs no validity
    clause of its own. -/
theorem fs_set_sorted : ∀ (fs : Fs) (p : path) (d : List byte),
    fs_sorted fs = true → fs_sorted (fs_set fs p d) = true := by
  intro fs
  induction fs with
  | nil => intro p d _; rfl
  | cons qd r ih =>
    intro p d hs
    obtain ⟨q, e⟩ := qd
    have hs' := hs
    rw [fs_sorted_cons, Bool.and_eq_true] at hs'
    obtain ⟨hh, hr⟩ := hs'
    simp only [fs_set]
    by_cases h1 : path_ltb p q = true
    · rw [ite_eq_left h1]
      rw [fs_sorted_cons, Bool.and_eq_true]
      exact ⟨h1, hs⟩
    · rw [ite_eq_right h1]
      by_cases h2 : path_eqb p q = true
      · rw [ite_eq_left h2]
        have hpq : p = q := (path_eqb_eq p q).mp h2
        rw [hpq]
        rw [fs_sorted_cons, Bool.and_eq_true]
        exact ⟨hh, hr⟩
      · rw [ite_eq_right h2]
        rw [fs_sorted_cons, Bool.and_eq_true]
        refine ⟨?_, ih p d hr⟩
        exact fs_set_lt_head r q p d
          (path_ltb_total p q (bool_eq_false_of_ne_true h1) (bool_eq_false_of_ne_true h2)) hh

/-- Insertion keeps any property that holds of every key and of the key
    being inserted.  `valid_fs`'s NUL-free clause is the instance this
    file is written for. -/
theorem fs_set_keys : ∀ (P : path → Prop) (fs : Fs) (p : path) (d : List byte),
    (∀ pf ∈ fs, P pf.1) → P p → ∀ pf ∈ fs_set fs p d, P pf.1 := by
  intro P fs
  induction fs with
  | nil =>
    intro p d _ hp pf hpf
    simp only [fs_set, List.mem_singleton] at hpf
    rw [hpf]
    exact hp
  | cons qd r ih =>
    intro p d hfs hp pf hpf
    obtain ⟨q, e⟩ := qd
    have hq : P q := hfs (q, e) (by simp)
    have hr : ∀ x ∈ r, P x.1 := fun x hx => hfs x (by simp [hx])
    simp only [fs_set] at hpf
    by_cases h1 : path_ltb p q = true
    · rw [ite_eq_left h1] at hpf
      simp only [List.mem_cons] at hpf
      rcases hpf with hpf | hpf | hpf
      · rw [hpf]; exact hp
      · rw [hpf]; exact hq
      · exact hr pf hpf
    · rw [ite_eq_right h1] at hpf
      by_cases h2 : path_eqb p q = true
      · rw [ite_eq_left h2] at hpf
        simp only [List.mem_cons] at hpf
        rcases hpf with hpf | hpf
        · rw [hpf]; exact hp
        · exact hr pf hpf
      · rw [ite_eq_right h2] at hpf
        simp only [List.mem_cons] at hpf
        rcases hpf with hpf | hpf
        · rw [hpf]; exact hq
        · exact ih p d hr hp pf hpf

/-- A lookup misses when no key IS the path.  The counterpart of
    `fs_set_keys` for the read side: a caller holding a fact about every
    key of an image gets the `none` from it without unfolding the
    fixpoint.  `Run.absolute_divergent_not_seeded` is the caller this is
    written for. -/
theorem fs_lookup_none_of_keys : ∀ (fs : Fs) (p : path),
    (∀ qd ∈ fs, qd.1 ≠ p) → fs_lookup fs p = none := by
  intro fs
  induction fs with
  | nil => intro p _; rfl
  | cons qd r ih =>
    intro p h
    obtain ⟨q, d⟩ := qd
    have hq : q ≠ p := h (q, d) (by simp)
    have hr : ∀ x ∈ r, x.1 ≠ p := fun x hx => h x (by simp [hx])
    simp only [fs_lookup]
    by_cases hpq : path_eqb p q = true
    · rw [ite_eq_left hpq]
      exact absurd ((path_eqb_eq p q).mp hpq) (Ne.symm hq)
    · rw [ite_eq_right hpq]
      exact ih p hr

/-- Validity predicate for an initial file-system image: it must be in
    the CANONICAL sorted form (trace events compare final file systems
    with `=`, so the representation must be unique — see the header
    note), and paths must be NUL-free byte strings so a program can
    actually name them.  (Bounding clauses on bytes are enforced by the
    `byte` type.) -/
def valid_fs (fs0 : Fs) : Prop :=
  fs_sorted fs0 = true ∧ ∀ pf ∈ fs0, BitVec.ofInt 8 0 ∉ pf.1

/-- The byte '/', the one byte this file has to interpret.

    Paths are uninterpreted here (see the header), and the separator's
    MEANING lives in `Sys.Fs.Namei` — `path_has_slash`, `dir_prefixb`
    and the trailing-separator tests are all there.  What is needed at
    this rung is only the byte itself, for `key_is_relative` below, and
    that file sits above this one, so the constant is spelled here too.
    The two are pinned equal where the second is defined
    (`Sys.Fs.Namei.slash_byte_is_path_slash_byte`), so moving either is a
    compile error rather than a silent divergence. -/
def path_slash_byte : byte := BitVec.ofInt 8 47

/-- A key is CWD-RELATIVE when it does not begin with the separator.

    THE EMPTY KEY COUNTS AS RELATIVE.  It begins with nothing, so it
    begins with no '/'; and it is a key no program can name anyway
    (`Uaccess.read_cstr` of an empty pathname is the -ENOENT every path
    spec answers before it looks anything up), so admitting it costs no
    reachable behaviour and excluding it would be a clause about a key
    nothing reads.

    This is a statement about the FIRST byte and about nothing else: a
    key may still carry separators inside it ("a/b"), and that key is
    relative.  What "relative" buys is exactly the one thing the device
    arms need — such a key is not, and does not live under, an absolute
    path like "/dev/null". -/
def key_is_relative (p : path) : Prop :=
  match p with
  | [] => True
  | b :: _ => b ≠ path_slash_byte

/-- Every key of an image is cwd-relative.

    THIS IS NOT A CLAUSE OF `valid_fs`, and the reason is the seeding.
    `Run.valid_input` reads `valid_fs` on `State.in_fs`, the image AFTER
    `State.fs_seed_tmp` has inserted each declared /tmp entry under the
    absolute key "/tmp/<name>"; a clause here would therefore make every
    input with a non-empty declaration invalid and silently remove those
    inputs from every theorem.  So this predicate is carried by
    `Run.valid_input` over `State.in_image_fs`, the PRE-SEED image, as a
    conjunct of its own — see the note on that definition.

    No boolean twin, because `valid_fs` beside it has none: the image
    predicates in this file are read by proofs, not computed by the
    checker. -/
def fs_keys_relative (fs : Fs) : Prop :=
  ∀ pf ∈ fs, key_is_relative pf.1

/-! ## File contents: byte-list read/write at an offset -/

/-- `firstn` is unchanged when its index is capped at the input list's
    length. -/
theorem firstn_min_length {A : Type} (n : Nat) (l : List A) :
    List.take (min n l.length) l = List.take n l := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-- The file's bytes from `off` onward, counted down IN `Int` against the
    list rather than through a `Nat` index.

    This exists so that no read builds `word_to_nat off`, and that is
    load-bearing rather than an optimization.  `word_to_nat` is
    `Z.to_nat` (BvBase), and the extracted checker keeps `nat` as unary
    Peano — Checks/Extraction.v imports ExtrOcamlZBigInt, which realizes
    `Z` with zarith and leaves `nat` alone — so `word_to_nat off` costs
    one OCaml stack frame per unit of `off`, and an lseek can put `off`
    anywhere below 2^63.  `skipn` would stop at the end of the list, but
    only after that numeral had been built.

    Recursing on the LIST instead bounds the work by the file rather
    than by the offset, and the recursive call is in tail position, so
    the extracted form runs in constant stack.  `file_from_skipn` proves
    it equal to the `skipn` it replaces, so nothing downstream has to
    know it is here. -/
def file_from (data : List byte) (off : Int) : List byte :=
  match data with
  | [] => []
  | _ :: tl => if off ≤ 0 then data else file_from tl (off - 1)

theorem file_from_skipn : ∀ (data : List byte) (off : Int),
    0 ≤ off → file_from data off = List.drop off.toNat data := by
  intro data
  induction data with
  | nil => intro off _; rw [List.drop_nil]; exact file_from.eq_1 off
  | cons b tl ih =>
    intro off hoff
    simp only [file_from]
    by_cases h : off ≤ 0
    · rw [ite_eq_left h]
      have h0 : off = 0 := by omega
      rw [h0]
      rfl
    · rw [ite_eq_right h]
      rw [ih (off - 1) (by omega)]
      have hsucc : off.toNat = (off - 1).toNat + 1 := by omega
      rw [hsucc, List.drop_succ_cons]

/-- Read up to `count` bytes starting at `off`; truncated at end-of-file
    (this is where a file read returns fewer bytes than asked, and 0
    bytes at or past the end).

    NEITHER argument reaches `Nat` unbounded.  `off` does not cross at
    all: `file_from` walks the file in `Int`, so a read is not charged
    for how far out it seeks.  `count` crosses only after being capped
    at what is left of the file, so a vectored read may name the whole
    `State.MAX_RW_COUNT` aggregate without building that numeral — a
    caller-side bound such as `Uaccess.rw_bytes_max` is then a statement
    about the transfer, not the only thing standing between the checker
    and its stack.  `file_read_unguarded` proves the pair is
    extensionally the ordinary `firstn`/`skipn` definition. -/
def file_read (data : List byte) (off count : word) : List byte :=
  let rest := file_from data (word_to_nat off : Int)
  List.take (word_to_nat_bounded count rest.length) rest

theorem file_read_unguarded : ∀ (data : List byte) (off count : word),
    file_read data off count
      = List.take (word_to_nat count) (List.drop (word_to_nat off) data) := by
  intro data off count
  simp only [file_read]
  rw [word_to_nat_bounded_eq_min, firstn_min_length, file_from_skipn]
  · simp
  · exact Int.natCast_nonneg _

/-- Overwrite `bs` at offset `off`, extending the file if needed.  A write
    of a NONEMPTY `bs` past the current end zero-fills the gap
    (sparse-file semantics).

    A zero-length write leaves the file untouched, as on Linux: `write(fd,
    buf, 0)` on a regular file transfers nothing and never extends the
    file, even when the fd's offset sits past end-of-file (an lseek can
    put it there).  Without the `[]` arm the padding below would zero-
    extend the file out to `off` on a write that Linux makes no change
    for.  For `off <= length data` the two arms agree, so this is exactly
    the past-EOF corner. -/
def file_write (data : List byte) (off : word) (bs : List byte) : List byte :=
  match bs with
  | [] => data                                -- zero-length write: no effect
  | _ :: _ =>
      let padded :=
        data ++ List.replicate (word_to_nat off - data.length) (BitVec.ofInt 8 0)
      List.take (word_to_nat off) padded
        ++ bs ++ List.drop (word_to_nat off + bs.length) padded

/-- Set the file's length to exactly `len`: a SHRINK drops the tail, a
    GROW zero-fills out to the new length (`ftruncate`; see
    `Open.ftruncate_spec`).  Both directions are one expression — for
    `len <= length data` the `repeat` is empty (its count is a `Nat`
    subtraction), and for `len >= length data` the `firstn` is the whole
    file.

    Linux makes the grown region a HOLE rather than allocating it, but a
    hole reads back as zero bytes (`truncate_setsize` in mm/truncate.c
    zeroes the partial tail folio through `folio_zero_range`, and the
    read path materializes an unmapped block as zeros; Linux v6.1
    through v6.12), so a byte list of zeros is the right content — it is
    the representation that differs, not the observation.

    `word_to_nat len` is built in full here, exactly as `file_write`
    builds `word_to_nat off`, and NOTHING IN THIS DEFINITION BOUNDS IT.
    What bounds it is the guard that all three of its call sites apply
    first — `Open.ftruncate_spec`, `Checks.Sys.Fs.Open.check_ftruncate`
    and `Checks.Witness.Fs.Open.ftruncate_witness`, which agree arm for
    arm: `Open.modeled_truncate_gap` admits a grow only while
    `len <= length data + rw_bytes_max`, and a shrink has
    `len <= length data` outright, so on both sides the numeral is
    bounded by the file itself plus a constant.  The
    `word_to_nat_bounded` trick `file_read` uses does not apply — capping
    the `firstn` by `length data` would be invisible, but the `repeat`
    count is exactly what a grow must add and capping THAT would drop
    the zeros — so there is no version of this that is safe without the
    call-site guard, and pretending otherwise with a half-cap would only
    hide where the bound really lives. -/
def file_truncate (data : List byte) (len : word) : List byte :=
  List.take (word_to_nat len) data
    ++ List.replicate (word_to_nat len - data.length) (BitVec.ofInt 8 0)

/-! ## Sanity checks (`by decide`) -/

-- equality and order on paths
example : path_eqb [0x61, 0x62] [0x61, 0x62] = true := by decide
example : path_eqb [0x61] [0x62] = false := by decide
-- a shorter prefix sorts first
example : path_ltb [0x61] [0x61, 0x62] = true := by decide
example : path_ltb [0x62] [0x61, 0x62] = false := by decide
-- the separator byte is '/'
example : path_slash_byte = (0x2f : byte) := by decide

-- an empty image has no entry
example : fs_lookup ([] : Fs) [0x2f] = none := by decide

-- insert then look up: a hit, and a miss on another key
example : fs_lookup (fs_set [] [0x61, 0x62] [0x41]) [0x61, 0x62] = some [0x41] := by decide
example : fs_lookup (fs_set [] [0x61] [0x41]) [0x62] = none := by decide

-- replacing an existing key keeps a single entry
example : fs_set (fs_set [] [0x61] [0x41]) [0x61] [0x42] = [([0x61], [0x42])] := by decide

-- insertion places a key in sorted position
example : fs_set [([0x62], [0x42])] [0x61] [0x41]
    = [([0x61], [0x41]), ([0x62], [0x42])] := by decide

-- sortedness of a canonical image, and of its reverse
example : fs_sorted [([0x61], [0x41]), ([0x62], [0x42])] = true := by decide
example : fs_sorted [([0x62], [0x42]), ([0x61], [0x41])] = false := by decide

-- unlink drops exactly the named entry
example : fs_remove [([0x61], [0x41]), ([0x62], [0x42])] [0x61] = [([0x62], [0x42])] := by decide
example : fs_remove [([0x61], [0x41])] [0x62] = [([0x61], [0x41])] := by decide

-- reads truncate at end-of-file
example : file_read [0x61, 0x62, 0x63] 1 2 = [0x62, 0x63] := by decide
example : file_read [0x61, 0x62] 1 5 = [0x62] := by decide
example : file_read [0x61, 0x62] 2 1 = [] := by decide
example : file_read [] 0 4 = [] := by decide

-- a write inside the file overwrites; a write past EOF zero-fills the gap
example : file_write [0x61, 0x62] 0 [0x7a] = [0x7a, 0x62] := by decide
example : file_write [0x61] 3 [0x7a, 0x79] = [0x61, 0x00, 0x00, 0x7a, 0x79] := by decide
-- a zero-length write never extends the file
example : file_write [0x61] 5 [] = [0x61] := by decide

-- truncate shrinks by dropping the tail, and grows by zero-filling
example : file_truncate [0x61, 0x62, 0x63] 2 = [0x61, 0x62] := by decide
example : file_truncate [0x61] 3 = [0x61, 0x00, 0x00] := by decide
example : file_truncate [0x61, 0x62] 2 = [0x61, 0x62] := by decide

end LinuxSem.LinuxProcessSem.Fs
