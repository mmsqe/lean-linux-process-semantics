/-
  * Common.LibWritev — `writev` to a channel fd with SHORT WRITES, as a shape node.

  Image-independent (Section over `segs`).

  musl's `__stdio_write` flushes a FILE with

      writev(f->fd, iov, iovcnt)     iov = [{f->wbase, f->wpos - f->wbase}, {buf, len}]

  where (musl 1.2.6) an EMPTY first iovec is dropped before the first call
  (`iovcnt = 1`, `iov = &iovs[1]`), and the retry loop re-issues the call on
  the undelivered remainder.

  THE SPEC (`ReadWrite.writev_spec`): on a channel fd the kernel delivers a
  NONDETERMINISTIC NONEMPTY PREFIX of the gathered bytes `bs = bs1 ++ bs2` —
  any `k` with `1 <= k <= length bs` — emitting `map (WriteEv fd) (firstn k bs)`
  and returning `k`; memory and model are unchanged.  The vector must be fully
  readable (iovec array and both buffers: then the gatherable prefix is the
  whole flattening) AND inside the user address space (`access_okb`, i.e.
  `base + len <= TASK_SIZE` for the array and for every buffer — the import
  path tests each range before it reads it), its total must be `>= 1` (a zero
  total is the degenerate `ret_only 0`, see `rz_writev1_zero`),
  `<= rw_bytes_max` (else UNMODELED — kept symbolic) and `<= 2^30` (below the
  kernel's `MAX_RW_COUNT` clamp and the error-encoding range).

  Provided:
  - `writev_check`        : the checker's exact answer family at the ecall;
  - `rz_writev_pending`   : the node at the pending state, continuation
                            quantified over the delivered length `k` AND
                            allowed to depend on it (shape `t_alt (fun i :
                            wr_index bs => t_emit (map (WriteEv fd) (firstn i
                            bs)) (T i))`);
  - `rz_writev2` / `rz_writev1` : the `mkst`/`getr` forms for iovcnt 2 / 1;
  - `rz_writev2_wall` / `rz_writev1_wall` : the packaged form the
    `__stdio_write` LOOP proof uses: if after every delivery `k` the rest of
    the loop realizes `t_emit (map (WriteEv fd) (skipn k bs)) K`, the call site
    realizes `t_emit (map (WriteEv fd) bs) K` — short writes are invisible in
    the trace (`ShapeAlg.t_alt_wall`);
  - `rz_writev2_ch` : the full-delivery special case as a plain continuation
    (`t_write_ch`);
  - `rz_writev1_zero` : the degenerate zero-total call (ret 0, no event);
  - `t_alt_wall_nat` : the same trace identity indexed by a bare `nat` range
    instead of `wr_index`.

  NOTES
  ==========

  (1) NAMES.  `Z` is `Int`, `N`/`nat` are
      `Nat`, `word` is `BitVec 64` and `byte` is `BitVec 8`.
  (2) MISSING MODULES.  None of those is in this tree
      yet, and the missing pieces are not only proofs but DEFINITIONS:
      * the executable checker `check_syscall` / `CheckOk` / `CheckReject` /
        `check_writev` and its soundness/completeness lemmas
        (`check_syscall_ok_iff`, `check_syscall_err_iff`) — the whole
        `Checks/` layer, 65k lines, an explicit non-goal for now
;
      * the shape algebra `TSet` / `t_eq` / `t_emit` / `t_alt` / `wr_index` /
        `wr_full` / `t_write_ch` / `t_alt_wall` / `realizes` / `node_ok`
        (`Common/ShapeAlg`);
      * the overlay-read layer `rdn` / `seg_rom` (`Common/PropExec`) and its
        bridges `read_bytes_map_read_byte` (`Common/CatSim`),
        `ms_read_bytes_rdn` (`Common/CatExec`), `le_word_v` (`PropExec`);
      * the count/`Int` kit `u64_range`, `u64_lit` (`Common/PropExec`).
      So that every part of THIS file that does not need the checker can still
      be stated and typechecked, everything this file uses from those modules
      is reproduced in the delimited "PREREQUISITES" sections below: faithful
      copies of exactly the definitions and lemmas, each annotated with its
       home, in this file's namespace so they cannot collide with the
      real modules when those land.
      SOME OF THOSE MODULES HAVE SINCE LANDED and the copies are now
      redundant.  Mechanical replacement, when the integrator wires this file
      into the root module:

        this file                         real module (already in the tree)
        --------------------------------  ---------------------------------
        `seg_rom`, `rdn`, `rdn_length`,   `Common/PropExec.lean`
        `le_word_v`, `u64_range`
        `bytes_le_to_Z_8`                 `Common/PropExec.lean` is expected
                                          to grow it (it is currently proved
                                          from the `BvBase` byte recursion
                                          here, like `Sys/Uapi.lean` does)
        `read_bytes_map_read_byte`        `Common/CatSim.lean`
        `ms_read_bytes_rdn`               `Common/CatExec.lean`
        `is_prefix_app_mono`              `Common/CatSim.lean`
        `is_prefix_app_r`,                `Common/ShapeAlg.lean` (not yet
        `is_prefix_app_split`,            stated; `AsanAcct.lean` likewise
        `is_prefix_nil_r`                 copies `ShapeAlg.node_ok` verbatim)
        `TSet`, `t_eq`, `t_emit`, `t_alt`, `Common/ShapeAlg.lean` (not yet
        `t_nil`, `t_alt2`, `wr_index`,     stated)
        `wr_full`, `t_write_ch`,
        `t_emit_nil_eq`, `t_alt_wall`,
        `node_ok`, `realizes`,
        `realizes_nonempty`
      The two declarations whose STATEMENTS mention the shape algebra
      (`t_alt_wall_nat`, `rz_wall`) must be re-stated against
      `Common.ShapeAlg`'s `t_emit`/`t_alt`/`t_eq`/`realizes` at that point:
      their proofs are the ones below, unchanged.
  (3) EIGHT OF NINE NOW PROVED; ONE STILL DEFERRED.  When this file was
      first stated the executable checker (`Checks/ExecutableSpecs`,
      `check_syscall`, `Checks.Sys.Fs.ReadWrite.check_writev`,
      `check_syscall_ok_iff` / `check_syscall_err_iff`) did not exist and the
      nine declarations below could not even be stated.  It has since
      landed, so eight of the nine are proved here AT the
      statements -- `check_syscall_writev`, `writev_check`,
      `rz_writev_pending`, `rz_writev2`, `rz_writev1`, `rz_writev2_wall`,
      `rz_writev1_wall`, `rz_writev2_ch` -- on top of two new prerequisite
      blocks: PREREQUISITES (C) below (the slice of `Common/AgentNodes`,
      `Common/Nodes` and `Common/ShapeAlg` those proofs need) and
      `Common/CatSim`'s two `apply_effect` lemmas.
      Only `rz_writev1_zero` -- the degenerate zero-total `writev(fd, [{b1,
      0}], 1)` -- is still deferred; its exact statement is at the end of
      this file.  It needs no new idea, only the single-descriptor import
      reduction (`import_iovecs`'s `nr_segs == 1` short circuit at a
      zero-length descriptor) and the `check_ret_only_copyins` inversion.
      This file still has no proof holes and no escape hatches (AGENTS.md,
      ground rule 3).
  (4) WHAT WAS IMPORTED, AND WHAT IS STILL A COPY.  `Common/PropExec.lean`
      and `Checks/ExecutableSpecs.lean` are now imported: the state
      vocabulary `mkst`/`getr`/`regupd`/`v_addi`/`step_ecall` is
      `PropExec`'s and `check_syscall` is `ExecutableSpecs`'s.
      `Common/SpinAlg.lean` also holds a copy of the shape algebra, but its
      `realizes` is SpinAlg's own inductive and PREREQUISITES (A)'s copy is
      what every statement here (and in this file's consumers) names, so the
      copies are KEPT unchanged.  The five primitives the new nodes need on
      top of them -- `mkCfg`, `sstep_instr_inv`, `node_instr`, `rz_silent1`,
      `rz_step` -- are copied into PREREQUISITES (C), each annotated with its
       home.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Checks.ExecutableSpecs

set_option autoImplicit false

namespace LinuxSem.Common.LibWritev

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.LinuxProcessSem.Sys.Syscall (fd32 fd32_id w_is0 w_is0_pos)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (iovcnt32)
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.ReadWrite (check_writev)

/-  ambient `FPState` instance (`Local Instance libwritev_fx`):
   `PropExec.mkst`'s FP half is a typeclass field, and `LibWritev` pins
   it to the process-entry one, so the `PropExec` step lemmas and this
   file's `mkst` states are stated at the same shape. -/
local instance libwritev_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/-! The `PropExec` state/instruction vocabulary `LibWritev` writes
    `mkst`/`getr`/`regupd`/`v_addi`/`step_ecall` in.  The memory layer
    (`seg_rom`, `rdn`) is this file's own copy, in PREREQUISITES (B), so it
    is deliberately NOT opened here. -/
open LinuxSem.Common.PropExec (mkst getr regupd v_addi step_ecall
  arg_reg_0 arg_reg_1 arg_reg_2 getr_nz)

/-! =========================================================================
    PREREQUISITES (A) — the shape algebra, `Common/ShapeAlg`
    =========================================================================

    Not part of `LibWritev`: the slice of the shape algebra that
    `LibWritev` consumes.  Delete this section when `Common/ShapeAlg.lean`
    lands. -/

/-! ## Prefix lemmas (`Common/ShapeAlg`, `Common/CatSim`) -/

theorem is_prefix_app_r {A : Type} (l m a : List A)
    (H : is_prefix a l) : is_prefix a (l ++ m) := by
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

theorem is_prefix_app_mono {A : Type} (l a b : List A)
    (H : is_prefix a b) : is_prefix (l ++ a) (l ++ b) := by
  induction l with
  | nil => exact H
  | cons x l ih => exact ⟨rfl, ih⟩

theorem is_prefix_app_split {A : Type} (l a b : List A)
    (H : is_prefix b (l ++ a)) :
    is_prefix b l ∨ ∃ b', b = l ++ b' ∧ is_prefix b' a := by
  induction l generalizing b with
  | nil => exact Or.inr ⟨b, rfl, H⟩
  | cons x l ih =>
    cases b with
    | nil => exact Or.inl (is_prefix_nil _)
    | cons y b =>
      obtain ⟨rfl, H'⟩ := H
      rcases ih b H' with Hp | ⟨b', rfl, Hp⟩
      · exact Or.inl ⟨rfl, Hp⟩
      · exact Or.inr ⟨b', rfl, Hp⟩

theorem is_prefix_nil_r {A : Type} (a : List A) (H : is_prefix a []) : a = [] := by
  cases a with
  | nil => rfl
  | cons _ _ => exact False.elim H

/-! ## The shape algebra (`Common/ShapeAlg`, LAYER 1) -/

/-- A shape.  Intended invariant (established for every shape a configuration
    realizes, see `realizes_nonempty` / `realizes_pclosed`): nonempty and
    prefix-closed. -/
abbrev TSet : Type := List event → Prop

/-- Extensional equality of shapes. -/
def t_eq (T T' : TSet) : Prop := ∀ tr, T tr ↔ T' tr

theorem t_eq_refl (T : TSet) : t_eq T T := fun _ => Iff.rfl

theorem t_eq_sym (T T' : TSet) (H : t_eq T T') : t_eq T' T :=
  fun tr => (H tr).symm

theorem t_eq_trans (T1 T2 T3 : TSet) (H12 : t_eq T1 T2) (H23 : t_eq T2 T3) :
    t_eq T1 T3 :=
  fun tr => (H12 tr).trans (H23 tr)

/-- The terminated shape: only the empty trace. -/
def t_nil : TSet := fun tr => tr = []

/-- Emit a fixed block of events, then continue as `T`.  The left disjunct is
    what keeps the result prefix-closed: a run may be observed part-way
    through the block. -/
def t_emit (evs : List event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs ∨ ∃ tr', tr = evs ++ tr' ∧ T tr'

/-- Indexed nondeterministic choice. -/
def t_alt {I : Type} (f : I → TSet) : TSet := fun tr => ∃ i, f i tr

/-- Binary choice. -/
def t_alt2 (A B : TSet) : TSet := fun tr => A tr ∨ B tr

/-- The index type of a single channel write's resolutions: the delivered
    length, any nonempty prefix of the buffer.  (For an empty buffer the type
    is EMPTY — the model EFAULTs an empty readable prefix, so no realized
    shape ever contains one.) -/
def wr_index (buf : List byte) : Type := { n : Nat // 1 ≤ n ∧ n ≤ buf.length }

/-- The full delivery, as a member of `wr_index`. -/
def wr_full (buf : List byte) (Hnb : 1 ≤ buf.length) : wr_index buf :=
  ⟨buf.length, Hnb, Nat.le_refl _⟩

/-- A single `write(ch, ...)` of buffer `buf`: the environment delivers a
    chosen nonempty prefix, then the continuation. -/
def t_write_ch (ch : word) (buf : List byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf => t_emit ((buf.take i.1).map (event.WriteEv ch)) T)

/-- A shape prefixed by no events is that shape (given nonemptiness, which
    every realized shape has). -/
theorem t_emit_nil_eq (T : TSet) (H0 : T []) : t_eq (t_emit [] T) T := by
  intro tr
  unfold t_emit
  constructor
  · rintro (Hp | ⟨tr', rfl, HT⟩)
    · rw [is_prefix_nil_r tr Hp]; exact H0
    · simpa using HT
  · intro HT
    exact Or.inr ⟨tr, rfl, HT⟩

/-- A single retry-loop write node collapses to one `t_emit` of the whole
    buffer: the per-delivery alternatives denote the same set. -/
theorem t_alt_wall (ch : word) (rest : List byte) (T : TSet)
    (_HT : T []) (Hnb : 1 ≤ rest.length) :
    t_eq (t_alt (fun i : wr_index rest =>
            t_emit ((rest.take i.1).map (event.WriteEv ch))
                   (t_emit ((rest.drop i.1).map (event.WriteEv ch)) T)))
         (t_emit (rest.map (event.WriteEv ch)) T) := by
  intro tr
  constructor
  · rintro ⟨⟨n, hn1, hn2⟩, Hi⟩
    rcases Hi with Hp | ⟨tr1, rfl, Hi⟩
    · refine Or.inl ?_
      have hsplit : rest.map (event.WriteEv ch)
          = (rest.take n).map (event.WriteEv ch) ++ (rest.drop n).map (event.WriteEv ch) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact is_prefix_app_r _ _ _ Hp
    · rcases Hi with Hp | ⟨tr2, rfl, Ht⟩
      · refine Or.inl ?_
        have hsplit : rest.map (event.WriteEv ch)
            = (rest.take n).map (event.WriteEv ch) ++ (rest.drop n).map (event.WriteEv ch) := by
          rw [← List.map_append, List.take_append_drop]
        rw [hsplit]
        exact is_prefix_app_mono _ _ _ Hp
      · refine Or.inr ⟨tr2, ?_, Ht⟩
        simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · rintro (Hp | ⟨tr', rfl, Ht⟩)
    · refine ⟨wr_full rest Hnb, ?_⟩
      simp only [wr_full, List.take_length]
      exact Or.inl Hp
    · refine ⟨wr_full rest Hnb, ?_⟩
      simp only [wr_full, List.take_length, List.drop_length, List.map_nil]
      exact Or.inr ⟨tr', rfl, Or.inr ⟨tr', rfl, Ht⟩⟩

/-! ## Realization (`Common/ShapeAlg`, LAYER 2) -/

/-- The syscall/step boundary interface.  A node at configuration `c` is
    characterized by an index type `I` of RESOLUTIONS, the events each
    resolution emits, and the successor configuration each resolution reaches.
    `node_ok` says the set of admissible transitions is EXACTLY that — which in
    particular rules out `SError`, and hence rules out both faults and
    unmodeled configurations, at this node. -/
def node_ok (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config) : Prop :=
  (∀ i, sstep segs c (evs i) (.SNext (nx i))) ∧
  (∀ e st, sstep segs c e st → ∃ i, e = evs i ∧ st = .SNext (nx i))

/-- The one reachability relation. -/
inductive realizes (segs : List Segment) : config → TSet → Prop where
  | node {c : config} {I : Type} (evs : I → List event) (nx : I → config)
      (T : I → TSet) (i0 : I)
      (hnode : node_ok segs c I evs nx)
      (hcont : ∀ i, realizes segs (nx i) (T i)) :
      realizes segs c (t_alt (fun i => t_emit (evs i) (T i)))
  | halt {c : config} (h : m_halted c.cfg_model ≠ none) :
      realizes segs c t_nil
  | conseq {c : config} {T T' : TSet}
      (h : realizes segs c T) (heq : t_eq T T') :
      realizes segs c T'

/-- Every realized shape contains the empty trace. -/
theorem realizes_nonempty (segs : List Segment) (c : config) (T : TSet)
    (H : realizes segs c T) : T [] := by
  induction H with
  | node evs nx T i0 hnode hcont ih =>
    exact ⟨i0, Or.inl (is_prefix_nil _)⟩
  | halt h => rfl
  | conseq h heq ih => exact (heq []).mp ih

/-! =========================================================================
    LibWritev — image-independent prelude
    ========================================================================= -/

/-- `a + b` in `Int` form: the `bv` addition is the `Int` addition of the
    unsigned values, truncated to 64 bits by `Z_to_bv`. -/
theorem bv_add_Zform (a b : word) :
    a + b = BitVec.ofInt 64 ((a.toNat : Int) + (b.toNat : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  have h : ((a.toNat : Int) + (b.toNat : Int)) = ((a.toNat + b.toNat : Nat) : Int) := by
    omega
  rw [h]
  rfl

/-- `word_to_nat` of a small literal word is the literal. -/
theorem word_to_nat_Z (z : Int) (Hz1 : 0 ≤ z) (Hz2 : z < 2 ^ 64) :
    word_to_nat (BitVec.ofInt 64 z) = z.toNat := by
  unfold word_to_nat
  rw [BitVec.toNat_ofInt]
  have h2' : z < ((2 ^ 64 : Nat) : Int) := by
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    exact Hz2
  rw [Int.emod_eq_of_lt Hz1 h2']

theorem u64_roundtrip' (x : word) :
    BitVec.ofInt 64 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have h2' : (x.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    have := x.isLt
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    omega
  rw [Int.emod_eq_of_lt (by omega) h2']
  rfl

/-- `access_okb` from the one inequality the caller has
    (`Uaccess.access_okb_intro` takes the length as a word; the import path
    also asks it of `Int` lengths). -/
theorem access_okb_of_le (b : word) (n : Int)
    (_Hn : 0 ≤ n) (H : (b.toNat : Int) + n ≤ TASK_SIZE) :
    access_okb b n = true := by
  unfold access_okb
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor <;> omega

/-! =========================================================================
    PREREQUISITES (B) — bytes and overlay reads
    =========================================================================

    Not part of `LibWritev`: the slice of `Common/PropExec`,
    `Common/CatSim`, `Common/CatExec` and `BvBase` that `LibWritev`
    consumes.  Delete this section when those modules land. -/

/-! ## Little-endian byte round-trip (`Common/PropExec`, `BvBase`) -/

/- `BvBase`'s general `bytes_le_to_Z_of_le_bytes` round trip
   used to have no counterpart in `BvBase.lean`; it now does (proved at
   the bottom of that file from the `Nat` byte recursion), so the reason
   for keeping the 8-byte instance here is no longer absence: `LibWritev`
   needs it over `bytes_le_to_Nat`, and the same three `private` helpers
   `Sys/Uapi.lean`'s `struct stat` block carries, at the same statements,
   are what the local proof consumes. -/

/-- Splitting one byte off the front of a little-endian read: the byte is the
    low eight bits and the rest is shifted up by eight. -/
private theorem bytes_le_to_Nat_cons (b : byte) (rest : List byte) :
    bytes_le_to_Nat (b :: rest) = bytes_le_to_Nat rest * 256 + b.toNat := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [bytes_le_to_Nat]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb]
  simp [Nat.shiftLeft_eq]

/-- One limb of the modulus arithmetic below. -/
private theorem mod_mul_256_of (q r M : Nat) (hr : r < 256) (hM : 0 < M) :
    (256 * q + r) % (256 * M) = 256 * (q % M) + r := by
  have hqM : q % M < M := Nat.mod_lt _ hM
  have hrM : r < 256 * M := by omega
  rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt (by omega)]

/-- `Z_to_le_bytes`'s shift, at a `Nat`-valued argument. -/
private theorem int_shiftRight_8_natCast (m : Nat) :
    ((m : Int) >>> 8) = ((m / 256 : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.ofNat_ediv_ofNat]

/-- The low byte of a `Nat`, as `Z_to_le_bytes` encodes it. -/
private theorem toNat_ofInt_8_nat (m : Nat) :
    (BitVec.ofInt 8 (m : Int)).toNat = m % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_emod (Int.natCast_nonneg m) (by decide)]
  rw [show ((2 ^ 8 : Nat) : Int) = (256 : Int) by decide]
  simp

private theorem mod_mul_256 (x M : Nat) (hM : 0 < M) :
    x % (256 * M) = 256 * ((x / 256) % M) + x % 256 := by
  have h := mod_mul_256_of (x / 256) (x % 256) M (Nat.mod_lt _ (by decide)) hM
  rwa [Nat.div_add_mod] at h

/-- The round trip: reading back `k` little-endian bytes of `m` gives `m`
    truncated to `8k` bits. -/
theorem bytes_le_to_Nat_Z_to_le_bytes (k m : Nat) :
    bytes_le_to_Nat (Z_to_le_bytes k (m : Int)) = m % 2 ^ (8 * k) := by
  induction k generalizing m with
  | zero => simp [Z_to_le_bytes, bytes_le_to_Nat, Nat.mod_one]
  | succ k ih =>
    rw [Z_to_le_bytes, int_shiftRight_8_natCast m]
    rw [bytes_le_to_Nat_cons, ih (m / 256), toNat_ofInt_8_nat]
    have hM : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    rw [Nat.mul_comm (2 ^ (8 * k)) (2 ^ 8)]
    rw [show 2 ^ 8 = 256 by decide, mod_mul_256 m (2 ^ (8 * k)) hM]
    omega

/-- `PropExec.bytes_le_to_Z_8`: the 8 little-endian bytes of `v`
    read back as `v`'s unsigned value — what turns the byte list a `read_u64`
    decodes back into the word it came from. -/
theorem bytes_le_to_Z_8 (v : word) :
    bytes_le_to_Z (word_to_le_bytes 8 v) = (v.toNat : Int) := by
  unfold bytes_le_to_Z word_to_le_bytes
  rw [bytes_le_to_Nat_Z_to_le_bytes]
  rw [show 8 * 8 = 64 by decide, Nat.mod_eq_of_lt v.isLt]

/-- `PropExec.le_word_v`: a byte list whose little-endian value is a
    word's unsigned value decodes back to that word. -/
theorem le_word_v (bs : List byte) (v : word)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    le_bytes_to_word bs = v := by
  unfold le_bytes_to_word
  rw [Hv, u64_roundtrip']

/-! ## `Nat`/`Int` count kit (`Common/PropExec`) -/

/-- `u64_range`: every word's unsigned value is below `2^64`. -/
theorem u64_range (x : word) : (x.toNat : Int) < 2 ^ 64 := by
  have := x.isLt
  omega

/-- `u64_lit`: a small literal's unsigned value is the literal. -/
theorem u64_lit (z : Int) (h1 : 0 ≤ z) (h2 : z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt]
  have h2' : z < ((2 ^ 64 : Nat) : Int) := by
    rw [← show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from by decide]
    exact h2
  rw [Int.emod_eq_of_lt h1 h2']

/-! ## Overlay reads (`Common/PropExec`) -/

/-- The loaded segments as a read-only byte source. -/
def seg_rom (segs : List Segment) : word → Option byte :=
  fun addr =>
    match memory_read segs addr 1 with
    | some (b :: _) => some b
    | _ => none

/-- Read `n` bytes starting at `a`: each byte from the overlay `mem` if
    present, else from the loaded segments; fail on any miss. -/
def rdn (segs : List Segment) (mem : word → Option byte) (a : word) :
    Nat → Option (List byte)
  | 0 => some []
  | n + 1 =>
    match (match mem a with | some b => some b | none => seg_rom segs a) with
    | some b =>
      match rdn segs mem (a + 1) n with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- `rdn` returns exactly the number of bytes it was asked for. -/
theorem rdn_length (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte), rdn segs mem a n = some bs → bs.length = n := by
  induction n with
  | zero =>
    intro a bs H
    simp only [rdn, Option.some.injEq] at H
    subst H; rfl
  | succ n ih =>
    intro a bs H
    simp only [rdn] at H
    split at H
    · rename_i b hb
      split at H
      · rename_i rest hrest
        simp only [Option.some.injEq] at H
        subst H
        simp only [List.length_cons, ih (a + 1) rest hrest]
      · exact absurd H (by simp)
    · exact absurd H (by simp)

/-! ## Memory-read bridges (`Common/CatSim`, `Common/CatExec`) -/

/-- `read_bytes_map` over `ms_read_byte` is `ms_read_bytes`. -/
theorem read_bytes_map_read_byte (ms : machine_state) (a len : word) :
    read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len := by
  rw [read_bytes_map_eq]
  unfold ms_read_bytes
  have key : ∀ (k : Nat) (a : word),
      read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      simp only [read_bytes_aux, ms_read_bytes_aux]
      rw [ih]
      cases ms_read_byte ms a <;> rfl
  exact key _ _

/-- The same walk through `rdn`. -/
theorem ms_read_bytes_aux_rdn (segs : List Segment) (ms : machine_state) (n : Nat) :
    ∀ (addr : word), ms.ms_rom = seg_rom segs →
      ms_read_bytes_aux ms addr n = rdn segs ms.ms_mem addr n := by
  induction n with
  | zero => intro addr _; rfl
  | succ n ih =>
    intro addr Hrom
    have hbyte : ms_read_byte ms addr
        = (match ms.ms_mem addr with | some b => some b | none => seg_rom segs addr) := by
      unfold ms_read_byte
      rw [Hrom]
      rfl
    cases hm : ms.ms_mem addr with
    | some b =>
      simp only [ms_read_bytes_aux, rdn, hbyte, hm]
      exact congrArg (fun x => match x with
        | some rest => some (b :: rest) | none => none) (ih (addr + 1) Hrom)
    | none =>
      simp only [ms_read_bytes_aux, rdn, hbyte, hm]
      cases hr : memory_read segs addr 1 with
      | none => simp only [seg_rom, hr]
      | some l =>
        cases l with
        | nil => simp only [seg_rom, hr]
        | cons b r =>
          simp only [seg_rom, hr]
          exact congrArg (fun x => match x with
            | some rest => some (b :: rest) | none => none) (ih (addr + 1) Hrom)

/-- `ms_read_bytes` is `rdn` over the machine's own overlay. -/
theorem ms_read_bytes_rdn (segs : List Segment) (ms : machine_state)
    (addr len : word) (Hrom : ms.ms_rom = seg_rom segs) :
    ms_read_bytes ms addr len = rdn segs ms.ms_mem addr (word_to_nat len) :=
  ms_read_bytes_aux_rdn segs ms (word_to_nat len) addr Hrom

/-! =========================================================================
    The trace identity that makes short writes harmless
    ========================================================================= -/

/-- `ShapeAlg.t_alt_wall`, re-indexed by a plain `nat` with an explicit range
    guard (the spelling a loop proof by induction on the remainder finds
    convenient): choosing ANY nonempty delivered prefix and then emitting the
    rest is, as a trace set, emitting the whole buffer. -/
theorem t_alt_wall_nat (ch : word) (bs : List byte) (K : TSet)
    (HK : K []) (Hnb : 1 ≤ bs.length) :
    t_eq (t_alt (fun k : Nat =>
            fun tr => (1 ≤ k ∧ k ≤ bs.length) ∧
              t_emit ((bs.take k).map (event.WriteEv ch))
                     (t_emit ((bs.drop k).map (event.WriteEv ch)) K) tr))
         (t_emit (bs.map (event.WriteEv ch)) K) := by
  intro tr
  rw [← t_alt_wall ch bs K HK Hnb tr]
  unfold t_alt
  constructor
  · rintro ⟨k, Hk, Ht⟩
    exact ⟨⟨k, Hk⟩, Ht⟩
  · rintro ⟨⟨k, Hk⟩, Ht⟩
    exact ⟨k, Hk, Ht⟩

/-- The packaged consequence rule: a node delivering any nonempty prefix,
    each continuation emitting the corresponding remainder, realizes the full
    emission. -/
theorem rz_wall (segs : List Segment) (c : config) (ch : word) (bs : List byte)
    (K : TSet) (Hnb : 1 ≤ bs.length) (HK : K [])
    (H : realizes segs c (t_alt (fun i : wr_index bs =>
      t_emit ((bs.take i.1).map (event.WriteEv ch))
             (t_emit ((bs.drop i.1).map (event.WriteEv ch)) K)))) :
    realizes segs c (t_emit (bs.map (event.WriteEv ch)) K) :=
  realizes.conseq H (t_alt_wall ch bs K HK Hnb)

/-! =========================================================================
    The iovec layer (`Section WithSegs`)
    ========================================================================= -/

section WithSegs

variable (segs : List Segment)

/-- Read an 8-byte word through `rdn` and decode it. -/
theorem read_u64_rdn (ms : machine_state) (a v : word)
    (Hrom : ms.ms_rom = seg_rom segs)
    (H : rdn segs ms.ms_mem a 8 = some (word_to_le_bytes 8 v)) :
    read_u64 (ms_read_byte ms) a = some v := by
  unfold read_u64
  rw [read_bytes_map_read_byte, ms_read_bytes_rdn segs ms a (BitVec.ofInt 64 8) Hrom]
  have h8 : word_to_nat (BitVec.ofInt 64 8) = 8 := by decide
  rw [h8, H]
  simp only [Option.some.injEq]
  exact le_word_v _ _ (bytes_le_to_Z_8 v)

theorem read_bytes_map_rdn (ms : machine_state) (a n : word) (bs : List byte)
    (Hrom : ms.ms_rom = seg_rom segs)
    (H : rdn segs ms.ms_mem a (word_to_nat n) = some bs) :
    read_bytes_map (ms_read_byte ms) a n = some bs := by
  rw [read_bytes_map_read_byte, ms_read_bytes_rdn segs ms a n Hrom]
  exact H

/-- The iovec array at `iov` decodes to `iovs` (each entry: base, then length,
    8-byte little-endian; lengths below 2^63). -/
def iov_array (mem : word → Option byte) (iov : word) (iovs : List (word × word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8 = some (word_to_le_bytes 8 b) ∧
      rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8 = some (word_to_le_bytes 8 n) ∧
      (n.toNat : Int) < 2 ^ 63 ∧
      iov_array mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) r

theorem read_iovec_entry_of_array (ms : machine_state) (b n : word)
    (r : List (word × word)) (iov : word)
    (Hrom : ms.ms_rom = seg_rom segs)
    (Ha : iov_array segs ms.ms_mem iov ((b, n) :: r)) :
    read_iovec_entry (ms_read_byte ms) iov = .IovEntry b n := by
  obtain ⟨Hb, Hn, Hlt, _⟩ := Ha
  unfold read_iovec_entry
  rw [read_u64_rdn segs ms iov b Hrom Hb]
  rw [show iov + (8 : word) = BitVec.ofInt 64 ((iov.toNat : Int) + 8)
      from bv_add_Zform iov 8]
  rw [read_u64_rdn segs ms _ n Hrom Hn]
  dsimp only
  have hgt : ¬ (2 ^ 63 : Int) ≤ (n.toNat : Int) := by omega
  rw [ite_eq_right hgt]

theorem copy_iovecs_of_array (ms : machine_state) (iovs : List (word × word)) :
    ∀ (iov : word), ms.ms_rom = seg_rom segs →
      iov_array segs ms.ms_mem iov iovs →
      copy_iovecs_aux (ms_read_byte ms) iov iovs.length = .ImpOk iovs := by
  induction iovs with
  | nil => intro iov _ _; rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro iov Hrom Ha
    simp only [List.length_cons, copy_iovecs_aux]
    rw [read_iovec_entry_of_array segs ms b n rest iov Hrom Ha]
    obtain ⟨_, _, _, Hr⟩ := Ha
    rw [show iov + (16 : word) = BitVec.ofInt 64 ((iov.toNat : Int) + 16)
        from bv_add_Zform iov 16]
    rw [ih _ Hrom Hr]

/-- The source buffers: every entry's `len` bytes at `base` are readable. -/
def iov_bufs (mem : word → Option byte) (iovs : List (word × word))
    (bss : List (List byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = some bs ∧ iov_bufs mem r bss'
  | _, _ => False

theorem gather_of_bufs (ms : machine_state) (iovs : List (word × word)) :
    ∀ (bss : List (List byte)), ms.ms_rom = seg_rom segs →
      iov_bufs segs ms.ms_mem iovs bss →
      gather_iovecs (ms_read_byte ms) iovs = some bss.flatten := by
  induction iovs with
  | nil =>
    intro bss Hrom Hb
    cases bss with
    | nil => rfl
    | cons _ _ => exact False.elim Hb
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro bss Hrom Hb
    cases bss with
    | nil => exact False.elim Hb
    | cons bs bss' =>
      obtain ⟨H1, H2⟩ := Hb
      simp only [gather_iovecs, List.flatten_cons]
      rw [read_bytes_map_rdn segs ms b n bs Hrom H1, ih bss' Hrom H2]

theorem cap_iovecs_id (iovs : List (word × word)) :
    ∀ (left : Int), iovs_total iovs ≤ left → cap_iovecs_aux iovs left = iovs := by
  induction iovs with
  | nil => intro left _; rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    intro left H
    simp only [cap_iovecs_aux, iovs_total] at *
    have hnn := iovs_total_nonneg rest
    have hmin : min left (n.toNat : Int) = (n.toNat : Int) := by omega
    rw [hmin]
    rw [show (BitVec.ofInt 64 (n.toNat : Int)) = n from u64_roundtrip' n]
    rw [ih _ (by omega)]

/-- Every buffer lies inside the user address space — what the import path's
    per-segment `access_okb` asks (`base + len <= TASK_SIZE`). -/
def iov_bufs_ok (iovs : List (word × word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (b.toNat : Int) + (n.toNat : Int) ≤ TASK_SIZE ∧ iov_bufs_ok r

theorem iovs_access_okb_of_ok (iovs : List (word × word))
    (H : iov_bufs_ok iovs) : iovs_access_okb iovs = true := by
  induction iovs with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨b, n⟩ := hd
    obtain ⟨Hb, Hr⟩ := H
    simp only [iovs_access_okb, List.all_cons, Bool.and_eq_true]
    exact ⟨access_okb_intro b n Hb, ih Hr⟩

/-- The import path (`State.import_iovecs`): a readable, in-range vector of
    `1..1024` entries imports as itself. -/
theorem import_iovecs_of_array (ms : machine_state) (iovs : List (word × word))
    (iov : word) (Hrom : ms.ms_rom = seg_rom segs)
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs)
    (Hbok : iov_bufs_ok iovs) :
    import_iovecs (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int)) = .ImpOk iovs := by
  obtain ⟨Hc1, Hc2⟩ := Hcnt
  cases iovs with
  | nil => simp at Hc1
  | cons hd rest =>
    obtain ⟨b, n⟩ := hd
    cases rest with
    | nil =>
      -- ONE entry: `__import_iovec`'s `nr_segs == 1` short-circuit
      obtain ⟨Hb, Hn, Hlt, _⟩ := Harr
      obtain ⟨Hokb, _⟩ := Hbok
      simp only [List.length_cons, List.length_nil] at Hc1 Hc2 Hiok ⊢
      unfold import_iovecs
      have h1 : bv_eqb (BitVec.ofInt 64 ((1 : Nat) : Int)) (1 : word) = true := by
        rw [bv_eqb_eq]
        rfl
      rw [ite_eq_left h1]
      have hok16 : access_okb iov 16 = true :=
        access_okb_of_le iov 16 (by omega) (by omega)
      rw [hok16]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [read_iovec_entry_of_array segs ms b n [] iov Hrom ⟨Hb, Hn, Hlt, trivial⟩]
      dsimp only
      have hMAX : (0 : Int) ≤ MAX_RW_COUNT := by unfold MAX_RW_COUNT; decide
      have hokn : access_okb b (min (n.toNat : Int) MAX_RW_COUNT) = true :=
        access_okb_of_le b _
          (by have := Int.min_le_left (n.toNat : Int) MAX_RW_COUNT; omega)
          (by have hle := Int.min_le_left (n.toNat : Int) MAX_RW_COUNT; omega)
      rw [hokn]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    | cons hd2 rest2 =>
      -- TWO or more: the general `copy_iovecs_aux` + `access_ok` path
      obtain ⟨b2, n2⟩ := hd2
      obtain ⟨Hb, Hn, Hlt, Harr'⟩ := Harr
      obtain ⟨Hbok, Hbok'⟩ := Hbok
      generalize hL : ((b, n) :: (b2, n2) :: rest2).length = L at Hc1 Hc2 Hiok ⊢
      have hL2 : 2 ≤ L := by rw [← hL]; simp
      have hL1024 : L ≤ 1024 := Hc2
      have hL64 : ((L : Int)) < 2 ^ 64 := by
        have : ((1024 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by decide
        omega
      have hval : (BitVec.ofInt 64 ((L : Int))).toNat = L := by
        rw [u64_lit]
        · omega
        · omega
        · omega
      have hne1 : bv_eqb (BitVec.ofInt 64 ((L : Int))) (1 : word) = false := by
        have h : ¬ (BitVec.ofInt 64 (L : Int)) = (1 : word) := by
          intro heq
          have h3 := congrArg BitVec.toNat heq
          rw [hval] at h3
          simp at h3
          omega
        simpa [bv_eqb] using h
      have hne0 : bv_eqb (BitVec.ofInt 64 ((L : Int))) (0 : word) = false := by
        have h : ¬ (BitVec.ofInt 64 (L : Int)) = (0 : word) := by
          intro heq
          have h3 := congrArg BitVec.toNat heq
          rw [hval] at h3
          simp at h3
          omega
        simpa [bv_eqb] using h
      have hvalZ : (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int) = (L : Int) := by
        rw [hval]
      have hIOV : ¬ IOV_MAX < (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int) := by
        rw [hvalZ]
        show ¬ (1024 : Int) < (L : Int)
        omega
      have hok16 : access_okb iov (16 * (((BitVec.ofInt 64 ((L : Int))).toNat : Nat) : Int)) = true := by
        rw [hvalZ]
        apply access_okb_of_le
        · omega
        · exact Hiok
      have hcopy : copy_iovecs_aux (ms_read_byte ms) iov
            (word_to_nat (BitVec.ofInt 64 ((L : Int))))
          = .ImpOk ((b, n) :: (b2, n2) :: rest2) := by
        rw [show word_to_nat (BitVec.ofInt 64 ((L : Int))) = L from by
          unfold word_to_nat
          rw [hval]]
        rw [← hL]
        exact copy_iovecs_of_array segs ms ((b, n) :: (b2, n2) :: rest2) iov Hrom
          ⟨Hb, Hn, Hlt, Harr'⟩
      have hacc : iovs_access_okb ((b, n) :: (b2, n2) :: rest2) = true :=
        iovs_access_okb_of_ok _ ⟨Hbok, Hbok'⟩
      unfold import_iovecs
      have hg1 : ¬ (bv_eqb (BitVec.ofInt 64 ((L : Int))) (1 : word) = true) := by
        rw [hne1]; simp
      have hg0 : ¬ (bv_eqb (BitVec.ofInt 64 ((L : Int))) (0 : word) = true) := by
        rw [hne0]; simp
      rw [ite_eq_right hg1, ite_eq_right hg0, ite_eq_right hIOV]
      simp only [hok16, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hcopy]
      dsimp only
      rw [hacc]
      simp only [ite_true]

end WithSegs

/-! =========================================================================
    PREREQUISITES (C) — the pending-`ecall` state, `Common/AgentNodes`
    =========================================================================

    Not part of `LibWritev`: the slice of `Common/AgentNodes` that
    `LibWritev` consumes, so that `rz_writev1`/`rz_writev2`/
    `rz_writev1_zero` can be stated in the `mkst`/`getr` vocabulary the
    per-binary walk proofs use.  `Common/AgentNodes.lean` is not in this
    tree; delete this section when it lands. -/

/-- A configuration from its two halves . -/
abbrev mkCfg (ms : machine_state) (model : Model) : config := ⟨ms, model⟩

/-- Every admissible transition out of a raw instruction step with an empty
    lazy ledger is that step. -/
theorem sstep_instr_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (evs : List event) (st : step_to)
    (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hss : sstep segs (mkCfg ms model) evs st) :
    evs = [] ∧ st = .SNext (mkCfg ms' model) := by
  have hnl := mi_account_step_no_lazy segs ms model Hlazy
  cases Hss with
  | instr a b c d hh hsvc hacc =>
    rw [hnl, Hstep] at hacc
    obtain ⟨rfl, rfl⟩ := machine_result.MachineOk.inj hacc
    exact ⟨rfl, rfl⟩
  | instr_fault a b hh hsvc hacc => rw [hnl, Hstep] at hacc; simp at hacc
  | instr_unmodeled a b hh hsvc hacc => rw [hnl, Hstep] at hacc; simp at hacc
  | syscall a b c d e f g hh hsvc hspec hh' hmat => exact absurd hsvc (by simp [Hsvc])
  | syscall_materialization_fault a b c d e f hh hsvc hspec hh' hmat =>
      exact absurd hsvc (by simp [Hsvc])
  | exit a b c d e f g hh hsvc hspec hh' hk => exact absurd hsvc (by simp [Hsvc])
  | killed a b c d e f g hh hsvc hspec hk => exact absurd hsvc (by simp [Hsvc])
  | syscall_unmodeled a b c hh hsvc hspec => exact absurd hsvc (by simp [Hsvc])

/-- An ordinary instruction step is the `Unit`-indexed silent node.
 -/
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

/-- A silent `Unit`-indexed node collapses to its continuation.   -/
theorem rz_silent1 (segs : List Segment) (c c' : config) (T : TSet)
    (Hnode : node_ok segs c Unit (fun _ => []) (fun _ => c'))
    (Hc : realizes segs c' T) : realizes segs c T := by
  have h0 : T [] := realizes_nonempty segs c' T Hc
  refine realizes.conseq (c := c) (T := t_alt (fun _ : Unit => t_emit [] T)) ?_ ?_
  · exact realizes.node (fun _ => []) (fun _ => c') (fun _ => T) () Hnode
      (fun i => by cases i; exact Hc)
  · intro tr
    constructor
    · rintro ⟨i, Hi⟩
      cases i
      exact (t_emit_nil_eq T h0 tr).1 Hi
    · intro H
      exact ⟨(), (t_emit_nil_eq T h0 tr).2 H⟩

/-- Instruction steps. -/
theorem rz_step (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms')
    (Hc : realizes segs (mkCfg ms' model) T) : realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep) Hc

/-- The machine state sitting ON the `ecall` with `ms_svc_pending = some x8`,
    i.e. `RiscvSemantics.step` of `mkst regs pc mem rom` at an `ecall`
    (`step_ecall_epend`). -/
def epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : machine_state :=
  { ms_regs := regs,
    ms_fregs := (inferInstance : LinuxSem.Common.PropExec.FPState).fp_regs,
    ms_pc_val := pc,
    ms_svc_pending := some x8, ms_resv := none,
    ms_fcsr := (inferInstance : LinuxSem.Common.PropExec.FPState).fp_csr,
    ms_mem := mem, ms_rom := rom }

/-- The `ecall` instruction step lands in `epend`. -/
theorem step_ecall_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom)
      = .MachineOk (epend regs pc mem rom (getr regs 17)) := by
  rw [step_ecall segs regs pc mem rom w HF HE]
  rfl

theorem epend_svc (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_svc_pending = some x8 := rfl

/-- The syscall-argument views of the pending state are the `getr` reads of
    `a0`/`a1`/`a2`. -/
theorem ms_gpr_epend0 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((0 : Nat) : Int))) = getr regs 10
  rw [show BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) from arg_reg_0]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (10 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend1 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((1 : Nat) : Int))) = getr regs 11
  rw [show BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) from arg_reg_1]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (11 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend2 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((2 : Nat) : Int))) = getr regs 12
  rw [show BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) from arg_reg_2]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (12 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_mem_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_mem = mem := rfl

theorem ms_rom_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_rom = rom := rfl

/-- The post-syscall state of a return-only effect is the plain
    return-value update. -/
theorem adv_set_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 v : word) :
    advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
      = mkst (regupd regs 10 v) (v_addi pc 4) mem rom := by
  unfold set_gpr0 set_reg advance_past_svc epend mkst ms_pc regupd v_addi
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (10 : reg) 0 (by decide),
    ite_eq_right (by simp : ¬ (false = true)), bv_add_Zform]
  rw [show (BitVec.ofInt 64 4).toNat = 4 from by decide]
  rfl

/-- Enter the syscall node: the `ecall` instruction step itself. -/
theorem rz_sys (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hc : realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T) :
    realizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  rz_step segs (mkst regs pc mem rom) model (epend regs pc mem rom (getr regs 17)) T
    Hh Hlazy rfl (step_ecall_epend segs regs pc mem rom w HF HE) Hc

/-- The event a HALTING step appends: an exit's `ExitEv`, or — when the
    post-model is killed — the `KillEv` of `Run.sstep.killed`.  A killed
    model is halted, so the third arm below covers both steps with one
    `m_halted model' = Some code` witness; every caller refutes that arm
    from its own "no outcome halts" fact and never looks at the event. -/
def halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | some sig => .KillEv sig (m_fs m')
  | none => .ExitEv code (m_fs m')

/-- Inversion of one transition at a pending syscall, phrased through the
    checker.  Three `CheckOk` sub-cases: the ordinary step (into the
    MATERIALIZED post-model), the materialization fault, the exit. -/
theorem sstep_svc_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (e : List event) (st : step_to)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hss : sstep segs (mkCfg ms model) e st) :
    (∃ eff model' evs,
        check_syscall (sys_input segs ms x8) eff model = .CheckOk model' evs ∧
        (((∃ model'', m_halted model' = none ∧ e = evs ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' ∧
            st = .SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          ∨ (m_halted model' = none ∧ e = [] ∧
            materialize_model_accesses model' (syscall_effect_accesses eff) = none ∧
            st = .SError)
          ∨ (∃ code, m_halted model' = some code ∧ e = evs ++ [halt_ev model' code] ∧
            st = .SNext (mkCfg ms model')))))
    ∨ (∃ eff, check_syscall (sys_input segs ms x8) eff model = .CheckUnmodeled ∧
        e = [] ∧ st = .SError) := by
  cases Hss with
  | instr a b c d p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_fault a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | instr_unmodeled a b p5 p6 p7 => exact absurd p6 (by simp [Hsvc])
  | syscall a b c d mp mpp evs1 p8 p9 hspec p11 hmat =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      exact Or.inl ⟨d, mp, e, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inl ⟨mpp, p11, rfl, hmat, rfl⟩⟩
  | syscall_materialization_fault a b c d mp evs1 p7 p8 hspec p10 hmat =>
      rw [Hsvc] at p8
      obtain rfl := Option.some.inj p8
      exact Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inr (Or.inl ⟨p10, rfl, hmat, rfl⟩)⟩
  | exit a b c d mp evs1 code p8 p9 hspec p11 hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      refine Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
        Or.inr (Or.inr ⟨code, p11, ?_, rfl⟩)⟩
      rw [show halt_ev mp code = event.ExitEv code (m_fs mp) from by unfold halt_ev; rw [hk]]
  | killed a b c d mp evs1 sig p8 p9 hspec hk =>
      rw [Hsvc] at p9
      obtain rfl := Option.some.inj p9
      cases hc : m_halted mp with
      | none =>
          rw [m_killed_of_m_halted_none mp hc] at hk
          simp at hk
      | some code =>
          refine Or.inl ⟨d, mp, evs1, (check_syscall_ok_iff _ _ _ _ _).mpr hspec,
            Or.inr (Or.inr ⟨code, hc, ?_, rfl⟩)⟩
          rw [show halt_ev mp code = event.KillEv sig (m_fs mp) from by unfold halt_ev; rw [hk]]
  | syscall_unmodeled a b c p4 p5 hspec =>
      rw [Hsvc] at p5
      obtain rfl := Option.some.inj p5
      exact Or.inr ⟨mkEffect (BitVec.ofInt 64 0) [] [], (check_syscall_err_iff _ _ _).mpr hspec,
        rfl, rfl⟩

/-- The forward direction every node uses: an admissible, non-halting
    checker answer into a model without lazy mappings is an `sstep`. -/
theorem sstep_of_check (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hc : check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs)
    (Hh' : m_halted m' = none) (Hlazy : m_vm_lazy m' = []) :
    sstep segs (mkCfg ms model) evs
      (.SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')) := by
  refine .syscall ms model x8 eff m' m' evs Hh Hsvc ((check_syscall_ok_iff _ _ _ _ _).mp Hc) Hh' ?_
  rw [materialize_model_accesses_no_lazy m' (syscall_effect_accesses eff) Hlazy]

/-! =========================================================================
    `check_syscall` at sysno 66 is `check_writev`
    ========================================================================= -/

/-- The `DispatchCompute` lemma restated here (same proof), so this file does
    not import the dispatch tree and its `Progress` closure (a closure guard;
    the `RefNodes` idiom). -/
theorem check_syscall_writev (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : i.in_sysno.toNat = 66) :
    check_syscall i eff m
      = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have h : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table (i.in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_writev := by
    rw [H]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, h,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_writev]

/-! =========================================================================
    The syscall-input views of a raw `mkst`-side machine state
    ========================================================================= -/

theorem in_sysno_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem in_mem_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_mem = ms_read_byte ms := rfl

theorem in_arg0_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

theorem in_arg1_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := rfl

theorem in_arg2_si (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := rfl

/-! =========================================================================
    The checker at a writev ecall
    ========================================================================= -/

section WithSegsChecker

variable (segs : List Segment)

/-- The checker at a writev ecall on channel `fd` with a fully readable,
    in-range vector of total `tot` in `[1, min rw_bytes_max 2^30]`: the
    admissible answers are exactly the nonempty delivered prefixes. -/
theorem writev_check (ms : machine_state) (x8 : word) (model : Model)
    (fd : Int) (iov : word) (iovs : List (word × word)) (bss : List (List byte))
    (Hrom : ms.ms_rom = seg_rom segs)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (Hno : x8.toNat = 66)
    (H0 : ms_gpr ms 0 = BitVec.ofInt 64 fd)
    (H1 : ms_gpr ms 1 = iov)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 (iovs.length : Int))
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs)
    (Hbok : iov_bufs_ok iovs)
    (Hbufs : iov_bufs segs ms.ms_mem iovs bss)
    (Ht1 : 1 ≤ iovs_total iovs) (_Htmax : iovs_total iovs ≤ rw_bytes_max)
    (Ht30 : iovs_total iovs ≤ 2 ^ 30) :
    (bss.flatten.length : Int) = iovs_total iovs ∧
    ∀ eff, check_syscall (sys_input segs ms x8) eff model
      = match eff with
        | .mkEffectU ret [] [] [] [] ci =>
            if decide (1 ≤ (ret.toNat : Int))
               && decide ((ret.toNat : Int) ≤ iovs_total iovs)
               && !(addr_is_error_b ret) then
              if access_ranges_eqb ci
                   (import_iovecs_accesses (ms_read_byte ms) iov
                      (BitVec.ofInt 64 (iovs.length : Int))
                    ++ iov_prefix_accesses iovs ret.toNat)
              then .CheckOk model ((bss.flatten.take ret.toNat).map (.WriteEv (BitVec.ofInt 64 fd)))
              else .CheckReject
            else .CheckReject
        | _ => .CheckReject := by
  have Hg : gather_iovecs (ms_read_byte ms) iovs = some bss.flatten :=
    gather_of_bufs segs ms iovs bss Hrom Hbufs
  have Hlen : ((bss.flatten.length : Nat) : Int) = iovs_total iovs :=
    gather_iovecs_length (ms_read_byte ms) iovs bss.flatten Hg
  have hlennat : bss.flatten.length ≤ 2 ^ 30 := by
    have := Hlen; omega
  -- the gates in front of the answer family
  have hbsne : bss.flatten.length ≠ 0 := by omega
  have htotne : iovs_total iovs ≠ 0 := by omega
  refine ⟨Hlen, ?_⟩
  intro eff
  rw [check_syscall_writev (sys_input segs ms x8) eff model (by rw [in_sysno_si]; exact Hno)]
  rw [in_arg0_si, in_arg1_si, in_arg2_si, H0, H1, H2]
  -- the fd argument survives `fd32` (it is below 2^32)
  have hfdv : (BitVec.ofInt 64 fd).toNat = fd.toNat :=
    u64_lit fd (by omega) (by omega)
  have hfd32 : (BitVec.ofInt 64 fd).toNat < 2 ^ 32 := by rw [hfdv]; omega
  rw [fd32_id _ hfd32]
  -- the count argument survives `iovcnt32`
  have hcntv : (BitVec.ofInt 64 ((iovs.length : Nat) : Int)).toNat = iovs.length :=
    u64_lit _ (by omega) (by omega)
  have hcnt32 : iovcnt32 (BitVec.ofInt 64 ((iovs.length : Nat) : Int))
      = BitVec.ofInt 64 ((iovs.length : Nat) : Int) := by
    simp only [iovcnt32, LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32]
    apply BitVec.eq_of_toNat_eq
    rw [hcntv]
    show (BitVec.ofNat 64 (iovs.length % 2 ^ 32)).toNat = iovs.length
    rw [Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  unfold check_writev
  rw [Hfd]
  dsimp only
  rw [show w_is0 (BitVec.ofInt 64 fd) = false from w_is0_pos _ (by rw [hfdv]; omega)]
  rw [in_mem_si]
  rw [hcnt32]
  rw [import_iovecs_of_array segs ms iovs iov Hrom Hcnt Hiok Harr Hbok]
  dsimp only
  -- the `cap_iovecs` clamp is the identity at this total
  have Hcap : cap_iovecs iovs = iovs := by
    unfold cap_iovecs
    exact cap_iovecs_id iovs MAX_RW_COUNT (by unfold MAX_RW_COUNT; omega)
  rw [Hcap]
  have hwg : writev_gathered (ms_read_byte ms) iovs = bss.flatten := by
    unfold writev_gathered
    rw [Hcap]
    exact gather_prefix_full (ms_read_byte ms) iovs bss.flatten Hg
  rw [hwg, Hlen]
  rw [show (iovs_total iovs == (0 : Int)) = false from beq_eq_false_iff_ne.mpr htotne,
      show (bss.flatten.length == 0) = false from beq_eq_false_iff_ne.mpr hbsne]
  simp only [Bool.false_eq_true, ite_false]
  have hlenv : (len_word bss.flatten).toNat = bss.flatten.length := by
    unfold len_word
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have herr : addr_is_error_b (len_word bss.flatten) = false := by
    unfold addr_is_error_b
    have h : ¬ (two_pow_64 - 4096 < ((len_word bss.flatten).toNat : Int)) := by
      rw [hlenv]; unfold two_pow_64; omega
    simp [h]
  rw [ite_eq_right (by rw [herr]; exact Bool.false_ne_true)]
  -- the answer family: only the no-write, no-copy effect reaches the gate
  cases eff with
  | mkEffectU ret ws zs us cs ci =>
    cases ws with
    | nil =>
      cases zs with
      | nil =>
        cases us with
        | nil =>
          cases cs with
          | nil => rfl
          | cons _ _ => rfl
        | cons _ _ => rfl
      | cons _ _ => rfl
    | cons _ _ => rfl

end WithSegsChecker

/-! =========================================================================
    `apply_effect` of a no-write effect is the plain return-value update
    ========================================================================= -/

/-- `Common/CatSim`'s `apply_effect_no_write`. -/
theorem apply_effect_no_write (ms : machine_state) (r : word) :
    apply_effect ms (mkEffect r [] []) = set_gpr0 ms r := by
  unfold apply_effect set_gpr0 mkEffect
  rfl

/-- `Common/CatSim`'s `apply_effect_copyins_no_write`: a recorded
    copy-in ledger changes neither the memory nor the machine state. -/
theorem apply_effect_copyins_no_write (ms : machine_state) (r : word)
    (copyins : List (word × Nat)) :
    apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r := by
  unfold apply_effect with_copyins set_gpr0 mkEffect
  rfl

/-! =========================================================================
    The node at the pending state
    ========================================================================= -/

section WithSegsPending

variable (segs : List Segment)

/-- The node at the pending state: resolutions = delivered lengths. -/
theorem rz_writev_pending (ms : machine_state) (x8 : word) (model : Model)
    (fd : Int) (iov : word) (iovs : List (word × word)) (bss : List (List byte))
    (T : Nat → TSet)
    (Hrom : ms.ms_rom = seg_rom segs)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31) (Hno : x8.toNat = 66)
    (H0 : ms_gpr ms 0 = BitVec.ofInt 64 fd) (H1 : ms_gpr ms 1 = iov)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 (iovs.length : Int))
    (Hcnt : 1 ≤ iovs.length ∧ iovs.length ≤ 1024)
    (Hiok : (iov.toNat : Int) + 16 * (iovs.length : Int) ≤ TASK_SIZE)
    (Harr : iov_array segs ms.ms_mem iov iovs) (Hbok : iov_bufs_ok iovs)
    (Hbufs : iov_bufs segs ms.ms_mem iovs bss)
    (Ht1 : 1 ≤ iovs_total iovs) (Htmax : iovs_total iovs ≤ rw_bytes_max)
    (Ht30 : iovs_total iovs ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bss.flatten.length →
            realizes segs
              (mkCfg (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 (k : Int)))) model)
              (T k)) :
    realizes segs (mkCfg ms model)
      (t_alt (fun i : wr_index bss.flatten =>
         t_emit ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  obtain ⟨Hlen, Hchk⟩ :=
    writev_check segs ms x8 model fd iov iovs bss Hrom Hfd Hfdr Hno H0 H1 H2 Hcnt Hiok
      Harr Hbok Hbufs Ht1 Htmax Ht30
  have hnb : 1 ≤ bss.flatten.length := by omega
  -- one delivery: the effect the checker admits, and its successor
  let effs : wr_index bss.flatten → SyscallEffect := fun i =>
    ⟨BitVec.ofInt 64 (i.1 : Int), [], [], [], [],
      import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
        ++ iov_prefix_accesses iovs i.1⟩
  have hstep (i : wr_index bss.flatten) :
      check_syscall (sys_input segs ms x8) (effs i) model
        = .CheckOk model ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) := by
    have hk1 : 1 ≤ i.1 := i.2.1
    have hk2 : i.1 ≤ bss.flatten.length := i.2.2
    have hkv : (BitVec.ofInt 64 (i.1 : Int)).toNat = i.1 :=
      u64_lit _ (by omega) (by omega)
    have hi30 : ((i.1 : Nat) : Int) ≤ 2 ^ 30 := by
      have h1 : ((bss.flatten.length : Nat) : Int) ≤ 2 ^ 30 := by rw [Hlen]; exact Ht30
      omega
    have hle : ((i.1 : Nat) : Int) ≤ iovs_total iovs := by
      rw [← Hlen]; omega
    have herr : addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)) = false := by
      unfold addr_is_error_b
      rw [hkv]
      exact decide_eq_false_iff_not.mpr (by unfold two_pow_64; omega)
    have h1 : decide (1 ≤ ((i.1 : Nat) : Int)) = true := by
      rw [decide_eq_true_eq]; omega
    have h2 : decide (((i.1 : Nat) : Int) ≤ iovs_total iovs) = true := by
      rw [decide_eq_true_eq]; exact hle
    have h3 : (!(addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)))) = true := by
      rw [herr]; rfl
    have hcond : ((decide (1 ≤ ((i.1 : Nat) : Int))
        && decide (((i.1 : Nat) : Int) ≤ iovs_total iovs)
        && !(addr_is_error_b (BitVec.ofInt 64 (i.1 : Int)))) = true) := by
      rw [h1, h2, h3]; rfl
    rw [Hchk]
    dsimp only [effs]
    rw [hkv, ite_eq_left hcond, ite_eq_left (access_ranges_eqb_refl _)]
  refine realizes.node (c := mkCfg ms model)
    (fun i : wr_index bss.flatten =>
      (bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)))
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)))) model)
    (fun i => T i.1) (wr_full bss.flatten hnb) ?_ (fun i => Hk i.1 i.2.1 i.2.2)
  constructor
  · intro i
    have hgoal := sstep_of_check segs ms model x8 (effs i) model
      ((bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)))
      Hh Hsvc (hstep i) Hh Hlazy
    rwa [show apply_effect ms (effs i)
          = set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)) from by
        dsimp only [effs]
        exact apply_effect_copyins_no_write ms _ _] at hgoal
  · intro e st hss
    have Hinv : ∀ (eff : SyscallEffect) (m' : Model) (ev : List event),
        check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
        ∃ i : wr_index bss.flatten,
          eff = effs i ∧ m' = model ∧
          ev = (bss.flatten.take i.1).map (.WriteEv (BitVec.ofInt 64 fd)) := by
      intro eff m' ev hc
      rw [Hchk] at hc
      cases eff with
      | mkEffectU ret ws zs us cs ci =>
        cases ws with
        | cons _ _ => simp at hc
        | nil =>
        cases zs with
        | cons _ _ => simp at hc
        | nil =>
        cases us with
        | cons _ _ => simp at hc
        | nil =>
        cases cs with
        | cons _ _ => simp at hc
        | nil =>
          dsimp only at hc
          -- the three gates, then the copy-in ledger, then the answer
          by_cases hgate : (decide (1 ≤ ((ret.toNat : Nat) : Int))
              && decide (((ret.toNat : Nat) : Int) ≤ iovs_total iovs)
              && !(addr_is_error_b ret)) = true
          · rw [ite_eq_left hgate] at hc
            by_cases hci : access_ranges_eqb ci
                (import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
                  ++ iov_prefix_accesses iovs ret.toNat) = true
            · rw [ite_eq_left hci] at hc
              cases hc
              have hg := hgate
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
              obtain ⟨⟨hg1, hg2⟩, _⟩ := hg
              have hci' := (access_ranges_eqb_eq ci _).mp hci
              refine ⟨⟨ret.toNat, by omega, ?_⟩, ?_, rfl, rfl⟩
              · omega
              · dsimp only [effs]
                rw [u64_roundtrip' ret, hci']
            · rw [ite_eq_right hci] at hc
              exact absurd hc (by simp)
          · rw [ite_eq_right hgate] at hc
            exact absurd hc (by simp)
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, harm⟩ | ⟨eff, hc, he, hst⟩
    · rcases harm with ⟨m'', hh', he, hmat, hst⟩ | ⟨hh', he, hmat, hst⟩
                     | ⟨code, hh', he, hks, hst⟩
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        subst heff
        rw [hm] at hmat
        subst hev
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        obtain rfl := Option.some.inj hmat
        refine ⟨i, he, ?_⟩
        rw [hst, show apply_effect ms (effs i)
              = set_gpr0 ms (BitVec.ofInt 64 (i.1 : Int)) from by
            dsimp only [effs]
            exact apply_effect_copyins_no_write ms _ _]
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        rw [hm] at hmat
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        simp at hmat
      · obtain ⟨i, heff, hm, hev⟩ := Hinv eff model' ev hc
        rw [hm] at hh'
        rw [Hh] at hh'
        simp at hh'
    · exfalso
      rw [Hchk] at hc
      cases eff with
      | mkEffectU ret ws zs us cs ci =>
        cases ws with
        | cons _ _ => simp at hc
        | nil =>
        cases zs with
        | cons _ _ => simp at hc
        | nil =>
        cases us with
        | cons _ _ => simp at hc
        | nil =>
        cases cs with
        | cons _ _ => simp at hc
        | nil =>
          dsimp only at hc
          by_cases hgate : (decide (1 ≤ ((ret.toNat : Nat) : Int))
              && decide (((ret.toNat : Nat) : Int) ≤ iovs_total iovs)
              && !(addr_is_error_b ret)) = true
          · rw [ite_eq_left hgate] at hc
            by_cases hci : access_ranges_eqb ci
                (import_iovecs_accesses (ms_read_byte ms) iov (BitVec.ofInt 64 (iovs.length : Int))
                  ++ iov_prefix_accesses iovs ret.toNat) = true
            · rw [ite_eq_left hci] at hc
              exact absurd hc (by simp)
            · rw [ite_eq_right hci] at hc
              exact absurd hc (by simp)
          · rw [ite_eq_right hgate] at hc
            exact absurd hc (by simp)


/-- ONE iovec (musl: nothing buffered, `iov = &iovs[1]`, `iovcnt = 1`). -/
theorem rz_writev1 (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int) (iov b1 n1 : word)
    (bs1 : List byte) (T : Nat → TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 1)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Hiok : (iov.toNat : Int) + 16 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int)) (_Htmax : (n1.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bs1.length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) (T k)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_alt (fun i : wr_index bs1 =>
         t_emit ((bs1.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  have hno : (getr regs 17).toNat = 66 := by
    rw [H17]; exact u64_lit 66 (by omega) (by omega)
  have hp : realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
      (t_alt (fun i : wr_index bs1 =>
         t_emit ((bs1.take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
    have hraw := rz_writev_pending segs (epend regs pc mem (seg_rom segs) (getr regs 17))
      (getr regs 17) model fd iov [(b1, n1)] [bs1] T
      rfl Hh Hlazy rfl Hfd Hfdr hno
      (by rw [ms_gpr_epend0]; exact H10)
      (by rw [ms_gpr_epend1]; exact H11)
      (by rw [ms_gpr_epend2, H12]; rfl)
      (by exact ⟨by simp, by simp⟩)
      (by simpa using Hiok)
      (by
        refine ⟨Rb1, Rn1, ?_, trivial⟩
        show (n1.toNat : Int) < 2 ^ 63
        omega)
      (by exact ⟨Hb1, trivial⟩)
      (by exact ⟨Rs1, trivial⟩)
      (by simpa [iovs_total] using Ht1) (by simpa [iovs_total] using _Htmax)
      (by simpa [iovs_total] using Ht30)
      (by
        intro k hk1 hk2
        rw [adv_set_epend]
        exact Hk k hk1 (by simpa using hk2))
    have hfl : ([bs1] : List (List byte)).flatten = bs1 := List.append_nil bs1
    rw [hfl] at hraw
    exact hraw
  exact rz_sys segs regs pc mem (seg_rom segs) model w _ Hh Hlazy HF HE hp


/-- From the `mkst` state on the ecall, TWO iovecs (musl: buffered bytes +
    the new data; the second may be empty, e.g. the final flush
    `f->write(f, 0, 0)` passes `[{wbase, n1}, {NULL, 0}]`).  The three
    `TASK_SIZE` premises are the import path's range tests: a binary's iovec
    array and buffers are stack, image or allocator addresses far below
    `State.TASK_SIZE` = 2^47, so each costs the caller one `omega`. -/
theorem rz_writev2 (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (T : Nat → TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) (T k)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_alt (fun i : wr_index (bs1 ++ bs2) =>
         t_emit (((bs1 ++ bs2).take i.1).map (.WriteEv (BitVec.ofInt 64 fd))) (T i.1))) := by
  have hno : (getr regs 17).toNat = 66 := by
    rw [H17]; exact u64_lit 66 (by omega) (by omega)
  -- the second descriptor sits at `iov + 16`, so its length at `iov + 24`
  have hTASK64 : TASK_SIZE < 2 ^ 64 := by unfold TASK_SIZE; decide
  have h16 : (BitVec.ofInt 64 ((iov.toNat : Int) + 16)).toNat = iov.toNat + 16 :=
    u64_lit _ (by omega) (by omega)
  have hat : (BitVec.ofInt 64 ((BitVec.ofInt 64 ((iov.toNat : Int) + 16)).toNat + 8))
      = BitVec.ofInt 64 ((iov.toNat : Int) + 24) := by
    rw [h16]
    congr 1
  have hraw := rz_writev_pending segs (epend regs pc mem (seg_rom segs) (getr regs 17))
    (getr regs 17) model fd iov [(b1, n1), (b2, n2)] [bs1, bs2] T
    rfl Hh Hlazy rfl Hfd Hfdr hno
    (by rw [ms_gpr_epend0]; exact H10)
    (by rw [ms_gpr_epend1]; exact H11)
    (by rw [ms_gpr_epend2, H12]; rfl)
    (by exact ⟨by simp, by simp⟩)
    (by simpa using Hiok)
    (by
      refine ⟨Rb1, Rn1, ?_, Rb2, ?_, ?_, trivial⟩
      · have : (n1.toNat : Int) < 2 ^ 63 := by omega
        simpa using this
      · exact hat.symm ▸ Rn2
      · show (n2.toNat : Int) < 2 ^ 63
        omega)
    (by exact ⟨Hb1, ⟨Hb2, trivial⟩⟩)
    (by exact ⟨Rs1, ⟨Rs2, trivial⟩⟩)
    (by simpa [iovs_total] using Ht1) (by simpa [iovs_total] using _Htmax)
    (by simpa [iovs_total] using Ht30)
    (by
      intro k hk1 hk2
      rw [adv_set_epend]
      exact Hk k hk1 (by simpa using hk2))
  have hfl : ([bs1, bs2] : List (List byte)).flatten = bs1 ++ bs2 := by
    simp
  rw [hfl] at hraw
  exact rz_sys segs regs pc mem (seg_rom segs) model w _ Hh Hlazy HF HE hraw

/-- The LOOP-facing corollary: if, after each delivery of `k` bytes, the
    remainder of `__stdio_write` (re-issue on the rest, then return)
    realizes "emit the undelivered suffix, then `K`", the call site realizes
    the full emission.  Short writes leave no trace. -/
theorem rz_writev2_wall (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (HK : K [])
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit (((bs1 ++ bs2).drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_emit ((bs1 ++ bs2).map (.WriteEv (BitVec.ofInt 64 fd))) K) := by
  -- the checker's own length guarantee pins the delivered total
  have L1 : bs1.length = n1.toNat := rdn_length segs mem n1.toNat b1 bs1 Rs1
  have L2 : bs2.length = n2.toNat := rdn_length segs mem n2.toNat b2 bs2 Rs2
  have hnb : 1 ≤ (bs1 ++ bs2).length := by
    rw [List.length_append, L1, L2]; omega
  refine rz_wall segs _ (BitVec.ofInt 64 fd) (bs1 ++ bs2) K hnb HK ?_
  exact rz_writev2 segs regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2
    (fun k => t_emit (((bs1 ++ bs2).drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok
    Hb1 Hb2 Ht1 _Htmax Ht30 Hk

/-- The same for ONE iovec. -/
theorem rz_writev1_wall (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int) (iov b1 n1 : word)
    (bs1 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 1)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Hiok : (iov.toNat : Int) + 16 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int)) (_Htmax : (n1.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) ≤ 2 ^ 30)
    (HK : K [])
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ bs1.length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model)
              (t_emit ((bs1.drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_emit (bs1.map (.WriteEv (BitVec.ofInt 64 fd))) K) := by
  have L1 : bs1.length = n1.toNat := rdn_length segs mem n1.toNat b1 bs1 Rs1
  have hnb : 1 ≤ bs1.length := by rw [L1]; omega
  refine rz_wall segs _ (BitVec.ofInt 64 fd) bs1 K hnb HK ?_
  exact rz_writev1 segs regs pc mem model w fd iov b1 n1 bs1
    (fun k => t_emit ((bs1.drop k).map (.WriteEv (BitVec.ofInt 64 fd))) K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rs1 Hiok
    Hb1 Ht1 _Htmax Ht30 Hk

/-- The FULL-delivery special case as a plain continuation: if the code
    after the syscall does not care how much was delivered (musl loops; this
    form is for callers that re-establish the same `K` from every
    post-state, e.g. by re-entering the loop), the shape is `t_write_ch`. -/
theorem rz_writev2_ch (regs : BvMap word) (pc : word) (mem : word → Option byte)
    (model : Model) (w : BitVec 32) (fd : Int)
    (iov b1 n1 b2 n2 : word) (bs1 bs2 : List byte) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 fd)
             = some (.FdChannel (BitVec.ofInt 64 fd)))
    (Hfdr : 0 < fd ∧ fd < 2 ^ 31)
    (H17 : getr regs 17 = BitVec.ofInt 64 66)
    (H10 : getr regs 10 = BitVec.ofInt 64 fd)
    (H11 : getr regs 11 = iov) (H12 : getr regs 12 = BitVec.ofInt 64 2)
    (Rb1 : rdn segs mem iov 8 = some (word_to_le_bytes 8 b1))
    (Rn1 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 8)) 8
             = some (word_to_le_bytes 8 n1))
    (Rb2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 16)) 8
             = some (word_to_le_bytes 8 b2))
    (Rn2 : rdn segs mem (BitVec.ofInt 64 ((iov.toNat : Int) + 24)) 8
             = some (word_to_le_bytes 8 n2))
    (Rs1 : rdn segs mem b1 n1.toNat = some bs1)
    (Rs2 : rdn segs mem b2 n2.toNat = some bs2)
    (Hiok : (iov.toNat : Int) + 32 ≤ TASK_SIZE)
    (Hb1 : (b1.toNat : Int) + (n1.toNat : Int) ≤ TASK_SIZE)
    (Hb2 : (b2.toNat : Int) + (n2.toNat : Int) ≤ TASK_SIZE)
    (Ht1 : 1 ≤ (n1.toNat : Int) + (n2.toNat : Int))
    (_Htmax : (n1.toNat : Int) + (n2.toNat : Int) ≤ rw_bytes_max)
    (Ht30 : (n1.toNat : Int) + (n2.toNat : Int) ≤ 2 ^ 30)
    (Hk : ∀ k : Nat, 1 ≤ k → k ≤ (bs1 ++ bs2).length →
            realizes segs
              (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
                (v_addi pc 4) mem (seg_rom segs)) model) K) :
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model)
      (t_write_ch (BitVec.ofInt 64 fd) (bs1 ++ bs2) K) := by
  unfold t_write_ch
  exact rz_writev2 segs regs pc mem model w fd iov b1 n1 b2 n2 bs1 bs2 (fun _ => K)
    HF HE Hh Hlazy Hfd Hfdr H17 H10 H11 H12 Rb1 Rn1 Rb2 Rn2 Rs1 Rs2 Hiok
    Hb1 Hb2 Ht1 _Htmax Ht30 Hk

end WithSegsPending


/-! =========================================================================
    REMAINING — the one declaration still deferred
    =========================================================================

    `rz_writev1_zero`, the degenerate zero-total `writev(fd, [{b1, 0}], 1)`
    that musl's `f->write(f, 0, 0)` issues when nothing is buffered: the
    checker answers `ret_only_copyins [(iov, 16)] 0 model []`, so the call is
    deterministic, silent, and returns 0.  Everything it needs is in the tree
    now (the eight proved siblings above, `import_iovecs_of_array`'s
    `nr_segs == 1` short circuit, `import_iovecs_accesses`,
    `check_ret_only_copyins_ok_iff` and the `adv_set_epend` bridge); it is
    deferred only for lack of a worked proof.  The `Hmax` premise is `rw_bytes_max`'s
    non-negativity and, like `writev_check`'s `_Htmax`, stays a premise for
    the callers' sake.) -/

end LinuxSem.Common.LibWritev
