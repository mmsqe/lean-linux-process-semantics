/-
  * Common.DrainAlg — the [read(0, …)] node and the BOUNDED drain loop,
      in the shape algebra of [Common.ShapeAlg].

  TRUST BOUNDARY: image-INDEPENDENT proof library, written against the
  star-based [LinuxProcessSem.Run] trace semantics.  Additive: nothing
  in [ShapeAlg], [StreamSim] or [DrainSim] is changed or shadowed.

  Two things live here.

  ** 1. The [read(0, buf, cnt)] node ([node_read0] / [rz_read0]).

  [ShapeAlg]'s table of nodes lists "read(0, …) — chunkings of the
  stream" but the file itself stops at [mmap]; this supplies the
  missing entry.  The ingredients are exactly the [*_ok] +
  [sstep_*_inv] pair [Common/StreamSim] already proves ([read0_ok_eof],
  [read0_ok_bytes], [sstep_read_inv]), repackaged as the single
  [node_ok] interface, so the index type is the set of ADMISSIBLE READ
  RESOLUTIONS at the current stream:

    [rd_adm s cnt bs]  =  "bs = [] and the stream is at EOF"
                       or "bs is a nonempty <= cnt byte prefix of s".

  Both resolutions are packaged as one sigma type ([RdIdx]) rather than
  a sum, which is what makes the successor a plain function of [bs]
  ([rd_next] matches on [bs]: the empty list is EOF and every block is
  nonempty, so the match is exhaustive and non-overlapping).

  ** 2. The BOUNDED drain loop ([t_drain] / [rz_drain]).

  [Common/DrainSim] covers "read stdin to EOF in fixed-size chunks,
  folding each byte through [f]".  That loop has NO bound: on an
  infinite [InputStream] it never terminates, so — as
  [Common/SHAPE_ALGEBRA.md] records under "What this does not cover
  yet" — it cannot be given an INDUCTIVE [realizes] derivation, and
  [DrainSim] has to keep its own bespoke [drain_obs_iff]/[drain_no_error]
  pair.  ([DrainSim.drain_from] itself is fine on an infinite stream:
  the [out_tail s'] of a chunking that leaves [s' = ICons _ _] is [],
  so the trace set is a perfectly ordinary prefix-closed set with no
  maximal element.  It is the DERIVATION, not the denotation, that the
  inductive [realizes] cannot supply.)

  The loop shape here is different and strictly easier: the common
  "slurp stdin into a fixed-size arena" prologue

    len = 0;
    for (;;) {
      if (len >= CAP) break;
      r = read(0, buf + len, CAP - len);
      if (r < 0) die(...);        (* not reachable in the model *)
      if (r == 0) break;
      len += r;
    }

  is bounded by CAP: every admissible read delivers at least one byte,
  so the loop runs at most CAP times WHATEVER the stream is, including
  an infinite one.  That makes it an ordinary structural recursion on a
  [Nat] fuel, and hence an ordinary inductive [realizes] derivation —
  no coinduction and no step indexing.  [rz_drain] below is that
  derivation, proved once, with the continuation [Tfin] (the shape of
  everything after the loop) as a parameter, and with the per-binary
  obligation stated as a single "every loop head runs to a read whose
  EOF successor is the tail and whose block successors are loop heads"
  hypothesis.

  The pay-off is that the arena's contents at loop exit are
  [List.take CAP stdin] — a FUNCTION of the stream, not a nondeterministic
  fold — which is what lets an otherwise wildly nondeterministic
  chunking collapse to a deterministic tail.  [drain_acc_firstn] proves
  that: every [acc] the loop can exit with is the first [CAP] bytes of
  the original stream (as a list).

  Conventions follow [StreamSim]/[DrainSim]: bytes are [byte = BitVec 8],
  counts are [word = BitVec 64], the read fd/count checks are
  Z-characterized ([(x8.toNat : Int) = 63]).

  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `firstn` → `List.take`,
    `lia` → `omega`, `fst`/`snd` unchanged, `exist _ x H` → `⟨x, H⟩`,
    `proj1_sig i` → `i.1`.
 Every one of
    them is explicit (not implicit) at the call site.
  - **`rd_adm`'s EOF clause is `s 0 = none`, not `s = IEof`.**  Under the
    function encoding those differ on JUNK streams (a value of the type
    that answers `none` at 0 and `some _` later, which no `IEof`/`ICons`
    stream ever is), and `s = IEof` is not what [StreamSim] proves: its
    `read0_ok_eof` takes `m_stdin model 0 = none` and its
    `sstep_read_inv` RETURNS `m_stdin model 0 = none`.  This is
    why [rd_adm_inhab] needs no extra hypothesis here, whereas the
    `s = IEof` spelling would need `stream_sticky`.
-/
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.StreamSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.WallSim
import LinuxSem.Common.ExitSim
import LinuxSem.Common.SimInv
import LinuxSem.Common.StreamExec
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Common.SharedFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.EquivalenceDefinition
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamExec
open LinuxSem.Common.WallSim
open LinuxSem.Common.StreamSim
open LinuxSem.Common.MmapSim
open LinuxSem.Common.ShapeAlg

namespace LinuxSem.Common.DrainAlg
open LinuxSem.Common.SharedFacts (is_prefix_app_mono is_prefix_app_r)

/-- The FP state at process entry, so that the `PropExec`/`MmapSim` lemmas
    the imported modules state elaborate.  Same local instance
    `SpinAlg.lean` declares. -/
local instance drainalg_fx : PropExec.FPState := PropExec.fx0

/- =========================================================================
   Admissible read resolutions
   ========================================================================= -/

/-- The resolutions of a [read(0, buf, cnt)] against remaining input [s].
    [StreamSim.read0_ok_inv] says these are exactly the outcomes the
    model admits. -/
def rd_adm (s : InputStream) (cnt : word) (bs : List byte) : Prop :=
  (bs = [] ∧ s 0 = none)
  ∨ ((1 : Int) ≤ (bs.length : Int)
      ∧ (bs.length : Int) ≤ (cnt.toNat : Int)
      ∧ (stream_take s bs.length).1 = bs)

def RdIdx (s : InputStream) (cnt : word) : Type :=
  { bs : List byte // rd_adm s cnt bs }

/-- This tree's replacement for  `destruct s as [|b s']`:
    a stream whose head is `some b` IS `ICons b` of its own tail (the
    function encoding makes that an equation rather than a case). -/
theorem eq_icons {s : InputStream} {b : byte} (h : s 0 = some b) :
    s = ICons b (fun n => s (n + 1)) := by
  funext n
  cases n with
  | zero => simpa [ICons] using h
  | succ n => simp [ICons]

/-- Every read has at least one resolution: EOF, or the one-byte block. -/
theorem rd_adm_inhab (s : InputStream) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int)) : ∃ bs, rd_adm s cnt bs := by
  cases h : s 0 with
  | none => exact ⟨[], Or.inl ⟨rfl, h⟩⟩
  | some b =>
    refine ⟨[b], Or.inr ⟨by simp, by simp; omega, ?_⟩⟩
    rw [eq_icons h]
    simp [stream_take, ICons]

theorem rd_adm_eof_nil (s : InputStream) (cnt : word) (bs : List byte)
    (H : rd_adm s cnt bs) (Hb : bs = []) : s 0 = none := by
  rcases H with ⟨-, Hs⟩ | ⟨Hlo, -, -⟩
  · exact Hs
  · subst Hb
    simp at Hlo

/-- A block resolution is nonempty. -/
theorem rd_adm_block_nonnil (bs : List byte)
    (H : (1 : Int) ≤ (bs.length : Int)) : bs ≠ [] := by
  rintro rfl
  simp at H

/-- The successor configuration of a read resolution.  The match on [bs]
    is exhaustive and non-overlapping: EOF returns 0 bytes, every block
    is nonempty. -/
def rd_next (ms : machine_state) (model : Model) (buf : word)
    (bs : List byte) : config :=
  match bs with
  | [] => mkCfg (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0))) model
  | _ :: _ =>
      mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
            (with_stdin (stream_take (m_stdin model) bs.length).2 model)

theorem rd_next_stdin_block (ms : machine_state) (model : Model) (buf : word)
    (bs : List byte) (H : bs ≠ []) :
    m_stdin (rd_next ms model buf bs).cfg_model
      = (stream_take (m_stdin model) bs.length).2 := by
  cases bs with
  | nil => exact absurd rfl H
  | cons b bs => rfl

/- =========================================================================
   The arena contents are a FUNCTION of the stream
   ========================================================================= -/

/-- The list of bytes an [InputStream] delivers in its first [k]. -/
def stream_firstn (s : InputStream) (k : Nat) : List byte :=
  (stream_take s k).1

theorem stream_take_split (k1 k2 : Nat) (s : InputStream) :
    (stream_take s (k1 + k2)).1
      = (stream_take s k1).1
        ++ (stream_take (stream_take s k1).2 k2).1 :=
  congrArg Prod.fst (stream_take_add k1 k2 s)

theorem stream_take_cons_pos (b : byte) (s : InputStream) (k : Nat)
    (H : 1 ≤ k) :
    (stream_take (ICons b s) k).1 = b :: (stream_take s (k - 1)).1 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [stream_take_cons]
    rfl

theorem stream_take_ge (k1 : Nat) : ∀ (k2 : Nat) (s : InputStream),
    k1 ≤ k2 →
    (stream_take s k1).1.length < k1 →
    (stream_take s k2).1 = (stream_take s k1).1 := by
  induction k1 with
  | zero =>
    intro k2 s Hle Hlen
    rw [stream_take_zero] at Hlen
    simp only [List.length_nil] at Hlen
    omega
  | succ k1 ih =>
    intro k2 s Hle Hlen
    cases k2 with
    | zero => omega
    | succ k2 =>
      cases h : s 0 with
      | none => rw [stream_take_none h k1, stream_take_none h k2]
      | some b =>
        have h1 := stream_take_some h k1
        have h2 := stream_take_some h k2
        simp only [h1, h2, List.length_cons] at Hlen ⊢
        rw [ih k2 (fun n => s (n + 1)) (by omega) (by omega)]

/-- Whatever chunking the loop takes, it exits with exactly the first
    [cap] bytes of the stream (or all of them, if there are fewer).  This
    is why the tail is a function of the input even though the read loop
    is nondeterministic. -/
theorem stream_take_app_take (s : InputStream) (bs : List byte) (k : Nat)
    (Hpre : (stream_take s bs.length).1 = bs) :
    bs ++ (stream_take (stream_take s bs.length).2 k).1
      = (stream_take s (bs.length + k)).1 := by
  rw [stream_take_split bs.length k s, Hpre]

/- =========================================================================
   The node
   ========================================================================= -/

section WithSegs

variable (segs : List Segment)

/-- The [read(0, buf, cnt)] node: the admissible transitions out of a
    read-pending configuration are EXACTLY the [RdIdx]-indexed family.
    Clause 1 is [StreamSim.read0_ok_eof]/[read0_ok_bytes], clause 2 is
    [StreamSim.sstep_read_inv]. -/
theorem node_read0 (ms : machine_state) (model : Model) (buf cnt x8 : word)
    (w : List byte)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0)
      = some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 63)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0)
    (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    -- the range passes [access_ok]: [vfs_read] tests it before the fd's
    -- content is consulted
    (Haok : access_okb buf (cnt.toNat : Int) = true) :
    node_ok segs (mkCfg ms model) (RdIdx (m_stdin model) cnt)
      (fun i => i.1.map (event.ReadEv (BitVec.ofInt 64 0)))
      (fun i => rd_next ms model buf i.1) := by
  constructor
  · -- completeness
    rintro ⟨bs, Hadm⟩
    rcases Hadm with ⟨rfl, Heof⟩ | ⟨Hlo, Hhi, Hpre⟩
    · -- EOF: return 0, no events, model unchanged
      have h := sstep.syscall (mi_loaded_segments := segs) ms model x8
        (mkEffect (BitVec.ofInt 64 0) [] []) model model []
        Hh Hsvc
        (read0_ok_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2
          (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok))
        Hh (materialize_model_accesses_no_lazy model _ Hlazy)
      simpa [rd_next, apply_effect_no_write] using h
    · -- a block off the head of the stream
      have Hne : bs ≠ [] := rd_adm_block_nonnil bs Hlo
      have h := sstep.syscall (mi_loaded_segments := segs) ms model x8
        (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (bs.map (event.ReadEv (BitVec.ofInt 64 0)))
        Hh Hsvc
        (read0_ok_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2
          (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok) Hlo Hhi Hpre)
        (by rw [StreamSim.m_halted_with_stdin]; exact Hh)
        (by rw [materialize_model_accesses_no_lazy _ _
                  (by rw [StreamSim.m_vm_lazy_with_stdin]; exact Hlazy)])
      cases bs with
      | nil => exact absurd rfl Hne
      | cons b bs => simpa [rd_next, Hg1] using h
  · -- soundness
    intro e st Hss
    rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w e st
        Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
      ⟨Heof, rfl, hst⟩ | ⟨bs, Hlo, Hhi, Hpre, rfl, hst⟩
    · exact ⟨⟨[], Or.inl ⟨rfl, Heof⟩⟩, rfl, hst⟩
    · refine ⟨⟨bs, Or.inr ⟨Hlo, Hhi, Hpre⟩⟩, rfl, ?_⟩
      cases bs with
      | nil => simp at Hlo
      | cons b bs => simpa [rd_next] using hst

/-- The trace set of a read node on channel [rch]: choose a resolution,
    emit its [ReadEv]s, continue as [K bs].  The write-side twin is
    [ShapeAlg.t_write_ch]. -/
def t_read_ch (rch : word) (s : InputStream) (cnt : word)
    (K : List byte → TSet) : TSet :=
  t_alt (fun i : RdIdx s cnt =>
           t_emit ((i.1.map (event.ReadEv rch))) (K i.1))

/-- The same node on channel 0, the only channel a read can name:
    [ReadWrite.read_spec] answers -EBADF on the rest directly, and
    [ReadWrite.readv_spec] does so through [ReadWrite.readable_fd].  This is
    the form [rz_read0] realizes. -/
def t_read0 (s : InputStream) (cnt : word) (K : List byte → TSet) : TSet :=
  t_read_ch (BitVec.ofInt 64 0) s cnt K

/-- The introduction rule.  Continuation-polymorphic, like every other
    combinator in [ShapeAlg]. -/
theorem rz_read0 (ms : machine_state) (model : Model) (buf cnt x8 : word)
    (w : List byte) (K : List byte → TSet)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0)
      = some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 63)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0)
    (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    -- the range passes [access_ok]: [vfs_read] tests it before the fd's
    -- content is consulted
    (Haok : access_okb buf (cnt.toNat : Int) = true)
    (HK : ∀ bs, rd_adm (m_stdin model) cnt bs →
       realizes segs (rd_next ms model buf bs) (K bs)) :
    realizes segs (mkCfg ms model) (t_read0 (m_stdin model) cnt K) := by
  obtain ⟨bs0, Hbs0⟩ := rd_adm_inhab (m_stdin model) cnt Hcnt.1
  unfold t_read0 t_read_ch
  refine .rz_node (mkCfg ms model) (RdIdx (m_stdin model) cnt)
    (fun i => i.1.map (event.ReadEv (BitVec.ofInt 64 0)))
    (fun i => rd_next ms model buf i.1)
    (fun i => K i.1) ⟨bs0, Hbs0⟩
    (node_read0 segs ms model buf cnt x8 w Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok)
    ?_
  rintro ⟨bs, Hbs⟩
  exact HK bs Hbs

/-- Emitting [a] then [b] is emitting [a ++ b].  (Purely about [t_emit];
    it belongs next to [ShapeAlg.t_emit_nil_eq], but [ShapeAlg] is not
    edited here.) -/
theorem t_emit_app (a b : List event) (T : TSet) :
    t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T) := by
  intro tr
  unfold t_emit
  constructor
  · rintro (Hp | ⟨tr', he, Hrest⟩)
    · exact Or.inl (is_prefix_app_r a b tr Hp)
    · rcases Hrest with Hp | ⟨tr'', he2, HT⟩
      · subst he
        exact Or.inl (is_prefix_app_mono a tr' b Hp)
      · subst he
        subst he2
        exact Or.inr ⟨tr'', by rw [List.append_assoc], HT⟩
  · rintro (Hp | ⟨tr', he, HT⟩)
    · rcases is_prefix_app_split a b tr Hp with Hp' | ⟨tr1, he1, Hp'⟩
      · exact Or.inl Hp'
      · exact Or.inr ⟨tr1, he1, Or.inl Hp'⟩
    · subst he
      exact Or.inr ⟨b ++ tr', by rw [List.append_assoc], Or.inr ⟨tr', rfl, HT⟩⟩

/- =========================================================================
   The bounded drain loop
   ========================================================================= -/

section Drain

/-- The arena capacity.  Every read is [read(0, buf + |acc|, cap - |acc|)]
    and the loop stops at [|acc| = cap] or at EOF, whichever comes first.

    Two facts about it ride along as explicit hypotheses of the lemmas
    below: [Hcap] ([cap] is far below [2^64], so the count word does not
    wrap) and [Hcap_modeled] — the loop never asks for more than the
    model judges ([Uaccess.rw_bytes_max]): each read is capped by what is
    left of [cap].
 See the module header. -/
def dcnt (cap : Nat) (acc : List byte) : word :=
  BitVec.ofInt 64 ((cap - acc.length : Nat) : Int)

theorem dcnt_pos (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64) (acc : List byte)
    (H : acc.length < cap) : (0 : Int) < ((dcnt cap acc).toNat : Int) := by
  have h : ((dcnt cap acc).toNat : Int) = ((cap - acc.length : Nat) : Int) := by
    unfold dcnt
    refine toNat_ofInt_eq_self (by omega) ?_
    rw [Int.natCast_pow]
    exact Int.lt_of_le_of_lt (Int.ofNat_le.mpr (Nat.sub_le cap acc.length)) Hcap
  omega

theorem dcnt_max (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max) (acc : List byte)
    (H : acc.length ≤ cap) : ((dcnt cap acc).toNat : Int) ≤ rw_bytes_max := by
  have h : ((dcnt cap acc).toNat : Int) = ((cap - acc.length : Nat) : Int) := by
    unfold dcnt
    refine toNat_ofInt_eq_self (by omega) ?_
    rw [Int.natCast_pow]
    exact Int.lt_of_le_of_lt (Int.ofNat_le.mpr (Nat.sub_le cap acc.length)) Hcap
  rw [h]
  have h1 : ((cap - acc.length : Nat) : Int) ≤ (cap : Int) :=
    Int.ofNat_le.mpr (Nat.sub_le cap acc.length)
  omega

theorem dcnt_val (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64) (acc : List byte)
    (H : acc.length ≤ cap) :
    ((dcnt cap acc).toNat : Int) = ((cap - acc.length : Nat) : Int) := by
  unfold dcnt
  refine toNat_ofInt_eq_self (by omega) ?_
  rw [Int.natCast_pow]
  exact Int.lt_of_le_of_lt (Int.ofNat_le.mpr (Nat.sub_le cap acc.length)) Hcap

/-- The loop's trace set.  [n] is a FUEL: structural recursion needs one,
    because a resolution consumes [length bs] units of capacity rather
    than exactly one.  It is instantiated at [cap] by [rz_drain_top]; the
    invariant [cap - length acc <= n] (which every iteration preserves,
    since blocks are nonempty) is what makes the fuel never bite. -/
def t_drain_ch (cap : Nat) (Tfin : List byte → TSet) (rch : word) (n : Nat)
    (s : InputStream) (acc : List byte) : TSet :=
  match n with
  | 0 => Tfin acc
  | n' + 1 =>
      if cap ≤ acc.length then Tfin acc
      else t_read_ch rch s (dcnt cap acc)
             (fun bs =>
                match bs with
                | [] => Tfin acc
                | _ :: _ =>
                    t_drain_ch cap Tfin rch n' (stream_take s bs.length).2 (acc ++ bs))

/-- The loop at channel 0, which is what a binary realizes.  NOTE that
    this is a [def] wrapping the [Fixpoint] above, so it does not
    reduce on its own: unfolding one iteration takes
    [simp only [t_drain, t_drain_ch]], not [simp only [t_drain]], which
    is silently inert. -/
def t_drain (cap : Nat) (Tfin : List byte → TSet) (n : Nat) (s : InputStream)
    (acc : List byte) : TSet :=
  t_drain_ch cap Tfin (BitVec.ofInt 64 0) n s acc

/- -------------------------------------------------------------------------
   The chunking is INVISIBLE: the drain shape collapses to one deterministic
   block of read events followed by the tail at the first [cap] bytes of
   stdin.
   ------------------------------------------------------------------------- -/

/-- A [read] emits one [ReadEv] PER BYTE, so a chunking contributes
    `(blocks.map ...)` — flattened — to the trace no matter how the
    bytes were split across syscalls.  Therefore the whole nondeterministic
    loop denotes a SINGLE deterministic shape: emit the first
    [cap - |acc|] bytes of the remaining stream, then run the tail on
    what the arena ended up holding.

    This is the lemma that makes the pattern usable.  Two binaries may
    chunk stdin completely differently — different buffer sizes,
    different short-read behavior — and still realize the same [TSet],
    because the [TSet] does not mention the chunking at all.  It is also
    what turns "the arena holds SOME interleaving of the input" into
    "the arena holds the first [cap] bytes of stdin", i.e. what makes the
    tail a function of the input.

    [Htfin_ne] is the tail shape's nonemptiness (see the note below). -/
theorem t_drain_ch_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet)
    (Htfin_ne : ∀ acc, Tfin acc [])
    (rch : word) (n : Nat) (s : InputStream) (acc : List byte)
    (Hn : cap - acc.length ≤ n) (Hle : acc.length ≤ cap) :
    t_eq (t_drain_ch cap Tfin rch n s acc)
      (t_emit ((stream_take s (cap - acc.length)).1.map (event.ReadEv rch))
        (Tfin (acc ++ (stream_take s (cap - acc.length)).1))) := by
  revert s acc
  induction n with
  | zero =>
    -- fuel out: the invariant forces the capacity to be out too
    intro s acc Hn Hle
    have h0 : cap - acc.length = 0 := by omega
    simp only [t_drain_ch, h0, stream_take_zero, List.map_nil, List.append_nil]
    exact t_eq_sym (t_emit_nil_eq (Tfin acc) (Htfin_ne acc))
  | succ n ih =>
    intro s acc Hn Hle
    by_cases hfull : cap ≤ acc.length
    · have h0 : cap - acc.length = 0 := by omega
      simp only [t_drain_ch, ite_eq_left hfull, h0, stream_take_zero, List.map_nil,
        List.append_nil]
      exact t_eq_sym (t_emit_nil_eq (Tfin acc) (Htfin_ne acc))
    · -- one read, then the rest of the loop
      simp only [t_drain_ch, ite_eq_right hfull]
      have Hm : 1 ≤ cap - acc.length := by omega
      have Hdc : ((dcnt cap acc).toNat : Int) = ((cap - acc.length : Nat) : Int) :=
        dcnt_val cap Hcap acc Hle
      intro tr
      unfold t_read_ch t_alt
      constructor
      · -- every resolution's traces are in the collapsed shape
        rintro ⟨⟨bs, Hadm⟩, Hi⟩
        simp only [] at Hi
        cases bs with
        | nil =>
          -- EOF: the stream is empty, so the first [cap - |acc|] bytes are []
          rcases Hadm with ⟨-, Hs⟩ | ⟨Hlo, -, -⟩
          · have htake : (stream_take s (cap - acc.length)).1 = [] := by
              cases cap - acc.length with
              | zero => rfl
              | succ m' => exact congrArg Prod.fst (stream_take_none Hs m')
            rw [htake]
            simpa using Hi
          · simp only [List.length_nil] at Hlo
            omega
        | cons b0 bs0 =>
          -- a block: peel it off and use the induction hypothesis
          rcases Hadm with ⟨Hbad, -⟩ | ⟨Hlo, Hhi, Hpre⟩
          · exact absurd Hbad (by simp)
          · have Hblen : (b0 :: bs0).length ≤ cap - acc.length := by
              have h1 : (↑(b0 :: bs0).length : Int) ≤ ((cap - acc.length : Nat) : Int) := by
                rw [← Hdc]
                exact Hhi
              exact Int.ofNat_le.mp h1
            have hpos : 1 ≤ (b0 :: bs0).length := by simp
            have Hsplit : (stream_take s (cap - acc.length)).1
                = (b0 :: bs0) ++ (stream_take (stream_take s (b0 :: bs0).length).2
                    (cap - acc.length - (b0 :: bs0).length)).1 := by
              have h := stream_take_split (b0 :: bs0).length
                (cap - acc.length - (b0 :: bs0).length) s
              rw [show (b0 :: bs0).length + (cap - acc.length - (b0 :: bs0).length)
                  = cap - acc.length from by omega, Hpre] at h
              exact h
            have hlen1 : (acc ++ b0 :: bs0).length ≤ cap := by
              rw [List.length_append]
              omega
            have hlen2 : cap - (acc ++ b0 :: bs0).length ≤ n := by
              rw [List.length_append]
              omega
            have IH' := ih (stream_take s (b0 :: bs0).length).2 (acc ++ b0 :: bs0)
              hlen2 hlen1
            have hcap' : cap - (acc ++ b0 :: bs0).length
                = cap - acc.length - (b0 :: bs0).length := by
              rw [List.length_append]
              omega
            rw [hcap'] at IH'
            rw [Hsplit, List.map_append]
            rw [show acc ++ ((b0 :: bs0)
                  ++ (stream_take (stream_take s (b0 :: bs0).length).2
                        (cap - acc.length - (b0 :: bs0).length)).1)
                = (acc ++ b0 :: bs0)
                  ++ (stream_take (stream_take s (b0 :: bs0).length).2
                        (cap - acc.length - (b0 :: bs0).length)).1
                from (List.append_assoc _ _ _).symm]
            refine (t_emit_app ((b0 :: bs0).map (event.ReadEv rch)) _ _ tr).1 ?_
            exact (t_emit_cong ((b0 :: bs0).map (event.ReadEv rch)) _ _ IH' tr).1 Hi
      · -- conversely, the byte-at-a-time chunking realizes everything
        intro Hrhs
        cases h : s 0 with
        | none =>
          -- nothing left to read: the EOF resolution
          refine ⟨⟨[], Or.inl ⟨rfl, h⟩⟩, ?_⟩
          have htake : (stream_take s (cap - acc.length)).1 = [] := by
            cases cap - acc.length with
            | zero => rfl
            | succ m' => exact congrArg Prod.fst (stream_take_none h m')
          rw [htake] at Hrhs
          simpa using Hrhs
        | some b =>
          -- deliver exactly one byte: the finest chunking realizes
          -- every trace the collapsed shape contains
          have hs : s = ICons b (fun n => s (n + 1)) := eq_icons h
          have hpre : (stream_take s 1).1 = [b] := by
            rw [hs]
            simp [stream_take, ICons]
          have hst1 : stream_take s 1 = ([b], fun n => s (n + 1)) := by
            rw [hs]
            rfl
          refine ⟨⟨[b], Or.inr ⟨by simp,
            by rw [Hdc]; exact Int.ofNat_le.mpr Hm, hpre⟩⟩, ?_⟩
          change t_emit ([b].map (event.ReadEv rch))
            (t_drain_ch cap Tfin rch n (stream_take s [b].length).2 (acc ++ [b])) tr
          simp only [List.length_cons, List.length_nil]
          rw [hst1]
          simp only [List.map_cons, List.map_nil]
          have hlen1 : (acc ++ [b]).length ≤ cap := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have hlen2 : cap - (acc ++ [b]).length ≤ n := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have IH' := ih (fun n => s (n + 1)) (acc ++ [b]) hlen2 hlen1
          have hcap' : cap - (acc ++ [b]).length = cap - acc.length - 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          rw [hcap'] at IH'
          rw [hs, stream_take_cons_pos b (fun n => s (n + 1)) (cap - acc.length) Hm] at Hrhs
          refine (t_emit_cong [event.ReadEv rch b] _ _ IH' tr).2 ?_
          refine (t_emit_app [event.ReadEv rch b] _ _ tr).2 ?_
          rw [show (acc ++ [b])
                ++ (stream_take (fun n => s (n + 1)) (cap - acc.length - 1)).1
              = acc ++ (b :: (stream_take (fun n => s (n + 1))
                      (cap - acc.length - 1)).1)
              from by simp]
          exact Hrhs

/-- The collapse at channel 0, which is the form a binary uses. -/
theorem t_drain_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc [])
    (n : Nat) (s : InputStream) (acc : List byte)
    (Hn : cap - acc.length ≤ n) (Hle : acc.length ≤ cap) :
    t_eq (t_drain cap Tfin n s acc)
      (t_emit ((stream_take s (cap - acc.length)).1.map (event.ReadEv (BitVec.ofInt 64 0)))
        (Tfin (acc ++ (stream_take s (cap - acc.length)).1))) :=
  t_drain_ch_collapse cap Hcap Tfin Htfin_ne (BitVec.ofInt 64 0) n s acc Hn Hle

/-- The same collapse at the loop's entry, with an empty accumulator. -/
theorem t_drain_ch_top_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc [])
    (rch : word) (s : InputStream) :
    t_eq (t_drain_ch cap Tfin rch cap s [])
      (t_emit ((stream_firstn s cap).map (event.ReadEv rch))
        (Tfin (stream_firstn s cap))) := by
  unfold stream_firstn
  have H := t_drain_ch_collapse cap Hcap Tfin Htfin_ne rch cap s []
    (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
  simpa using H

/-- The collapse at the loop's entry on channel 0, which is how a binary
    uses it ([Examples.arena_tee_ns] is the one in the tree). -/
theorem t_drain_top_collapse (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Tfin : List byte → TSet) (Htfin_ne : ∀ acc, Tfin acc [])
    (s : InputStream) :
    t_eq (t_drain cap Tfin cap s [])
      (t_emit ((stream_firstn s cap).map (event.ReadEv (BitVec.ofInt 64 0)))
        (Tfin (stream_firstn s cap))) :=
  t_drain_ch_top_collapse cap Hcap Tfin Htfin_ne (BitVec.ofInt 64 0) s

/-- The loop rule.  Ordinary induction on the fuel — no coinduction, no
    step indexing, because the loop is bounded by [cap] on EVERY stream.
 The buffer
      address [buf] is existential — the combinator does not care WHERE
      the arena is, only that the whole remaining count is writable there.
      [read_bytes_map] walks the range in word arithmetic, which wraps at
      2^64, so being mapped is not [access_ok]; an arena address is far
      under [State.TASK_SIZE], so this is one inequality per binary. -/
theorem rz_drain (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ (acc : List byte) (c : config), LH acc c → cap ≤ acc.length →
      realizes segs c (Tfin acc))
    (Hread : ∀ (acc : List byte) (c : config), LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted c.cfg_model = none ∧
        m_vm_lazy c.cfg_model = [] ∧
        fd_lookup (m_fds c.cfg_model) (BitVec.ofInt 64 0)
          = some (FdEntry.FdChannel (BitVec.ofInt 64 0)) ∧
        msteps segs c.cfg_ms ms1 ∧
        ms1.ms_svc_pending = some x8 ∧
        (x8.toNat : Int) = 63 ∧
        ms_gpr ms1 0 = BitVec.ofInt 64 0 ∧
        ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf ((dcnt cap acc).toNat : Int) = true ∧
        realizes segs (rd_next ms1 c.cfg_model buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin c.cfg_model) (dcnt cap acc) bs → bs ≠ [] →
           LH (acc ++ bs) (rd_next ms1 c.cfg_model buf bs)))
    (n : Nat) (acc : List byte) (c : config)
    (Hn : cap - acc.length ≤ n) (HLH : LH acc c) :
    realizes segs c (t_drain cap Tfin n (m_stdin c.cfg_model) acc) := by
  induction n generalizing acc c with
  | zero =>
    simp only [t_drain, t_drain_ch]
    exact Hfull acc c HLH (by omega)
  | succ n ih =>
    simp only [t_drain, t_drain_ch]
    by_cases hfull : cap ≤ acc.length
    · rw [ite_eq_left hfull]
      exact Hfull acc c HLH hfull
    · rw [ite_eq_right hfull]
      obtain ⟨ms1, buf, x8, w, Hh, Hlazy, Hfd, Hms, Hsvc, Hno, Hg0, Hg1, Hg2, Hw,
        Haok, Heof, Hblk⟩ := Hread acc c HLH (by omega)
      obtain ⟨ms0, model⟩ := c
      simp only at Hh Hlazy Hfd Hms Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Heof Hblk
      have Hcnt' : 0 < ((dcnt cap acc).toNat : Int)
          ∧ ((dcnt cap acc).toNat : Int) ≤ rw_bytes_max :=
        ⟨dcnt_pos cap Hcap acc (by omega), dcnt_max cap Hcap Hcap_modeled acc (by omega)⟩
      refine rz_msteps segs ms0 ms1 model _ Hh Hlazy Hms ?_
      refine rz_read0 segs ms1 model buf (dcnt cap acc) x8 w _
        Hcnt' Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok ?_
      intro bs Hadm
      cases bs with
      | nil => exact Heof
      | cons b0 bs0 =>
        have hne : (b0 :: bs0) ≠ [] := by simp
        have Hblk' := Hblk (b0 :: bs0) Hadm hne
        have ih' := ih (acc ++ b0 :: bs0) (rd_next ms1 model buf (b0 :: bs0))
          (by simp only [List.length_cons, List.length_append]; omega) Hblk'
        rw [rd_next_stdin_block ms1 model buf (b0 :: bs0) hne] at ih'
        exact ih'

/-- The loop rule as a binary would use it: from the initial loop head
    with an empty accumulator. -/
theorem rz_drain_top (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ (acc : List byte) (c : config), LH acc c → cap ≤ acc.length →
      realizes segs c (Tfin acc))
    (Hread : ∀ (acc : List byte) (c : config), LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted c.cfg_model = none ∧
        m_vm_lazy c.cfg_model = [] ∧
        fd_lookup (m_fds c.cfg_model) (BitVec.ofInt 64 0)
          = some (FdEntry.FdChannel (BitVec.ofInt 64 0)) ∧
        msteps segs c.cfg_ms ms1 ∧
        ms1.ms_svc_pending = some x8 ∧
        (x8.toNat : Int) = 63 ∧
        ms_gpr ms1 0 = BitVec.ofInt 64 0 ∧
        ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf ((dcnt cap acc).toNat : Int) = true ∧
        realizes segs (rd_next ms1 c.cfg_model buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin c.cfg_model) (dcnt cap acc) bs → bs ≠ [] →
           LH (acc ++ bs) (rd_next ms1 c.cfg_model buf bs)))
    (c : config) (H : LH [] c) :
    realizes segs c (t_drain cap Tfin cap (m_stdin c.cfg_model) []) :=
  rz_drain segs cap Hcap Hcap_modeled LH Tfin Hfull Hread cap [] c
    (by simp only [List.length_nil]; omega) H

/- =========================================================================
   A COMMON COMPOSITION: mmap arena, then drain, then the tail
   ========================================================================= -/

/-- "Single anonymous [mmap] prologue, then slurp stdin into the arena,
    then a deterministic tail."  This is a common composition.  Without
    the shape algebra it would need a bespoke [Common/] file per
    (allocator, loop, tail) triple: [MmapSim] owns the two-resolution mmap node and
    [DrainSim] owns the read loop, and neither can appear under the
    other's relation.

    Here it is [rz_mmap] with [rz_drain_top] plugged into its success
    continuation and [ShapeAlg.cat_realizes] into its failure
    continuation.  The two facts that make it go through are that
    [MmapSim.mmap_model] touches only [vm_maps] — so the post-mmap
    model has the SAME [m_stdin] as the pre-mmap one, which is what
    makes the drain shape independent of WHICH address the kernel
    granted — and that [t_drain]'s continuation [Tfin] is a parameter,
    so the tail may be any [realizes] derivation at all (a write list
    and an exit, as here; or a nested loop).

    Note the shape of the conclusion: a two-element [t_alt2], exactly
    the two-element outcome set a single-mmap example is
    specified against. -/
theorem rz_mmap_drain (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Hfull : ∀ (acc : List byte) (c : config), LH acc c → cap ≤ acc.length →
      realizes segs c (Tfin acc))
    (Hread : ∀ (acc : List byte) (c : config), LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted c.cfg_model = none ∧
        m_vm_lazy c.cfg_model = [] ∧
        fd_lookup (m_fds c.cfg_model) (BitVec.ofInt 64 0)
          = some (FdEntry.FdChannel (BitVec.ofInt 64 0)) ∧
        msteps segs c.cfg_ms ms1 ∧
        ms1.ms_svc_pending = some x8 ∧
        (x8.toNat : Int) = 63 ∧
        ms_gpr ms1 0 = BitVec.ofInt 64 0 ∧
        ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf ((dcnt cap acc).toNat : Int) = true ∧
        realizes segs (rd_next ms1 c.cfg_model buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin c.cfg_model) (dcnt cap acc) bs → bs ≠ [] →
           LH (acc ++ bs) (rd_next ms1 c.cfg_model buf bs)))
    (ms0 ms : machine_state) (model : Model) (x8 : word) (bf : List (List byte)) (cf : word)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    -- the mmap failed: the binary's failure tail, a (retry-loop) write
    -- list and an exit
    (Hfail : ∀ e, e ∈ mmap_errnos →
      to_wallexit segs (BitVec.ofInt 64 1) bf cf
        (advance_past_svc (set_gpr0 ms (errno_ret e))))
    -- the mmap succeeded at [a]: the binary reaches its drain loop head
    (Hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      LH [] (mkCfg (advance_past_svc
                      (apply_effect ms
                        (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                  (mmap_model a (page_round_up (ms_gpr ms 1)) model)))
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbf : bufs_modeled bf) :
    realizes segs (mkCfg ms0 model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
              (t_drain cap Tfin cap (m_stdin model) [])) := by
  refine rz_msteps segs ms0 ms model _ Hh Hlazy Hms ?_
  refine rz_mmap segs ms model x8 _ _ Hh Hlazy Hsvc Hno Hargs ?_ ?_ Hex
  · intro e He
    exact wall_realizes segs _ model bf cf Hh Hlazy Hfd (Hfail e He) Hbf
  · intro a Ha
    -- [mmap_model] rewrites only [vm_maps], so the remaining stdin — and
    -- hence the whole drain shape — is untouched by the grant.
    exact rz_drain_top segs cap Hcap Hcap_modeled LH Tfin Hfull Hread _ (Hsucc a Ha)

/-- The same composition with the drain's chunking nondeterminism
    ELIMINATED ([t_drain_top_collapse]).  This is the shape a
    single-mmap-then-slurp binary is actually specified against: a
    two-element outcome set, one branch per [mmap] resolution, the
    success branch a deterministic function of the input stream.  Note
    that [cap] and [Tfin] are the only things the source and the target
    have to agree on — NOT how either of them chunks its reads. -/
theorem rz_mmap_drain_det (cap : Nat) (Hcap : (cap : Int) < 2 ^ 64)
    (Hcap_modeled : (cap : Int) ≤ rw_bytes_max)
    (LH : List byte → config → Prop) (Tfin : List byte → TSet)
    (Htfin_ne : ∀ acc, Tfin acc [])
    (Hfull : ∀ (acc : List byte) (c : config), LH acc c → cap ≤ acc.length →
      realizes segs c (Tfin acc))
    (Hread : ∀ (acc : List byte) (c : config), LH acc c → acc.length < cap →
      ∃ ms1 buf x8 w,
        m_halted c.cfg_model = none ∧
        m_vm_lazy c.cfg_model = [] ∧
        fd_lookup (m_fds c.cfg_model) (BitVec.ofInt 64 0)
          = some (FdEntry.FdChannel (BitVec.ofInt 64 0)) ∧
        msteps segs c.cfg_ms ms1 ∧
        ms1.ms_svc_pending = some x8 ∧
        (x8.toNat : Int) = 63 ∧
        ms_gpr ms1 0 = BitVec.ofInt 64 0 ∧
        ms_gpr ms1 1 = buf ∧
        ms_gpr ms1 2 = dcnt cap acc ∧
        read_bytes_map (ms_writable_byte segs ms1) buf (dcnt cap acc) = some w ∧
        access_okb buf ((dcnt cap acc).toNat : Int) = true ∧
        realizes segs (rd_next ms1 c.cfg_model buf []) (Tfin acc) ∧
        (∀ bs, rd_adm (m_stdin c.cfg_model) (dcnt cap acc) bs → bs ≠ [] →
           LH (acc ++ bs) (rd_next ms1 c.cfg_model buf bs)))
    (ms0 ms : machine_state) (model : Model) (x8 : word) (bf : List (List byte)) (cf : word)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hfd : fd1chan model)
    (Hms : msteps segs ms0 ms)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_args_ok ms)
    (Hfail : ∀ e, e ∈ mmap_errnos →
      to_wallexit segs (BitVec.ofInt 64 1) bf cf
        (advance_past_svc (set_gpr0 ms (errno_ret e))))
    (Hsucc : ∀ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true →
      LH [] (mkCfg (advance_past_svc
                      (apply_effect ms
                        (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                  (mmap_model a (page_round_up (ms_gpr ms 1)) model)))
    (Hex : ∃ a, grant_ok (ms_gpr ms 0) model a
        (page_round_up_Z ((ms_gpr ms 1).toNat : Int)) = true)
    (Hbf : bufs_modeled bf) :
    realizes segs (mkCfg ms0 model)
      (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
              (t_emit ((stream_firstn (m_stdin model) cap).map
                         (event.ReadEv (BitVec.ofInt 64 0)))
                      (Tfin (stream_firstn (m_stdin model) cap)))) := by
  refine realizes.rz_conseq _ _ _ (rz_mmap_drain segs cap Hcap Hcap_modeled LH Tfin
    Hfull Hread ms0 ms model x8 bf cf Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex Hbf) ?_
  exact t_alt2_congr _ _ _ _ (t_eq_refl _)
    (t_drain_top_collapse cap Hcap Tfin Htfin_ne (m_stdin model))

end Drain

end WithSegs


