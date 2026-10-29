/-
  * Common.DrainSim — drain-then-emit read-loop simulation.

  TRUST BOUNDARY: image-INDEPENDENT proof library, written against the
  star-based `LinuxProcessSem.Run` trace semantics.

  Shape covered: binaries that read ALL of stdin to EOF in `cnt`-byte
  chunks (a parameter, like StreamSim's; tail1-ns instantiates 1024),
  folding the delivered bytes through an abstract step function
  `f : A → byte → Option A` (with `none` = "abort immediately with exit
  code `ec`", no output), and at EOF emit `out aF` (one write syscall
  carrying the whole buffer, which the model always completes) followed by
  exit 0; `out aF = []` means no write at all.

  The per-binary obligation is a loop-head predicate
  `LH : A → machine_state → Prop` together with a proof that every
  `LH a` state runs deterministically to a read-pending ecall (`to_rd a`)
  whose

  - EOF continuation reaches the finishing phase `to_out (out a)` (a single
    write of `out a`, then exit 0 — or directly exit 0 when `out a` is
    empty), and whose
  - every-block continuation, for a delivered block `bs`, reaches a new
    loop head `LH a'` when `procs f a bs = some a'`, or an exit-`ec` ecall
    when `procs f a bs = none`.

  This file turns that per-iteration fact into the full trace
  characterization (`drain_obs_iff` against `drain_from cnt f out ec a0`),
  the no-error fact (`drain_no_error`), and the pair equivalence
  (`drain_strong_equiv`).  Reuses `Common.StreamSim`'s model/read toolbox
  (`M_loop`, `wseg_ok`, `read0_*`, `sstep_read_inv`, `block_ok`) and
  `Common.ExitSim`/`Common.CatSim`'s exit/write machinery.

  Conventions, following StreamSim:

  - bytes are `byte = BitVec 8`, channel ids/counts/exit codes are
    `word = BitVec 64`; `f : A → byte → Option A`, `out : A → List byte`,
    `ec : word` with `(ec.toNat : Int) < 256`, `cnt : word` with
    `0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max`;
  - the pending syscall numbers are Z-characterized: `ReadPend`/`WrFin`
    carry a quantified `x8` with `(x8.toNat : Int) = 63` (resp. `64`);
  - `block_ok` is 2 conjuncts (the byte-range clause is typed away);
    length bounds are `Int` comparisons over `(bs.length : Int)`;
  - the read return value is `len_word bs`; channels/exit codes are spelled
    `BitVec.ofInt 64 0` / `BitVec.ofInt 64 1`.

  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `length` → `List.length`,
    `concat` → `List.flatten`, `lia` → `omega`.
  - `mkCfg ms model` is the `config` constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` constructor
    `⟨sp, brk0, mb, rnd⟩`.
  - `Common.StreamSim`'s `block_ok` was typed away in this tree (nothing
    downstream used it), so this file introduces it: the same 2-conjunct
    shape, spelled over `(bs.length : Int)`.
-/
import LinuxSem.Common.StreamSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.PropExec
import LinuxSem.Checks.Sys.Fs.ReadWrite
import LinuxSem.Common.SharedFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.DrainSim
open LinuxSem.Common.SharedFacts (is_prefix_app_mono is_prefix_app_r)

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.WallSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamSim

variable [fx : FPState]

/- =========================================================================
   Abstract byte-stream processing.
   ========================================================================= -/

section Proc

variable {A : Type}

/-- Fold the abstract step function `f` over a delivered byte stream,
    starting from abstract state `a`: `none` at any byte means the binary
    aborts immediately (exit `ec`, no output).  This is the per-binary
    "what did the program compute so far" function; the simulation never
    looks inside it. -/
def procs (f : A → byte → Option A) (a : A) (bs : List byte) : Option A :=
  match bs with
  | [] => some a
  | b :: rest =>
      match f a b with
      | some a' => procs f a' rest
      | none => none

/-- Processing a concatenation is processing the first part, then the
    second from where the first left off.  The induction is on the FIRST
    list, generalizing the abstract state . -/
theorem procs_app (f : A → byte → Option A) (bs1 bs2 : List byte) (a : A) :
    procs f a (bs1 ++ bs2) =
      match procs f a bs1 with
      | some a' => procs f a' bs2
      | none => none := by
  induction bs1 generalizing a with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.cons_append, procs]
      cases h : f a b with
      | some a' => exact ih a'
      | none => rfl

end Proc

/- =========================================================================
   The abstract trace set.
   ========================================================================= -/

/-- An admissible read block for the `cnt`-byte chunked reader (same
    2-conjunct shape as StreamSim's `block_ok`; the byte-range clause is
    typed away by `byte = BitVec 8`). -/
def block_ok (cnt : word) (bs : List byte) : Prop :=
  1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cnt.toNat : Int)

/-- All read events of a list of blocks, in order, delivered on channel
    `rch`.  The write-side twin is `CatSim.wevents_ch`. -/
def reads_ch (rch : word) (blocks : List (List byte)) : List event :=
  blocks.flatMap (fun bs => bs.map (event.ReadEv rch))

theorem reads_ch_cons (rch : word) (bs : List byte) (blocks : List (List byte)) :
    reads_ch rch (bs :: blocks) = bs.map (event.ReadEv rch) ++ reads_ch rch blocks := rfl

/-- All read events of a list of blocks, in order.  Channel 0 is the only
    one a read can name: `ReadWrite.read_spec` answers -EBADF on every
    other. -/
def reads (blocks : List (List byte)) : List event :=
  reads_ch (BitVec.ofInt 64 0) blocks

theorem reads_cons (bs : List byte) (blocks : List (List byte)) :
    reads (bs :: blocks) = bs.map (event.ReadEv (BitVec.ofInt 64 0)) ++ reads blocks :=
  reads_ch_cons (BitVec.ofInt 64 0) bs blocks

section Traces

variable {A : Type}

/-- What the run emits after its last read block: the loop only finishes
    when the INPUT RUNS OUT, so the write-out and exit 0 appear exactly in
    the chunkings that consumed the whole stream.  While input remains, the
    trace so far is just a prefix of a longer run.

     matches the stream (`IEof` / `ICons _ _`); over
    the function encoding the same test is the observation `s 0`. -/
def out_tail (out : A → List byte) (s : InputStream) (a : A) (fs : Fs.Fs) : List event :=
  match s 0 with
  | none =>
      (out a).map (event.WriteEv (BitVec.ofInt 64 1)) ++
        [event.ExitEv (BitVec.ofInt 64 0) fs]
  | some _ => []

/-- Traces admissible from abstract state `a` on the remaining input `s`,
    with reads delivered on channel `rch`: either the blocks read so far
    all process fine (and, if they exhausted the input, the run finishes
    with the write-out of the final state and exit 0), or the last
    delivered block aborts processing and the run finishes with exit `ec`
    (no output).  WHICH bytes each block holds is fixed by `s` —
    `StreamSim.chunks` — so only the read CHUNKING is nondeterministic.

    `rch` is a parameter of the TRACE ALGEBRA only; it does not widen what
    a program may read. -/
def drain_from_ch (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (tr : List event) : Prop :=
  (∃ blocks s' a',
     chunks cnt s blocks s' ∧
     procs f a (List.flatten blocks) = some a' ∧
     is_prefix tr (reads_ch rch blocks ++ out_tail out s' a' fs))
  ∨ (∃ blocks bs s' a',
     chunks cnt s (blocks ++ [bs]) s' ∧
     procs f a (List.flatten blocks) = some a' ∧
     procs f a' bs = none ∧
     is_prefix tr (reads_ch rch (blocks ++ [bs]) ++ [event.ExitEv ec fs]))

/-- The same, reading channel 0 — the only channel a read can name:
    `ReadWrite.read_spec` answers -EBADF on the rest directly, and
    `ReadWrite.readv_spec` does so through `ReadWrite.readable_fd`.  This is
    the form the realization lemmas below (`star_drain_only`,
    `drain_obs_iff`) are stated with. -/
def drain_from (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : Fs.Fs) (s : InputStream) (tr : List event) : Prop :=
  drain_from_ch cnt f out ec (BitVec.ofInt 64 0) a fs s tr

theorem drain_from_ch_prefix (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream) (tr tr' : List event) :
    drain_from_ch cnt f out ec rch a fs s tr → is_prefix tr' tr →
      drain_from_ch cnt f out ec rch a fs s tr' := by
  intro H Hp'
  rcases H with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
    ⟨blocks, bs, s', a', HC, Hp, Hn, Hpref⟩
  · exact Or.inl ⟨blocks, s', a', HC, Hp, is_prefix_trans Hp' Hpref⟩
  · exact Or.inr ⟨blocks, bs, s', a', HC, Hp, Hn, is_prefix_trans Hp' Hpref⟩

theorem drain_from_prefix (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : Fs.Fs) (s : InputStream) (tr tr' : List event) :
    drain_from cnt f out ec a fs s tr → is_prefix tr' tr →
      drain_from cnt f out ec a fs s tr' :=
  drain_from_ch_prefix cnt f out ec (BitVec.ofInt 64 0) a fs s tr tr'

theorem drain_from_ch_nil (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream) :
    drain_from_ch cnt f out ec rch a fs s [] :=
  Or.inl ⟨[], s, a, chunks.nil s, rfl, is_prefix_nil _⟩

theorem drain_from_nil (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : Fs.Fs) (s : InputStream) :
    drain_from cnt f out ec a fs s [] :=
  drain_from_ch_nil cnt f out ec (BitVec.ofInt 64 0) a fs s

/-- At end of input: the finishing phase. -/
theorem drain_from_ch_out (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : Fs.Fs) (tr : List event)
    (Hp : is_prefix tr
      ((out a).map (event.WriteEv (BitVec.ofInt 64 1)) ++
        [event.ExitEv (BitVec.ofInt 64 0) fs])) :
    drain_from_ch cnt f out ec rch a fs IEof tr :=
  Or.inl ⟨[], IEof, a, chunks.nil IEof, rfl, Hp⟩

theorem drain_from_out (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : Fs.Fs) (tr : List event)
    (Hp : is_prefix tr
      ((out a).map (event.WriteEv (BitVec.ofInt 64 1)) ++
        [event.ExitEv (BitVec.ofInt 64 0) fs])) :
    drain_from cnt f out ec a fs IEof tr :=
  drain_from_ch_out cnt f out ec (BitVec.ofInt 64 0) a fs tr Hp

theorem drain_from_ch_block (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a a1 : A) (fs : Fs.Fs) (s : InputStream)
    (bs : List byte) (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hs : procs f a bs = some a1)
    (Hd : drain_from_ch cnt f out ec rch a1 fs (stream_take s bs.length).2 tr) :
    drain_from_ch cnt f out ec rch a fs s (bs.map (event.ReadEv rch) ++ tr) := by
  rcases Hd with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
    ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩
  · refine Or.inl ⟨bs :: blocks, s', a', ?_, ?_, ?_⟩
    · exact chunks.cons s bs blocks s' Hlo Hhi Hpre HC
    · rw [List.flatten_cons, procs_app, Hs]
      exact Hp
    · rw [reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref
  · refine Or.inr ⟨bs :: blocks, bsE, s', a', ?_, ?_, Hn, ?_⟩
    · exact chunks.cons s bs (blocks ++ [bsE]) s' Hlo Hhi Hpre HC
    · rw [List.flatten_cons, procs_app, Hs]
      exact Hp
    · rw [List.cons_append, reads_ch_cons, List.append_assoc]
      exact is_prefix_app_mono _ _ _ Hpref

theorem drain_from_block (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a a1 : A) (fs : Fs.Fs) (s : InputStream)
    (bs : List byte) (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hs : procs f a bs = some a1)
    (Hd : drain_from cnt f out ec a1 fs (stream_take s bs.length).2 tr) :
    drain_from cnt f out ec a fs s (bs.map (event.ReadEv (BitVec.ofInt 64 0)) ++ tr) :=
  drain_from_ch_block cnt f out ec (BitVec.ofInt 64 0) a a1 fs s bs tr Hlo Hhi Hpre Hs Hd

theorem drain_from_ch_err (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (rch : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (bs : List byte) (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hn : procs f a bs = none)
    (Hp : is_prefix tr [event.ExitEv ec fs]) :
    drain_from_ch cnt f out ec rch a fs s (bs.map (event.ReadEv rch) ++ tr) := by
  refine Or.inr ⟨[], bs, (stream_take s bs.length).2, a, ?_, rfl, Hn, ?_⟩
  · exact chunks.cons s bs [] (stream_take s bs.length).2 Hlo Hhi Hpre (chunks.nil _)
  · simp only [List.nil_append, reads_ch, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact is_prefix_app_mono _ _ _ Hp

theorem drain_from_err (cnt : word) (f : A → byte → Option A) (out : A → List byte)
    (ec : word) (a : A) (fs : Fs.Fs) (s : InputStream)
    (bs : List byte) (tr : List event)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take s bs.length).1 = bs)
    (Hn : procs f a bs = none)
    (Hp : is_prefix tr [event.ExitEv ec fs]) :
    drain_from cnt f out ec a fs s (bs.map (event.ReadEv (BitVec.ofInt 64 0)) ++ tr) :=
  drain_from_ch_err cnt f out ec (BitVec.ofInt 64 0) a fs s bs tr Hlo Hhi Hpre Hn Hp

end Traces

/- =========================================================================
   Model plumbing.
   ========================================================================= -/

theorem fd1chan_with_stdin (s : InputStream) (m : Model) (H : fd1chan m) :
    fd1chan (with_stdin s m) := H

theorem m_fds_with_stdin (s : InputStream) (m : Model) : m_fds (with_stdin s m) = m_fds m :=
  rfl

/- =========================================================================
   The generic drain-loop theory.
   ========================================================================= -/

section Drain

variable {A : Type}

/-- The state runs (deterministically) to some `LH a` loop-head state. -/
def lh_next (segs : List Segment) (LH : A → machine_state → Prop) (a : A)
    (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH a ms'

/-- A write-pending ecall state that delivers exactly `bs` to stdout and
    then reaches exit 0.  Delivery is a `WallSim.to_wall` put-style RETRY
    LOOP, not a single ecall: each write may return any nonempty prefix of
    what is left, so the return is NOT pinned to a2 and `bs` may take one
    syscall or many.  The nonemptiness side condition is the loop's own
    (`to_wall` never delivers zero bytes). -/
def WrFin (segs : List Segment) (bs : List byte) (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧
    to_wall segs (BitVec.ofInt 64 1) ms bs (to_exit segs (BitVec.ofInt 64 0))

/-- The finishing phase: emit `bs` (empty = no write) then exit 0. -/
inductive to_out (segs : List Segment) : List byte → machine_state → Prop where
  | tout_exit (ms : machine_state) :
      to_exit segs (BitVec.ofInt 64 0) ms → to_out segs [] ms
  | tout_wr (bs : List byte) (ms : machine_state) :
      WrFin segs bs ms → to_out segs bs ms
  | tout_step (bs : List byte) (ms ms' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_out segs bs ms' → to_out segs bs ms

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable) at
    abstract state `a`, together with both continuations. -/
def ReadPend (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (a : A) (ms : machine_state) : Prop :=
  ∃ buf x8,
  ms.ms_svc_pending = some x8 ∧
  (x8.toNat : Int) = 63 ∧
  ms_gpr ms 0 = BitVec.ofInt 64 0 ∧
  ms_gpr ms 1 = buf ∧
  ms_gpr ms 2 = cnt ∧
  (∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w) ∧
  -- the destination range passes `access_ok`: `vfs_read` tests
  -- `buf + cnt <= TASK_SIZE` before it looks at the input, and being
  -- mapped is not that — `read_bytes_map` walks the range in word
  -- arithmetic, which wraps at 2^64.  Like `buf_modeled (out a)` below,
  -- this is carried on the states the binary actually reaches, and a
  -- binary's read buffer is far under `State.TASK_SIZE`.
  access_okb buf (cnt.toNat : Int) = true ∧
  to_out segs (out a) (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0))) ∧
  -- the finishing phase emits `out a` in ONE write, so it has to be
  -- inside the transfer size the model judges (`Uaccess.rw_bytes_max`).
  -- Carried here, on the states the binary actually reaches, rather than
  -- as a claim about `out` at every abstract state — the per-binary
  -- proof discharges it exactly where its own length caps are known.
  buf_modeled (out a) ∧
  (∀ bs,
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ (cnt.toNat : Int) →
    match procs f a bs with
    | some a' => lh_next segs LH a'
        (advance_past_svc (apply_effect ms
          (mkEffect (len_word bs) [(buf, bs)] [])))
    | none => to_exit segs ec
        (advance_past_svc (apply_effect ms
          (mkEffect (len_word bs) [(buf, bs)] []))))

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) :
    A → machine_state → Prop where
  | trd_here (a : A) (ms : machine_state) :
      ReadPend segs cnt f out ec LH a ms → to_rd segs cnt f out ec LH a ms
  | trd_step (a : A) (ms ms' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_rd segs cnt f out ec LH a ms' → to_rd segs cnt f out ec LH a ms

theorem msteps_to_rd (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) (a : A)
    (ms ms' : machine_state) :
    msteps segs ms ms' → to_rd segs cnt f out ec LH a ms' →
      to_rd segs cnt f out ec LH a ms := by
  intro H
  induction H with
  | mst_refl ms => intro Hrd; exact Hrd
  | mst_step ms ms' ms'' hsvc hstep h ih =>
      intro Hrd
      exact to_rd.trd_step a ms ms' hsvc hstep (ih Hrd)

theorem msteps_to_out (segs : List Segment) (bs : List byte) (ms ms' : machine_state) :
    msteps segs ms ms' → to_out segs bs ms' → to_out segs bs ms := by
  intro H
  induction H with
  | mst_refl ms => intro Ho; exact Ho
  | mst_step ms ms' ms'' hsvc hstep h ih =>
      intro Ho
      exact to_out.tout_step bs ms ms' hsvc hstep (ih Ho)

/-- A finishing phase IS a write-all tail derivation down to the exit
    line (the `to_out` instruction prefix becomes `twt_step`s). -/
theorem to_out_wall_tail (segs : List Segment) (bs : List byte) (ms : machine_state) :
    to_out segs bs ms →
      to_wall_tail segs (BitVec.ofInt 64 1) ms bs
        (to_exit segs (BitVec.ofInt 64 0)) := by
  intro H
  induction H with
  | tout_exit ms Hte => exact to_wall_tail.twt_done ms _ Hte
  | tout_wr bs ms HWF =>
      obtain ⟨Hnb, Hwl⟩ := HWF
      exact to_wall_tail.twt_more ms bs _ Hnb Hwl
  | tout_step bs ms ms' hsvc hstep ho ih =>
      exact to_wall_tail.twt_step ms ms' bs _ hsvc hstep ih

/-- The single per-binary hypothesis, applied. -/
theorem lh_next_to_rd (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) :
    lh_next segs LH a ms → to_rd segs cnt f out ec LH a ms := by
  rintro ⟨ms', Hm, HL⟩
  exact msteps_to_rd segs cnt f out ec LH a ms ms' Hm (H_LH a ms' HL)

/- -------------------------------------------------------------------------
   Straight lines are event-free star runs.
   ------------------------------------------------------------------------- -/

theorem to_rd_star (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop) (a : A)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → to_rd segs cnt f out ec LH a ms →
    ∃ msR, ReadPend segs cnt f out ec LH a msR ∧ star segs ⟨ms, model⟩ [] ⟨msR, model⟩ := by
  intro Hh Hlazy Hrd
  induction Hrd with
  | trd_here ms HRP => exact ⟨ms, HRP, star.refl _⟩
  | trd_step ms ms' hsvc hstep hrd ih =>
      obtain ⟨msR, HRP, Hstar⟩ := ih
      refine ⟨msR, HRP, ?_⟩
      have hss : sstep segs ⟨ms, model⟩ [] (.SNext ⟨ms', model⟩) := by
        refine sstep.instr ms model ms' model Hh hsvc ?_
        rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]
      have hstep' := star.step ⟨ms, model⟩ [] ⟨ms', model⟩ [] ⟨msR, model⟩ hss Hstar
      simpa using hstep'

theorem msteps_star (segs : List Segment) (ms ms' : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → msteps segs ms ms' →
    star segs ⟨ms, model⟩ [] ⟨ms', model⟩ := by
  intro Hh Hlazy H
  induction H with
  | mst_refl ms => exact star.refl _
  | mst_step ms ms1 ms2 hsvc hstep h ih =>
      have hss : sstep segs ⟨ms, model⟩ [] (.SNext ⟨ms1, model⟩) := by
        refine sstep.instr ms model ms1 model Hh hsvc ?_
        rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]
      have hstep' := star.step ⟨ms, model⟩ [] ⟨ms1, model⟩ [] ⟨ms2, model⟩ hss ih
      simpa using hstep'

/- -------------------------------------------------------------------------
   The finishing phase: admissibility and exhaustiveness.
   ------------------------------------------------------------------------- -/

theorem to_out_star_admits (segs : List Segment) (bs : List byte) (ms : machine_state)
    (model : Model) :
    fd1chan model → m_halted model = none → m_vm_lazy model = [] →
    to_out segs bs ms → buf_modeled bs →
    ∃ c, star segs ⟨ms, model⟩
      (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
        [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)]) c := by
  intro Hfd1 Hh Hlazy Ho Hbm
  revert Hbm
  induction Ho with
  | tout_exit ms Hte =>
      intro Hbm
      obtain ⟨c, Hstar⟩ := to_exit_star_admits segs (BitVec.ofInt 64 0) ms model Hh Hlazy Hte
      exact ⟨c, by simpa [band0_255] using Hstar⟩
  | tout_wr bs ms HWF =>
      intro Hbm
      obtain ⟨Hnb, Hwl⟩ := HWF
      refine to_wall_star_admits segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        ms bs (to_exit segs (BitVec.ofInt 64 0)) Hwl Hbm model
        [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)] Hh Hlazy
        (fd1chan_fdchan model Hfd1) ?_
      intro ms' Hex
      obtain ⟨c, Hstar⟩ := to_exit_star_admits segs (BitVec.ofInt 64 0) ms' model Hh Hlazy Hex
      exact ⟨c, by simpa [band0_255] using Hstar⟩
  | tout_step bs ms ms' hsvc hstep ho ih =>
      intro Hbm
      obtain ⟨c, Hstar⟩ := ih Hbm
      refine ⟨c, ?_⟩
      have hss : sstep segs ⟨ms, model⟩ [] (.SNext ⟨ms', model⟩) := by
        refine sstep.instr ms model ms' model Hh hsvc ?_
        rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]
      have hstep' := star.step ⟨ms, model⟩ [] ⟨ms', model⟩
        (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
          [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)]) c hss Hstar
      simpa using hstep'

theorem to_out_star_only (segs : List Segment) (bs : List byte) (ms : machine_state)
    (model : Model) :
    fd1chan model → m_halted model = none → m_vm_lazy model = [] →
    to_out segs bs ms → buf_modeled bs →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      is_prefix tr (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
        [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)]) := by
  intro Hfd1 Hh Hlazy Ho Hbm
  revert Hbm
  induction Ho with
  | tout_exit ms Hte =>
      intro Hbm tr c Hstar
      rcases to_exit_star_only segs (BitVec.ofInt 64 0) ms model Hh Hlazy Hte tr c Hstar
        with h | h
      · subst h
        exact is_prefix_nil _
      · subst h
        simpa [band0_255] using
          is_prefix_refl [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)]
  | tout_wr bs ms HWF =>
      intro Hbm tr c Hstar
      obtain ⟨Hnb, Hwl⟩ := HWF
      refine to_wall_star_only segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        ms bs (to_exit segs (BitVec.ofInt 64 0)) Hwl Hbm model
        [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)] Hh Hlazy
        (fd1chan_fdchan model Hfd1) ?_ tr c Hstar
      intro ms' tr' c' Hex Hstar'
      rcases to_exit_star_only segs (BitVec.ofInt 64 0) ms' model Hh Hlazy Hex tr' c' Hstar'
        with h | h
      · subst h
        exact is_prefix_nil _
      · subst h
        simpa [band0_255] using
          is_prefix_refl [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)]
  | tout_step bs ms ms' hsvc hstep ho ih =>
      intro Hbm tr c Hstar
      cases Hstar with
      | refl => exact is_prefix_nil _
      | step =>
          rename_i evs c2 tr2 hss hstar2
          obtain ⟨hevs, hc2⟩ :=
            sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy hsvc hstep hss
          subst hevs
          cases hc2
          simpa using ih Hbm tr2 c hstar2

/- -------------------------------------------------------------------------
   Channel-read spec facts at count `cnt`: thin corollaries of StreamSim's
   `cnt`-parameterized read0_* family (audit 1.1/3.1), instantiated at the
   section's `cnt`/`Hcnt` instead of re-proving the whole family
   (StreamSim's own consumer uses 4096 via the same parameterized lemmas).
   ------------------------------------------------------------------------- -/

theorem read0_check_eof_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Heof : m_stdin model 0 = none)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    -- the range passes `access_ok`: `vfs_read` tests it before the fd's
    -- content is consulted
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    check_read (sys_input segs ms x8)
      (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (BitVec.ofInt 64 0) [] []) model
      = .CheckOk model [] :=
  read0_check_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok

theorem read0_ok_eof_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Heof : m_stdin model 0 = none)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) model []) :=
  read0_ok_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok

theorem read0_check_bytes_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (w : List byte) (bs : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    check_read (sys_input segs ms x8)
      (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
      = .CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model)
          (bs.map (event.ReadEv (BitVec.ofInt 64 0))) :=
  read0_check_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre

theorem read0_ok_bytes_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (w : List byte) (bs : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
        (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (bs.map (event.ReadEv (BitVec.ofInt 64 0)))) :=
  read0_ok_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre

theorem read0_ok_inv_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (buf : word) (w : List byte) (eff : SyscallEffect) (model' : Model)
    (evs : List event)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (cnt.toNat : Int) = true)
    (Hspec : Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)) :
    (m_stdin model 0 = none ∧ eff = mkEffect (BitVec.ofInt 64 0) [] [] ∧
      model' = model ∧ evs = []) ∨
    (∃ bs, 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cnt.toNat : Int) ∧
        (stream_take (m_stdin model) bs.length).1 = bs ∧
        eff = mkEffect (len_word bs) [(buf, bs)] [] ∧
        model' = with_stdin (stream_take (m_stdin model) bs.length).2 model ∧
        evs = bs.map (event.ReadEv (BitVec.ofInt 64 0))) :=
  read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model' evs
    Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec

theorem read0_no_err_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model)
    (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled :=
  read0_no_unmodeled cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok

theorem sstep_read_inv_cnt (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (model : Model) (buf : word)
    (x8 : word) (w : List byte) (evs : List event) (st : step_to) :
    m_halted model = none →
    m_vm_lazy model = [] →
    fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)) →
    ms.ms_svc_pending = some x8 →
    (x8.toNat : Int) = 63 →
    ms_gpr ms 0 = BitVec.ofInt 64 0 → ms_gpr ms 1 = buf → ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) buf cnt = some w →
    -- the range passes `access_ok`: `vfs_read` tests it before the fd's
    -- content is consulted
    access_okb buf (cnt.toNat : Int) = true →
    sstep segs ⟨ms, model⟩ evs st →
    (m_stdin model 0 = none ∧ evs = [] ∧
     st = .SNext ⟨advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0)), model⟩)
    ∨ (∃ bs,
       1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cnt.toNat : Int) ∧
        (stream_take (m_stdin model) bs.length).1 = bs ∧
        evs = bs.map (event.ReadEv (BitVec.ofInt 64 0)) ∧
        st = .SNext ⟨advance_past_svc
               (apply_effect ms
                  (mkEffect (len_word bs) [(buf, bs)] [])),
               with_stdin (stream_take (m_stdin model) bs.length).2 model⟩) :=
  sstep_read_inv cnt Hcnt segs ms model buf x8 w evs st

/- -------------------------------------------------------------------------
   Admissibility: every drain trace is realized.
   ------------------------------------------------------------------------- -/

/-- One loop iteration: deliver block `bs` off the front of the model's
    input, run the per-binary continuation, and land at the successor
    state with the shortened input. -/
theorem drain_read_step (segs : List Segment) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (bs : List byte) (ms : machine_state) (model : Model) (buf : word) (x8 : word)
    (w : List byte) :
    M_loop model →
    ms.ms_svc_pending = some x8 →
    (x8.toNat : Int) = 63 →
    ms_gpr ms 0 = BitVec.ofInt 64 0 → ms_gpr ms 1 = buf →
    ms_gpr ms 2 = cnt →
    read_bytes_map (ms_writable_byte segs ms) buf cnt = some w →
    access_okb buf (cnt.toNat : Int) = true →
    1 ≤ (bs.length : Int) → (bs.length : Int) ≤ (cnt.toNat : Int) →
    (stream_take (m_stdin model) bs.length).1 = bs →
    sstep segs ⟨ms, model⟩ (bs.map (event.ReadEv (BitVec.ofInt 64 0)))
      (.SNext ⟨advance_past_svc (apply_effect ms
                     (mkEffect (len_word bs) [(buf, bs)] [])),
                  with_stdin (stream_take (m_stdin model) bs.length).2 model⟩) := by
  intro HM Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hlo Hhi Hpre
  have Hfd0 := HM.1
  have Hh := HM.2.2.1
  have Hlazy := HM.2.2.2
  refine sstep.syscall ms model x8
    (mkEffect (len_word bs) [(buf, bs)] [])
    (with_stdin (stream_take (m_stdin model) bs.length).2 model)
    (with_stdin (stream_take (m_stdin model) bs.length).2 model)
    (bs.map (event.ReadEv (BitVec.ofInt 64 0))) Hh Hsvc ?_ Hh ?_
  · simpa only [Hg1] using
      read0_ok_bytes_cnt cnt Hcnt segs ms x8 model w bs Hno Hfd0 Hg0 Hg2
        (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok) Hlo Hhi Hpre
  · rw [materialize_model_accesses_no_lazy _ _
      (by rw [m_vm_lazy_with_stdin]; exact Hlazy)]

theorem drain_star_admits_ok (segs : List Segment) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (s : InputStream) (blocks : List (List byte)) (s' : InputStream) :
    chunks cnt s blocks s' →
    ∀ (a a' : A) (ms : machine_state) (model : Model),
      M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a (List.flatten blocks) = some a' →
      ∃ c, star segs ⟨ms, model⟩
        (reads blocks ++ out_tail out s' a' (m_fs model)) c := by
  intro HC
  induction HC with
  | nil s =>
      intro a a' ms model HM Hst Hrd Hp
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      have ha : a' = a := by
        simp only [List.flatten, procs] at Hp
        exact (Option.some.inj Hp).symm
      rw [ha] at *
      cases hs : s 0 with
      | none =>
          -- the input has run out: EOF read, then the finishing phase
          obtain ⟨msR, HRP, Hstar0⟩ :=
            to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
            Hbytes⟩ := HRP
          have Hst' : m_stdin model 0 = none := by rw [Hst]; exact hs
          have HssE : sstep segs ⟨msR, model⟩ []
              (.SNext ⟨advance_past_svc (set_gpr0 msR (BitVec.ofInt 64 0)), model⟩) := by
            rw [← apply_effect_no_write msR (BitVec.ofInt 64 0)]
            refine sstep.syscall msR model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
              model model [] Hh Hsvc ?_ Hh ?_
            · exact read0_ok_eof_cnt cnt Hcnt segs msR x8 model w Hno Hfd0 Hst' Hg0 Hg2
                (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok)
            · rw [materialize_model_accesses_no_lazy model _ Hlazy]
          obtain ⟨c, Hstar2⟩ :=
            to_out_star_admits segs (out a) _ model Hfd1 Hh Hlazy Hout Hobm
          refine ⟨c, ?_⟩
          simp only [out_tail, hs, List.nil_append]
          exact star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ c
            (star.step ⟨msR, model⟩ [] _ _ c HssE Hstar2)
      | some b0 =>
          -- input remains: nothing more is emitted along this chunking
          refine ⟨⟨ms, model⟩, ?_⟩
          simp only [out_tail, hs, List.nil_append]
          exact star.refl _
  | cons s bs blocks s'' hlo hhi hpre hc ih =>
      intro a a' ms model HM Hst Hrd Hp
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      have Hp2 : procs f a (bs ++ List.flatten blocks) = some a' := Hp
      rw [procs_app] at Hp2
      cases hp1 : procs f a bs with
      | none =>
          rw [hp1] at Hp2
          exact absurd Hp2 (by simp)
      | some a1 =>
          rw [hp1] at Hp2
          obtain ⟨msR, HRP, Hstar0⟩ :=
            to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
            Hbytes⟩ := HRP
          have Hcont := Hbytes bs hlo hhi
          rw [hp1] at Hcont
          have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
            rw [← Hst]
            exact M_loop_take bs.length model HM
          have Hst' : m_stdin (with_stdin (stream_take s bs.length).2 model)
              = (stream_take s bs.length).2 := rfl
          have HssR : sstep segs ⟨msR, model⟩
              (bs.map (event.ReadEv (BitVec.ofInt 64 0)))
              (.SNext ⟨advance_past_svc (apply_effect msR
                  (mkEffect (len_word bs) [(buf, bs)] [])),
                with_stdin (stream_take s bs.length).2 model⟩) := by
            have h := drain_read_step segs cnt Hcnt bs msR model buf x8 w HM Hsvc Hno
              Hg0 Hg1 Hg2 Hw Haok hlo hhi (by rw [Hst]; exact hpre)
            rwa [Hst] at h
          obtain ⟨msL, Hms, HLa1⟩ := Hcont
          have Hrd1 : to_rd segs cnt f out ec LH a1
              (advance_past_svc (apply_effect msR
                (mkEffect (len_word bs) [(buf, bs)] []))) :=
            msteps_to_rd segs cnt f out ec LH a1 _ _ Hms (H_LH a1 msL HLa1)
          obtain ⟨c, Hstar3⟩ := ih a1 a' _ _ HM' Hst' Hrd1 Hp2
          rw [StreamSim.m_fs_with_stdin] at Hstar3
          refine ⟨c, ?_⟩
          rw [reads_cons, List.append_assoc]
          exact star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ c
            (star.step ⟨msR, model⟩ _ _ _ c HssR Hstar3)

theorem drain_star_admits_err (segs : List Segment) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hec : (ec.toNat : Int) < 256)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (s : InputStream) (blocks : List (List byte)) (s1 : InputStream) :
    chunks cnt s blocks s1 →
    ∀ (a a' : A) (bsE : List byte) (ms : machine_state) (model : Model),
      M_loop model → m_stdin model = s → to_rd segs cnt f out ec LH a ms →
      procs f a (List.flatten blocks) = some a' →
      1 ≤ (bsE.length : Int) → (bsE.length : Int) ≤ (cnt.toNat : Int) →
      (stream_take s1 bsE.length).1 = bsE →
      procs f a' bsE = none →
      ∃ c, star segs ⟨ms, model⟩
        (reads (blocks ++ [bsE]) ++ [event.ExitEv ec (m_fs model)]) c := by
  intro HC
  induction HC with
  | nil s =>
      intro a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      have ha : a' = a := by
        simp only [List.flatten, procs] at Hp
        exact (Option.some.inj Hp).symm
      rw [ha] at Hn
      obtain ⟨msR, HRP, Hstar0⟩ :=
        to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
        Hbytes⟩ := HRP
      have Hcont := Hbytes bsE HloE HhiE
      rw [Hn] at Hcont
      have Hh' : m_halted (with_stdin (stream_take s bsE.length).2 model) = none := Hh
      have Hlazy' : m_vm_lazy (with_stdin (stream_take s bsE.length).2 model) = [] := by
        rw [m_vm_lazy_with_stdin]; exact Hlazy
      have HssR : sstep segs ⟨msR, model⟩
          (bsE.map (event.ReadEv (BitVec.ofInt 64 0)))
          (.SNext ⟨advance_past_svc (apply_effect msR
              (mkEffect (len_word bsE) [(buf, bsE)] [])),
            with_stdin (stream_take s bsE.length).2 model⟩) := by
        have h := drain_read_step segs cnt Hcnt bsE msR model buf x8 w HM Hsvc Hno
          Hg0 Hg1 Hg2 Hw Haok HloE HhiE (by rw [Hst]; exact HpreE)
        rwa [Hst] at h
      obtain ⟨c, Hstar2⟩ :=
        to_exit_star_admits segs ec _ (with_stdin (stream_take s bsE.length).2 model)
          Hh' Hlazy' Hcont
      refine ⟨c, ?_⟩
      simp only [List.nil_append, reads, reads_ch, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      have hstar2' : star segs
          ⟨advance_past_svc (apply_effect msR (mkEffect (len_word bsE) [(buf, bsE)] [])),
            with_stdin (stream_take s bsE.length).2 model⟩
          [event.ExitEv ec (m_fs model)] c := by
        rw [← land_255_small ec Hec]
        simpa only [StreamSim.m_fs_with_stdin] using Hstar2
      exact star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ c
        (star.step ⟨msR, model⟩ _ _ _ c HssR hstar2')
  | cons s bs blocks s'' hlo hhi hpre hc ih =>
      intro a a' bsE ms model HM Hst Hrd Hp HloE HhiE HpreE Hn
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      have Hp2 : procs f a (bs ++ List.flatten blocks) = some a' := Hp
      rw [procs_app] at Hp2
      cases hp1 : procs f a bs with
      | none =>
          rw [hp1] at Hp2
          exact absurd Hp2 (by simp)
      | some a1 =>
          rw [hp1] at Hp2
          obtain ⟨msR, HRP, Hstar0⟩ :=
            to_rd_star segs cnt f out ec LH a ms model Hh Hlazy Hrd
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
            Hbytes⟩ := HRP
          have Hcont := Hbytes bs hlo hhi
          rw [hp1] at Hcont
          have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
            rw [← Hst]
            exact M_loop_take bs.length model HM
          have Hst' : m_stdin (with_stdin (stream_take s bs.length).2 model)
              = (stream_take s bs.length).2 := rfl
          have HssR : sstep segs ⟨msR, model⟩
              (bs.map (event.ReadEv (BitVec.ofInt 64 0)))
              (.SNext ⟨advance_past_svc (apply_effect msR
                  (mkEffect (len_word bs) [(buf, bs)] [])),
                with_stdin (stream_take s bs.length).2 model⟩) := by
            have h := drain_read_step segs cnt Hcnt bs msR model buf x8 w HM Hsvc Hno
              Hg0 Hg1 Hg2 Hw Haok hlo hhi (by rw [Hst]; exact hpre)
            rwa [Hst] at h
          obtain ⟨msL, Hms, HLa1⟩ := Hcont
          have Hrd1 : to_rd segs cnt f out ec LH a1
              (advance_past_svc (apply_effect msR
                (mkEffect (len_word bs) [(buf, bs)] []))) :=
            msteps_to_rd segs cnt f out ec LH a1 _ _ Hms (H_LH a1 msL HLa1)
          obtain ⟨c, Hstar3⟩ :=
            ih a1 a' bsE _ _ HM' Hst' Hrd1 Hp2 HloE HhiE HpreE Hn
          rw [StreamSim.m_fs_with_stdin] at Hstar3
          refine ⟨c, ?_⟩
          rw [List.cons_append, reads_cons, List.append_assoc]
          exact star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ c
            (star.step ⟨msR, model⟩ _ _ _ c HssR Hstar3)

/- -------------------------------------------------------------------------
   Exhaustiveness: every run trace is a drain trace.
   ------------------------------------------------------------------------- -/

theorem star_drain_only (segs : List Segment) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hec : (ec.toNat : Int) < 256)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms) :
    ∀ (c0 : config) (tr : List event) (c' : config), star segs c0 tr c' →
    ∀ (a : A) (ms : machine_state) (model : Model), c0 = ⟨ms, model⟩ →
    M_loop model → to_rd segs cnt f out ec LH a ms →
      drain_from cnt f out ec a (m_fs model) (m_stdin model) tr := by
  intro c0 tr c' Hstar
  induction Hstar with
  | refl c =>
      intro a ms model Heq HM Hrd
      exact drain_from_nil cnt f out ec a (m_fs model) (m_stdin model)
  | step =>
      rename_i c1 evs c2 tr2 c3 hss hstar2 ih
      intro a ms model Heq HM Hrd
      rw [Heq] at hss
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      cases Hrd with
      | trd_here =>
          rename_i HRP
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
            Hbytes⟩ := HRP
          rcases sstep_read_inv_cnt cnt Hcnt segs ms model buf x8 w evs (.SNext c2)
              Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok hss
            with ⟨Hs, Hevs, Hc2⟩ | ⟨bs, Hlo, Hhi, Hpre, Hevs, Hc2⟩
          · -- end of input: the rest is the finishing phase
            cases Hc2
            have Hpref :=
              to_out_star_only segs (out a) _ model Hfd1 Hh Hlazy Hout Hobm tr2 c3 hstar2
            rw [Hevs]
            simp only [List.nil_append]
            refine Or.inl ⟨[], m_stdin model, a, chunks.nil _, rfl, ?_⟩
            simpa only [out_tail, Hs, reads_ch, List.flatMap_nil, List.nil_append]
              using Hpref
          · -- bytes
            cases Hc2
            have Hcont := Hbytes bs Hlo Hhi
            cases hp1 : procs f a bs with
            | some a1 =>
                rw [hp1] at Hcont
                obtain ⟨msL, Hms, HLa1⟩ := Hcont
                have Hrd1 : to_rd segs cnt f out ec LH a1
                    (advance_past_svc (apply_effect ms
                      (mkEffect (len_word bs) [(buf, bs)] []))) :=
                  msteps_to_rd segs cnt f out ec LH a1 _ _ Hms (H_LH a1 msL HLa1)
                rw [Hevs]
                refine drain_from_block cnt f out ec a a1 (m_fs model) (m_stdin model) bs tr2
                  Hlo Hhi ?_ hp1 ?_
                · exact Hpre
                · exact ih a1 _ _ rfl (M_loop_take bs.length model HM) Hrd1
            | none =>
                rw [hp1] at Hcont
                rw [Hevs]
                refine drain_from_err cnt f out ec a (m_fs model) (m_stdin model) bs tr2
                  Hlo Hhi ?_ hp1 ?_
                · exact Hpre
                · have Hh' : m_halted
                      (with_stdin (stream_take (m_stdin model) bs.length).2 model) = none := Hh
                  have Hlazy' : m_vm_lazy
                      (with_stdin (stream_take (m_stdin model) bs.length).2 model) = [] := by
                    rw [m_vm_lazy_with_stdin]; exact Hlazy
                  rcases to_exit_star_only segs ec _
                      (with_stdin (stream_take (m_stdin model) bs.length).2 model)
                      Hh' Hlazy' Hcont tr2 c3 hstar2 with h | h
                  · rw [h]; exact is_prefix_nil _
                  · rw [h, land_255_small ec Hec, StreamSim.m_fs_with_stdin]
                    exact is_prefix_refl _
      | trd_step =>
          rename_i ms' hrd' hsvc hstep
          obtain ⟨Hevs, Hc2⟩ :=
            sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy hsvc hstep hss
          cases Hc2
          rw [Hevs]
          exact ih a ms' model rfl HM hrd'

/- -------------------------------------------------------------------------
   No error: the phase invariant.
   ------------------------------------------------------------------------- -/

/-- The phase invariant of a drain loop: either the model still has its
    stdin/stdout channels and the machine is on its way to (or at) a read —
    or inside the write-out, which is a write-all tail derivation down to
    the exit line — or the model is already on the exit path 0, or on the
    abort path `ec`. -/
def dinv (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (c : config) : Prop :=
  (M_loop c.cfg_model ∧ ∃ a, to_rd segs cnt f out ec LH a c.cfg_ms)
  ∨ (fd1chan c.cfg_model ∧ m_halted c.cfg_model = none ∧
      m_vm_lazy c.cfg_model = [] ∧
      ∃ rest, buf_modeled rest ∧
        to_wall_tail segs (BitVec.ofInt 64 1) c.cfg_ms rest
          (to_exit segs (BitVec.ofInt 64 0)))
  ∨ on_path segs (BitVec.ofInt 64 0) c
  ∨ on_path segs ec c

theorem wall_out_dinv_step (segs : List Segment) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word)
    (LH : A → machine_state → Prop)
    (rest : List byte) (ms : machine_state) (model : Model) (evs : List event)
    (ms' : machine_state) (model' : Model) :
    fd1chan model → m_halted model = none → m_vm_lazy model = [] →
    buf_modeled rest →
    to_wall_tail segs (BitVec.ofInt 64 1) ms rest (to_exit segs (BitVec.ofInt 64 0)) →
    sstep segs ⟨ms, model⟩ evs (.SNext ⟨ms', model'⟩) →
    dinv segs cnt f out ec LH ⟨ms', model'⟩ := by
  intro Hfd1 Hh Hlazy Hbm Ht Hss
  have Hfdc : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model :=
    fd1chan_fdchan model Hfd1
  revert Hbm
  cases Ht with
  | twt_done msD kD hkD =>
      intro Hbm
      refine Or.inr (Or.inr (Or.inl ?_))
      refine on_path_step segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs ⟨ms', model'⟩ ?_ Hss
      exact Or.inl ⟨Hh, Hlazy, hkD⟩
  | twt_more =>
      rename_i hnbM hwl
      intro Hbm
      obtain ⟨n, Hn1, Hn2, _hevs, Hc2, Ht2⟩ :=
        sstep_to_wall_inv segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
          ms rest (to_exit segs (BitVec.ofInt 64 0)) model evs (.SNext ⟨ms', model'⟩)
          Hh Hlazy Hfdc Hbm hwl Hss
      cases Hc2
      exact Or.inr (Or.inl ⟨Hfd1, Hh, Hlazy, rest.drop n,
        buf_modeled_skipn n rest Hbm, Ht2⟩)
  | twt_step =>
      rename_i msS' hsvcS hstepS ht'
      intro Hbm
      obtain ⟨_hevs, Hc2⟩ :=
        sstep_instr_inv segs ms model msS' evs (.SNext ⟨ms', model'⟩) Hlazy hsvcS hstepS Hss
      cases Hc2
      exact Or.inr (Or.inl ⟨Hfd1, Hh, Hlazy, rest, Hbm, ht'⟩)

theorem dinv_step (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (c : config) (evs : List event) (c' : config) :
    dinv segs cnt f out ec LH c → sstep segs c evs (.SNext c') →
      dinv segs cnt f out ec LH c' := by
  intro Hinv Hss
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hinv with ⟨HM, a, Hrd⟩ | ⟨Hfd1, Hh, Hlazy, rest, Hbm, Ht⟩ | Hop | Hop
  · have Hfd0 := HM.1
    have Hfd1 := HM.2.1
    have Hh := HM.2.2.1
    have Hlazy := HM.2.2.2
    cases Hrd with
    | trd_here =>
        rename_i HRP
        obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
          Hbytes⟩ := HRP
        rcases sstep_read_inv_cnt cnt Hcnt segs ms model buf x8 w evs (.SNext ⟨ms', model'⟩)
            Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss
          with ⟨Hs, Hevs, Hc2⟩ | ⟨bs, Hlo, Hhi, Hpre, Hevs, Hc2⟩
        · cases Hc2
          exact Or.inr (Or.inl ⟨Hfd1, Hh, Hlazy, out a, Hobm,
            to_out_wall_tail segs (out a) _ Hout⟩)
        · cases Hc2
          have Hcont := Hbytes bs Hlo Hhi
          cases hp1 : procs f a bs with
          | some a1 =>
              rw [hp1] at Hcont
              obtain ⟨msL, Hms, HLa1⟩ := Hcont
              exact Or.inl ⟨M_loop_take bs.length model HM, a1,
                msteps_to_rd segs cnt f out ec LH a1 _ _ Hms (H_LH a1 msL HLa1)⟩
          | none =>
              rw [hp1] at Hcont
              exact Or.inr (Or.inr (Or.inr (Or.inl
                ⟨Hh, (by rw [m_vm_lazy_with_stdin]; exact Hlazy), Hcont⟩)))
    | trd_step =>
        rename_i ms1 hrd' hsvc hstep
        obtain ⟨_hevs, Hc2⟩ :=
          sstep_instr_inv segs ms model ms1 evs (.SNext ⟨ms', model'⟩) Hlazy hsvc hstep Hss
        cases Hc2
        exact Or.inl ⟨HM, a, hrd'⟩
  · exact wall_out_dinv_step segs cnt f out ec LH rest ms model evs ms' model'
      Hfd1 Hh Hlazy Hbm Ht Hss
  · exact Or.inr (Or.inr (Or.inl
      (on_path_step segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs ⟨ms', model'⟩ Hop Hss)))
  · exact Or.inr (Or.inr (Or.inr
      (on_path_step segs ec ⟨ms, model⟩ evs ⟨ms', model'⟩ Hop Hss)))

theorem dinv_no_error (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (c : config) (evs : List event) :
    dinv segs cnt f out ec LH c → ¬ sstep segs c evs .SError := by
  intro Hinv Hss
  obtain ⟨ms, model⟩ := c
  rcases Hinv with ⟨HM, a, Hrd⟩ | ⟨Hfd1, Hh, Hlazy, rest, Hbm, Ht⟩ | Hop | Hop
  · have Hfd0 := HM.1
    have Hh := HM.2.2.1
    have Hlazy := HM.2.2.2
    cases Hrd with
    | trd_here =>
        rename_i HRP
        obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hout, Hobm,
          Hbytes⟩ := HRP
        rcases sstep_read_inv_cnt cnt Hcnt segs ms model buf x8 w evs .SError
            Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss
          with ⟨_a1, _a2, Hc2⟩ | ⟨_bs, _b1, _b2, _b3, _b4, Hc2⟩ <;> cases Hc2
    | trd_step =>
        rename_i ms1 hrd' hsvc hstep
        obtain ⟨_hevs, Hc2⟩ :=
          sstep_instr_inv segs ms model ms1 evs .SError Hlazy hsvc hstep Hss
        cases Hc2
  · have Hfdc : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model :=
      fd1chan_fdchan model Hfd1
    cases Ht with
    | twt_done =>
        rename_i hkD
        exact on_path_no_error segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs
          (Or.inl ⟨Hh, Hlazy, hkD⟩) Hss
    | twt_more =>
        rename_i hnbM hwl
        exact to_wall_no_error_sstep segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
          ms rest (to_exit segs (BitVec.ofInt 64 0)) model evs Hh Hlazy Hfdc Hbm hwl Hss
    | twt_step =>
        rename_i msS' hsvcS hstepS ht'
        obtain ⟨_hevs, Hc2⟩ :=
          sstep_instr_inv segs ms model msS' evs .SError Hlazy hsvcS hstepS Hss
        cases Hc2
  · exact on_path_no_error segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs Hop Hss
  · exact on_path_no_error segs ec ⟨ms, model⟩ evs Hop Hss

theorem star_dinv (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (c : config) (tr : List event) (c' : config) :
    dinv segs cnt f out ec LH c → star segs c tr c' → dinv segs cnt f out ec LH c' :=
  star_inv segs (dinv segs cnt f out ec LH)
    (dinv_step segs cnt f out ec LH Hcnt H_LH) c tr c'

theorem to_rd_no_error (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) (model : Model) :
    M_loop model → to_rd segs cnt f out ec LH a ms →
      ¬ reaches_error segs ⟨ms, model⟩ := by
  intro HM Hrd
  exact inv_no_reaches_error segs (dinv segs cnt f out ec LH)
    (dinv_step segs cnt f out ec LH Hcnt H_LH)
    (dinv_no_error segs cnt f out ec LH Hcnt) ⟨ms, model⟩ (Or.inl ⟨HM, a, Hrd⟩)

/- -------------------------------------------------------------------------
   Whole-run packaging from the initial state.
   ------------------------------------------------------------------------- -/

theorem drain_obs_iff (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hec : (ec.toNat : Int) < 256)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      drain_from cnt f out ec a0 (in_fs inp) inp.in_stdin tr := by
  intro tr
  have Hst0 : m_stdin (init_model (segments_reserved segs) brk0 mb sp lim inp)
      = inp.in_stdin := rfl
  have Hfs0 : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp)
      = in_fs inp := rfl
  have HM0 : M_loop (init_model (segments_reserved segs) brk0 mb sp lim inp) :=
    init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    have Hd := star_drain_only segs cnt f out ec LH Hcnt Hec H_LH
      (init_config segs pc ph sp brk0 mb rnd lim inp) tr' c Hstar a0
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl HM0 Hrd
    rw [Hst0, Hfs0] at Hd
    exact drain_from_prefix cnt f out ec a0 (in_fs inp) inp.in_stdin tr' tr Hd Hp
  · intro H
    rcases H with ⟨blocks, s', a', HC, Hp, Hpref⟩ |
      ⟨blocks, bsE, s', a', HC, Hp, Hn, Hpref⟩
    · obtain ⟨c, Hstar⟩ :=
        drain_star_admits_ok segs cnt f out ec LH Hcnt H_LH inp.in_stdin blocks s' HC a0 a'
          (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
            inp.in_hwcap)
          (init_model (segments_reserved segs) brk0 mb sp lim inp) HM0 Hst0 Hrd Hp
      rw [Hfs0] at Hstar
      exact ⟨_, c, Hstar, Hpref⟩
    · obtain ⟨s1, HC1, HC2⟩ := chunks_split cnt blocks [bsE] inp.in_stdin s' HC
      obtain ⟨HloE, HhiE, HpreE, _⟩ := chunks_single_inv cnt s1 bsE s' HC2
      obtain ⟨c, Hstar⟩ :=
        drain_star_admits_err segs cnt f out ec LH Hcnt Hec H_LH inp.in_stdin blocks s1 HC1
          a0 a' bsE
          (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
            inp.in_hwcap)
          (init_model (segments_reserved segs) brk0 mb sp lim inp) HM0 Hst0 Hrd Hp
          HloE HhiE HpreE Hn
      rw [Hfs0] at Hstar
      exact ⟨_, c, Hstar, Hpref⟩

theorem drain_no_error (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  refine to_rd_no_error segs cnt f out ec LH Hcnt H_LH a0 _ _
    (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) ?_
  exact Hrd

/- -------------------------------------------------------------------------
   The omni reading: as for `StreamSim`, the loop invariant is a proof of
   `OmniRun.coexec … never_errors` by coinduction, and the trace
   characterisation is the prefix judgment.
   ------------------------------------------------------------------------- -/

theorem to_rd_coexec (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (a : A) (ms : machine_state) (model : Model) :
    M_loop model → to_rd segs cnt f out ec LH a ms → coexec segs ⟨ms, model⟩ never_errors := by
  intro HM Hrd
  exact inv_coexec segs (dinv segs cnt f out ec LH)
    (dinv_step segs cnt f out ec LH Hcnt H_LH)
    (dinv_no_error segs cnt f out ec LH Hcnt) ⟨ms, model⟩ (Or.inl ⟨HM, a, Hrd⟩)

theorem drain_omni_corun (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp never_errors := by
  simpa [omni_corun, mkImage, init_config] using
    to_rd_coexec segs cnt f out ec LH Hcnt H_LH a0 _ _
      (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) Hrd

theorem drain_omni_cosafe (segs : List Segment) (cnt : word) (f : A → byte → Option A)
    (out : A → List byte) (ec : word) (LH : A → machine_state → Prop)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (Hec : (ec.toNat : Int) < 256)
    (H_LH : ∀ (a : A) (ms : machine_state), LH a ms → to_rd segs cnt f out ec LH a ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput) (a0 : A)
    (Hrd : to_rd segs cnt f out ec LH a0
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)) :
    omni_cosafe (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (drain_from cnt f out ec a0 (in_fs inp) inp.in_stdin) := by
  have h : cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp)
      (drain_from cnt f out ec a0 (in_fs inp) inp.in_stdin) := by
    refine (cosafe_obs_iff segs _ _ ?_).mpr ?_
    · -- prefix-closed, through the trace-set characterisation itself
      intro t t' Ht Hp
      exact drain_from_prefix cnt f out ec a0 (in_fs inp) inp.in_stdin t t' Ht Hp
    · intro tr Hobs
      exact (drain_obs_iff segs cnt f out ec LH Hcnt Hec H_LH pc ph sp brk0 mb rnd lim inp
        a0 Hrd tr).mp Hobs
  simpa [omni_cosafe, mkImage, init_config] using h

end Drain

/- =========================================================================
   Pair equivalence: `drain_from cnt f out ec a0 fs0 stdin0` does not mention
   the binary, so two binaries that both satisfy it are observably equivalent
   — ON THE SAME INPUT STREAM, which is what the theorem shape quantifies
   over.  Both binaries must read at the SAME chunk count `cnt` (the trace
   set fixes the admissible chunkings).
   ========================================================================= -/

/-- The omni equivalence of two drain loops on the same input stream, at
    the two role budgets. -/
theorem drain_omni_strong_equiv (A : Type) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word) (a0 : A)
    (source_segs : List Segment) (rLH : A → machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (aLH : A → machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput)
    (Hec : (ec.toNat : Int) < 256)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (HrLH : ∀ (a : A) (ms : machine_state),
      rLH a ms → to_rd source_segs cnt f out ec rLH a ms)
    (HaLH : ∀ (a : A) (ms : machine_state),
      aLH a ms → to_rd target_segs cnt f out ec aLH a ms)
    (Hr : to_rd source_segs cnt f out ec rLH a0
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap))
    (Ha : to_rd target_segs cnt f out ec aLH a0
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · refine coexec_conseq source_segs _ never_errors (covered source_segs) ?_ ?_
    · exact drain_omni_corun source_segs cnt f out ec rLH Hcnt HrLH rpc rph rsp rbrk rmb
        rrnd source_alloc_limit inp a0 Hr
    · intro tr o h
      exact never_errors_covered source_segs tr o h
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (drain_obs_iff source_segs cnt f out ec rLH Hcnt Hec HrLH rpc rph rsp rbrk
        rmb rrnd source_alloc_limit inp a0 Hr tr).trans
        (drain_obs_iff target_segs cnt f out ec aLH Hcnt Hec HaLH apc aph asp abrk amb
          arnd target_alloc_limit inp a0 Ha tr).symm
    · exact drain_omni_corun target_segs cnt f out ec aLH Hcnt HaLH apc aph asp abrk amb
        arnd target_alloc_limit inp a0 Ha

theorem drain_strong_equiv (A : Type) (cnt : word)
    (f : A → byte → Option A) (out : A → List byte) (ec : word) (a0 : A)
    (source_segs : List Segment) (rLH : A → machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (aLH : A → machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (inp : ProcInput)
    (Hec : (ec.toNat : Int) < 256)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (HrLH : ∀ (a : A) (ms : machine_state),
      rLH a ms → to_rd source_segs cnt f out ec rLH a ms)
    (HaLH : ∀ (a : A) (ms : machine_state),
      aLH a ms → to_rd target_segs cnt f out ec aLH a ms)
    (Hr : to_rd source_segs cnt f out ec rLH a0
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap))
    (Ha : to_rd target_segs cnt f out ec aLH a0
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)) :
    (modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
     equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
           (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (drain_no_error source_segs cnt f out ec rLH Hcnt HrLH rpc rph rsp rbrk rmb rrnd
        rlim inp a0 Hr)
  · right
    constructor
    · intro tr
      exact (drain_obs_iff source_segs cnt f out ec rLH Hcnt Hec HrLH rpc rph rsp rbrk
        rmb rrnd rlim inp a0 Hr tr).trans
        (drain_obs_iff target_segs cnt f out ec aLH Hcnt Hec HaLH apc aph asp abrk amb
          arnd alim inp a0 Ha tr).symm
    · exact drain_no_error target_segs cnt f out ec aLH Hcnt HaLH apc aph asp abrk amb
        arnd alim inp a0 Ha

/-! -/

section Sanity

example : procs (fun (a : Nat) (_ : byte) => some (a + 1)) 0 [] = some 0 := rfl

example : procs (fun (a : Nat) (_ : byte) => some (a + 1)) 0 [7, 8] = some 2 := rfl

example : procs (fun (_ : Nat) (_ : byte) => (none : Option Nat)) 0 [7] = none := rfl

example : reads [] = [] := rfl

example : reads [[7], []] = [event.ReadEv (BitVec.ofInt 64 0) 7] := rfl

example : reads_ch (BitVec.ofInt 64 0) [[7, 8]] =
    [event.ReadEv (BitVec.ofInt 64 0) 7, event.ReadEv (BitVec.ofInt 64 0) 8] := rfl

example : out_tail (fun (_ : Nat) => [9]) IEof 0 [] =
    [event.WriteEv (BitVec.ofInt 64 1) 9, event.ExitEv (BitVec.ofInt 64 0) []] := rfl

example : out_tail (fun (_ : Nat) => [9]) (ICons 7 IEof) 0 [] = [] := rfl

example : block_ok (BitVec.ofInt 64 4) [1, 2] := by
  unfold block_ok
  decide

example : ¬ block_ok (BitVec.ofInt 64 4) [] := by
  unfold block_ok
  decide

example : drain_from (BitVec.ofInt 64 4) (fun (a : Nat) (_ : byte) => some a) (fun _ => [])
    (BitVec.ofInt 64 0) 0 [] IEof [] :=
  drain_from_nil _ _ _ _ _ _ _

end Sanity
