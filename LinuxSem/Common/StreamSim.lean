/-
  * Common.StreamSim — reusable star-semantics infrastructure for binaries
    that loop { n = read(0, buf, cnt); if n <= 0 exit(0); write(1, buf, n) }
    with a single cnt-byte buffer (streamcat).

  TRUST BOUNDARY: image-INDEPENDENT proof library, written against the
  star-based `LinuxProcessSem.Run` trace semantics.

  Channel ids, counts and exit codes are `word = BitVec 64`; blocks are
  `List byte` with `byte = BitVec 8`.  Following the ExitSim/CatSim
  conventions:

  - the read-syscall number test is Z-characterized: the pending number
    `x8` satisfies `(x8.toNat : Int) = 63` (mirroring CatSim's
    `tw_write`; avoids pinning a particular `BitVec` literal spelling), and
    `ReadPend`/`WrPend` carry that `x8` existentially;
  - fd/channel 0 and 1 are spelled `BitVec.ofInt 64 0` / `BitVec.ofInt 64 1`
    (the `init_model` spelling);
  - the chunk size is `cnt : word` with the hypothesis
    `0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max`; block-length
    bounds are `Int` comparisons over `(bs.length : Int)` and `cnt.toNat`;
  - block clauses are typed away by `byte = BitVec 8` (`block_ok` is
    2 conjuncts).

  Under the current model a channel read on fd 0 (count cnt > 0, channel
  not yet at EOF, destination buffer writable-mapped) has EXACTLY these
  admissible outcomes:

  - EOF-now: ret 0, no writes, no events; EOF becomes STICKY in the model,
    so the program's n<=0 exit path is LIVE and ends the trace with
    `ExitEv 0 fs0`;
  - any 1..cnt bytes `bs` of the environment's choosing, written into the
    buffer and recorded one byte-carrying `ReadEv 0 b` per byte.  Short
    reads are real.

  A single channel write to fd 1 delivers a nonempty prefix of the
  environment's choosing — one `WriteEv 1 b` per delivered byte — and
  leaves the model untouched.  The binaries therefore echo each block
  through a put-style RETRY loop (WallSim's `to_wall` node): however the
  deliveries chunk, they concatenate to exactly the block, so each
  iteration contributes the `ReadEv`s of its block followed by ALL of
  its `WriteEv`s.  Hence the observable trace set of a streamcat-shaped
  binary is exactly `stream_traces cnt fs0`: the prefixes of

      flat_map iter_ev blocks ++ [ExitEv 0 fs0]

  over all lists of admissible blocks (a prefix of the never-EOF
  infinite run lies within finitely many blocks, so this form also
  covers non-terminating resolutions).

  The per-binary proof supplies a loop-head predicate `LH` and a proof
  that every `LH` state runs (deterministically) to a read-pending ecall
  state (`to_rd`) whose EOF continuation reaches an exit(0) ecall and
  whose every-bytes continuation reaches the echo write-pending state
  with a write-all derivation (`WallSim.to_wall`) of the whole block
  down to an `LH` state.  This file turns that single per-iteration
  fact into the full trace characterization (`stream_obs_iff`), the
  no-error fact, and the pair equivalence (`stream_strong_equiv`).

  NOTES.

  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `bv_and` → `&&&`, `length` →
    `List.length`, `lia` → `omega`.
  - `Section Loop`'s `Variable segs : list Segment` / `LH` / `cnt` become
    EXPLICIT LEADING PARAMETERS of every declaration that mentions them, in
    that order (`segs`, `LH`, `cnt`), exactly as `ExitSim`/`WallSim` do for
    their sections.   - `mkCfg ms model` is the `config` constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` constructor
    `⟨sp, brk0, mb, rnd⟩`; `mkEffect r ws zs` is `mkEffect r ws zs`;
    `mkImage segs pc ph` is `mkImage segs pc ph`.
  - `ms_writable_byte segs ms` takes the loaded segments explicitly (where
    `RiscvSemantics` has them as a `WithMemImage` section variable), so the
     `ms_writable_byte segs ms` spelling is already this tree's.
 On the streams this file
    quantifies over (the model never builds a stream that resumes after
    `none`), that is the same function; `Init`'s inputs are the only
    streams the theorems of this file are instantiated at.
  - `check_read`'s  `cbv beta iota` / `norm_fd32` normalization is
    a single `simp only` in this tree: `fd32` of a concrete `BitVec` word is
    the word by computation, so no `Ltac` is needed.
-/
import LinuxSem.Common.WallSim
import LinuxSem.Common.StreamExec
import LinuxSem.Common.SimInv
import LinuxSem.Checks.Sys.Fs.ReadWrite
import LinuxSem.Common.SharedFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.StreamSim
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

variable [fx : FPState]

/- =========================================================================
   Syscall-input decoding facts (in addition to ExitSim/CatSim's).
   ========================================================================= -/

theorem in_arg1_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := rfl

/-- Which arm answers this number, on the SPEC side.  `syscall_spec` is
    `dispatch spec_table`, so fixing the number settles the table lookup by
    conversion — the same one-line argument `Checks.Sys.DispatchCompute`
    makes for `check_syscall`, made here so that this file needs only the
    read checker rather than the module restating every arm's. -/
theorem syscall_spec_read (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : Outcome SyscallEffect Model event) :
    (x8.toNat : Int) = 63 →
    (Specs.syscall_spec (sys_input segs ms x8) model o ↔
      Sys.Fs.ReadWrite.read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (sys_input segs ms x8) model o) := by
  intro Hno
  unfold Specs.syscall_spec
  have hlookup : Sys.Dispatch.lookup_arm spec_table
      (((sys_input segs ms x8).in_sysno).toNat : Int)
      = some (arm 63 (fun i => Sys.Fs.ReadWrite.read_spec (fd32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2))) := by
    rw [in_sysno_sys_input, Hno]
    rfl
  rw [Sys.Dispatch.dispatch_arm spec_table (sys_input segs ms x8) model o
    (arm 63 (fun i => Sys.Fs.ReadWrite.read_spec (fd32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2))) hlookup]
  rfl

theorem in_arg2_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := rfl

theorem in_wmem_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_wmem = ms_writable_byte segs ms := rfl

/- =========================================================================
   Small word facts.  (`w_is0_pos` lives in `LinuxProcessSem.Specs`, which
   this file imports, so the write-count gate has a single derivation.)
   ========================================================================= -/

/-- The masked exit code of exit(0). -/
theorem band0_255 :
    (BitVec.ofInt 64 0) &&& (BitVec.ofInt 64 255) = BitVec.ofInt 64 0 := by decide

/- =========================================================================
   Model helpers.
   ========================================================================= -/

theorem m_fs_with_stdin (s : InputStream) (m : Model) : m_fs (with_stdin s m) = m_fs m := rfl

theorem m_halted_with_stdin (s : InputStream) (m : Model) :
    m_halted (with_stdin s m) = m_halted m := rfl

theorem m_fds_with_stdin (s : InputStream) (m : Model) :
    m_fds (with_stdin s m) = m_fds m := rfl

theorem m_vm_lazy_with_stdin (s : InputStream) (m : Model) :
    m_vm_lazy (with_stdin s m) = m_vm_lazy m := rfl

/-- The model invariant maintained across loop iterations: fd 0/1 are the
    stdin/stdout channels, and the model is not halted.  Nothing is said
    about WHAT is left in `m_stdin`: it shrinks as the loop runs, and each
    lemma below relates it to the blocks delivered so far.  (End of
    input is the stream's own `IEof`, so the invariant need not say
    that stdin has not yet delivered EOF.  Nor is there a byte-range
    condition: the stream's elements are `byte`.) -/
def M_loop (model : Model) : Prop :=
  fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
    some (FdEntry.FdChannel (BitVec.ofInt 64 0)) ∧
  fd_lookup (m_fds model) (BitVec.ofInt 64 1) =
    some (FdEntry.FdChannel (BitVec.ofInt 64 1)) ∧
  m_halted model = none ∧
  m_vm_lazy model = []

theorem init_M_loop (reserved : List (word × word)) (brk0 mb sp : word) (lim : Int)
    (inp : ProcInput) :
    M_loop (init_model reserved brk0 mb sp lim inp) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Consuming a read block preserves the invariant. -/
theorem M_loop_take (k : Nat) (model : Model) (H : M_loop model) :
    M_loop (with_stdin (stream_take (m_stdin model) k).2 model) := by
  obtain ⟨H0, H1, Hh, Hlazy⟩ := H
  exact ⟨H0, H1, Hh, Hlazy⟩

theorem M_loop_fd1chan (model : Model) (H : M_loop model) : fd1chan model := H.2.1

/- =========================================================================
   The writable-view range check, reduced to a vm_compute-able boolean over
   the static segment image.  `ms_writable_byte` consults the writable
   overlay FIRST and falls back to the segment bytes; an overlay entry can
   only override a defined segment byte with another defined byte, so if the
   segment view alone is defined on the whole range the writable view is too,
   for EVERY machine state.  Addresses are `word`s; the segment lookup is the
   interpreter's Z-comparison `find_segment` (segments are N-based snapshot
   data).
   ========================================================================= -/

/-- `wseg_ok segs a n`: the static segment view is defined AND writable on
    the `n` bytes starting at `a` — the `vm_compute`-able premiss that the
    writable view is defined there (`wseg_ok_wdef`). -/
def wseg_ok (segs : List Segment) (a : word) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n + 1 =>
      match find_segment segs (a.toNat : Int) 1 with
      | some seg =>
          (seg_writable seg &&
            (match segment_byte_at seg.seg_bytes (a.toNat - seg.seg_base) with
             | some _ => true
             | none => false) &&
            wseg_ok segs (a + 1) n)
      | none => false

theorem wseg_ok_read_aux (segs : List Segment) (n : Nat) :
    ∀ (a : word) (ms : machine_state), wseg_ok segs a n = true →
      ∃ w, read_bytes_aux (ms_writable_byte segs ms) a n = some w := by
  induction n with
  | zero =>
      intro a ms _
      exact ⟨[], rfl⟩
  | succ n ih =>
      intro a ms H
      cases hseg : find_segment segs (a.toNat : Int) 1 with
      | none =>
          simp only [wseg_ok, hseg] at H
          exact absurd H (by simp)
      | some seg =>
          simp only [wseg_ok, hseg] at H
          simp only [Bool.and_eq_true] at H
          obtain ⟨Hwrbyte, Hrec⟩ := H
          obtain ⟨Hwr, Hbyte⟩ := Hwrbyte
          cases hb : segment_byte_at seg.seg_bytes (a.toNat - seg.seg_base) with
          | none =>
              simp only [hb] at Hbyte
              exact absurd Hbyte (by simp)
          | some b =>
              simp only [hb] at Hbyte
              obtain ⟨w, Hw⟩ := ih (a + 1) ms Hrec
              have Hdef : ∃ b0, ms_writable_byte segs ms a = some b0 := by
                unfold ms_writable_byte wview
                cases hm : ms.ms_mem a with
                | some b' => exact ⟨b', rfl⟩
                | none =>
                    simp only [hm, hseg, Hwr, hb, Bool.true_and, ite_true]
                    exact ⟨b, rfl⟩
              obtain ⟨b0, Hb0⟩ := Hdef
              refine ⟨b0 :: w, ?_⟩
              simp only [read_bytes_aux, Hb0, Hw]

theorem wseg_ok_wdef (segs : List Segment) (a len : word) (ms : machine_state)
    (H : wseg_ok segs a (word_to_nat len) = true) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) a len = some w := by
  rw [read_bytes_map_eq]
  exact wseg_ok_read_aux segs (word_to_nat len) a ms H

/- =========================================================================
   Channel-read spec facts (fd 0, count `cnt`), through the verified checker.
   Parameterized over the chunk count `cnt` (audit 1.1/3.1): every consumer
   (StreamSim's own loop shape below, DrainSim's 1024-byte shape, ...)
   instantiates `cnt` directly instead of re-proving this family.
   `Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max` is
   needed only to discharge `w_is0 cnt = false` (a literal fact when `cnt` is
   a numeral, but not definitionally so for an abstract `cnt`).  The pending
   syscall number is Z-characterized `((x8.toNat : Int) = 63`, the
   dispatcher's test).

   Which bytes a read delivers is fixed by the model's remaining input
   stream `m_stdin`: the two shapes below are end-of-input
   (`m_stdin model 0 = none`, return 0) and deliver-the-`bs.length`-byte
   prefix of the remaining input (which then advances past it).
   ========================================================================= -/

/-- At least one byte of the destination is writable — the checker's
    fail-closed guard — whenever the whole `cnt`-byte buffer is. -/
theorem read0_wmem1 (cnt : word) (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (w : List byte)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w) :
    ∃ w1, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1)
            (BitVec.ofInt 64 1) = some w1 := by
  rw [in_wmem_sys_input]
  refine ⟨_, read_bytes_map_prefix _ _ cnt _ w ?_ Hw⟩
  have h1 : ((BitVec.ofInt 64 1).toNat : Int) = 1 := by decide
  omega

/-- The destination holds everything the stream could supply to this
    count: `read_spec`'s partial-destination decline does not fire when
    the whole `cnt` range is writable, since the bytes the source can
    supply are at most the clamped count. -/
theorem read0_wmem_need (cnt : word) (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (w : List byte)
    (s : InputStream)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w) :
    ∃ wn, read_bytes_map (sys_input segs ms x8).in_wmem (ms_gpr ms 1)
            (len_word (stream_take_z s (rw_count_clamp cnt)).1) = some wn := by
  rw [in_wmem_sys_input]
  have hcl := rw_count_clamp_of_rw cnt Hcnt.2
  have hlen := stream_take_length (rw_count_clamp cnt).toNat s
  have hcast : ((rw_count_clamp cnt).toNat : Int) = (cnt.toNat : Int) := by
    rw [hcl]; simp
  have h1 : ((stream_take_z s (rw_count_clamp cnt)).1.length : Int) ≤ (cnt.toNat : Int) := by
    have h2 : ((stream_take_z s (rw_count_clamp cnt)).1.length : Int)
        ≤ ((rw_count_clamp cnt).toNat : Int) := by
      exact_mod_cast hlen
    omega
  have hlt : ((stream_take_z s (rw_count_clamp cnt)).1.length : Int) < two_pow_64 := by
    have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
    omega
  refine ⟨_, read_bytes_map_prefix _ _ cnt _ w ?_ Hw⟩
  rw [u_len_word _ hlt]
  exact h1

/-- The EOF read, through the checker: at end of input a `cnt`-byte channel
    read on fd 0 answers 0 with no writes and no events. -/
theorem read0_check_eof (cnt : word) (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Heof : m_stdin model 0 = none)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    Checks.Sys.Fs.ReadWrite.check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
      (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (BitVec.ofInt 64 0) [] []) model = .CheckOk model [] := by
  have Hcnt0 : w_is0 cnt = false := w_is0_pos cnt (by omega)
  have hz : w_is0 (BitVec.ofInt 64 0) = true := by decide
  have hfd0 : fd32 (BitVec.ofInt 64 0) = BitVec.ofInt 64 0 := by decide
  have hieof : m_stdin model 0 = none := Heof
  rw [Hg0, Hg2]
  simp only [Checks.Sys.Fs.ReadWrite.check_read, hfd0, Hfd, hz, Hcnt0, Haok, hieof,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, check_ret_only,
    mkEffect, PropExec.bv_eqb_refl]

/-- The bytes read, through the checker: delivering the `bs.length`-byte
    prefix `bs` of the remaining input (with `1 ≤ length bs ≤ cnt`) answers
    `length bs`, writes exactly `(buf, bs)`, advances the stream past it and
    emits one `ReadEv 0` per byte. -/
theorem read0_check_bytes (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (bs : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true)
    (Hlo : 1 ≤ (bs.length : Int)) (Hhi : (bs.length : Int) ≤ (cnt.toNat : Int))
    (Hpre : (stream_take (m_stdin model) bs.length).1 = bs) :
    Checks.Sys.Fs.ReadWrite.check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
      (ms_gpr ms 1) (ms_gpr ms 2)
      (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
    = .CheckOk (with_stdin (stream_take (m_stdin model) bs.length).2 model)
        (bs.map (event.ReadEv (BitVec.ofInt 64 0))) := by
  obtain ⟨w1, Hw1⟩ := read0_wmem1 cnt Hcnt segs ms x8 w Hw
  obtain ⟨wn, Hwn⟩ := read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw
  have Hcnt0 : w_is0 cnt = false := w_is0_pos cnt (by omega)
  have hz : w_is0 (BitVec.ofInt 64 0) = true := by decide
  have hfd0 : fd32 (BitVec.ofInt 64 0) = BitVec.ofInt 64 0 := by decide
  have hcl := rw_count_clamp_of_rw cnt Hcnt.2
  have hlek : ((len_word bs).toNat : Int) ≤ (cnt.toNat : Int) := by
    have hlt : (bs.length : Int) < two_pow_64 := by
      have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
      omega
    rw [u_len_word bs hlt]
    exact Hhi
  have hwmem : wmem_ok (sys_input segs ms x8) (ms_gpr ms 1) (len_word bs) = true := by
    refine wmem_ok_of_full (sys_input segs ms x8) (ms_gpr ms 1) cnt w (len_word bs) ?_ hlek
    rw [in_wmem_sys_input]
    exact Hw
  have d1 : decide (1 ≤ (bs.length : Int)) = true := decide_eq_true Hlo
  have d2 : decide ((bs.length : Int) ≤ rw_count_clamp cnt) = true := by
    rw [hcl]; exact decide_eq_true Hhi
  have hl : listN_eqb (stream_take (m_stdin model) bs.length).1 bs = true := by
    rw [Hpre]; exact (listN_eqb_eq bs bs).mpr rfl
  have hcond : (bv_eqb (ms_gpr ms 1) (ms_gpr ms 1) && bv_eqb (len_word bs) (len_word bs)
      && decide (1 ≤ (bs.length : Int)) && decide ((bs.length : Int) ≤ rw_count_clamp cnt)
      && listN_eqb (stream_take (m_stdin model) bs.length).1 bs
      && wmem_ok (sys_input segs ms x8) (ms_gpr ms 1) (len_word bs)) = true := by
    rw [PropExec.bv_eqb_refl, PropExec.bv_eqb_refl, d1, d2, hl, hwmem]
    rfl
  rw [Hg0, Hg2]
  cases hs : m_stdin model 0 with
  | none =>
      exfalso
      obtain ⟨k, hk⟩ : ∃ k, bs.length = k + 1 := ⟨bs.length - 1, by omega⟩
      rw [hk] at Hpre
      rw [stream_take_none hs k] at Hpre
      rw [← Hpre] at Hlo
      simp at Hlo
  | some b0 =>
      simp only [Checks.Sys.Fs.ReadWrite.check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, mkEffect,
        Hw1, Hwn, hcond]

/-- The EOF answer, on the SPEC side. -/
theorem read0_ok_eof (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Heof : m_stdin model 0 = none)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) model []) := by
  refine (syscall_spec_read segs ms x8 model _ Hno).mpr ?_
  exact check_read_sound_ok _ _ _ _ _ _ _ _
    (read0_check_eof cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok)

/-- The delivered-bytes answer, on the SPEC side. -/
theorem read0_ok_bytes (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (bs : List byte)
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
        (bs.map (event.ReadEv (BitVec.ofInt 64 0)))) := by
  refine (syscall_spec_read segs ms x8 model _ Hno).mpr ?_
  exact check_read_sound_ok _ _ _ _ _ _ _ _
    (read0_check_bytes cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre)

/-- The read never takes the error transition (the destination is writable). -/
theorem read0_no_unmodeled (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (w : List byte)
    (Hno : (x8.toNat : Int) = 63)
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = some w)
    (Haok : access_okb (ms_gpr ms 1) (cnt.toNat : Int) = true) :
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hspec
  obtain ⟨w1, Hw1⟩ := read0_wmem1 cnt Hcnt segs ms x8 w Hw
  obtain ⟨wn, Hwn⟩ := read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw
  have Hcnt0 : w_is0 cnt = false := w_is0_pos cnt (by omega)
  have hz : w_is0 (BitVec.ofInt 64 0) = true := by decide
  have hfd0 : fd32 (BitVec.ofInt 64 0) = BitVec.ofInt 64 0 := by decide
  have hck := check_read_complete_unmodeled (sys_input segs ms x8) (fd32 (ms_gpr ms 0))
    (ms_gpr ms 1) (ms_gpr ms 2) model (mkEffect (BitVec.ofInt 64 0) [] [])
    ((syscall_spec_read segs ms x8 model _ Hno).mp Hspec)
  rw [Hg0, Hg2] at hck
  cases hs : m_stdin model 0 with
  | none =>
      simp only [Checks.Sys.Fs.ReadWrite.check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, mkEffect] at hck
      exact check_ret_only_no_unmodeled _ _ _ _ hck
  | some b0 =>
      simp only [Checks.Sys.Fs.ReadWrite.check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, mkEffect,
        Hw1, Hwn] at hck
      exact absurd hck (by simp)

/-- Every admissible outcome of the read IS one of the two shapes, and
    WHICH one is decided by the remaining input, not by the environment.
    `InputStream` is a total function here, so an input that happens to end
    at 0 need not be `IEof`; the read spec and the checker observe exactly
    `m_stdin m 0`, and every use below consumes the fact in that form. -/
theorem read0_ok_inv (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (x8 : word) (model : Model) (buf : word)
    (w : List byte) (eff : SyscallEffect) (model' : Model) (evs : List event)
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
        evs = bs.map (event.ReadEv (BitVec.ofInt 64 0))) := by
  obtain ⟨w1, Hw1⟩ := read0_wmem1 cnt Hcnt segs ms x8 w (by rw [Hg1]; exact Hw)
  obtain ⟨wn, Hwn⟩ :=
    read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) (by rw [Hg1]; exact Hw)
  rw [Hg1] at Hw1 Hwn
  have Hcnt0 : w_is0 cnt = false := w_is0_pos cnt (by omega)
  have hz : w_is0 (BitVec.ofInt 64 0) = true := by decide
  have hfd0 : fd32 (BitVec.ofInt 64 0) = BitVec.ofInt 64 0 := by decide
  have hcl := rw_count_clamp_of_rw cnt Hcnt.2
  have hck : check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
      (ms_gpr ms 2) eff model = .CheckOk model' evs := by
    refine check_read_complete_ok _ _ _ _ _ _ _ _ ?_
    exact (syscall_spec_read segs ms x8 model _ Hno).mp Hspec
  rw [Hg0, Hg1, Hg2] at hck
  cases hs : m_stdin model 0 with
  | none =>
      simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
      obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff _ _ _ _ _ _).mp hck
      exact Or.inl ⟨rfl, heff, hm, hevs⟩
  | some b0 =>
      simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ite_false, ite_true, mkEffect, Hw1, Hwn] at hck
      obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
      cases ws with
      | nil =>
        simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
          Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
        exact absurd hck (by simp)
      | cons p rest =>
        obtain ⟨a, bs⟩ := p
        cases rest with
        | cons q rest2 =>
          simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
            Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
          exact absurd hck (by simp)
        | nil =>
          cases zs with
          | cons z zs' =>
            simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
              Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
            exact absurd hck (by simp)
          | nil =>
            cases us with
            | cons u us' =>
              simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
                Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
              exact absurd hck (by simp)
            | nil =>
              cases cs with
              | cons c cs' =>
                simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
                  Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
                exact absurd hck (by simp)
              | nil =>
                cases copyins with
                | cons ci ci' =>
                  simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
                    Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hck
                  exact absurd hck (by simp)
                | nil =>
                  simp only [check_read, hfd0, Hfd, hz, Hcnt0, Haok, hs, Bool.not_true,
                    Bool.not_false, Bool.false_eq_true, ite_false, ite_true, mkEffect,
                    Hw1, Hwn] at hck
                  by_cases hc : (bv_eqb a buf && bv_eqb ret (len_word bs)
                      && decide (1 ≤ (bs.length : Int))
                      && decide ((bs.length : Int) ≤ rw_count_clamp cnt)
                      && listN_eqb (stream_take (m_stdin model) bs.length).1 bs
                      && wmem_ok (sys_input segs ms x8) buf (len_word bs)) = true
                  · rw [ite_eq_left hc] at hck
                    cases hck
                    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
                      Bool.and_eq_true, Bool.and_eq_true] at hc
                    obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, _⟩ := hc
                    rw [bv_eqb_eq] at hA hB
                    rw [listN_eqb_eq] at hE
                    have hC' : 1 ≤ (bs.length : Int) := of_decide_eq_true hC
                    have hD' : (bs.length : Int) ≤ (cnt.toNat : Int) := by
                      have h := of_decide_eq_true hD
                      rw [hcl] at h
                      exact h
                    exact Or.inr ⟨bs, hC', hD', hE, by rw [hA, hB], rfl, rfl⟩
                  · rw [ite_eq_right hc] at hck
                    exact absurd hck (by simp)

/- =========================================================================
   One-step inversion at a read-pending config.
   ========================================================================= -/

/-- The ONLY transitions out of a read-pending configuration: the EOF answer
    (return 0, straight on) or a delivery of `bs` (the read effect applied,
    the stream advanced, one `ReadEv 0` per byte).  The error, exit and kill
    transitions are all excluded by the read's own shape. -/
theorem sstep_read_inv (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (segs : List Segment) (ms : machine_state) (model : Model) (buf : word) (x8 : word)
    (w : List byte) (evs : List event) (st : step_to)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hfd : fd_lookup (m_fds model) (BitVec.ofInt 64 0) =
      some (FdEntry.FdChannel (BitVec.ofInt 64 0)))
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 63)
    (Hg0 : ms_gpr ms 0 = BitVec.ofInt 64 0) (Hg1 : ms_gpr ms 1 = buf)
    (Hg2 : ms_gpr ms 2 = cnt)
    (Hw : read_bytes_map (ms_writable_byte segs ms) buf cnt = some w)
    (Haok : access_okb buf (cnt.toNat : Int) = true)
    (Hss : sstep segs ⟨ms, model⟩ evs st) :
    (m_stdin model 0 = none ∧ evs = [] ∧
      st = .SNext ⟨advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0)), model⟩) ∨
    (∃ bs, 1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cnt.toNat : Int) ∧
        (stream_take (m_stdin model) bs.length).1 = bs ∧
        evs = bs.map (event.ReadEv (BitVec.ofInt 64 0)) ∧
        st = .SNext ⟨advance_past_svc
            (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])),
          with_stdin (stream_take (m_stdin model) bs.length).2 model⟩) := by
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_fault ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x8' eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      rcases read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model1 evs
          Hno Hfd Hg0 Hg1 Hg2 Hw Haok hspec with
        ⟨hst, heff, hm, hevs⟩ | ⟨bs, hlo, hhi, hpre, heff, hm, hevs⟩
      · refine Or.inl ⟨hst, hevs, ?_⟩
        rw [heff] at hmat ⊢
        rw [hm] at hmat
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        have h2 : model2 = model := (Option.some.inj hmat).symm
        rw [h2]
        rw [apply_effect_no_write]
      · refine Or.inr ⟨bs, hlo, hhi, hpre, hevs, ?_⟩
        rw [heff] at hmat ⊢
        rw [hm] at hmat
        have hlazy' : m_vm_lazy
            (with_stdin (stream_take (m_stdin model) bs.length).2 model) = [] := by
          rw [m_vm_lazy_with_stdin]; exact Hlazy
        rw [materialize_model_accesses_no_lazy _ _ hlazy'] at hmat
        have h2 : model2 = with_stdin (stream_take (m_stdin model) bs.length).2 model :=
          (Option.some.inj hmat).symm
        rw [h2]
  | syscall_materialization_fault ms0 model0 x8' eff model1 evs0 hh hsvc hspec hh' hmat =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      rcases read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model1 evs0
          Hno Hfd Hg0 Hg1 Hg2 Hw Haok hspec with
        ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
      · rw [hm] at hmat
        rw [materialize_model_accesses_no_lazy model _ Hlazy] at hmat
        exact absurd hmat (by simp)
      · rw [hm] at hmat
        have hlazy' : m_vm_lazy
            (with_stdin (stream_take (m_stdin model) bs.length).2 model) = [] := by
          rw [m_vm_lazy_with_stdin]; exact Hlazy
        rw [materialize_model_accesses_no_lazy _ _ hlazy'] at hmat
        exact absurd hmat (by simp)
  | exit ms0 model0 x8' eff model1 evs0 code hh hsvc hspec hh' hk =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      rcases read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model1 evs0
          Hno Hfd Hg0 Hg1 Hg2 Hw Haok hspec with
        ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
      · rw [hm, Hh] at hh'
        exact absurd hh' (by simp)
      · rw [hm, m_halted_with_stdin, Hh] at hh'
        exact absurd hh' (by simp)
  | killed ms0 model0 x8' eff model1 evs0 sig hh hsvc hspec hk =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      rcases read0_ok_inv cnt Hcnt segs ms x8 model buf w eff model1 evs0
          Hno Hfd Hg0 Hg1 Hg2 Hw Haok hspec with
        ⟨_, _, hm, _⟩ | ⟨bs, _, _, _, _, hm, _⟩
      · rw [hm, m_killed_of_m_halted_none model Hh] at hk
        exact absurd hk (by simp)
      · rw [hm, m_killed_with_stdin, m_killed_of_m_halted_none model Hh] at hk
        exact absurd hk (by simp)
  | syscall_unmodeled ms0 model0 x8' hh hsvc hspec =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      exact read0_no_unmodeled cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok) hspec

/- =========================================================================
   The trace-set characterization.
   ========================================================================= -/

/-- How a run CHUNKS its input: `chunks cnt s blocks s'` says the loop can
    consume `s` as the successive read blocks `blocks`, leaving `s'`
    unread.  Each block is a nonempty prefix of at most `cnt` bytes of
    what remains — WHICH bytes is fixed by the input, only how many is
    the read's (short-read) nondeterminism. -/
inductive chunks (cnt : word) : InputStream → List (List byte) → InputStream → Prop where
  | nil (s : InputStream) : chunks cnt s [] s
  | cons (s : InputStream) (bs : List byte) (blocks : List (List byte))
      (s'' : InputStream) :
      1 ≤ (bs.length : Int) →
      (bs.length : Int) ≤ (cnt.toNat : Int) →
      (stream_take s bs.length).1 = bs →
      chunks cnt (stream_take s bs.length).2 blocks s'' →
      chunks cnt s (bs :: blocks) s''

/-- Chunkings compose and decompose along list concatenation — used by
    consumers (DrainSim) that need to talk about "the blocks before the
    last one". -/
theorem chunks_app (cnt : word) (s : InputStream) (l1 : List (List byte))
    (s1 : InputStream) (l2 : List (List byte)) (s2 : InputStream) :
    chunks cnt s l1 s1 → chunks cnt s1 l2 s2 → chunks cnt s (l1 ++ l2) s2 := by
  intro H1
  revert l2 s2
  induction H1 with
  | nil s =>
      intro l2 s2 H2
      exact H2
  | cons s bs blocks s'' hlo hhi hpre hc ih =>
      intro l2 s2 H2
      exact chunks.cons s bs (blocks ++ l2) s2 hlo hhi hpre (ih l2 s2 H2)

theorem chunks_split (cnt : word) (l1 : List (List byte)) :
    ∀ (l2 : List (List byte)) (s s2 : InputStream),
      chunks cnt s (l1 ++ l2) s2 →
      ∃ s1, chunks cnt s l1 s1 ∧ chunks cnt s1 l2 s2 := by
  induction l1 with
  | nil =>
      intro l2 s s2 H
      exact ⟨s, chunks.nil s, by simpa using H⟩
  | cons bs l1 ih =>
      intro l2 s s2 H
      cases H with
      | cons s0 bs0 blocks0 s3 hlo hhi hpre hc =>
          obtain ⟨s1, H1, H2⟩ := ih l2 _ _ hc
          exact ⟨s1, chunks.cons s bs l1 s1 hlo hhi hpre H1, H2⟩

/-- Inversion for a one-block chunking. -/
theorem chunks_single_inv (cnt : word) (s : InputStream) (bs : List byte)
    (s' : InputStream) :
    chunks cnt s [bs] s' →
    1 ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cnt.toNat : Int) ∧
    (stream_take s bs.length).1 = bs ∧ s' = (stream_take s bs.length).2 := by
  intro H
  cases H with
  | cons s0 bs0 blocks0 s2 hlo hhi hpre hc =>
      cases hc with
      | nil s3 =>
          exact ⟨hlo, hhi, hpre, rfl⟩

/-- One loop iteration's events, reading on channel `rch`: the block is
    read byte-by-byte and echoed byte-by-byte to stdout.  The echo write
    may take several (possibly short) channel writes, but the put-style
    retry loop always delivers the WHOLE block, so — chunking-
    independently — an iteration's write contribution is all of `bs`.

    Only the READ channel is a parameter here; the write channel has its
    own parametric family in `ShapeAlg.t_writes_ch`. -/
def iter_ev_ch (rch : word) (bs : List byte) : List event :=
  bs.map (event.ReadEv rch) ++ bs.map (event.WriteEv (BitVec.ofInt 64 1))

/-- One loop iteration's events, reading on stdin — the only channel a
    read can name (`ReadWrite.read_spec` answers -EBADF on the rest). -/
def iter_ev (bs : List byte) : List event :=
  iter_ev_ch (BitVec.ofInt 64 0) bs

/-- What follows the last block: the loop exits 0 exactly when the input
    has run out.  While input remains, the run has not stopped — the
    trace so far is just a prefix.

     matches the stream (`IEof` / `ICons _ _`); over
    the function encoding the same test is the observation `s 0`. -/
def eof_tail (s : InputStream) (fs : Fs.Fs) : List event :=
  match s 0 with
  | none => [event.ExitEv (BitVec.ofInt 64 0) fs]
  | some _ => []

/-- The trace set of an echo loop with a `cnt`-byte buffer reading
    channel `rch` on input `s`: the prefixes of

        flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs

    over all chunkings of `s` into read blocks. -/
def stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : List event) : Prop :=
  ∃ blocks s',
    chunks cnt s blocks s' ∧
    is_prefix tr (blocks.flatMap (iter_ev_ch rch) ++ eof_tail s' fs)

/-- The full observable trace set of a streamcat binary with a `cnt`-byte
    buffer on input `s`.  Reads name channel 0 because `ReadWrite.read_spec`
    answers -EBADF on every other.  The exit event appears only in the
    chunkings that reached the end of the input; an INFINITE input
    contributes only the (unbounded, but each finite) block prefixes,
    which is exactly right — such a run never exits. -/
def stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream) (tr : List event) : Prop :=
  stream_traces_ch (BitVec.ofInt 64 0) cnt fs s tr

theorem stream_traces_ch_prefix_closed (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr tr' : List event) :
    stream_traces_ch rch cnt fs s tr → is_prefix tr' tr →
      stream_traces_ch rch cnt fs s tr' := by
  intro H Hp'
  obtain ⟨blocks, s', HC, Hp⟩ := H
  exact ⟨blocks, s', HC, is_prefix_trans Hp' Hp⟩

theorem stream_traces_prefix_closed (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr tr' : List event) :
    stream_traces cnt fs s tr → is_prefix tr' tr → stream_traces cnt fs s tr' :=
  stream_traces_ch_prefix_closed _ cnt fs s tr tr'

/- =========================================================================
   The generic loop theory, parameterized over the `cnt`-byte buffer size.
   ========================================================================= -/

/-- The state runs (deterministically) to some loop-head state. -/
def lh_next (segs : List Segment) (LH : machine_state → Prop) (ms : machine_state) : Prop :=
  ∃ ms', msteps segs ms ms' ∧ LH ms'

/-- A write-pending ecall state echoing block `bs`: the environment may
    deliver any nonempty prefix per syscall, so the binary's put-style
    retry loop must deliver ALL of `bs` — across one or more writes —
    and then run back to a loop head.  That is exactly WallSim's
    write-all node with the loop-head continuation. -/
def WrPend (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms : machine_state) : Prop :=
  1 ≤ bs.length ∧ to_wall segs (BitVec.ofInt 64 1) ms bs (lh_next segs LH)

/-- Straight line of instructions to a write-pending state for block `bs`. -/
inductive to_wr (segs : List Segment) (LH : machine_state → Prop) (bs : List byte) :
    machine_state → Prop where
  | twr_here (ms : machine_state) : WrPend segs LH bs ms → to_wr segs LH bs ms
  | twr_step (ms ms' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wr segs LH bs ms' → to_wr segs LH bs ms

/-- A read-pending ecall state (fd 0, count `cnt`, buffer a1 writable),
    together with both continuations:
    - when the input has run out, the run reaches an exit(0) ecall;
    - on any admissible block, the run reaches the echo write and returns to
      a loop head. -/
def ReadPend (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms : machine_state) : Prop :=
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
  -- arithmetic, which wraps at 2^64.  A binary's read buffer is a
  -- link-time or allocator address far under `State.TASK_SIZE`, so this
  -- costs a caller one inequality (`Uaccess.access_okb_intro`).
  access_okb buf (cnt.toNat : Int) = true ∧
  to_exit segs (BitVec.ofInt 64 0)
    (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0))) ∧
  (∀ bs,
    1 ≤ (bs.length : Int) →
    (bs.length : Int) ≤ (cnt.toNat : Int) →
    to_wr segs LH bs (advance_past_svc (apply_effect ms
      (mkEffect (len_word bs) [(buf, bs)] []))))

/-- The `to_wr` analogue of `msteps_to_rd` below: prepend a straight-line
    run to a write-pending derivation.  This is what lets a caller reach
    the echo write through a PROVED `msteps` — e.g. the one a
    `Common/Hoare` triple yields via `triple_msteps` — instead of
    stepping the instructions in the `to_wr` derivation itself. -/
theorem msteps_to_wr (segs : List Segment) (LH : machine_state → Prop)
    (bs : List byte) (ms ms' : machine_state) :
    msteps segs ms ms' → to_wr segs LH bs ms' → to_wr segs LH bs ms := by
  intro H
  induction H with
  | mst_refl ms => intro Hwr; exact Hwr
  | mst_step ms ms' ms'' hsvc hstep h ih =>
      intro Hwr
      exact to_wr.twr_step ms ms' hsvc hstep (ih Hwr)

/-- A write phase IS a write-all tail derivation (the `to_wr` instruction
    prefix becomes `twt_step`s in front of the `to_wall` node). -/
theorem to_wr_wall_tail (segs : List Segment) (LH : machine_state → Prop)
    (bs : List byte) (ms : machine_state) :
    to_wr segs LH bs ms → to_wall_tail segs (BitVec.ofInt 64 1) ms bs (lh_next segs LH) := by
  intro H
  induction H with
  | twr_here ms HWP =>
      obtain ⟨hnb, hw⟩ := HWP
      exact to_wall_tail.twt_more ms bs (lh_next segs LH) hnb hw
  | twr_step ms ms' hsvc hstep hwr ih =>
      exact to_wall_tail.twt_step ms ms' bs (lh_next segs LH) hsvc hstep ih

/-- Straight line of instructions to a read-pending state. -/
inductive to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word) :
    machine_state → Prop where
  | trd_here (ms : machine_state) : ReadPend segs LH cnt ms → to_rd segs LH cnt ms
  | trd_step (ms ms' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_rd segs LH cnt ms' → to_rd segs LH cnt ms

theorem msteps_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms ms' : machine_state) :
    msteps segs ms ms' → to_rd segs LH cnt ms' → to_rd segs LH cnt ms := by
  intro H
  induction H with
  | mst_refl ms => intro Hrd; exact Hrd
  | mst_step ms ms' ms'' hsvc hstep h ih =>
      intro Hrd
      exact to_rd.trd_step ms ms' hsvc hstep (ih Hrd)

/-- The single per-binary hypothesis, applied: every loop head runs to a
    read. -/
theorem lh_next_to_rd (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) (ms : machine_state) :
    lh_next segs LH ms → to_rd segs LH cnt ms := by
  intro ⟨ms', hm, hl⟩
  exact msteps_to_rd segs LH cnt ms ms' hm (H_LH ms' hl)

/- -------------------------------------------------------------------------
   Straight lines are event-free star runs.
   ------------------------------------------------------------------------- -/

theorem to_rd_star (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → to_rd segs LH cnt ms →
    ∃ msR, ReadPend segs LH cnt msR ∧ star segs ⟨ms, model⟩ [] ⟨msR, model⟩ := by
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

theorem to_wr_star (segs : List Segment) (LH : machine_state → Prop) (bs : List byte)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → to_wr segs LH bs ms →
    ∃ msW, WrPend segs LH bs msW ∧ star segs ⟨ms, model⟩ [] ⟨msW, model⟩ := by
  intro Hh Hlazy Hwr
  induction Hwr with
  | twr_here ms HWP => exact ⟨ms, HWP, star.refl _⟩
  | twr_step ms ms' hsvc hstep hwr ih =>
      obtain ⟨msW, HWP, Hstar⟩ := ih
      refine ⟨msW, HWP, ?_⟩
      have hss : sstep segs ⟨ms, model⟩ [] (.SNext ⟨ms', model⟩) := by
        refine sstep.instr ms model ms' model Hh hsvc ?_
        rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]
      have hstep' := star.step ⟨ms, model⟩ [] ⟨ms', model⟩ [] ⟨msW, model⟩ hss Hstar
      simpa using hstep'

/- -------------------------------------------------------------------------
   Admissibility: every stream trace is realized.
   ------------------------------------------------------------------------- -/

theorem stream_star_admits (segs : List Segment) (LH : machine_state → Prop)
    (cnt : word) (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (s : InputStream) (blocks : List (List byte)) (s' : InputStream) :
    chunks cnt s blocks s' →
    ∀ (ms : machine_state) (model : Model),
      M_loop model → m_stdin model = s → to_rd segs LH cnt ms →
      ∃ c, star segs ⟨ms, model⟩
        (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model)) c := by
  intro HC
  induction HC with
  | nil s =>
      intro ms model HM Hst Hrd
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      obtain ⟨msR, HRP, Hstar0⟩ := to_rd_star segs LH cnt ms model Hh Hlazy Hrd
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
      cases hs : s 0 with
      | none =>
          obtain ⟨c, Hstar2⟩ := to_exit_star_admits segs (BitVec.ofInt 64 0)
            (advance_past_svc (set_gpr0 msR (BitVec.ofInt 64 0))) model Hh Hlazy Hex
          refine ⟨c, ?_⟩
          have HssE : sstep segs ⟨msR, model⟩ []
              (.SNext ⟨advance_past_svc (set_gpr0 msR (BitVec.ofInt 64 0)), model⟩) := by
            rw [← apply_effect_no_write msR (BitVec.ofInt 64 0)]
            refine sstep.syscall msR model x8 (mkEffect (BitVec.ofInt 64 0) [] []) model model []
              Hh Hsvc ?_ Hh ?_
            · refine read0_ok_eof cnt Hcnt segs msR x8 model w Hno Hfd0 ?_ Hg0 Hg2 ?_
                (by rw [Hg1]; exact Haok)
              · rw [Hst]; exact hs
              · rw [Hg1]; exact Hw
            · rw [materialize_model_accesses_no_lazy model _ Hlazy]
          have e1 : eof_tail s (m_fs model)
              = [event.ExitEv ((BitVec.ofInt 64 0) &&& (BitVec.ofInt 64 255)) (m_fs model)] := by
            simp only [eof_tail, hs, band0_255]
          rw [e1]
          simpa using star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ _
            (star_trans segs ⟨msR, model⟩ [] _
              (star_one segs ⟨msR, model⟩ [] _ HssE) _ _ Hstar2)
      | some b0 =>
          refine ⟨⟨ms, model⟩, ?_⟩
          simp only [List.flatMap_nil, List.nil_append, eof_tail, hs]
          exact star.refl _
  | cons s bs blocks s'' hlo hhi hpre hc ih =>
      intro ms model HM Hst Hrd
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      obtain ⟨msR, HRP, Hstar0⟩ := to_rd_star segs LH cnt ms model Hh Hlazy Hrd
      obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
      have Hwr : to_wr segs LH bs (advance_past_svc (apply_effect msR
          (mkEffect (len_word bs) [(buf, bs)] []))) := Hbytes bs hlo hhi
      have Hh' : m_halted (with_stdin (stream_take s bs.length).2 model) = none := Hh
      have hlazy' : m_vm_lazy (with_stdin (stream_take s bs.length).2 model) = [] := by
        rw [m_vm_lazy_with_stdin]; exact Hlazy
      have HM' : M_loop (with_stdin (stream_take s bs.length).2 model) := by
        rw [← Hst]
        exact M_loop_take bs.length model HM
      have Hst' : m_stdin (with_stdin (stream_take s bs.length).2 model)
          = (stream_take s bs.length).2 := rfl
      have Hfdc' : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
          (with_stdin (stream_take s bs.length).2 model) :=
        fd1chan_fdchan _ (M_loop_fd1chan _ HM')
      have Hbmbs : buf_modeled bs := by
        unfold buf_modeled
        omega
      have HssR : sstep segs ⟨msR, model⟩ (bs.map (event.ReadEv (BitVec.ofInt 64 0)))
          (.SNext ⟨advance_past_svc (apply_effect msR (mkEffect (len_word bs) [(buf, bs)] [])),
            with_stdin (stream_take s bs.length).2 model⟩) := by
        refine sstep.syscall msR model x8 (mkEffect (len_word bs) [(buf, bs)] [])
          (with_stdin (stream_take s bs.length).2 model)
          (with_stdin (stream_take s bs.length).2 model)
          (bs.map (event.ReadEv (BitVec.ofInt 64 0))) Hh Hsvc ?_ Hh' ?_
        · have hok := read0_ok_bytes cnt Hcnt segs msR x8 model w bs Hno Hfd0 Hg0 Hg2
            (by rw [Hg1]; exact Hw) (by rw [Hg1]; exact Haok) hlo hhi (by rw [Hst]; exact hpre)
          rw [Hg1, Hst] at hok
          exact hok
        · rw [materialize_model_accesses_no_lazy _ _ hlazy']
      have Hcont : ∀ ms', lh_next segs LH ms' →
          ∃ c, star segs ⟨ms', with_stdin (stream_take s bs.length).2 model⟩
            (blocks.flatMap iter_ev ++
              eof_tail s'' (m_fs (with_stdin (stream_take s bs.length).2 model))) c := by
        intro ms' Hlh
        exact ih ms' _ HM' Hst' (lh_next_to_rd segs LH cnt H_LH ms' Hlh)
      obtain ⟨c, Hstar1⟩ := to_wall_tail_star_admits segs (BitVec.ofInt 64 1)
        (BitVec.ofInt 64 1) fd32_1
        (advance_past_svc (apply_effect msR (mkEffect (len_word bs) [(buf, bs)] [])))
        bs (lh_next segs LH) (to_wr_wall_tail segs LH bs _ Hwr) Hbmbs
        (with_stdin (stream_take s bs.length).2 model)
        (blocks.flatMap iter_ev ++
          eof_tail s'' (m_fs (with_stdin (stream_take s bs.length).2 model)))
        Hh' hlazy' Hfdc' Hcont
      refine ⟨c, ?_⟩
      have hflat : (bs :: blocks).flatMap iter_ev ++ eof_tail s'' (m_fs model)
          = (bs.map (event.ReadEv (BitVec.ofInt 64 0)) ++
              (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
                (blocks.flatMap iter_ev ++ eof_tail s'' (m_fs model)))) := by
        simp [iter_ev, iter_ev_ch, List.cons_append, List.append_assoc]
      rw [hflat]
      simpa using star_trans segs ⟨ms, model⟩ [] ⟨msR, model⟩ Hstar0 _ _
        (star.step ⟨msR, model⟩ (bs.map (event.ReadEv (BitVec.ofInt 64 0))) _ _ c HssR Hstar1)

/- -------------------------------------------------------------------------
   No error: the phase invariant.
   ------------------------------------------------------------------------- -/

/-- The phase invariant of a stream loop: either the model still has its
    stdin/stdout channels and the machine is on its way to (or at) a read, or
    inside the echo write-all — or the model is already on the exit path. -/
def sinv (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (c : config) : Prop :=
  (M_loop c.cfg_model ∧
    (to_rd segs LH cnt c.cfg_ms ∨
      ∃ bs, 1 ≤ bs.length ∧ buf_modeled bs ∧
        to_wall_tail segs (BitVec.ofInt 64 1) c.cfg_ms bs (lh_next segs LH)))
  ∨ on_path segs (BitVec.ofInt 64 0) c

theorem sinv_step (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (c : config) (evs : List event) (c' : config) :
    sinv segs LH cnt c → sstep segs c evs (.SNext c') → sinv segs LH cnt c' := by
  intro Hinv Hss
  obtain ⟨ms, model⟩ := c
  obtain ⟨ms', model'⟩ := c'
  rcases Hinv with ⟨HM, Hphase⟩ | Hop
  · have Hfd0 := HM.1
    have Hfd1 := HM.2.1
    have Hh := HM.2.2.1
    have Hlazy := HM.2.2.2
    have Hfdc : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model :=
      fd1chan_fdchan _ (M_loop_fd1chan _ HM)
    rcases Hphase with Hrd | ⟨bs, Hnb, Hbm, Hwt⟩
    · cases Hrd with
      | trd_here ms0 HRP =>
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
          rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (.SNext ⟨ms', model'⟩)
              Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
            ⟨_hst, _hevs, hc2⟩ | ⟨bs', hlo, hhi, _hpre, _hevs, hc2⟩
          · cases hc2
            exact Or.inr (Or.inl ⟨Hh, Hlazy, Hex⟩)
          · cases hc2
            exact Or.inl ⟨M_loop_take bs'.length model HM,
              Or.inr ⟨bs', by omega, by unfold buf_modeled; omega,
                to_wr_wall_tail segs LH bs' _ (Hbytes bs' hlo hhi)⟩⟩
      | trd_step ms0 ms1 hsvc hstep hrd' =>
          obtain ⟨_, hc2⟩ :=
            sstep_instr_inv segs ms model ms1 evs (.SNext ⟨ms', model'⟩) Hlazy hsvc hstep Hss
          cases hc2
          exact Or.inl ⟨HM, Or.inl hrd'⟩
    · cases Hwt with
      | twt_done ms0 hk =>
          simp at Hnb
      | twt_more ms0 rest k hnb hw =>
          obtain ⟨n, hn1, hn2, _hevs, hst, hwt2⟩ :=
            sstep_to_wall_inv segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
              ms bs (lh_next segs LH) model evs (.SNext ⟨ms', model'⟩)
              Hh Hlazy Hfdc Hbm hw Hss
          cases hst
          by_cases hne : n = bs.length
          · subst hne
            rw [List.drop_length] at hwt2
            obtain ⟨msL, HmL, HlhL⟩ :=
              to_wall_tail_nil_msteps segs (BitVec.ofInt 64 1) _
                (lh_next segs LH) hwt2
            exact Or.inl ⟨HM, Or.inl (msteps_to_rd segs LH cnt _ _ HmL
              (lh_next_to_rd segs LH cnt H_LH msL HlhL))⟩
          · exact Or.inl ⟨HM, Or.inr ⟨bs.drop n,
              by rw [List.length_drop]; omega, buf_modeled_skipn n bs Hbm, hwt2⟩⟩
      | twt_step ms0 ms1 rest k hsvc hstep ht =>
          obtain ⟨_, hc2⟩ :=
            sstep_instr_inv segs ms model ms1 evs (.SNext ⟨ms', model'⟩) Hlazy hsvc hstep Hss
          cases hc2
          exact Or.inl ⟨HM, Or.inr ⟨bs, Hnb, Hbm, ht⟩⟩
  · exact Or.inr (on_path_step segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs ⟨ms', model'⟩ Hop Hss)

theorem sinv_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (c : config) (evs : List event) :
    sinv segs LH cnt c → ¬ sstep segs c evs .SError := by
  intro Hinv Hss
  obtain ⟨ms, model⟩ := c
  rcases Hinv with ⟨HM, Hphase⟩ | Hop
  · have Hfd0 := HM.1
    have Hfd1 := HM.2.1
    have Hh := HM.2.2.1
    have Hlazy := HM.2.2.2
    have Hfdc : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model :=
      fd1chan_fdchan _ (M_loop_fd1chan _ HM)
    rcases Hphase with Hrd | ⟨bs, Hnb, Hbm, Hwt⟩
    · cases Hrd with
      | trd_here ms0 HRP =>
          obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
          rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs .SError
              Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
            ⟨_, _, hc2⟩ | ⟨_, _, _, _, _, hc2⟩
          · simp at hc2
          · simp at hc2
      | trd_step ms0 ms1 hsvc hstep hrd' =>
          obtain ⟨_, hc2⟩ :=
            sstep_instr_inv segs ms model ms1 evs .SError Hlazy hsvc hstep Hss
          simp at hc2
    · cases Hwt with
      | twt_done ms0 hk => simp at Hnb
      | twt_more ms0 rest k hnb hw =>
          exact to_wall_no_error_sstep segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
            fd32_1 ms bs (lh_next segs LH) model evs Hh Hlazy Hfdc Hbm hw Hss
      | twt_step ms0 ms1 rest k hsvc hstep ht =>
          obtain ⟨_, hc2⟩ :=
            sstep_instr_inv segs ms model ms1 evs .SError Hlazy hsvc hstep Hss
          simp at hc2
  · exact on_path_no_error segs (BitVec.ofInt 64 0) ⟨ms, model⟩ evs Hop Hss

theorem star_sinv (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (c : config) (tr : List event) (c' : config) :
    sinv segs LH cnt c → star segs c tr c' → sinv segs LH cnt c' :=
  star_inv segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH) c tr c'

theorem to_rd_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (ms : machine_state) (model : Model) :
    M_loop model → to_rd segs LH cnt ms → ¬ reaches_error segs ⟨ms, model⟩ := by
  intro HM Hrd
  exact inv_no_reaches_error segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH)
    (sinv_no_error segs LH cnt Hcnt) ⟨ms, model⟩ (Or.inl ⟨HM, Or.inl Hrd⟩)

/- -------------------------------------------------------------------------
   Exhaustiveness: every run trace is a stream trace.
   ------------------------------------------------------------------------- -/

theorem star_loop_only (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms) :
    ∀ (c0 : config) (tr : List event) (c' : config), star segs c0 tr c' →
    ∀ (ms : machine_state) (model : Model), c0 = ⟨ms, model⟩ → M_loop model →
    (to_rd segs LH cnt ms →
       ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
         is_prefix tr (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model))) ∧
    (∀ (bs : List byte), 1 ≤ bs.length → buf_modeled bs →
       to_wall_tail segs (BitVec.ofInt 64 1) ms bs (lh_next segs LH) →
       ∃ blocks s', chunks cnt (m_stdin model) blocks s' ∧
         is_prefix tr (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
           (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model)))) := by
  intro c0 tr c' Hstar
  induction Hstar with
  | refl c =>
      intro ms model _ _
      exact ⟨fun _ => ⟨[], m_stdin model, chunks.nil _, is_prefix_nil _⟩,
             fun _ _ _ _ => ⟨[], m_stdin model, chunks.nil _, is_prefix_nil _⟩⟩
  | step c1 evs c2 tr2 c3 Hss Hstar ih =>
      intro ms model Heq HM
      rw [Heq] at Hss
      have Hfd0 := HM.1
      have Hfd1 := HM.2.1
      have Hh := HM.2.2.1
      have Hlazy := HM.2.2.2
      have Hfdc : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model :=
        fd1chan_fdchan _ (M_loop_fd1chan _ HM)
      refine ⟨?_, ?_⟩
      · intro Hrd
        cases Hrd with
        | trd_here ms0 HRP =>
            obtain ⟨buf, x8, Hsvc, Hno, Hg0, Hg1, Hg2, ⟨w, Hw⟩, Haok, Hex, Hbytes⟩ := HRP
            rcases sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (.SNext c2)
                Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss with
              ⟨hs, hevs, hc2⟩ | ⟨bs, hlo, hhi, hpre, hevs, hc2⟩
            · cases hc2
              rcases to_exit_star_only segs (BitVec.ofInt 64 0)
                (advance_past_svc (set_gpr0 ms (BitVec.ofInt 64 0))) model Hh Hlazy Hex
                tr2 c3 Hstar with h | h
              · subst h
                exact ⟨[], m_stdin model, chunks.nil _, by
                  simp only [hevs, List.nil_append]; exact is_prefix_nil _⟩
              · subst h
                refine ⟨[], m_stdin model, chunks.nil _, ?_⟩
                have e1 : eof_tail (m_stdin model) (m_fs model)
                    = [event.ExitEv (BitVec.ofInt 64 0) (m_fs model)] := by
                  simp only [eof_tail, hs]
                have e2 : event.ExitEv (BitVec.ofInt 64 0) (m_fs model)
                    = event.ExitEv ((BitVec.ofInt 64 0) &&& (BitVec.ofInt 64 255))
                        (m_fs model) := by rw [band0_255]
                rw [hevs, e1, e2]
                simp only [List.nil_append]
                exact is_prefix_refl _
            · cases hc2
              have hnb : 1 ≤ bs.length := by omega
              have hbm : buf_modeled bs := by unfold buf_modeled; omega
              have hwt : to_wall_tail segs (BitVec.ofInt 64 1)
                  (advance_past_svc (apply_effect ms
                    (mkEffect (len_word bs) [(buf, bs)] [])))
                  bs (lh_next segs LH) :=
                to_wr_wall_tail segs LH bs _ (Hbytes bs hlo hhi)
              obtain ⟨blocks, s', HCb, Hp⟩ :=
                (ih (advance_past_svc (apply_effect ms
                      (mkEffect (len_word bs) [(buf, bs)] [])))
                    (with_stdin (stream_take (m_stdin model) bs.length).2 model) rfl
                  (M_loop_take bs.length model HM)).2 bs hnb hbm hwt
              rw [m_fs_with_stdin] at Hp
              refine ⟨bs :: blocks, s', chunks.cons (m_stdin model) bs blocks s' hlo hhi ?_ HCb, ?_⟩
              · exact hpre
              · rw [hevs]
                have e : (bs :: blocks).flatMap iter_ev ++ eof_tail s' (m_fs model)
                    = bs.map (event.ReadEv (BitVec.ofInt 64 0)) ++
                      (bs.map (event.WriteEv (BitVec.ofInt 64 1)) ++
                        (blocks.flatMap iter_ev ++ eof_tail s' (m_fs model))) := by
                  simp [iter_ev, iter_ev_ch, List.cons_append, List.append_assoc]
                rw [e]
                exact is_prefix_app_mono (bs.map (event.ReadEv (BitVec.ofInt 64 0))) tr2 _ Hp
        | trd_step ms0 ms1 hsvc hstep hrd' =>
            obtain ⟨hevs, hc2⟩ :=
              sstep_instr_inv segs ms model ms1 evs (.SNext c2) Hlazy hsvc hstep Hss
            cases hc2
            obtain ⟨blocks, s', HCb, Hp⟩ := (ih ms1 model rfl HM).1 hrd'
            exact ⟨blocks, s', HCb, by rw [hevs]; simpa using Hp⟩
      · intro bs Hnb Hbm Hwt
        cases Hwt with
        | twt_done ms0 hk => simp at Hnb
        | twt_more ms0 rest k hnb hw =>
            obtain ⟨n, hn1, hn2, hevs, hst, hwt2⟩ :=
              sstep_to_wall_inv segs (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
                ms bs (lh_next segs LH) model evs (.SNext c2) Hh Hlazy Hfdc Hbm hw Hss
            cases hst
            by_cases hne : n = bs.length
            · subst hne
              rw [List.drop_length] at hwt2
              obtain ⟨msL, HmL, HlhL⟩ :=
                to_wall_tail_nil_msteps segs (BitVec.ofInt 64 1) _ (lh_next segs LH) hwt2
              obtain ⟨blocks, s', HCb, Hp⟩ :=
                (ih (advance_past_svc (set_gpr0 ms (len_word (bs.take bs.length)))) model rfl HM).1
                  (msteps_to_rd segs LH cnt _ _ HmL (lh_next_to_rd segs LH cnt H_LH msL HlhL))
              refine ⟨blocks, s', HCb, ?_⟩
              rw [hevs, List.take_length]
              exact is_prefix_app_mono (bs.map (event.WriteEv (BitVec.ofInt 64 1))) tr2 _ Hp
            · obtain ⟨blocks, s', HCb, Hp⟩ :=
                (ih (advance_past_svc (set_gpr0 ms (len_word (bs.take n)))) model rfl HM).2
                  (bs.drop n) (by rw [List.length_drop]; omega) (buf_modeled_skipn n bs Hbm) hwt2
              refine ⟨blocks, s', HCb, ?_⟩
              rw [hevs]
              have hsplit : bs.map (event.WriteEv (BitVec.ofInt 64 1))
                  = (bs.take n).map (event.WriteEv (BitVec.ofInt 64 1))
                    ++ (bs.drop n).map (event.WriteEv (BitVec.ofInt 64 1)) := by
                rw [← List.map_append, List.take_append_drop]
              rw [hsplit, List.append_assoc]
              exact is_prefix_app_mono ((bs.take n).map (event.WriteEv (BitVec.ofInt 64 1))) tr2 _ Hp
        | twt_step ms0 ms1 rest k hsvc hstep ht =>
            obtain ⟨hevs, hc2⟩ :=
              sstep_instr_inv segs ms model ms1 evs (.SNext c2) Hlazy hsvc hstep Hss
            cases hc2
            obtain ⟨blocks, s', HCb, Hp⟩ := (ih ms1 model rfl HM).2 bs Hnb Hbm ht
            exact ⟨blocks, s', HCb, by rw [hevs]; simpa using Hp⟩

/- -------------------------------------------------------------------------
   Whole-run packaging from the initial state.
   ------------------------------------------------------------------------- -/

theorem stream_obs_iff (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt
      (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid) (inp.in_hwcap))) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      stream_traces cnt (in_fs inp) (inp.in_stdin) tr := by
  intro tr
  have Hst0 : m_stdin (init_model (segments_reserved segs) brk0 mb sp lim inp) = inp.in_stdin := rfl
  have Hfs0 : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp := rfl
  have HM0 : M_loop (init_model (segments_reserved segs) brk0 mb sp lim inp) :=
    init_M_loop (segments_reserved segs) brk0 mb sp lim inp
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨blocks, s', HC, Hp'⟩ :=
      (star_loop_only segs LH cnt Hcnt H_LH (init_config segs pc ph sp brk0 mb rnd lim inp)
        tr' c Hstar
        (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid)
          (inp.in_hwcap))
        (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl HM0).1 Hrd
    rw [Hst0] at HC
    rw [Hfs0] at Hp'
    exact ⟨blocks, s', HC, is_prefix_trans Hp Hp'⟩
  · rintro ⟨blocks, s', HC, Hp⟩
    obtain ⟨c, Hstar⟩ :=
      stream_star_admits segs LH cnt Hcnt H_LH (inp.in_stdin) blocks s' HC
        (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid)
          (inp.in_hwcap))
        (init_model (segments_reserved segs) brk0 mb sp lim inp) HM0 Hst0 Hrd
    rw [Hfs0] at Hstar
    exact ⟨blocks.flatMap iter_ev ++ eof_tail s' (in_fs inp), c, Hstar, Hp⟩

theorem stream_no_error (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt
      (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid) (inp.in_hwcap))) :
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  refine to_rd_no_error segs LH cnt Hcnt H_LH _ _
    (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) ?_
  exact Hrd

/- -------------------------------------------------------------------------
   The omni reading.  A stream loop need not terminate (the input stream is
   coinductive), so its judgments are the coinductive pair: the loop
   invariant IS a proof of `OmniRun.coexec … never_errors`, by coinduction
   along `sinv_step` and with no `Run.star` in sight, and the trace
   characterisation is the prefix judgment `OmniRun.cosafe`.
   ------------------------------------------------------------------------- -/

theorem to_rd_coexec (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (ms : machine_state) (model : Model) :
    M_loop model → to_rd segs LH cnt ms → coexec segs ⟨ms, model⟩ never_errors := by
  intro HM Hrd
  exact inv_coexec segs (sinv segs LH cnt) (sinv_step segs LH cnt Hcnt H_LH)
    (sinv_no_error segs LH cnt Hcnt) ⟨ms, model⟩ (Or.inl ⟨HM, Or.inl Hrd⟩)

theorem stream_omni_corun (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt
      (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid) (inp.in_hwcap))) :
    omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp never_errors := by
  simpa [omni_corun, mkImage, init_config] using
    to_rd_coexec segs LH cnt Hcnt H_LH _ _
      (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) Hrd

theorem stream_omni_cosafe (segs : List Segment) (LH : machine_state → Prop) (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (H_LH : ∀ ms, LH ms → to_rd segs LH cnt ms)
    (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
    (inp : ProcInput)
    (Hrd : to_rd segs LH cnt
      (init_machine_state segs pc ph sp rnd (inp.in_argv) (inp.in_envp) (inp.in_uid) (inp.in_hwcap))) :
    omni_cosafe (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (stream_traces cnt (in_fs inp) (inp.in_stdin)) := by
  have h : cosafe segs (init_config segs pc ph sp brk0 mb rnd lim inp)
      (stream_traces cnt (in_fs inp) (inp.in_stdin)) := by
    refine (cosafe_obs_iff segs _ _ ?_).mpr ?_
    · intro t t' Ht Hp
      exact stream_traces_prefix_closed cnt (in_fs inp) (inp.in_stdin) t t' Ht Hp
    · intro tr Hobs
      exact (stream_obs_iff segs LH cnt Hcnt H_LH pc ph sp brk0 mb rnd lim inp Hrd tr).mp Hobs
  simpa [omni_cosafe, mkImage, init_config] using h

/- =========================================================================
   Pair equivalence: the characterization `stream_traces cnt fs0 stdin0` does
   not mention the binary, so two binaries that both satisfy it are
   equivalent — ON THE SAME INPUT STREAM, which is what the theorem shape
   quantifies over.
   ========================================================================= -/

/-- The omni equivalence of two stream loops on the same input stream,
    at the two role budgets. -/
theorem stream_omni_strong_equiv (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (source_segs : List Segment) (rLH : machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (aLH : machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput)
    (HrLH : ∀ ms, rLH ms → to_rd source_segs rLH cnt ms)
    (HaLH : ∀ ms, aLH ms → to_rd target_segs aLH cnt ms)
    (Hr : to_rd source_segs rLH cnt
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap))
    (Ha : to_rd target_segs aLH cnt
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · refine coexec_conseq source_segs _ never_errors (covered source_segs) ?_ ?_
    · exact stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp Hr
    · intro tr o h
      exact never_errors_covered source_segs tr o h
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
        source_alloc_limit inp Hr tr).trans
        (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd
          target_alloc_limit inp Ha tr).symm
    · exact stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd
        target_alloc_limit inp Ha

theorem stream_strong_equiv (cnt : word)
    (Hcnt : 0 < (cnt.toNat : Int) ∧ (cnt.toNat : Int) ≤ rw_bytes_max)
    (source_segs : List Segment) (rLH : machine_state → Prop) (rpc : Nat)
    (rph : PhdrInfo) (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (aLH : machine_state → Prop) (apc : Nat)
    (aph : PhdrInfo) (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (inp : ProcInput) (HrLH : ∀ ms, rLH ms → to_rd source_segs rLH cnt ms)
    (HaLH : ∀ ms, aLH ms → to_rd target_segs aLH cnt ms)
    (Hr : to_rd source_segs rLH cnt
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap))
    (Ha : to_rd target_segs aLH cnt
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)) :
    (modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
     equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
           (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr)
  · right
    constructor
    · intro tr
      exact (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
        rlim inp Hr tr).trans
        (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd
          alim inp Ha tr).symm
    · exact stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd
        alim inp Ha

/-! -/

section Sanity

example : wseg_ok [] (BitVec.ofInt 64 0) 0 = true := by decide

example : wseg_ok [] (BitVec.ofInt 64 0) 1 = false := by decide

example : (BitVec.ofInt 64 0) &&& (BitVec.ofInt 64 255) = BitVec.ofInt 64 0 := by decide

example : (stream_take IEof 1).1 = [] := by decide

example : eof_tail IEof [] = [event.ExitEv (BitVec.ofInt 64 0) []] := rfl

example : eof_tail (ICons 7 IEof) [] = [] := rfl

example : iter_ev [] = [] := rfl

example : iter_ev_ch (BitVec.ofInt 64 0) [7]
    = [event.ReadEv (BitVec.ofInt 64 0) 7, event.WriteEv (BitVec.ofInt 64 1) 7] := rfl

example : chunks (BitVec.ofInt 64 4) IEof [] IEof := chunks.nil IEof

end Sanity
