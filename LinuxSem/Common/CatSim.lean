/-
  * Common.CatSim — reusable star-semantics infrastructure for binaries
    that perform a sequence of write(fd=1) syscalls before a terminating
    exit/exit_group syscall (e.g. cat-argv).

  TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.ExitSim),
  built over the star-based `LinuxProcessSem.Run` trace semantics.  Generic
  over the loaded segments `segs`.  The per-binary proof supplies, for each
  binary, an inductive `to_wexit segs ms bufs code` derivation (built by
  symbolic execution over the argv layout — see `Common.PropExec` step
  lemmas) with a SHARED `bufs` and `code`, and glues the two together via
  `cat_strong_equiv_te`.

  Syscall numbers, channel ids, and exit codes are `word = BitVec 64`;
  buffers are `List byte` with `byte = BitVec 8`.  Following the ExitSim
  conventions:

  - the write-syscall number test is `Int`-characterized: `tw_write` (and
    the `write1_*`/`sstep_write_inv` lemmas) carry a pending number `x8`
    with `(x8.toNat : Int) = 64` (mirroring `is_exit_no`; avoids pinning a
    particular `BitVec` literal spelling);
  - fd/channel 1 is spelled `BitVec.ofInt 64 1` (the `init_model` spelling);
  - `N.land code 255` is spelled `code &&& BitVec.ofInt 64 255`.

  An "exit-after-writes" binary runs a finite deterministic straight line
  of machine instructions punctuated by write(1, buf, len) syscalls, then an
  exit.  A channel write to fd 1 leaves the model untouched, but the
  ENVIRONMENT chooses how much of the buffer is delivered: any NONEMPTY
  prefix `buf.take n` (1 ≤ n ≤ buf.length) is admissible, returning the
  delivered length and emitting one `WriteEv 1 b` per delivered byte.  The
  machine side is still deterministic, so we capture a binary with an
  inductive `to_wexit` whose write node is RET-OBLIVIOUS: the continuation
  must handle every delivered length n.  The set of complete traces is then
  the per-buffer prefix choices `wpick`:

  - `obs_trace` of the run is exactly the prefixes of
    `full ++ [ExitEv code fs0]` for the `full` with `wpick 1 bufs full`
    (cat_obs_iff_te), and
  - the run can NEVER take the explicit error transition
    (`¬ reaches_error`; cat_no_error_run_te).

  Combined into `Equivalence.equiv` via `cat_strong_equiv_te`: two
  exit-after-writes binaries that emit the same buffers and exit code are
  observably equivalent (neither errors) — both denote the same set of
  delivery choices.

  NOTES.

  - `Section WithSegs`'s `Variable segs` and `Section WithSegsCh`'s
    `Variable segs fd ch` become EXPLICIT LEADING PARAMETERS on every
    declaration that mentions them, in that order — the same convention
    `ExitSim.lean` follows.
  - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` record constructor
    `⟨sp, brk0, mb, rnd⟩`.
  - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_and` is `&&&`,
    `bv_unsigned w` is `(w.toNat : Int)`, `Z.eqb a b` is `a == b`,
    `firstn n l` is `List.take n l`, `skipn n l` is `List.drop n l`,
    `nth_error` is `List.getElem?` (`l[i]?`), `length` is `List.length`,
    `lia` is `omega`.
  - `read_bytes_map`'s executable body is the chunked accumulator loop of
    `State.lean`; every proof below goes through `read_bytes_map_eq`.
  - `Section WithSegsCh`'s `Hypothesis Hfd32 : fd32 fd = fd` is a section
    hypothesis , so it becomes an explicit premise of
    `sstep_write_ch_inv` (its only consumer) here.
`ite` on a
    propositional side condition.  Every checker-facing proof below therefore
    peels the guards with `ite_eq_left` / `ite_eq_right` (naming the negations in
    `have`s so the tactic never has to guess the `Decidable` instance)
    instead of `rewrite H`, which cannot see through the instance.
  - helpers, four of them, each marked at its declaration:
    `rw_range_gate_false` restates `Uaccess.rw_range_in_range` in the exact
    `!(modeled_rw_range …) = false` spelling `check_write` branches on (a
    `decide`-coercion artifact of this tree, not a difference in content);
    `len_word_take_toNat` is the `len_word`/`take` arithmetic every
    delivered-length guard needs; and `write1_ok_model` / `write_ch_ok_model`
    are the MODEL half of the two `…_ok_inv` inversions, split out so the
    `sstep` arms whose event index is `evs ++ [ExitEv …]` never have to name
    the write's `evs`.  No  declaration is weakened by them.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Checks.Sys.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.ReadWrite.Write
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim

set_option autoImplicit false

namespace LinuxSem.Common.CatSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.OmniEquivalence

/- =========================================================================
   Small word facts.

   `w_is0_pos` lives in `LinuxProcessSem.Sys.Syscall`, next to `w_is0`.
   ========================================================================= -/

/- =========================================================================
   the write-side count gate in the spelling `check_write` uses.

   `Uaccess.rw_range_in_range` states `!(decide (modeled_rw_range buf count
   = false)) = true`; `check_write` branches on `!(modeled_rw_range buf
   count)`.    ========================================================================= -/

theorem rw_range_gate_false (buf count : word)
    (h : (count.toNat : Int) ≤ rw_bytes_max) :
    (!(modeled_rw_range buf count)) = false := by
  have H := rw_range_in_range buf count h
  cases hm : modeled_rw_range buf count with
  | false => simp [hm] at H
  | true => rfl

/- =========================================================================
   Memory-read bridge: `read_bytes_map` over `ms_read_byte` is
   `ms_read_bytes`.
   ========================================================================= -/

theorem read_aux_read_byte (ms : machine_state) (k : Nat) :
    ∀ a : word, read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k := by
  induction k with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    cases h : ms_read_byte ms a with
    | none => simp only [read_bytes_aux, ms_read_bytes_aux, h]
    | some b =>
      simp only [read_bytes_aux, ms_read_bytes_aux, h]
      rw [ih (a + 1)]
      cases ms_read_bytes_aux ms (a + 1) k <;> rfl

theorem read_bytes_map_read_byte (ms : machine_state) (a len : word) :
    read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len := by
  rw [read_bytes_map_eq]
  unfold ms_read_bytes
  exact read_aux_read_byte ms (word_to_nat len) a

/- =========================================================================
   `apply_effect` of a no-write effect just sets a0.
   ========================================================================= -/

theorem apply_effect_no_write (ms : machine_state) (r : word) :
    apply_effect ms (mkEffect r [] []) = set_gpr0 ms r := by
  unfold apply_effect set_gpr0 mkEffect
  rfl

theorem apply_effect_copyins_no_write (ms : machine_state) (r : word)
    (copyins : List (word × Nat)) :
    apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r := by
  unfold apply_effect with_copyins set_gpr0 mkEffect
  rfl

/- =========================================================================
   Argument decoding for a write syscall input.
   ========================================================================= -/

theorem in_sysno_sys_input64 (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_sysno = x8 := rfl

theorem in_arg0_sys_input64 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := rfl

theorem in_arg1_sys_input64 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1 := rfl

theorem in_arg2_sys_input64 (segs : List Segment) (ms : machine_state) (x8 : word) :
    in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2 := rfl

theorem in_mem_sys_input (segs : List Segment) (ms : machine_state) (x8 : word) :
    (sys_input segs ms x8).in_mem = ms_read_byte ms := rfl

/-- Which arm answers this number, on the SPEC side.  `syscall_spec` is
    `dispatch spec_table`, so fixing the number settles the table lookup by
    conversion and the dispatcher disappears — the same one-line argument
    `Checks.Sys.DispatchCompute` makes for `check_syscall`, made here instead
    so that this file needs only the write checker rather than the module
    that re-exports every arm's. -/
theorem syscall_spec_write (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (o : Outcome SyscallEffect Model event) :
    (x8.toNat : Int) = 64 →
    (Specs.syscall_spec (sys_input segs ms x8) model o ↔
      Sys.Fs.ReadWrite.write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
        (sys_input segs ms x8) model o) := by
  intro Hno
  unfold Specs.syscall_spec
  have hlookup : Sys.Dispatch.lookup_arm spec_table
      (((sys_input segs ms x8).in_sysno).toNat : Int)
      = some (arm 64 (fun i => Sys.Fs.ReadWrite.write_spec (fd32 (in_arg i 0))
          (in_arg i 1) (in_arg i 2))) := by
    rw [in_sysno_sys_input64, Hno]
    rfl
  rw [Sys.Dispatch.dispatch_arm spec_table (sys_input segs ms x8) model o
    (arm 64 (fun i => Sys.Fs.ReadWrite.write_spec (fd32 (in_arg i 0))
      (in_arg i 1) (in_arg i 2))) hlookup]
  rfl

/- =========================================================================
   fd 1 resolves to channel 1.
   ========================================================================= -/

/-- The fd is open on channel 1, and fd 1 is not stdin. -/
def fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (BitVec.ofInt 64 1) = some (FdEntry.FdChannel (BitVec.ofInt 64 1))

/-- One buffer is inside the transfer size the model judges, and a whole
    run's worth of them is.  `ReadWrite.write_spec` is `unmodeled` above
    `Uaccess.rw_bytes_max` (see the bound's own comment for why), so a
    write-then-exit derivation only tells us anything about a run whose
    writes all fit.  Carrying the obligation HERE, on the buffers the run
    emits, rather than as a premise of the write NODE, keeps it a single
    fact each binary proves once about its own output — the symbolic
    execution that builds the derivation is unaffected. -/
def buf_modeled (b : List byte) : Prop :=
  (b.length : Int) ≤ rw_bytes_max

def bufs_modeled (bufs : List (List byte)) : Prop :=
  ∀ b ∈ bufs, buf_modeled b

/- A for-all over a list is spelled `∀ x ∈ l, P x`, the repo-wide
   convention (`Common/Decimal.lean`, `Common/AsanPlacement.lean`): Lean
   4.31's core has no `List.Forall`. -/

/-- A binary that emits ONE buffer is the common case, so it gets the
    wrapper rather than each example unfolding the list for itself. -/
theorem bufs_modeled_single (b : List byte) (H : buf_modeled b) :
    bufs_modeled [b] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  exact hx ▸ H

/-- A retry loop reissues the write on the UNDELIVERED tail, so the
    obligation has to survive `List.drop`: a shorter buffer is still one
    the model can judge.  The empty tail — what the loop ends on — is the
    degenerate case. -/
theorem buf_modeled_nil : buf_modeled [] := by
  unfold buf_modeled rw_bytes_max
  decide

theorem buf_modeled_skipn (n : Nat) (b : List byte) (H : buf_modeled b) :
    buf_modeled (b.drop n) := by
  unfold buf_modeled at *
  rw [List.length_drop]
  omega

/- =========================================================================
   The channel-write spec facts, derived through the verified checker.  A
   channel write is not a singleton outcome: for every n with
   1 ≤ n ≤ buf.length, delivering `buf.take n` (with return the delivered
   length) is admissible, and EVERY admissible outcome is of that form.
   ========================================================================= -/

-- the pieces of `write1_check_n`'s arithmetic, named once.
theorem len_word_take_toNat {A : Type} (buf : List A) (n : Nat)
    (Hn : (n : Int) ≤ (buf.length : Int)) (Hbig : (buf.length : Int) < two_pow_64) :
    (len_word (buf.take n)).toNat = n := by
  have htake : (buf.take n).length = n := by rw [List.length_take]; omega
  have hlt : ((buf.take n).length : Int) < two_pow_64 := by rw [htake]; omega
  exact Int.ofNat_inj.mp (by rw [len_word_unsigned (buf.take n) hlt, htake])

theorem write1_check_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (buf : List byte) (n : Nat) :
    fd1chan model →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ n → n ≤ buf.length →
    check_write (sys_input segs ms x8)
      (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (with_copyins [(ms_gpr ms 1, n)]
        (mkEffect (len_word (buf.take n)) [] [])) model
      = .CheckOk model (List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n)) := by
  intro Hfd Hno Hg Hr Hcnt Hn1 Hn2
  unfold fd1chan at Hfd
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have Hcw : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max := by
    unfold buf_modeled at Hcnt; omega
  have Hmc : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    rw_range_gate_false (ms_gpr ms 1) (ms_gpr ms 2) Hcw
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have h32 : fd32 (BitVec.ofInt 64 1) = BitVec.ofInt 64 1 := by decide
  have hw1 : w_is0 (BitVec.ofInt 64 1) = false := by decide
  have hbig : (buf.length : Int) < two_pow_64 := by
    have hc : (ms_gpr ms 2).toNat < 2 ^ 64 := (ms_gpr ms 2).isLt
    have hc' : ((ms_gpr ms 2).toNat : Int) < (2 : Int) ^ 64 := by exact_mod_cast hc
    unfold two_pow_64
    omega
  have hret : (len_word (buf.take n)).toNat = n :=
    len_word_take_toNat buf n (by exact_mod_cast Hn2) hbig
  have Hg1 : decide (1 ≤ (n : Int)) = true := by
    rw [decide_eq_true_eq]; exact_mod_cast Hn1
  have Hg0 : (buf.length == 0) = false := by
    have h : buf.length ≠ 0 := by omega
    simp [h]
  unfold check_write
  simp only [Hg, h32, Hfd, hw1, Hmc, Hc, in_mem_sys_input, write_source_of_rw _ _ _ Hcw,
    readable_bytes_full _ _ _ _ Hrb, Hg0, with_copyins, hret]
  simp [Hg1, Hn2, access_ranges_eqb_refl]

/-- For every 1 ≤ n ≤ buf.length, the n-byte delivery is admissible. -/
theorem write1_ok_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (buf : List byte) (n : Nat) :
    fd1chan model →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ n → n ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (buf.take n)) [] [])) model
          (List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n))) := by
  intro Hfd Hno Hg Hr Hcnt Hn1 Hn2
  exact (syscall_spec_write segs ms x8 model _ Hno).mpr
    (check_write_sound_ok _ _ _ _ _ _ _ _
      (write1_check_n segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2))

/-- Every admissible write-to-fd-1 outcome delivers SOME nonempty prefix. -/
theorem write1_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (buf : List byte) :
    fd1chan model →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    1 ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      eff = with_copyins [(ms_gpr ms 1, n)]
              (mkEffect (len_word (buf.take n)) [] []) ∧ model' = model ∧
      evs = List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) := by
  intro Hfd Hno Hg Hr Hnb Hspec
  unfold fd1chan at Hfd
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc0 : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have h32 : fd32 (BitVec.ofInt 64 1) = BitVec.ofInt 64 1 := by decide
  have hw1 : w_is0 (BitVec.ofInt 64 1) = false := by decide
  have Hspec' := (syscall_spec_write segs ms x8 model _ Hno).mp Hspec
  have Hc := check_write_complete_ok _ _ _ _ _ _ _ _ Hspec'
  unfold check_write at Hc
  simp only [Hg, h32, Hfd, in_mem_sys_input] at Hc
  rw [ite_eq_right (by rw [hw1]; decide)] at Hc
  by_cases hmr : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = true
  · rw [ite_eq_left hmr] at Hc
    exact nomatch Hc
  · rw [ite_eq_right hmr] at Hc
    rw [ite_eq_right (by rw [Hc0]; decide)] at Hc
    -- the source the transfer sees is the CLAMPED prefix of the range the
    -- call named -- `buf` itself for every count under `MAX_RW_COUNT`, and
    -- a prefix of it above, which the gate above admits at an in-range
    -- buffer
    simp only [write_source_prefix (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb] at Hc
    have hcpos : 1 ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by
      have h2 : (1 : Int) ≤ (ms_gpr ms 2).toNat := by omega
      have h3 : (1 : Int) ≤ rw_count_clamp (ms_gpr ms 2) := by
        unfold rw_count_clamp
        rw [Int.le_min]
        exact ⟨h2, by unfold MAX_RW_COUNT; decide⟩
      have h0 := (rw_count_clamp_range (ms_gpr ms 2)).1
      omega
    have hg0 : ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length == 0) = false := by
      have h2 : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length ≠ 0 := by
        rw [List.length_take]; omega
      cases hb : ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length == 0) with
      | false => rfl
      | true =>
        rw [beq_iff_eq] at hb
        exact absurd hb h2
    rw [ite_eq_right (by rw [hg0]; decide)] at Hc
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    cases ws with
    | cons w ws' => simp at Hc
    | nil =>
      cases zs with
      | cons z zs' => simp at Hc
      | nil =>
        cases us with
        | cons u us' => simp at Hc
        | nil =>
          cases cs with
          | cons c cs' => simp at Hc
          | nil =>
            -- the shape is now ⟨ret, [], [], [], [], copyins⟩
            simp only [] at Hc
            by_cases hg : (decide (1 ≤ (ret.toNat : Int)) &&
                decide ((ret.toNat : Int) ≤
                  ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length : Int))) = true
            · rw [ite_eq_left hg] at Hc
              by_cases hr : access_ranges_eqb copyins
                  [(ms_gpr ms 1, ret.toNat)] = true
              · rw [ite_eq_left hr] at Hc
                cases Hc
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                obtain ⟨h1, h2⟩ := hg
                have hle_n : ret.toNat ≤ buf.length := by
                  rw [List.length_take] at h2
                  omega
                have hcopy : copyins = [(ms_gpr ms 1, ret.toNat)] :=
                  (access_ranges_eqb_eq _ _).mp hr
                have htake : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).take ret.toNat
                    = buf.take ret.toNat := by
                  rw [List.take_take, Nat.min_eq_left]
                  rw [List.length_take] at h2
                  omega
                have hlen_ret : len_word (buf.take ret.toNat) = ret :=
                  len_word_firstn_ret ret buf ⟨by omega, by exact_mod_cast hle_n⟩
                refine ⟨ret.toNat, ?_, ?_, ?_, ?_, ?_⟩
                · omega
                · exact hle_n
                · rw [hcopy, hlen_ret]
                  rfl
                · rfl
                · rw [htake]
              · rw [ite_eq_right hr] at Hc
                exact absurd Hc (by simp)
            · rw [ite_eq_right hg] at Hc
              exact absurd Hc (by simp)

/-- split of `write1_ok_inv`: just the MODEL half.  The exit,
    killed and materialization-fault arms of `sstep` only need to know the
    write left the model alone, and stating it apart keeps those arms from
    naming the event list the step was carrying (their event index is
    `evs ++ [ExitEv …]`, not the write's `evs`). -/
theorem write1_ok_model (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (model' : Model) (evs : List event)
    (buf : List byte) :
    fd1chan model →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    1 ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
    model' = model := by
  intro Hfd Hno Hg Hr Hnb Hspec
  obtain ⟨n, -, -, -, hm, -⟩ :=
    write1_ok_inv segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hnb Hspec
  exact hm

/-- Write to fd 1 with a readable buffer never takes the error transition:
    on this checker branch the answer is CheckOk or CheckReject only. -/
theorem write1_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (buf : List byte) :
    fd1chan model →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    -- a zero count is genuinely unmodeled when the range verdict is
    -- unclear (see `access_ok_zero` in the write spec), so the nonempty
    -- buffer is load-bearing here, not just convenient
    1 ≤ buf.length →
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hfd Hno Hg Hr Hcnt Hnb Hspec
  unfold fd1chan at Hfd
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have Hcw : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max := by
    unfold buf_modeled at Hcnt; omega
  have Hmc : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    rw_range_gate_false (ms_gpr ms 1) (ms_gpr ms 2) Hcw
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc0 : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have h32 : fd32 (BitVec.ofInt 64 1) = BitVec.ofInt 64 1 := by decide
  have hw1 : w_is0 (BitVec.ofInt 64 1) = false := by decide
  have Hspec' := (syscall_spec_write segs ms x8 model _ Hno).mp Hspec
  have Hc := check_write_complete_unmodeled (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) model
    (mkEffect (BitVec.ofInt 64 0) [] []) Hspec'
  unfold check_write at Hc
  simp only [Hg, h32, Hfd, in_mem_sys_input] at Hc
  rw [ite_eq_right (show ¬ ((w_is0 (BitVec.ofInt 64 1)) = true) by rw [hw1]; decide)] at Hc
  rw [ite_eq_right (show ¬ (((!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)))) = true)
    by rw [Hmc]; decide)] at Hc
  rw [ite_eq_right (show ¬ ((w_is0 (ms_gpr ms 2)) = true) by rw [Hc0]; decide)] at Hc
  simp only [write_source_of_rw (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) Hcw,
    readable_bytes_full (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb] at Hc
  cases hb : (buf.length == 0) with
  | true =>
    rw [ite_eq_left hb] at Hc
    exact check_ret_only_no_unmodeled _ _ _ _ Hc
  | false =>
    rw [ite_eq_right (show ¬ ((buf.length == 0) = true) by rw [hb]; decide)] at Hc
    try simp only [] at Hc
    split at Hc
    · split at Hc <;> exact nomatch Hc
    · exact nomatch Hc

/- =========================================================================
   Prefix helpers.
   ========================================================================= -/

/- =========================================================================
   Delivery choices.  A run's complete write trace is one `WriteEv ch` per
   delivered byte, where the environment picks, for EACH buffer, a nonempty
   prefix.  `wevents_ch` is the full-delivery instance.
   ========================================================================= -/

def wevents_ch (ch : word) : List (List byte) → List event
  | [] => []
  | buf :: rest => List.map (event.WriteEv ch) buf ++ wevents_ch ch rest

inductive wpick (ch : word) : List (List byte) → List event → Prop where
  | wp_nil : wpick ch [] []
  | wp_cons (buf : List byte) (bufs : List (List byte)) (n : Nat) (tr : List event) :
      1 ≤ n → n ≤ buf.length →
      wpick ch bufs tr →
      wpick ch (buf :: bufs) (List.map (event.WriteEv ch) (buf.take n) ++ tr)

/-- Full delivery is one of the choices (for nonempty buffers). -/
theorem wpick_wevents (ch : word) (bufs : List (List byte)) :
    (∀ b ∈ bufs, 1 ≤ b.length) → wpick ch bufs (wevents_ch ch bufs) := by
  intro H
  induction bufs with
  | nil => exact wpick.wp_nil
  | cons b bs ih =>
    have hb : 1 ≤ b.length := H b (by simp)
    have hbs : ∀ x ∈ bs, 1 ≤ x.length := fun x hx => H x (by simp [hx])
    have hc := wpick.wp_cons b bs b.length _ hb (Nat.le_refl _) (ih hbs)
    rw [List.take_length] at hc
    exact hc

/- =========================================================================
   `to_wexit`: the machine-deterministic straight line of writes then exit.
   The write node is RET-OBLIVIOUS: the environment may deliver any nonempty
   prefix, so the continuation must handle every delivered length n.
   ========================================================================= -/

inductive to_wexit (segs : List Segment) : machine_state → List (List byte) → word → Prop where
  | tw_exit (ms : machine_state) (x8 : word) :
      ms.ms_svc_pending = some x8 →
      is_exit_no x8 →
      to_wexit segs ms [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255)
  | tw_write (ms : machine_state) (x8 : word) (buf : List byte)
      (bufs : List (List byte)) (code : word) :
      ms.ms_svc_pending = some x8 →
      (x8.toNat : Int) = 64 →
      ms_gpr ms 0 = BitVec.ofInt 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
      1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
         to_wexit segs (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit segs ms (buf :: bufs) code
  | tw_step (ms ms' : machine_state) (bufs : List (List byte)) (code : word) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wexit segs ms' bufs code →
      to_wexit segs ms bufs code

/- Every example proof goes through the `_te`
   (to_wexit-witness-taken-directly) variants: see
   `cat_obs_iff_te`/`cat_no_error_run_te`/`cat_strong_equiv_te` below. -/

/- =========================================================================
   `msteps`: a run of ordinary (non-syscall) instruction steps.  Every such
   step is a `tw_step`, so a straight line of instructions prepended to a
   `to_wexit` configuration is again `to_wexit`.  This is the ergonomic bridge
   the per-binary loop proofs use: chain per-instruction `PropExec.step_*`
   facts into an `msteps`, then attach the write/exit tail.
   ========================================================================= -/

inductive msteps (segs : List Segment) : machine_state → machine_state → Prop where
  | mst_refl (ms : machine_state) : msteps segs ms ms
  | mst_step (ms ms' ms'' : machine_state) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      msteps segs ms' ms'' →
      msteps segs ms ms''

theorem msteps_one (segs : List Segment) (ms ms' : machine_state) :
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    msteps segs ms ms' := by
  intro Hsvc Hstep
  exact msteps.mst_step ms ms' ms' Hsvc Hstep (msteps.mst_refl ms')

theorem msteps_trans (segs : List Segment) (ms ms' ms'' : machine_state) :
    msteps segs ms ms' → msteps segs ms' ms'' → msteps segs ms ms'' := by
  intro H
  induction H with
  | mst_refl ms => intro H2; exact H2
  | mst_step ms ms' ms'' hsvc hstep hms ih =>
    intro H2
    exact msteps.mst_step _ _ _ hsvc hstep (ih H2)

theorem msteps_to_wexit (segs : List Segment) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word) :
    msteps segs ms ms' → to_wexit segs ms' bufs code → to_wexit segs ms bufs code := by
  intro H
  induction H with
  | mst_refl ms => intro Hw; exact Hw
  | mst_step ms ms' ms'' hsvc hstep hms ih =>
    intro Hw
    exact to_wexit.tw_step ms ms' bufs code hsvc hstep (ih Hw)

/-- Every buffer a `to_wexit` derivation writes is nonempty (the checker
    EFAULTs an empty readable prefix), so full delivery inhabits `wpick`. -/
theorem to_wexit_bufs_nonempty (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs ms bufs code →
    ∀ b ∈ bufs, 1 ≤ b.length := by
  intro H
  induction H with
  | tw_exit ms x8 hsvc hx8 =>
    intro b hb
    simp at hb
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hnb
    · exact ih buf.length hnb (Nat.le_refl _) b hb
  | tw_step ms ms' bufs code hsvc hstep hte ih => exact ih

/- =========================================================================
   One-step inversion for a write config.
   ========================================================================= -/

/-- The step that actually HAPPENED, inverted.  Being given `SNext` is
    already an exclusion of the error transition, so this needs nothing
    about the transfer size: it is the half a trace-prefix argument uses,
    where every step it reasons about is one the run took.  Only ruling
    the error transition OUT — `sstep_write_inv` below — has to know the
    write is modeled. -/
theorem sstep_write_next_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (evs : List event) (c' : config) :
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    ms.ms_svc_pending = some x8 →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    1 ≤ buf.length →
    sstep segs ⟨ms, model⟩ evs (.SNext c') →
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      evs = List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) ∧
      c' = ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩ := by
  intro Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall ms0 model0 x8' eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    obtain ⟨n, hn1, hn2, heff, hm1, hevs⟩ :=
      write1_ok_inv segs ms x8 model eff model1 evs buf Hfd Hno Hg Hr Hnb hspec
    subst eff
    rw [hm1, materialize_model_accesses_no_lazy model _ Hlazy] at hmat
    cases hmat
    exact ⟨n, hn1, hn2, hevs, by rw [apply_effect_copyins_no_write]⟩
  | exit ms0 model0 x8' eff model1 evs0 code hh hsvc hspec hh' hk =>
    exfalso
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    have hm1 := write1_ok_model segs ms x8 model eff model1 _ buf Hfd Hno Hg Hr Hnb hspec
    rw [hm1, Hh] at hh'
    exact nomatch hh'
  | killed ms0 model0 x8' eff model1 evs0 sig hh hsvc hspec hk =>
    exfalso
    have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
    rw [hx] at hspec
    have hm1 := write1_ok_model segs ms x8 model eff model1 _ buf Hfd Hno Hg Hr Hnb hspec
    rw [hm1, m_killed_of_m_halted_none model Hh] at hk
    exact nomatch hk

theorem sstep_write_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (buf : List byte) (evs : List event) (st : step_to) :
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    ms.ms_svc_pending = some x8 →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = BitVec.ofInt 64 1 →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ buf.length →
    sstep segs ⟨ms, model⟩ evs st →
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      evs = List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) ∧
      st = .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩ := by
  intro Hh Hlazy Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss
  cases st with
  | SNext c' =>
    obtain ⟨n, hn1, hn2, hevs, hc'⟩ :=
      sstep_write_next_inv segs ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss
    exact ⟨n, hn1, hn2, hevs, by rw [hc']⟩
  | SError =>
    exfalso
    cases Hss with
    | instr_fault ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | instr_unmodeled ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall_materialization_fault ms0 model0 x8' eff model1 evs0 hh hsvc hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      have hm1 := write1_ok_model segs ms x8 model eff model1 _ buf Hfd Hno Hg Hr Hnb hspec
      rw [hm1, materialize_model_accesses_no_lazy model _ Hlazy] at hmat
      exact nomatch hmat
    | syscall_unmodeled ms0 model0 x8' hh hsvc hspec =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      exact write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb hspec

/- =========================================================================
   Trace characterization.
   ========================================================================= -/

def wevents : List (List byte) → List event
  | [] => []
  | buf :: rest => List.map (event.WriteEv (BitVec.ofInt 64 1)) buf ++ wevents rest

/- =========================================================================
   The omni reading: one induction over `to_wexit` gives, for EVERY
   delivery choice at once, the exact trace, termination and error-freedom.
   The "admits" half (`to_wexit_star_admits` below) is the existential one
   and stays: an omni judgment is realised by SOME execution, and here every
   delivery choice has to be shown realised.
   ========================================================================= -/

def wexit_post (bufs : List (List byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (∃ full, wpick (BitVec.ofInt 64 1) bufs full ∧ tr = full ++ [event.ExitEv code fs])
    ∧ exits_with code tr o

theorem to_wexit_exec (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs ms bufs code →
    ∀ model,
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    bufs_modeled bufs →
    exec segs ⟨ms, model⟩ (wexit_post bufs code (m_fs model)) := by
  intro Hte
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro model Hh Hlazy Hfd Hbm
    refine exec_step_only segs ⟨ms, model⟩ (wexit_post [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model))
      [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
      ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ ?_ ?_ ?_
    · exact sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh hsvc
        (exit_dispatch_ok (sys_input segs ms x8) model (by
          rw [in_sysno_sys_input]; exact hx8)) rfl rfl
    · intro evs st hss
      obtain ⟨h1, h2⟩ := sstep_exit_inv segs ms model x8 evs st Hh hsvc hx8 hss
      refine ⟨?_, h2⟩
      rw [h1]
    · refine exec_halted segs
        ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ _ ?_ ?_
      · simp [m_halted_with_halted]
      · refine ⟨⟨[], wpick.wp_nil, ?_⟩, ?_, ?_⟩
        · rfl
        · simp [m_halted_with_halted]
        · simp [m_killed_with_halted]
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro model Hh Hlazy Hfd Hbm
    have Hb : buf_modeled buf := Hbm buf (by simp)
    have Hbs : bufs_modeled bufs := fun b hb => Hbm b (by simp [hb])
    refine exec.step ⟨ms, model⟩ (wexit_post (buf :: bufs) code (m_fs model)) Hh
      ⟨List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take buf.length),
        .SNext ⟨advance_past_svc (apply_effect ms
          (with_copyins [(ms_gpr ms 1, buf.length)]
            (mkEffect (len_word (buf.take buf.length)) [] []))), model⟩, ?_⟩ ?_ ?_
    · refine sstep.syscall ms model x8 _ model model _ Hh hsvc ?_ Hh ?_
      · exact write1_ok_n segs ms x8 model buf buf.length Hfd hno hg hr Hb
          hnb (Nat.le_refl _)
      · rw [materialize_model_accesses_no_lazy model _ Hlazy]
    · intro evs hss
      obtain ⟨n, -, -, -, hst⟩ :=
        sstep_write_inv segs ms model x8 buf evs .SError Hh Hlazy Hfd hsvc hno hg hr Hb hnb hss
      exact absurd hst (by simp)
    · intro evs c' hss
      obtain ⟨n, hn1, hn2, hevs, hc'⟩ :=
        sstep_write_next_inv segs ms model x8 buf evs c' Hh Hlazy Hfd hsvc hno hg hr hnb hss
      rw [hevs, hc']
      refine exec_conseq segs
        ⟨advance_past_svc (apply_effect ms
          (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))), model⟩
        _ _ (ih n hn1 hn2 model Hh Hlazy Hfd Hbs) ?_
      intro tr o h
      obtain ⟨⟨full, hpick, htr⟩, hx⟩ := h
      refine ⟨⟨List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n) ++ full,
        wpick.wp_cons buf bufs n full hn1 hn2 hpick, ?_⟩, hx⟩
      rw [htr, List.append_assoc]
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    intro model Hh Hlazy Hfd Hbm
    refine exec_step_only segs ⟨ms, model⟩ (wexit_post bufs code (m_fs model)) []
      ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih model Hh Hlazy Hfd Hbm

theorem to_wexit_star_admits (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs ms bufs code →
    ∀ model (full : List event),
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    bufs_modeled bufs →
    wpick (BitVec.ofInt 64 1) bufs full →
    ∃ c, star segs ⟨ms, model⟩ (full ++ [event.ExitEv code (m_fs model)]) c := by
  intro Hte
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro model full Hh Hlazy Hfd Hbm Hpick
    cases Hpick with
    | wp_nil =>
      refine ⟨⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩, ?_⟩
      have hss := sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh hsvc
        (exit_dispatch_ok (sys_input segs ms x8) model (by
          rw [in_sysno_sys_input]; exact hx8)) rfl rfl
      simpa using star_one segs ⟨ms, model⟩
        [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
        ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ hss
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro model full Hh Hlazy Hfd Hbm Hpick
    have Hb : buf_modeled buf := Hbm buf (by simp)
    have Hbs : bufs_modeled bufs := fun b hb => Hbm b (by simp [hb])
    cases Hpick with
    | wp_cons buf' bufs' n tr hn1 hn2 hpick =>
      obtain ⟨c, hstar⟩ := ih n hn1 hn2 model tr Hh Hlazy Hfd Hbs hpick
      refine ⟨c, ?_⟩
      rw [List.append_assoc]
      refine star.step ⟨ms, model⟩ (List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n))
        ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩
        (tr ++ [event.ExitEv code (m_fs model)]) c ?_ hstar
      have hss := sstep.syscall ms model x8
        (with_copyins [(ms_gpr ms 1, n)] (mkEffect (len_word (buf.take n)) [] []))
        model model (List.map (event.WriteEv (BitVec.ofInt 64 1)) (buf.take n))
        Hh hsvc (write1_ok_n segs ms x8 model buf n Hfd hno hg hr Hb hn1 hn2) Hh
        (by rw [materialize_model_accesses_no_lazy model _ Hlazy])
      rw [apply_effect_copyins_no_write] at hss
      exact hss
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    intro model full Hh Hlazy Hfd Hbm Hpick
    obtain ⟨c, hstar⟩ := ih model full Hh Hlazy Hfd Hbm Hpick
    refine ⟨c, ?_⟩
    exact star.step ⟨ms, model⟩ [] ⟨ms', model⟩ (full ++ [event.ExitEv code (m_fs model)]) c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])) hstar

theorem to_wexit_star_only (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs ms bufs code →
    ∀ model,
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    bufs_modeled bufs →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      ∃ full, wpick (BitVec.ofInt 64 1) bufs full ∧
        is_prefix tr (full ++ [event.ExitEv code (m_fs model)]) := by
  intro Hte model Hh Hlazy Hfd Hbm tr c Hstar
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _
      (exec_star segs _ _ tr c
        (to_wexit_exec segs ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar)
  obtain ⟨⟨full, hpick, heq⟩, -⟩ := HQ
  exact ⟨full, hpick, by rw [← heq]; exact is_prefix_app tr tr'⟩

/- =========================================================================
   No-error characterization: a corollary of `to_wexit_exec`.
   ========================================================================= -/

theorem to_wexit_no_error (segs : List Segment) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) :
    m_halted model = none →
    m_vm_lazy model = [] →
    fd1chan model →
    to_wexit segs ms bufs code →
    bufs_modeled bufs →
    ¬ reaches_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hfd Hte Hbm
  refine exec_no_error segs ⟨ms, model⟩ ?_
  refine exec_conseq segs ⟨ms, model⟩ (wexit_post bufs code (m_fs model)) never_errors
    (to_wexit_exec segs ms bufs code Hte model Hh Hlazy Hfd Hbm) ?_
  intro tr o h
  exact exits_with_never_errors code tr o h.2

/- =========================================================================
   Run-level packaging and the equivalence glue.
   ========================================================================= -/

theorem init_model_fd1chan (reserved : List (word × word)) (brk0 mb sp : word)
    (lim : Int) (inp : ProcInput) :
    fd1chan (init_model reserved brk0 mb sp lim inp) := by
  unfold fd1chan
  rfl

/- =========================================================================
   `to_wexit`-based entry points.

   For a cat-argv binary the write buffers depend on argv, which is
   universally quantified, so a fuel-bounded EXECUTABLE witness could never
   be closed by computation (there is no concrete argv to read).  The
   per-binary proof therefore builds the inductive `to_wexit` directly, by
   symbolic execution over the argv layout (see `Common.PropExec` step
   lemmas); these are the entry points every example uses.
   ========================================================================= -/

/-- The run-level omni judgment of a write-then-exit binary. -/
theorem cat_omni_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (wexit_post bufs code (in_fs inp)) := by
  intro Hte Hbm
  show exec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (wexit_post bufs code (in_fs inp))
  exact to_wexit_exec segs _ bufs code Hte
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl
    (init_model_fd1chan _ _ _ _ _ _) Hbm

theorem cat_obs_iff_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ ∃ full, wpick (BitVec.ofInt 64 1) bufs full ∧
          is_prefix tr (full ++ [event.ExitEv code (in_fs inp)]) := by
  intro Hte Hbm tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  have Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp) :=
    init_model_fd1chan _ _ _ _ _ _
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨full, hw, hpref⟩ :=
      to_wexit_star_only segs _ bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar
    exact ⟨full, hw, is_prefix_trans Hp hpref⟩
  · rintro ⟨full, hw, hp⟩
    obtain ⟨c, hstar⟩ :=
      to_wexit_star_admits segs _ bufs code Hte _ full Hh Hlazy Hfd Hbm hw
    exact ⟨full ++ [event.ExitEv code (in_fs inp)], c, hstar, hp⟩

theorem cat_no_error_run_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro Hte Hbm
  refine exec_no_error segs _ ?_
  refine exec_conseq segs _ (wexit_post bufs code (in_fs inp)) never_errors
    (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) ?_
  intro tr o h
  exact exits_with_never_errors code tr o h.2

/-- The code half of `wexit_post`, consumed and pinned: the run satisfies
    `MustExit.must_exit_with` at `code`, and at no other. -/
theorem cat_must_exit_with_te (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    must_exit_with code (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp := by
  intro Hte Hbm
  refine (must_exit_with_iff code (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp).mpr ?_
  refine exec_conseq segs _ _ _
    (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) ?_
  intro tr o h
  exact h.2

theorem cat_omni_run_te_code_unique (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (bufs : List (List byte)) (code code' : word) :
    to_wexit segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp (exits_with code') →
    code' = code := by
  intro Hte Hbm Hex
  have Hrun := cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm
  obtain ⟨tr, o, Hm, HQ⟩ := exec_realizes segs _ _ Hrun
  have Hx' := exec_sound segs _ _ Hex tr o Hm
  cases o with
  | OHalt c' =>
    obtain ⟨-, hxe⟩ := HQ
    exact Option.some.inj (Hx'.1.symm.trans hxe.1)
  | OError c' =>
    exact HQ.2.elim

/-- The omni equivalence for two exit-after-writes binaries whose
    `to_wexit` derivations emit the same buffers and exit code, at the two
    role budgets. -/
theorem cat_omni_strong_equiv_te
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (bufs : List (List byte)) (code : word)
    (inp : ProcInput) :
    to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  intro Hsource Htarget Hbm
  constructor
  · refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
          bufs code Hsource Hbm)) ?_
    intro tr o h
    exact never_errors_covered source_segs tr o (exits_with_never_errors code tr o h.2)
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp
        bufs code Hsource Hbm tr).trans
        (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
          bufs code Htarget Hbm tr).symm
    · refine (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp
        bufs code Htarget Hbm

/-- The `Equivalence`-level equivalence for two exit-after-writes binaries whose
    (symbolic, argv-dependent) `to_wexit` derivations emit the same buffers
    and exit code: both denote the same set of delivery choices. -/
theorem cat_strong_equiv_te
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bufs : List (List byte)) (code : word) (inp : ProcInput) :
    to_wexit source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    to_wexit target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) bufs code →
    bufs_modeled bufs →
    (modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp) ∧
     equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
           (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp)) := by
  intro Hsource Htarget Hbm
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm)
  · right
    constructor
    · intro tr
      exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
        Hsource Hbm tr).trans
        (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code
          Htarget Hbm tr).symm
    · exact cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code
        Htarget Hbm

/- #########################################################################
   CHANNEL-PARAMETRIC RESTATEMENT

   Everything above is hardwired to fd 1 (stdout).  A binary that reports on
   stderr has exactly the same SHAPE, with 2 in place of 1 and channel 2 in
   place of channel 1, so this section restates the write node and the
   write-then-exit relation over an ARBITRARY (fd, channel) pair.  Nothing
   above changes: `fd1chan_fdchan` and `to_wexit_ch_1` exhibit the fd-1
   development as the instance fd = ch = 1.
   ######################################################################### -/

/-- The fd is open on channel `ch`, and `ch` is not stdin (which
    `write_spec` rejects with -EBADF).  `fd` is stated already truncated
    to 32 bits, as `check_syscall` hands it to `check_write`. -/
def fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = some (FdEntry.FdChannel ch) ∧ w_is0 ch = false

theorem fd1chan_fdchan (model : Model) (H : fd1chan model) :
    fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) model := by
  unfold fdchan
  exact ⟨H, by decide⟩

theorem init_model_fdchan2 (reserved : List (word × word)) (brk0 mb sp : word)
    (lim : Int) (inp : ProcInput) :
    fdchan (BitVec.ofInt 64 2) (BitVec.ofInt 64 2) (init_model reserved brk0 mb sp lim inp) := by
  unfold fdchan
  exact ⟨rfl, by decide⟩

theorem write_ch_check_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte) (n : Nat) :
    fdchan fd ch model →
    fd32 fd = fd →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ n → n ≤ buf.length →
    check_write (sys_input segs ms x8)
      (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
      (with_copyins [(ms_gpr ms 1, n)]
        (mkEffect (len_word (buf.take n)) [] [])) model
      = .CheckOk model (List.map (event.WriteEv ch) (buf.take n)) := by
  intro Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2
  obtain ⟨Hfd, Hch⟩ := Hfdc
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have Hcw : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max := by
    unfold buf_modeled at Hcnt; omega
  have Hmc : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    rw_range_gate_false (ms_gpr ms 1) (ms_gpr ms 2) Hcw
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have hbig : (buf.length : Int) < two_pow_64 := by
    have hc : (ms_gpr ms 2).toNat < 2 ^ 64 := (ms_gpr ms 2).isLt
    have hc' : ((ms_gpr ms 2).toNat : Int) < (2 : Int) ^ 64 := by exact_mod_cast hc
    unfold two_pow_64
    omega
  have hret : (len_word (buf.take n)).toNat = n :=
    len_word_take_toNat buf n (by exact_mod_cast Hn2) hbig
  have Hg1 : decide (1 ≤ (n : Int)) = true := by
    rw [decide_eq_true_eq]; exact_mod_cast Hn1
  have Hg0 : (buf.length == 0) = false := by
    have h : buf.length ≠ 0 := by omega
    simp [h]
  unfold check_write
  simp only [Hg, H32, Hfd, in_mem_sys_input, write_source_of_rw _ _ _ Hcw,
    readable_bytes_full _ _ _ _ Hrb, Hg0, with_copyins, hret]
  rw [ite_eq_right (show ¬ ((w_is0 ch) = true) by rw [Hch]; decide)]
  rw [ite_eq_right (show ¬ ((!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = true)
    by rw [Hmc]; decide)]
  rw [ite_eq_right (show ¬ ((w_is0 (ms_gpr ms 2)) = true) by rw [Hc]; decide)]
  simp [Hg1, Hn2, access_ranges_eqb_refl]

theorem write_ch_ok_n (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte) (n : Nat) :
    fdchan fd ch model → fd32 fd = fd →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ n → n ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model
      (.ok (with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (buf.take n)) [] [])) model
          (List.map (event.WriteEv ch) (buf.take n))) := by
  intro Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2
  exact (syscall_spec_write segs ms x8 model _ Hno).mpr
    (check_write_sound_ok _ _ _ _ _ _ _ _
      (write_ch_check_n segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2))

theorem write_ch_ok_inv (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (eff : SyscallEffect) (model' : Model)
    (evs : List event) (buf : List byte) :
    fdchan fd ch model → fd32 fd = fd →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    1 ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      eff = with_copyins [(ms_gpr ms 1, n)]
              (mkEffect (len_word (buf.take n)) [] []) ∧ model' = model ∧
      evs = List.map (event.WriteEv ch) (buf.take n) := by
  intro Hfdc H32 Hno Hg Hr Hnb Hspec
  obtain ⟨Hfd, Hch⟩ := Hfdc
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc0 : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have Hspec' := (syscall_spec_write segs ms x8 model _ Hno).mp Hspec
  have Hc := check_write_complete_ok _ _ _ _ _ _ _ _ Hspec'
  unfold check_write at Hc
  simp only [Hg, H32, Hfd, in_mem_sys_input] at Hc
  rw [ite_eq_right (show ¬ ((w_is0 ch) = true) by rw [Hch]; decide)] at Hc
  by_cases hmr : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = true
  · rw [ite_eq_left hmr] at Hc
    exact nomatch Hc
  · rw [ite_eq_right hmr] at Hc
    rw [ite_eq_right (show ¬ ((w_is0 (ms_gpr ms 2)) = true) by rw [Hc0]; decide)] at Hc
    -- the source the transfer sees is the CLAMPED prefix of the range the
    -- call named -- `buf` itself for every count under `MAX_RW_COUNT`, and
    -- a prefix of it above, which the gate above admits at an in-range
    -- buffer
    simp only [write_source_prefix (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb] at Hc
    have hcpos : 1 ≤ (rw_count_clamp (ms_gpr ms 2)).toNat := by
      have h2 : (1 : Int) ≤ (ms_gpr ms 2).toNat := by omega
      have h3 : (1 : Int) ≤ rw_count_clamp (ms_gpr ms 2) := by
        unfold rw_count_clamp
        rw [Int.le_min]
        exact ⟨h2, by unfold MAX_RW_COUNT; decide⟩
      have h0 := (rw_count_clamp_range (ms_gpr ms 2)).1
      omega
    have hg0 : ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length == 0) = false := by
      have h2 : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length ≠ 0 := by
        rw [List.length_take]; omega
      cases hb : ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length == 0) with
      | false => rfl
      | true =>
        rw [beq_iff_eq] at hb
        exact absurd hb h2
    rw [ite_eq_right (show ¬ (((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length == 0) = true)
      by rw [hg0]; decide)] at Hc
    obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
    cases ws with
    | cons w ws' => simp at Hc
    | nil =>
      cases zs with
      | cons z zs' => simp at Hc
      | nil =>
        cases us with
        | cons u us' => simp at Hc
        | nil =>
          cases cs with
          | cons c cs' => simp at Hc
          | nil =>
            try simp only [] at Hc
            by_cases hg : (decide (1 ≤ (ret.toNat : Int)) &&
                decide ((ret.toNat : Int) ≤
                  ((buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).length : Int))) = true
            · rw [ite_eq_left hg] at Hc
              by_cases hr : access_ranges_eqb copyins
                  [(ms_gpr ms 1, ret.toNat)] = true
              · rw [ite_eq_left hr] at Hc
                cases Hc
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                obtain ⟨h1, h2⟩ := hg
                have hle_n : ret.toNat ≤ buf.length := by
                  rw [List.length_take] at h2
                  omega
                have hcopy : copyins = [(ms_gpr ms 1, ret.toNat)] :=
                  (access_ranges_eqb_eq _ _).mp hr
                have htake : (buf.take (rw_count_clamp (ms_gpr ms 2)).toNat).take ret.toNat
                    = buf.take ret.toNat := by
                  rw [List.take_take, Nat.min_eq_left]
                  rw [List.length_take] at h2
                  omega
                have hlen_ret : len_word (buf.take ret.toNat) = ret :=
                  len_word_firstn_ret ret buf ⟨by omega, by exact_mod_cast hle_n⟩
                refine ⟨ret.toNat, ?_, ?_, ?_, ?_, ?_⟩
                · omega
                · exact hle_n
                · rw [hcopy, hlen_ret]
                  rfl
                · rfl
                · rw [htake]
              · rw [ite_eq_right hr] at Hc
                exact absurd Hc (by simp)
            · rw [ite_eq_right hg] at Hc
              exact absurd Hc (by simp)

theorem write_ch_no_unmodeled (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (buf : List byte) :
    fdchan fd ch model → fd32 fd = fd →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    -- see `write1_no_unmodeled`: a zero count is genuinely unmodeled
    1 ≤ buf.length →
    ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled := by
  intro Hfdc H32 Hno Hg Hr Hcnt Hnb Hspec
  obtain ⟨Hfd, Hch⟩ := Hfdc
  have Hrb : read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = some buf := by
    rw [read_bytes_map_read_byte]; exact Hr
  have Hlen := read_bytes_map_length (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb
  have Hcw : ((ms_gpr ms 2).toNat : Int) ≤ rw_bytes_max := by
    unfold buf_modeled at Hcnt; omega
  have Hmc : (!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = false :=
    rw_range_gate_false (ms_gpr ms 1) (ms_gpr ms 2) Hcw
  have hblen : 0 < buf.length := by omega
  have hpos : 0 < (ms_gpr ms 2).toNat := by
    have h1 : (0 : Int) < (buf.length : Int) := by exact_mod_cast hblen
    omega
  have Hc0 : w_is0 (ms_gpr ms 2) = false := w_is0_pos _ hpos
  have Hspec' := (syscall_spec_write segs ms x8 model _ Hno).mp Hspec
  have Hc := check_write_complete_unmodeled (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) model
    (mkEffect (BitVec.ofInt 64 0) [] []) Hspec'
  unfold check_write at Hc
  simp only [Hg, H32, Hfd, in_mem_sys_input] at Hc
  rw [ite_eq_right (show ¬ ((w_is0 ch) = true) by rw [Hch]; decide)] at Hc
  rw [ite_eq_right (show ¬ ((!(modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2))) = true)
    by rw [Hmc]; decide)] at Hc
  rw [ite_eq_right (show ¬ ((w_is0 (ms_gpr ms 2)) = true) by rw [Hc0]; decide)] at Hc
  simp only [write_source_of_rw (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) Hcw,
    readable_bytes_full (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) buf Hrb] at Hc
  cases hb : (buf.length == 0) with
  | true =>
    rw [ite_eq_left hb] at Hc
    exact check_ret_only_no_unmodeled _ _ _ _ Hc
  | false =>
    rw [ite_eq_right (show ¬ ((buf.length == 0) = true) by rw [hb]; decide)] at Hc
    try simp only [] at Hc
    split at Hc
    · split at Hc <;> exact nomatch Hc
    · exact nomatch Hc

/-- split of `write_ch_ok_inv`, the channel analogue of
    `write1_ok_model`: the exit, killed and materialization-fault arms only
    need the model half. -/
theorem write_ch_ok_model (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (fd ch : word) (eff : SyscallEffect) (model' : Model)
    (evs : List event) (buf : List byte) :
    fdchan fd ch model → fd32 fd = fd →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    1 ≤ buf.length →
    Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
    model' = model := by
  intro Hfdc H32 Hno Hg Hr Hnb Hspec
  obtain ⟨n, -, -, -, hm, -⟩ :=
    write_ch_ok_inv segs ms x8 model fd ch eff model' evs buf
      Hfdc H32 Hno Hg Hr Hnb Hspec
  exact hm

/-- The channel-parametric `to_wexit`, with the same ret-oblivious write
    node.  (`ch` does not appear: the write node names only the FD.) -/
inductive to_wexit_ch (segs : List Segment) (fd : word) :
    machine_state → List (List byte) → word → Prop where
  | twc_exit (ms : machine_state) (x8 : word) :
      ms.ms_svc_pending = some x8 →
      is_exit_no x8 →
      to_wexit_ch segs fd ms [] (ms_gpr ms 0 &&& BitVec.ofInt 64 255)
  | twc_write (ms : machine_state) (x8 : word) (buf : List byte)
      (bufs : List (List byte)) (code : word) :
      ms.ms_svc_pending = some x8 →
      (x8.toNat : Int) = 64 →
      ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
      1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
         to_wexit_ch segs fd
           (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit_ch segs fd ms (buf :: bufs) code
  | twc_step (ms ms' : machine_state) (bufs : List (List byte)) (code : word) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wexit_ch segs fd ms' bufs code →
      to_wexit_ch segs fd ms bufs code

theorem msteps_to_wexit_ch (segs : List Segment) (fd : word)
    (ms ms' : machine_state) (bufs : List (List byte)) (code : word) :
    msteps segs ms ms' → to_wexit_ch segs fd ms' bufs code →
      to_wexit_ch segs fd ms bufs code := by
  intro H
  induction H with
  | mst_refl ms => intro Hw; exact Hw
  | mst_step ms ms' ms'' hsvc hstep hms ih =>
    intro Hw
    exact to_wexit_ch.twc_step ms ms' bufs code hsvc hstep (ih Hw)

theorem sstep_write_ch_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (model : Model) (x8 : word) (buf : List byte)
    (evs : List event) (st : step_to) :
    m_halted model = none →
    m_vm_lazy model = [] →
    fdchan fd ch model →
    ms.ms_svc_pending = some x8 →
    (x8.toNat : Int) = 64 →
    ms_gpr ms 0 = fd →
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf →
    buf_modeled buf →
    1 ≤ buf.length →
    sstep segs ⟨ms, model⟩ evs st →
    ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧
      evs = List.map (event.WriteEv ch) (buf.take n) ∧
      st = .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (buf.take n))), model⟩ := by
  intro Hh Hlazy Hfdc Hsvc Hno Hg Hr Hcnt Hnb Hss
  cases st with
  | SNext c' =>
    cases Hss with
    | instr ms0 model0 ms0' model0' hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall ms0 model0 x8' eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      obtain ⟨n, hn1, hn2, heff, hm1, hevs⟩ :=
        write_ch_ok_inv segs ms x8 model fd ch eff model1 evs buf
          Hfdc Hfd32 Hno Hg Hr Hnb hspec
      subst eff
      rw [hm1, materialize_model_accesses_no_lazy model _ Hlazy] at hmat
      cases hmat
      exact ⟨n, hn1, hn2, hevs, by rw [apply_effect_copyins_no_write]⟩
    | exit ms0 model0 x8' eff model1 evs0 code hh hsvc hspec hh' hk =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      have hm1 := write_ch_ok_model segs ms x8 model fd ch eff model1 _ buf
        Hfdc Hfd32 Hno Hg Hr Hnb hspec
      rw [hm1, Hh] at hh'
      exact nomatch hh'
    | killed ms0 model0 x8' eff model1 evs0 sig hh hsvc hspec hk =>
      exfalso
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      have hm1 := write_ch_ok_model segs ms x8 model fd ch eff model1 _ buf
        Hfdc Hfd32 Hno Hg Hr Hnb hspec
      rw [hm1, m_killed_of_m_halted_none model Hh] at hk
      exact nomatch hk
  | SError =>
    exfalso
    cases Hss with
    | instr_fault ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | instr_unmodeled ms0 model0 hh hsvc hacc =>
      exact absurd (hsvc.symm.trans Hsvc) (by simp)
    | syscall_materialization_fault ms0 model0 x8' eff model1 evs0 hh hsvc hspec hh' hmat =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      have hm1 := write_ch_ok_model segs ms x8 model fd ch eff model1 _ buf
        Hfdc Hfd32 Hno Hg Hr Hnb hspec
      rw [hm1, materialize_model_accesses_no_lazy model _ Hlazy] at hmat
      exact nomatch hmat
    | syscall_unmodeled ms0 model0 x8' hh hsvc hspec =>
      have hx : x8' = x8 := Option.some.inj (hsvc.symm.trans Hsvc)
      rw [hx] at hspec
      exact write_ch_no_unmodeled segs ms x8 model fd ch buf
        Hfdc Hfd32 Hno Hg Hr Hcnt Hnb hspec

/-- The fd-1 development IS the instance fd = ch = 1. -/
theorem to_wexit_ch_1 (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) :
    to_wexit segs ms bufs code →
    to_wexit_ch segs (BitVec.ofInt 64 1) ms bufs code := by
  intro H
  induction H with
  | tw_exit ms x8 hsvc hx8 => exact to_wexit_ch.twc_exit ms x8 hsvc hx8
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    exact to_wexit_ch.twc_write ms x8 buf bufs code hsvc hno hg hr hnb ih
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    exact to_wexit_ch.twc_step ms ms' bufs code hsvc hstep ih

theorem wevents_ch_1 (bufs : List (List byte)) :
    wevents_ch (BitVec.ofInt 64 1) bufs = wevents bufs := by
  induction bufs with
  | nil => rfl
  | cons b bs ih =>
    simp only [wevents_ch, wevents, ih]

/-!  They are checks, not  lemmas. -/

section Sanity

/-- The full-delivery event list of a one-byte buffer is one event. -/
example : (wevents_ch (BitVec.ofInt 64 1) [[BitVec.ofInt 8 65]]).length = 1 := by decide

/-- No buffers, no events. -/
example : wevents_ch (BitVec.ofInt 64 1) [] = [] := rfl

/-- `wevents` is the fd-1 instance, by computation. -/
example : wevents [[BitVec.ofInt 8 65], [BitVec.ofInt 8 66]] =
    wevents_ch (BitVec.ofInt 64 1) [[BitVec.ofInt 8 65], [BitVec.ofInt 8 66]] := by
  rw [wevents_ch_1]

/-- A one-byte buffer is inside the transfer the model judges. -/
example : buf_modeled [BitVec.ofInt 8 65] := by unfold buf_modeled; decide

/-- The empty buffer is the degenerate case. -/
example : buf_modeled [] := buf_modeled_nil

/-- Full delivery is a delivery choice. -/
example : wpick (BitVec.ofInt 64 1) [[BitVec.ofInt 8 65]]
    (List.map (event.WriteEv (BitVec.ofInt 64 1)) [BitVec.ofInt 8 65]) :=
  wpick_wevents _ _ (fun b hb => by
    simp only [List.mem_singleton] at hb
    subst hb
    decide)

end Sanity

end LinuxSem.Common.CatSim



