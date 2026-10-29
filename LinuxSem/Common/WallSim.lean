/-
  * Common.WallSim — the "write-all" retry node over a channel.

  TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.CatSim),
  built over the [LinuxProcessSem.Run] trace semantics and its omni
  reading [LinuxProcessSem.OmniRun].

  A channel write delivers a nondeterministic NONEMPTY prefix of the
  offered buffer (CatSim's delivered-length family).  Real binaries
  therefore wrap every program-level "write buf" in a put-style retry
  loop: after the write returns a0 = n (1 <= n <= len), the code
  advances the pointer by n, decrements the remaining count by n, and
  reissues the write iff the remainder is nonzero.  Each such loop
  performs one or more write syscalls whose deliveries concatenate to
  exactly the original buffer, so its trace contribution is exactly
  `[map (WriteEv ch) buf]` — independent of the chunking.

  [to_wall ms rest k] captures that shape: [ms] is a write-pending
  ecall state offering [rest] (nonempty) on [fd]; the machine delivers
  exactly [rest] across one or more (possibly short) channel writes,
  then reaches a state satisfying the continuation PREDICATE [k].
  [to_wall_tail ms rest k] is the between-syscalls form: the machine
  still owes [rest] (instruction steps, then — if [rest] is nonempty —
  another write-pending state; if [rest] is empty, a [k]-state).
  Because the continuation is a predicate, the node composes with any
  downstream shape (StreamSim's loop-head [lh_next], CatSim's
  [to_wexit], ...) without mutual induction across files.

  Conventions follow CatSim's [Section WithSegsCh]: generic over the
  loaded segments [segs] and an (fd, channel) pair with
  [fd32 fd = fd]; the pending syscall number is Z-characterized
  ([bv_unsigned x8 = 64%Z]); buffers are [list byte].

  NOTES.
 A consumer whose file has no FP state in scope supplies
    it with a local instance, the way `Common/ShapeAlg.lean` and
    `Common/SpinAlg.lean` already do
    (`local instance ... : FPState := PropExec.fx0`).
  - `Section WithSegsCh`'s `Variable segs`/`Variable fd ch` and its
    `Hypothesis Hfd32 : fd32 fd = fd` become EXPLICIT LEADING
    PARAMETERS on every declaration that mentions them, in that order,
    with `Hfd32` immediately after `fd ch` — the same convention
    `ExitSim.lean`, `CatSim.lean` and `MmapSim.lean` follow. Combined Scheme to_wall_mutind` has
    no Lean counterpart to *define*: Lean's mutual-inductive block
    generates `to_wall.rec` with one motive per member.   - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is `⟨sp, brk0, mb, rnd⟩`.
  - `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_and` is `&&&`,
    `bv_unsigned w` is `(w.toNat : Int)`, `firstn n l` is
    `List.take n l`, `skipn n l` is `List.drop n l`, `lia` is `omega`,
    `vm_compute; reflexivity` is `decide`.
  - `Forall` in `to_wallexit_bufs_nonempty` is spelled `∀ b ∈ bufs,
    1 ≤ b.length` (the repo-wide convention: Lean 4.31's core has no
    `List.Forall`).
  - DEPENDENCIES.  [Common.CatSim] supplies the channel-write facts
    ([sstep_write_ch_inv], [write_ch_ok_n]), [fdchan],
    [buf_modeled]/[bufs_modeled] (+ [buf_modeled_skipn]), [to_wexit],
    [msteps], [wevents] and [wevents_ch]; [Common.PropExec] supplies
    [mkst]/[getr]/[regupd]/[v_add]/[v_sub]/[v_addi] and the
    [arg_reg_*] index collapses; [Common.CatExec] supplies [adv_set];
    [Checks.Sys.Prelude] supplies [len_word_unsigned].
  The whole file is present: every definition and every
  lemma, including the mutual [to_wall]/[to_wall_tail] induction, the
  three star/exec readings ([to_wall_star_admits_mut],
  [to_wall_star_only_mut], [to_wall_exec_mut]), the [to_wallexit]
  fixpoint with its trace characterization and its four "bites", and
  the two run-level equivalences.  No proof hole, `admit`, extra postulate or
  `unsafe` is used.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
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
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SharedFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.WallSim
open LinuxSem.Common.SharedFacts (is_prefix_app_mono is_prefix_app_r)

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.CatExec

variable [fx : FPState]

/- =========================================================================
   The stdout/stderr fd literals are 32-bit-stable (the [fd32]
   truncation [check_syscall] applies leaves them unchanged) — the
   [Hfd32] instantiations every consumer needs.
   ========================================================================= -/

theorem fd32_1 : fd32 (BitVec.ofInt 64 1) = BitVec.ofInt 64 1 := by decide

theorem fd32_2 : fd32 (BitVec.ofInt 64 2) = BitVec.ofInt 64 2 := by decide

/- =========================================================================
   Put-loop arithmetic: the delivered length as a word, the pointer bump,
   and the count decrement, in the forms the per-binary retry-loop proofs
   meet (a0 = [len_word (firstn n bs)] after the write).
   ========================================================================= -/

/-- [bv_unsigned] of a modeled block length (all lengths here are far
    below 2^64). -/
theorem u_len_word {A : Type} (l : List A) (H : ((l.length : Int) < two_pow_64)) :
    ((len_word l).toNat : Int) = (l.length : Int) :=
  len_word_unsigned l H

/- [c_lts_0_pos] — [blez a0] falling through on a nonempty delivery —
   lives in PropExec, beside [c_lts_pos_0] and [c_lts_small], and so
   does [c_eq_0_of_u], the [beqz] on full delivery, beside
   [c_eq_0_false]. -/

theorem len_word_firstn_nat (n : Nat) (bs : List byte) (Hn : n ≤ bs.length) :
    len_word (bs.take n) = nat_to_word n := by
  unfold len_word nat_to_word
  rw [List.length_take, Nat.min_eq_left Hn]

theorem u_len_word_firstn (n : Nat) (bs : List byte) (Hn : n ≤ bs.length)
    (Hlen : ((bs.length : Int) < two_pow_64)) :
    ((len_word (bs.take n)).toNat : Int) = (n : Int) := by
  have htake : (bs.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left Hn]
  have hlen : (((bs.take n).length : Int) < two_pow_64) := by omega
  have h : ((len_word (bs.take n)).toNat : Int) = (((bs.take n).length : Int)) :=
    len_word_unsigned (bs.take n) hlen
  omega

/-- The pointer bump [add a1,a1,a0] after a delivery of [n] bytes lands
    on the address the suffix-read lemma [SeqExec.rdn_skipn] names. -/
theorem v_add_len_firstn (p : word) (n : Nat) (bs : List byte)
    (Hn : n ≤ bs.length) :
    v_add p (len_word (bs.take n)) = p + nat_to_word n := by
  rw [len_word_firstn_nat n bs Hn]
  unfold v_add nat_to_word
  bv_omega

/-- [v_add] variant landing on the canonical [Z_to_bv 64 (...)] form. -/
theorem v_add_len_firstn_Z (p : word) (n : Nat) (bs : List byte)
    (Hn : n ≤ bs.length) (Hlen : ((bs.length : Int) < two_pow_64)) :
    v_add p (len_word (bs.take n)) = BitVec.ofInt 64 ((p.toNat : Int) + (n : Int)) := by
  unfold v_add
  rw [u_len_word_firstn n bs Hn Hlen]

/-- [SeqExec.rdn_skipn]'s address, in the canonical form. -/
theorem word_add_nat_Z (p : word) (k : Nat) (Hk : ((k : Int) < two_pow_64)) :
    p + nat_to_word k = BitVec.ofInt 64 ((p.toNat : Int) + (k : Int)) := by
  unfold nat_to_word
  bv_omega

/-- The count decrement [sub a2,a2,a0] is the remainder's length. -/
theorem v_sub_len_firstn (n : Nat) (bs : List byte) (Hn : n ≤ bs.length)
    (Hlen : ((bs.length : Int) < two_pow_64)) :
    v_sub (len_word bs) (len_word (bs.take n)) = len_word (bs.drop n) := by
  have h1 : ((len_word (bs.take n)).toNat : Int) = (n : Int) :=
    u_len_word_firstn n bs Hn Hlen
  have h2 : ((len_word bs).toNat : Int) = (bs.length : Int) :=
    len_word_unsigned bs Hlen
  have h3 : ((len_word (bs.drop n)).toNat : Int) = (bs.length : Int) - (n : Int) := by
    rw [len_word_unsigned (bs.drop n) (by rw [List.length_drop]; omega), List.length_drop]
    omega
  have h4 : ((v_sub (len_word bs) (len_word (bs.take n))).toNat : Int)
      = (bs.length : Int) - (n : Int) := by
    rw [v_sub_small _ _ (by omega), h2, h1]
  apply BitVec.eq_of_toNat_eq
  omega

/- =========================================================================
   The write-all node.
   ========================================================================= -/

mutual
/-- [to_wall ms rest k]: [ms] is a write-pending ecall state offering
    [rest] (nonempty) on [fd]; the machine delivers exactly [rest] across
    one or more (possibly short) channel writes, then reaches a state
    satisfying [k].  The trace contribution is exactly
    [map (WriteEv ch) rest].  The write node is RET-OBLIVIOUS: the
    continuation must handle every delivered length [n]. -/
inductive to_wall (segs : List Segment) (fd : word) :
    machine_state → List byte → (machine_state → Prop) → Prop where
  | twl_write (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 64)
      (hg : ms_gpr ms 0 = fd)
      (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest)
      (hnb : 1 ≤ rest.length)
      (hcont : ∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) :
      to_wall segs fd ms rest k
/-- [to_wall_tail ms rest k]: the between-syscalls form — the machine still
    owes [rest] (instruction steps, then — if [rest] is nonempty — another
    write-pending state; if [rest] is empty, a [k]-state). -/
inductive to_wall_tail (segs : List Segment) (fd : word) :
    machine_state → List byte → (machine_state → Prop) → Prop where
  | twt_done (ms : machine_state) (k : machine_state → Prop) (hk : k ms) :
      to_wall_tail segs fd ms [] k
  | twt_more (ms : machine_state) (rest : List byte) (k : machine_state → Prop)
      (hnb : 1 ≤ rest.length) (hw : to_wall segs fd ms rest k) :
      to_wall_tail segs fd ms rest k
  | twt_step (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (ht : to_wall_tail segs fd ms' rest k) :
      to_wall_tail segs fd ms rest k
end

/-- The combined eliminator of the two members, with one motive each. -/
theorem to_wall_mutind (segs : List Segment) (fd : word)
    (P1 : machine_state → List byte → (machine_state → Prop) → Prop)
    (P2 : machine_state → List byte → (machine_state → Prop) → Prop)
    (h1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
        (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P2 (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      P1 ms rest k)
    (h2 : ∀ (ms : machine_state) (k : machine_state → Prop), k ms → P2 ms [] k)
    (h3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k → P1 ms rest k → P2 ms rest k)
    (h4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k → P2 ms' rest k → P2 ms rest k) :
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs fd ms rest k → P1 ms rest k) ∧
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs fd ms rest k → P2 ms rest k) :=
  ⟨fun ms rest k d =>
     to_wall.rec (motive_1 := fun ms rest k _ => P1 ms rest k)
       (motive_2 := fun ms rest k _ => P2 ms rest k) h1 h2 h3 h4 d,
   fun ms rest k d =>
     to_wall_tail.rec (motive_1 := fun ms rest k _ => P1 ms rest k)
       (motive_2 := fun ms rest k _ => P2 ms rest k) h1 h2 h3 h4 d⟩

/-- msteps-prepend glue (the ergonomic bridge per-binary loop proofs
    use, mirroring [CatSim.msteps_to_wexit]). -/
theorem msteps_to_wall_tail (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (rest : List byte) (k : machine_state → Prop) :
    msteps segs ms ms' → to_wall_tail segs fd ms' rest k →
      to_wall_tail segs fd ms rest k := by
  intro H
  induction H with
  | mst_refl ms => intro Hw; exact Hw
  | mst_step ms ms' ms'' hsvc hstep h ih =>
    intro Hw
    exact to_wall_tail.twt_step (ms := ms) (ms' := ms') (rest := rest) (k := k)
      hsvc hstep (ih Hw)

/-- An empty remainder is a straight instruction line to a [k]-state. -/
theorem to_wall_tail_nil_msteps (segs : List Segment) (fd : word) (ms : machine_state)
    (k : machine_state → Prop) :
    to_wall_tail segs fd ms [] k → ∃ ms', msteps segs ms ms' ∧ k ms' := by
  have c1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        rest.drop n = [] → ∃ ms', msteps segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) ms' ∧ k ms') →
      rest = [] → ∃ ms', msteps segs ms ms' ∧ k ms' := by
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hrest
    rw [hrest] at hnb
    simp at hnb
  have c2 : ∀ (ms : machine_state) (k : machine_state → Prop),
      k ms → [] = ([] : List byte) → ∃ ms', msteps segs ms ms' ∧ k ms' := by
    intro ms k hk _
    exact ⟨ms, msteps.mst_refl ms, hk⟩
  have c3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k →
      (rest = [] → ∃ ms', msteps segs ms ms' ∧ k ms') →
      rest = [] → ∃ ms', msteps segs ms ms' ∧ k ms' := by
    intro ms rest k hnb hw ih hrest
    rw [hrest] at hnb
    simp at hnb
  have c4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k →
      (rest = [] → ∃ ms'', msteps segs ms' ms'' ∧ k ms'') →
      rest = [] → ∃ ms'', msteps segs ms ms'' ∧ k ms'' := by
    intro ms ms' rest k hsvc hstep ht ih hrest
    obtain ⟨ms'', hm, hk⟩ := ih hrest
    exact ⟨ms'', msteps.mst_step ms ms' ms'' hsvc hstep hm, hk⟩
  obtain ⟨-, h2⟩ := to_wall_mutind segs fd _ _ c1 c2 c3 c4
  intro H
  exact h2 ms [] k H rfl

/- =========================================================================
   One-step inversion at the write-pending head, WITH the continuation: the
   delivered chunk is a nonempty prefix, and the remainder derivation
   continues at [skipn n rest].  This is the shape the downstream loop
   invariants ([sinv], [dinv]) and [to_wall_exec_mut] consume (an SError
   [st] is refuted by the [SNext] equation).
   ========================================================================= -/

theorem sstep_to_wall_inv (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop) (model : Model)
    (evs : List event) (st : step_to) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    buf_modeled rest → to_wall segs fd ms rest k →
    sstep segs ⟨ms, model⟩ evs st →
    ∃ n, 1 ≤ n ∧ n ≤ rest.length ∧
      evs = (rest.take n).map (event.WriteEv ch) ∧
      st = .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩ ∧
      to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
        (rest.drop n) k := by
  intro Hh Hlazy Hfdc Hbm Hw Hss
  revert Hbm
  cases Hw with
  | twl_write ms x8 rest k hsvc hno hg hr hnb hcont =>
    intro Hbm
    obtain ⟨n, hn1, hn2, hevs, hst⟩ :=
      sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
        Hh Hlazy Hfdc hsvc hno hg hr Hbm hnb Hss
    exact ⟨n, hn1, hn2, hevs, hst, hcont n hn1 hn2⟩

theorem to_wall_no_error_sstep (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd)
    (ms : machine_state) (rest : List byte) (k : machine_state → Prop) (model : Model)
    (evs : List event) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    buf_modeled rest → to_wall segs fd ms rest k →
    ¬ sstep segs ⟨ms, model⟩ evs .SError := by
  intro Hh Hlazy Hfdc Hbm Hw Hss
  obtain ⟨n, -, -, -, hst, -⟩ :=
    sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs .SError
      Hh Hlazy Hfdc Hbm Hw Hss
  simp at hst

/- =========================================================================
   Star admissibility: the retry loop realizes the full-buffer trace.  One
   syscall (full delivery) per node suffices as the witness.
   ========================================================================= -/

theorem to_wall_star_admits_mut (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (model : Model) (tr_k : List event) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs fd ms rest k → buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c) ∧
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs fd ms rest k → buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c) := by
  intro Hh Hlazy Hfdc
  have c1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length → buf_modeled (rest.drop n) →
        (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
        ∃ c, star segs ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩
          ((rest.drop n).map (event.WriteEv ch) ++ tr_k) c) →
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c := by
    -- twl_write: deliver everything in one syscall
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hbm hk
    obtain ⟨c, hstar⟩ :=
      ih rest.length hnb (Nat.le_refl _) (buf_modeled_skipn rest.length rest hbm) hk
    refine ⟨c, ?_⟩
    have hsplit : rest.map (event.WriteEv ch) ++ tr_k
        = (rest.take rest.length).map (event.WriteEv ch) ++
          ((rest.drop rest.length).map (event.WriteEv ch) ++ tr_k) := by
      rw [List.take_length, List.drop_length]
      simp
    rw [hsplit]
    refine star.step ⟨ms, model⟩ ((rest.take rest.length).map (event.WriteEv ch))
      ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take rest.length))), model⟩ _ c ?_ hstar
    exact sstep.syscall ms model x8
      (with_copyins [(ms_gpr ms 1, rest.length)]
        (mkEffect (len_word (rest.take rest.length)) [] []))
      model model ((rest.take rest.length).map (event.WriteEv ch)) Hh hsvc
      (write_ch_ok_n segs ms x8 model fd ch rest rest.length Hfdc Hfd32 hno hg hr hbm hnb
        (Nat.le_refl _))
      Hh (by rw [materialize_model_accesses_no_lazy model _ Hlazy])
  have c2 : ∀ (ms : machine_state) (k : machine_state → Prop), k ms →
      buf_modeled ([] : List byte) →
      (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((([] : List byte).map (event.WriteEv ch)) ++ tr_k) c := by
    -- twt_done: hand off to the continuation
    intro ms k hk hbm hK
    simpa using hK ms hk
  have c3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k →
      (buf_modeled rest →
        (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
        ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c) →
      buf_modeled rest →
      (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c := by
    -- twt_more
    intro ms rest k hnb hw ih hbm hk
    exact ih hbm hk
  have c4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k →
      (buf_modeled rest →
        (∀ ms'', k ms'' → ∃ c, star segs ⟨ms'', model⟩ tr_k c) →
        ∃ c, star segs ⟨ms', model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c) →
      buf_modeled rest →
      (∀ ms'', k ms'' → ∃ c, star segs ⟨ms'', model⟩ tr_k c) →
      ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c := by
    -- twt_step
    intro ms ms' rest k hsvc hstep ht ih hbm hk
    obtain ⟨c, hstar⟩ := ih hbm hk
    refine ⟨c, ?_⟩
    have hss : sstep segs ⟨ms, model⟩ [] (.SNext ⟨ms', model⟩) :=
      sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    simpa using star.step ⟨ms, model⟩ [] ⟨ms', model⟩
      ((rest.map (event.WriteEv ch)) ++ tr_k) c hss hstar
  exact to_wall_mutind segs fd _ _ c1 c2 c3 c4

theorem to_wall_star_admits (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (ms : machine_state) (rest : List byte)
    (k : machine_state → Prop) :
    to_wall segs fd ms rest k → buf_modeled rest → ∀ model tr_k,
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
    ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c := by
  intro Hw Hbm model tr_k Hh Hlazy Hfdc Hk
  exact (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).1 ms rest k Hw Hbm Hk

theorem to_wall_tail_star_admits (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (ms : machine_state) (rest : List byte)
    (k : machine_state → Prop) :
    to_wall_tail segs fd ms rest k → buf_modeled rest → ∀ model tr_k,
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ ms', k ms' → ∃ c, star segs ⟨ms', model⟩ tr_k c) →
    ∃ c, star segs ⟨ms, model⟩ ((rest.map (event.WriteEv ch)) ++ tr_k) c := by
  intro Hw Hbm model tr_k Hh Hlazy Hfdc Hk
  exact (to_wall_star_admits_mut segs fd ch Hfd32 model tr_k Hh Hlazy Hfdc).2 ms rest k Hw Hbm Hk

/- =========================================================================
   Star exhaustiveness: every trace out of the retry loop is a prefix of the
   full-buffer events followed by whatever the continuation admits.
   ========================================================================= -/

theorem to_wall_star_only_mut (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (model : Model) (T : List event) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs fd ms rest k → buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((rest.map (event.WriteEv ch)) ++ T)) ∧
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs fd ms rest k → buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((rest.map (event.WriteEv ch)) ++ T)) := by
  intro Hh Hlazy Hfdc
  have c1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length → buf_modeled (rest.drop n) →
        (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
        ∀ tr c, star segs ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩ tr c →
          is_prefix tr ((rest.drop n).map (event.WriteEv ch) ++ T)) →
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((rest.map (event.WriteEv ch)) ++ T) := by
    -- twl_write
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hbm hk tr c hstar
    cases hstar with
    | refl => exact is_prefix_nil _
    | step c1 evs c2 tr2 c3 hss hstar2 =>
      obtain ⟨n, hn1, hn2, hevs, hc2⟩ :=
        sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (.SNext c2)
          Hh Hlazy Hfdc hsvc hno hg hr hbm hnb hss
      subst hevs
      cases hc2
      have hsplit : rest.map (event.WriteEv ch) ++ T
          = (rest.take n).map (event.WriteEv ch) ++
            ((rest.drop n).map (event.WriteEv ch) ++ T) := by
        rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact is_prefix_app_mono _ _ _
        (ih n hn1 hn2 (buf_modeled_skipn n rest hbm) hk tr2 c hstar2)
  have c2 : ∀ (ms : machine_state) (k : machine_state → Prop), k ms →
      buf_modeled ([] : List byte) →
      (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((([] : List byte).map (event.WriteEv ch)) ++ T) := by
    -- twt_done
    intro ms k hk hbm hK tr c hstar
    simpa using hK ms tr c hk hstar
  have c3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k →
      (buf_modeled rest →
        (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
        ∀ tr c, star segs ⟨ms, model⟩ tr c →
          is_prefix tr ((rest.map (event.WriteEv ch)) ++ T)) →
      buf_modeled rest →
      (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((rest.map (event.WriteEv ch)) ++ T) := by
    -- twt_more
    intro ms rest k hnb hw ih hbm hk tr c hstar
    exact ih hbm hk tr c hstar
  have c4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k →
      (buf_modeled rest →
        (∀ ms'' tr c, k ms'' → star segs ⟨ms'', model⟩ tr c → is_prefix tr T) →
        ∀ tr c, star segs ⟨ms', model⟩ tr c →
          is_prefix tr ((rest.map (event.WriteEv ch)) ++ T)) →
      buf_modeled rest →
      (∀ ms'' tr c, k ms'' → star segs ⟨ms'', model⟩ tr c → is_prefix tr T) →
      ∀ tr c, star segs ⟨ms, model⟩ tr c →
        is_prefix tr ((rest.map (event.WriteEv ch)) ++ T) := by
    -- twt_step
    intro ms ms' rest k hsvc hstep ht ih hbm hk tr c hstar
    cases hstar with
    | refl => exact is_prefix_nil _
    | step c1 evs c2 tr2 c3 hss hstar2 =>
      obtain ⟨hevs, hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy hsvc hstep hss
      subst hevs
      cases hc2
      simpa using ih hbm hk tr2 c hstar2
  exact to_wall_mutind segs fd _ _ c1 c2 c3 c4

theorem to_wall_star_only (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (ms : machine_state) (rest : List byte)
    (k : machine_state → Prop) :
    to_wall segs fd ms rest k → buf_modeled rest → ∀ model T,
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ ms' tr c, k ms' → star segs ⟨ms', model⟩ tr c → is_prefix tr T) →
    ∀ tr c, star segs ⟨ms, model⟩ tr c →
      is_prefix tr ((rest.map (event.WriteEv ch)) ++ T) := by
  intro Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar
  exact (to_wall_star_only_mut segs fd ch Hfd32 model T Hh Hlazy Hfdc).1
    ms rest k Hw Hbm HK tr c Hstar

/- =========================================================================
   Ergonomic raw-ecall-record wrapper (mirrors CatExec/SeqExec's [_rec]
   entry points): the write node at the state [step_ecall] leaves.
   ========================================================================= -/

theorem twl_write_rec (segs : List Segment) (fd : word)
    (k : machine_state → Prop) (rest : List byte) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) :
    ((getr regs 17).toNat : Int) = 64 →
    reg_get regs 10 = fd →
    ms_read_bytes { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
                    ms_svc_pending := some (getr regs 17), ms_resv := none,
                    ms_fcsr := fx.fp_csr, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some rest →
    1 ≤ rest.length →
    (∀ n, 1 ≤ n → n ≤ rest.length →
       to_wall_tail segs fd (mkst (regupd regs 10 (len_word (rest.take n)))
         (v_addi pc 4) mem rom) (rest.drop n) k) →
    to_wall segs fd
      { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
        ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
        ms_mem := mem, ms_rom := rom }
      rest k := by
  intro H17 H10 Hr Hnb Hcont
  refine to_wall.twl_write _ (getr regs 17) rest k rfl H17 ?_ ?_ Hnb ?_
  · simp only [ms_gpr, arg_reg_0]
    exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]
    exact Hr
  · intro n hn1 hn2
    have hstep : advance_past_svc (set_gpr0
        { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
          ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
          ms_mem := mem, ms_rom := rom } (len_word (rest.take n)))
        = mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom :=
      adv_set regs pc _ mem rom _
    rw [hstep]
    exact Hcont n hn1 hn2

/- =========================================================================
   to_wallexit: an exit-after-writes run whose EVERY write goes through a
   put-style retry loop (a [to_wall] node).  Because each retry loop
   delivers exactly its full buffer — chunking-independently — the trace
   set of such a run is the ORIGINAL full-delivery form: the prefixes of
   [wevents_ch ch bufs ++ [ExitEv code fs]].  This is the wall-node
   counterpart of [CatSim.to_wexit] (whose ret-oblivious write node keeps
   serving binaries that genuinely propagate short deliveries).

   The base case [bufs = []] is [CatSim.to_wexit ms [] code] — the exit
   straight line — so all existing per-example exit-path lemmas apply
   unchanged.
   ========================================================================= -/

def to_wallexit (segs : List Segment) (fd : word) :
    List (List byte) → word → machine_state → Prop
  | [], code, ms => to_wexit segs ms [] code
  | buf :: rest, code, ms =>
      1 ≤ buf.length ∧ to_wall_tail segs fd ms buf (to_wallexit segs fd rest code)

/-- Every finite wall derivation bottoms out in a continuation state
    (deliver everything at each write). -/
theorem to_wall_k_ex_mut (segs : List Segment) (fd : word) :
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs fd ms rest k → ∃ ms', k ms') ∧
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs fd ms rest k → ∃ ms', k ms') := by
  have c1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length → ∃ ms', k ms') →
      ∃ ms', k ms' := by
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih
    exact ih rest.length hnb (Nat.le_refl _)
  have c2 : ∀ (ms : machine_state) (k : machine_state → Prop), k ms → ∃ ms', k ms' := by
    intro ms k hk
    exact ⟨ms, hk⟩
  have c3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k → (∃ ms', k ms') → ∃ ms', k ms' := by
    intro ms rest k hnb hw ih
    exact ih
  have c4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k → (∃ ms'', k ms'') → ∃ ms'', k ms'' := by
    intro ms ms' rest k hsvc hstep ht ih
    exact ih
  exact to_wall_mutind segs fd _ _ c1 c2 c3 c4

theorem to_wall_tail_k_ex (segs : List Segment) (fd : word) (ms : machine_state)
    (rest : List byte) (k : machine_state → Prop) :
    to_wall_tail segs fd ms rest k → ∃ ms', k ms' :=
  (to_wall_k_ex_mut segs fd).2 ms rest k

theorem to_wallexit_bufs_nonempty (segs : List Segment) (fd : word)
    (bufs : List (List byte)) (code : word) :
    ∀ ms, to_wallexit segs fd bufs code ms → ∀ b ∈ bufs, 1 ≤ b.length := by
  induction bufs with
  | nil =>
    intro ms hw b hb
    simp at hb
  | cons buf rest ih =>
    intro ms hw b hb
    obtain ⟨hnb, hw'⟩ := hw
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hnb
    · obtain ⟨ms', hk⟩ := to_wall_tail_k_ex segs fd ms buf _ hw'
      exact ih ms' hk b hb

/-- Single-instruction prepend, in the shape [StepTac.chain_step] consumes
    (the [to_wallexit] counterpart of [CatSim.to_wexit.tw_step]). -/
theorem twe_step (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word) :
    ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
    to_wallexit segs fd bufs code ms' → to_wallexit segs fd bufs code ms := by
  intro hsvc hstep hw
  cases bufs with
  | nil => exact to_wexit.tw_step ms ms' [] code hsvc hstep hw
  | cons buf rest =>
    obtain ⟨hnb, hw'⟩ := hw
    exact ⟨hnb, to_wall_tail.twt_step (ms := ms) (ms' := ms') (rest := buf)
      (k := to_wallexit segs fd rest code) hsvc hstep hw'⟩

theorem msteps_to_wallexit (segs : List Segment) (fd : word) (ms ms' : machine_state)
    (bufs : List (List byte)) (code : word) :
    msteps segs ms ms' → to_wallexit segs fd bufs code ms' →
      to_wallexit segs fd bufs code ms := by
  intro Hms
  cases bufs with
  | nil => exact msteps_to_wexit segs ms ms' [] code Hms
  | cons buf rest =>
    intro hw
    obtain ⟨hnb, hw'⟩ := hw
    exact ⟨hnb, msteps_to_wall_tail segs fd ms ms' buf
      (to_wallexit segs fd rest code) Hms hw'⟩

/- -------------------------------------------------------------------------
   The omni reading.  One mutual induction over [to_wall]/[to_wall_tail]
   gives, for every chunking at once, that the node emits exactly its buffer
   and then continues into a configuration satisfying the continuation's own
   judgment; [to_wallexit_exec] then chains the nodes and the exit into the
   exact full-delivery trace.  The star-only, star-admits and no-error lemmas
   below are its corollaries.
   ------------------------------------------------------------------------- -/

theorem to_wall_exec_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (model : Model) (Q : post) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall segs fd ms rest k → buf_modeled rest →
      (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o)) ∧
    (∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      to_wall_tail segs fd ms rest k → buf_modeled rest →
      (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o)) := by
  intro Hh Hlazy Hfdc
  have c1 : ∀ (ms : machine_state) (x8 : word) (rest : List byte)
      (k : machine_state → Prop),
      ms.ms_svc_pending = some x8 → (x8.toNat : Int) = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        to_wall_tail segs fd (advance_past_svc (set_gpr0 ms (len_word (rest.take n))))
          (rest.drop n) k) →
      (∀ n, 1 ≤ n → n ≤ rest.length → buf_modeled (rest.drop n) →
        (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
        exec segs ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩
          (fun tr o => ∃ tr', tr = (rest.drop n).map (event.WriteEv ch) ++ tr' ∧ Q tr' o)) →
      buf_modeled rest →
      (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o) := by
    -- twl_write: every delivered length is a successor, each covered by the IH
    intro ms x8 rest k hsvc hno hg hr hnb hcont ih hbm hK
    have hw : to_wall segs fd ms rest k :=
      to_wall.twl_write ms x8 rest k hsvc hno hg hr hnb hcont
    refine exec.step ⟨ms, model⟩ _ Hh ?_ ?_ ?_
    · -- progress: deliver everything in one syscall
      refine ⟨(rest.take rest.length).map (event.WriteEv ch),
        .SNext ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take rest.length))), model⟩, ?_⟩
      exact sstep.syscall ms model x8
        (with_copyins [(ms_gpr ms 1, rest.length)]
          (mkEffect (len_word (rest.take rest.length)) [] []))
        model model ((rest.take rest.length).map (event.WriteEv ch)) Hh hsvc
        (write_ch_ok_n segs ms x8 model fd ch rest rest.length Hfdc Hfd32 hno hg hr hbm hnb
          (Nat.le_refl _))
        Hh (by rw [materialize_model_accesses_no_lazy model _ Hlazy])
    · -- no error
      intro evs hss
      obtain ⟨n, -, -, -, habs, -⟩ :=
        sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs .SError
          Hh Hlazy Hfdc hbm hw hss
      simp at habs
    · -- every successor
      intro evs c' hss
      obtain ⟨n, hn1, hn2, hevs, hc', -⟩ :=
        sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs (.SNext c')
          Hh Hlazy Hfdc hbm hw hss
      subst hevs
      cases hc'
      refine exec_conseq segs
        ⟨advance_past_svc (set_gpr0 ms (len_word (rest.take n))), model⟩ _ _
        (ih n hn1 hn2 (buf_modeled_skipn n rest hbm) hK) ?_
      rintro tr o ⟨tr', htr, hQ⟩
      refine ⟨tr', ?_, hQ⟩
      rw [htr, ← List.append_assoc, ← List.map_append, List.take_append_drop]
  have c2 : ∀ (ms : machine_state) (k : machine_state → Prop), k ms →
      buf_modeled ([] : List byte) →
      (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (([] : List byte).map (event.WriteEv ch)) ++ tr' ∧ Q tr' o) := by
    -- twt_done: the continuation's own judgment
    intro ms k hk hbm hK
    refine exec_conseq segs ⟨ms, model⟩ Q _ (hK ms hk) ?_
    rintro tr o hQ
    exact ⟨tr, by simp, hQ⟩
  have c3 : ∀ (ms : machine_state) (rest : List byte) (k : machine_state → Prop),
      1 ≤ rest.length → to_wall segs fd ms rest k →
      (buf_modeled rest →
        (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
        exec segs ⟨ms, model⟩
          (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o)) →
      buf_modeled rest →
      (∀ ms', k ms' → exec segs ⟨ms', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o) := by
    -- twt_more
    intro ms rest k hnb hw ih hbm hK
    exact ih hbm hK
  have c4 : ∀ (ms ms' : machine_state) (rest : List byte) (k : machine_state → Prop),
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wall_tail segs fd ms' rest k →
      (buf_modeled rest →
        (∀ ms'', k ms'' → exec segs ⟨ms'', model⟩ Q) →
        exec segs ⟨ms', model⟩
          (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o)) →
      buf_modeled rest →
      (∀ ms'', k ms'' → exec segs ⟨ms'', model⟩ Q) →
      exec segs ⟨ms, model⟩
        (fun tr o => ∃ tr', tr = (rest.map (event.WriteEv ch)) ++ tr' ∧ Q tr' o) := by
    -- twt_step: one silent instruction
    intro ms ms' rest k hsvc hstep ht ih hbm hK
    refine exec_step_only segs ⟨ms, model⟩ _ [] ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih hbm hK
  exact to_wall_mutind segs fd _ _ c1 c2 c3 c4

/-- The exit straight line at the bottom of every [to_wallexit]: the
    [bufs = []] fragment of [CatSim.to_wexit], which needs no channel
    assumption. -/
theorem to_wexit_nil_exec_aux (segs : List Segment) (ms : machine_state)
    (bufs : List (List byte)) (code : word) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] →
    to_wexit segs ms bufs code → bufs = [] →
    exec segs ⟨ms, model⟩
      (fun tr o => tr = [event.ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  intro Hh Hlazy Hte
  induction Hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro _
    refine exec_step_only segs ⟨ms, model⟩
      (fun tr o => tr = [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
        ∧ exits_with (ms_gpr ms 0 &&& BitVec.ofInt 64 255) tr o)
      [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
      ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ ?_ ?_ ?_
    · exact sstep.exit ms model x8 (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model) []
        (ms_gpr ms 0 &&& BitVec.ofInt 64 255) Hh hsvc
        (exit_dispatch_ok (sys_input segs ms x8) model (by
          rw [in_sysno_sys_input]; exact hx8)) rfl rfl
    · intro evs st hss
      exact sstep_exit_inv segs ms model x8 evs st Hh hsvc hx8 hss
    · refine exec_halted segs
        ⟨ms, with_halted (ms_gpr ms 0 &&& BitVec.ofInt 64 255) model⟩ _ ?_ ?_
      · simp [m_halted_with_halted]
      · simp only [List.append_nil, true_and]
        refine ⟨?_, ?_⟩
        · simp [m_halted_with_halted]
        · simp [m_killed_with_halted]
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb hcont ih =>
    intro hbufs
    simp at hbufs
  | tw_step ms ms' bufs code hsvc hstep hte ih =>
    intro hbufs
    refine exec_step_only segs ⟨ms, model⟩ _ [] ⟨ms', model⟩ ?_ ?_ ?_
    · exact sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])
    · intro evs st hss
      exact sstep_instr_inv segs ms model ms' evs st Hlazy hsvc hstep hss
    · simpa using ih hbufs

theorem to_wexit_nil_exec (segs : List Segment) (ms : machine_state) (code : word)
    (model : Model) :
    m_halted model = none → m_vm_lazy model = [] →
    to_wexit segs ms [] code →
    exec segs ⟨ms, model⟩
      (fun tr o => tr = [event.ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  intro Hh Hlazy Hte
  exact to_wexit_nil_exec_aux segs ms [] code model Hh Hlazy Hte rfl

/-- THE judgment for a retry-loop run: exactly the full-delivery trace, then
    the exit, on every execution. -/
theorem to_wallexit_exec (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd)
    (bufs : List (List byte)) (code : word) :
    ∀ (ms : machine_state) (model : Model),
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    exec segs ⟨ms, model⟩
      (fun tr o => tr = wevents_ch ch bufs ++ [event.ExitEv code (m_fs model)] ∧
        exits_with code tr o) := by
  induction bufs with
  | nil =>
    intro ms model Hh Hlazy Hfdc Hbm Hw
    simpa only [wevents_ch, List.nil_append] using
      to_wexit_nil_exec segs ms code model Hh Hlazy Hw
  | cons buf rest ih =>
    intro ms model Hh Hlazy Hfdc Hbm Hw
    obtain ⟨hnb, hw⟩ := Hw
    have hb : buf_modeled buf := Hbm buf (by simp)
    have hbs : bufs_modeled rest := fun b hb' => Hbm b (by simp [hb'])
    refine exec_conseq segs ⟨ms, model⟩ _ _
      ((to_wall_exec_mut segs fd ch Hfd32 model _ Hh Hlazy Hfdc).2 ms buf
        (to_wallexit segs fd rest code) hw hb
        (fun ms' hk => ih ms' model Hh Hlazy Hfdc hbs hk)) ?_
    rintro tr o ⟨tr', htr, heq, hx⟩
    refine ⟨?_, hx⟩
    rw [htr, heq]
    simp only [wevents_ch]
    rw [List.append_assoc]

/- -------------------------------------------------------------------------
   Star admissibility and exhaustiveness for [to_wallexit] — the ORIGINAL
   full-delivery trace set — as corollaries of [to_wallexit_exec].
   ------------------------------------------------------------------------- -/

theorem to_wallexit_star_admits (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (bufs : List (List byte)) (code : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ∃ c, star segs ⟨ms, model⟩
      (wevents_ch ch bufs ++ [event.ExitEv code (m_fs model)]) c := by
  intro Hh Hlazy Hfdc Hbm Hw
  obtain ⟨tr, o, Hm, Heq, Hx⟩ :=
    exec_realizes segs _ _
      (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  cases o with
  | OHalt c' =>
    obtain ⟨Hstar, -⟩ := mexec_halt_star segs ⟨ms, model⟩ tr (.OHalt c') Hm c' rfl
    exact ⟨c', by rw [← Heq]; exact Hstar⟩
  | OError c' => exact Hx.elim

/-- Bites.  The judgment names the trace AND the code: it does not exit with
    any other code, its trace is no other list, and it does not stay silent.
    ([to_wallexit_no_other_exit] would survive a postcondition that forgot
    the writes; [to_wallexit_trace_unique] is the one that pins them.) -/
theorem to_wallexit_no_other_exit (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (bufs : List (List byte)) (code : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ∀ code', code' ≠ code → ¬ exec segs ⟨ms, model⟩ (exits_with code') := by
  intro Hh Hlazy Hfdc Hbm Hw code' Hne Hex
  obtain ⟨tr, o, Hm, HQ, Hx⟩ :=
    exec_realizes segs _ _
      (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  have Hx' := exec_sound segs _ _ Hex tr o Hm
  cases o with
  | OHalt c' =>
    have h1 : m_halted c'.cfg_model = some code := Hx.1
    have h2 : m_halted c'.cfg_model = some code' := Hx'.1
    exact Hne (Option.some.inj (h2.symm.trans h1))
  | OError c' => exact Hx

theorem to_wallexit_trace_unique (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (bufs : List (List byte)) (code : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ∀ tr', tr' ≠ wevents_ch ch bufs ++ [event.ExitEv code (m_fs model)] →
    ¬ exec segs ⟨ms, model⟩ (fun tr _ => tr = tr') := by
  intro Hh Hlazy Hfdc Hbm Hw tr' Hne Hex
  obtain ⟨tr, o, Hm, Heq, Hx⟩ :=
    exec_realizes segs _ _
      (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  have Heq' := exec_sound segs _ _ Hex tr o Hm
  apply Hne
  rw [← Heq', Heq]

theorem to_wallexit_not_silent (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (bufs : List (List byte)) (code : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ¬ cosafe segs ⟨ms, model⟩ (fun tr => tr = []) := by
  intro Hh Hlazy Hfdc Hbm Hw Hc
  obtain ⟨c', Hstar⟩ :=
    to_wallexit_star_admits segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw
  have hnil := cosafe_star segs ⟨ms, model⟩ (fun tr => tr = []) _ c' Hc Hstar
  simp at hnil

theorem to_wallexit_star_only (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (bufs : List (List byte)) (code : word)
    (ms : machine_state) (model : Model) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ∀ tr c, star segs ⟨ms, model⟩ tr c →
      is_prefix tr (wevents_ch ch bufs ++ [event.ExitEv code (m_fs model)]) := by
  intro Hh Hlazy Hfdc Hbm Hw tr c Hstar
  obtain ⟨tr', o, -, HQ⟩ :=
    exec_realizes segs _ _
      (exec_star segs _ _ tr c
        (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar)
  obtain ⟨Heq, -⟩ := HQ
  rw [← Heq]
  exact is_prefix_app tr tr'

/- -------------------------------------------------------------------------
   No-error: a corollary of the omni judgment.
   ------------------------------------------------------------------------- -/

theorem to_wallexit_no_error (segs : List Segment) (fd ch : word)
    (Hfd32 : fd32 fd = fd) (ms : machine_state) (model : Model)
    (bufs : List (List byte)) (code : word) :
    m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
    bufs_modeled bufs → to_wallexit segs fd bufs code ms →
    ¬ reaches_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hfdc Hbm Hw
  refine exec_no_error segs ⟨ms, model⟩ ?_
  refine exec_conseq segs ⟨ms, model⟩ _ never_errors
    (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw) ?_
  intro tr o h
  exact exits_with_never_errors code tr o h.2

/- =========================================================================
   [to_wallexit] at fd 1, in [CatSim.to_wexit]'s argument order — the
   drop-in replacement for a per-binary [to_wexit] chain whose writes all go
   through put-style retry loops.
   ========================================================================= -/

abbrev wexit1 (segs : List Segment) (ms : machine_state) (bufs : List (List byte))
    (code : word) : Prop :=
  to_wallexit segs (BitVec.ofInt 64 1) bufs code ms

/- =========================================================================
   Run-level packaging: the ORIGINAL full-delivery statements, for binaries
   whose every write is a put-style retry loop.
   ========================================================================= -/

/-- The run-level omni judgment of a retry-loop run. -/
theorem wall_omni_run (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (bufs : List (List byte))
    (code : word) :
    fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) →
    bufs_modeled bufs →
    to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp
      (fun tr o => tr = wevents_ch ch bufs ++ [event.ExitEv code (in_fs inp)] ∧
        exits_with code tr o) := by
  intro Hfdc Hbm Hw
  show exec segs (init_config segs pc ph sp brk0 mb rnd lim inp)
    (fun tr o => tr = wevents_ch ch bufs ++ [event.ExitEv code (in_fs inp)] ∧
      exits_with code tr o)
  exact to_wallexit_exec segs fd ch Hfd32 bufs code _
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl Hfdc Hbm Hw

theorem wall_obs_iff (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (bufs : List (List byte))
    (code : word) :
    fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) →
    bufs_modeled bufs →
    to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ is_prefix tr (wevents_ch ch bufs ++ [event.ExitEv code (in_fs inp)]) := by
  intro Hfdc Hbm Hw tr
  refine exec_obs_iff segs _ _ ?_ tr
  refine exec_conseq segs _ _ _
    (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code
      Hfdc Hbm Hw) ?_
  rintro tr' o ⟨Heq, Hx⟩
  exact ⟨Heq, exits_with_never_errors code tr' o Hx⟩

theorem wall_no_error_run (fd ch : word) (Hfd32 : fd32 fd = fd)
    (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word)
    (rnd : EntryDraw) (lim : Int) (inp : ProcInput) (bufs : List (List byte))
    (code : word) :
    fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) →
    bufs_modeled bufs →
    to_wallexit segs fd bufs code
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro Hfdc Hbm Hw
  refine exec_no_error segs _ ?_
  refine exec_conseq segs _ _ _
    (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code
      Hfdc Hbm Hw) ?_
  rintro tr o ⟨-, Hx⟩
  exact exits_with_never_errors code tr o Hx

/-- The omni equivalence for two retry-loop exit-after-writes binaries
    emitting the same buffers and exit code, at the two role budgets. -/
theorem wall_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (bufs : List (List byte)) (code : word) (inp : ProcInput) :
    to_wallexit source_segs (BitVec.ofInt 64 1) bufs code
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    to_wallexit target_segs (BitVec.ofInt 64 1) bufs code
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    bufs_modeled bufs →
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  intro Hsource Htarget Hbm
  have HfdS : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) :=
    fd1chan_fdchan _ (init_model_fd1chan _ _ _ _ _ _)
  have HfdT : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) :=
    fd1chan_fdchan _ (init_model_fd1chan _ _ _ _ _ _)
  constructor
  · refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (wall_omni_run (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
          source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
          HfdS Hbm Hsource)) ?_
    rintro tr o ⟨-, Hx⟩
    exact never_errors_covered source_segs tr o (exits_with_never_errors code tr o Hx)
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (wall_obs_iff (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
        HfdS Hbm Hsource tr).trans
        (wall_obs_iff (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
          target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
          HfdT Hbm Htarget tr).symm
    · refine (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact wall_no_error_run (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
        HfdT Hbm Htarget

/-- The [Equivalence]-level equivalence for two retry-loop exit-after-writes
    binaries emitting the same buffers and exit code — the statement
    [CatSim.cat_strong_equiv_te] had before short channel writes. -/
theorem wall_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (bufs : List (List byte)) (code : word) (inp : ProcInput) :
    to_wallexit source_segs (BitVec.ofInt 64 1) bufs code
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    to_wallexit target_segs (BitVec.ofInt 64 1) bufs code
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) →
    bufs_modeled bufs →
    modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
            (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  intro Hsource Htarget Hbm
  have HfdS : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) :=
    fd1chan_fdchan _ (init_model_fd1chan _ _ _ _ _ _)
  have HfdT : fdchan (BitVec.ofInt 64 1) (BitVec.ofInt 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) :=
    fd1chan_fdchan _ (init_model_fd1chan _ _ _ _ _ _)
  constructor
  · exact no_error_run_modeled source_segs rpc rph rsp rbrk rmb rrnd rlim inp
      (wall_no_error_run (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code HfdS Hbm Hsource)
  · right
    constructor
    · intro tr
      exact (wall_obs_iff (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
        HfdS Hbm Hsource tr).trans
        (wall_obs_iff (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
          target_segs apc aph asp abrk amb arnd alim inp bufs code
          HfdT Hbm Htarget tr).symm
    · exact wall_no_error_run (BitVec.ofInt 64 1) (BitVec.ofInt 64 1) fd32_1
        target_segs apc aph asp abrk amb arnd alim inp bufs code HfdT Hbm Htarget

/-!  They are checks, not  lemmas. -/

section Sanity

/-- The delivered prefix's [len_word] is the delivered length. -/
example : len_word (([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte).take 1)
    = nat_to_word 1 :=
  len_word_firstn_nat 1 _ (by decide)

/-- The pointer bump after a one-byte delivery. -/
example : v_add (BitVec.ofInt 64 100)
      (len_word (([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte).take 1))
    = BitVec.ofInt 64 100 + nat_to_word 1 :=
  v_add_len_firstn _ 1 _ (by decide)

/-- The count decrement is the remainder's length. -/
example : v_sub (len_word ([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte))
      (len_word (([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte).take 1))
    = len_word (([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte).drop 1) :=
  v_sub_len_firstn 1 _ (by decide) (by decide)

/-- [bv_unsigned] of a two-byte block. -/
example : ((len_word ([BitVec.ofInt 8 65, BitVec.ofInt 8 66] : List byte)).toNat : Int) = 2 :=
  u_len_word _ (by decide)

/-- The stdout/stderr literals are 32-bit stable, by computation. -/
example : fd32 (BitVec.ofInt 64 1) = BitVec.ofInt 64 1 := fd32_1
example : fd32 (BitVec.ofInt 64 2) = BitVec.ofInt 64 2 := fd32_2

/-- [wexit1] IS [to_wallexit] at fd 1. -/
example (ms : machine_state) (c : word) :
    wexit1 [] ms [] c = to_wallexit [] (BitVec.ofInt 64 1) [] c ms := rfl

/-- The fd-1 event list is [CatSim.wevents], by computation. -/
example : wevents_ch (BitVec.ofInt 64 1) [[BitVec.ofInt 8 65]]
    = wevents [[BitVec.ofInt 8 65]] :=
  wevents_ch_1 _

end Sanity

end LinuxSem.Common.WallSim

